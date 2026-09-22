//! The compiler-owned join boundary in MIR.
//!
//! Join syntax is currently expanded into ordinary Rust methods. This pass
//! runs while MIR is still in the initial analysis phase, before cleanup and
//! coroutine state transformation, and ties those bodies back to the resolved
//! `JoinDefinitions` descriptor. It records a small, typed operation stream
//! and conservative value-flow facts on the MIR body. The stream is the
//! hand-off point for compiler-owned CFA and proof-consuming lowering. The
//! narrow state-token storage pass consumes positive certificates here; wider
//! claim/completion/fusion lowering remains future work. It deliberately does
//! not infer semantics from generated method names or call into the library
//! runtime.

use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxHasher, FxIndexSet};
use rustc_hir::def_id::{DefId, LOCAL_CRATE, LocalDefId};
use rustc_index::Idx;
use rustc_middle::bug;
use rustc_middle::middle::joins::{
    JoinBodyRole, JoinCall, JoinCallEdge, JoinCallTargetKind, JoinCfaBodyRecord,
    JoinCfaClosureFact, JoinCfaConstraint, JoinCfaConstraintKind, JoinCfaContextFrame,
    JoinCfaFunctionFact,
    JoinCfaContextFrameKind, JoinCfaContextInstance, JoinCfaContextSummary, JoinCfaCrateSummary,
    JoinCfaEffects, JoinCfaFlowState, JoinCfaInstanceFact, JoinCfaInstanceStatus, JoinCfaRejection,
    JoinCfaSide, JoinCfaSummary, JoinCfaValue, JoinCfaValueFact, JoinChannelOccupancyFact,
    JoinEndpointEscape, JoinEndpointEscapeKind, JoinFusionFact, JoinInstanceClosedness,
    JoinInstanceClosednessReason, JoinLocalFact, JoinLoweringStrategy, JoinMirOperation,
    JoinOccupancyFact, JoinOperationKind, JoinQueueBound, JoinStateTokenLowering,
    JoinStateMachineProof, JoinStateMachineRule,
    JoinStateTokenProof, JoinStateTokenRejection, JoinStateTokenStatus, JoinStateTokenTransition,
    JoinStateTokenTransitionKind, JoinValueFlow, JoinValueFlowKind, JoinValueState,
};
use rustc_middle::mir::interpret::Scalar;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{
    self, AggregateKind, Body, CastKind, JoinIntrinsic, Location, Operand, Place, RETURN_PLACE,
    Rvalue, Statement, StatementKind, TerminatorKind,
};
use rustc_middle::ty::{self, GenericArgsRef, Ty, TyCtxt};
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_session::config::JoinCfaMode;
use rustc_span::Spanned;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fs;
use std::hash::{Hash, Hasher};

use crate::{MirPass, PassPolicy};

pub(super) struct JoinSemanticOps;

/// Consume a positive state-token certificate at the generated dynamic
/// endpoint constructor.  This is deliberately a separate pass from
/// `JoinSemanticOps`: the crate-level CFA query snapshots bodies by running
/// the semantic collector itself, so asking that query from the collector
/// would create a cycle.  The compiler interface forces the query before
/// borrow checking and this pass runs afterwards on the real pre-cleanup MIR.
pub(super) struct JoinStorageLowering;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum InstanceAlias {
    None,
    Unique { endpoint_def_id: u32, body_def_id: u32, block: u32, statement: u32 },
    Multiple,
    Unknown,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum FunctionAlias {
    None,
    Unique(u32),
    Multiple,
}

impl FunctionAlias {
    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::None, alias) | (alias, Self::None) => alias,
            (Self::Unique(left), Self::Unique(right)) if left == right => self,
            (Self::Multiple, _) | (_, Self::Multiple) => Self::Multiple,
            (Self::Unique(_), Self::Unique(_)) => Self::Multiple,
        }
    }
}

impl InstanceAlias {
    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::None, alias) | (alias, Self::None) => alias,
            (
                Self::Unique {
                    endpoint_def_id: left_endpoint,
                    body_def_id: left_body,
                    block: left_block,
                    statement: left_statement,
                },
                Self::Unique {
                    endpoint_def_id: right_endpoint,
                    body_def_id: right_body,
                    block: right_block,
                    statement: right_statement,
                },
            ) if left_endpoint == right_endpoint
                && left_body == right_body
                && left_block == right_block
                && left_statement == right_statement =>
            {
                self
            }
            (Self::Unknown, _) | (_, Self::Unknown) => Self::Unknown,
            (Self::Multiple, _) | (_, Self::Multiple) => Self::Multiple,
            (Self::Unique { .. }, Self::Unique { .. }) => Self::Multiple,
        }
    }
}

/// Locate the compiler descriptor for one body without consulting any later
/// MIR query. Returning the role separately keeps the generated frontend
/// shape out of the analysis itself.
fn body_descriptor<'tcx>(
    tcx: TyCtxt<'tcx>,
    local_def_id: LocalDefId,
) -> Option<(
    u32,
    u32,
    JoinBodyRole,
    u32,
    bool,
    bool,
    JoinQueueBound,
    Option<LocalDefId>,
    Option<u32>,
    Option<u32>,
)> {
    for endpoint in &tcx.join_definitions(()).endpoints {
        if endpoint.constructor_def_id == Some(local_def_id)
            || endpoint.scoped_constructor_def_id == Some(local_def_id)
        {
            return Some((
                endpoint.endpoint_def_id.map_or(u32::MAX, |id| id.index() as u32),
                0,
                JoinBodyRole::Constructor,
                0,
                false,
                endpoint.frontend_direct_unary,
                frontend_queue_bound(endpoint.frontend_queue_bound),
                endpoint.endpoint_def_id,
                None,
                None,
            ));
        }
        if let Some(channel) =
            endpoint.channels.iter().find(|channel| channel.method_def_id == local_def_id)
        {
            return Some((
                endpoint.endpoint_def_id.map_or(u32::MAX, |id| id.index() as u32),
                0,
                JoinBodyRole::Channel,
                endpoint.declared_arity,
                endpoint.declared_async_rule,
                endpoint.frontend_direct_unary,
                frontend_queue_bound(endpoint.frontend_queue_bound),
                endpoint.endpoint_def_id,
                Some(channel.index),
                None,
            ));
        }

        // The generated multi-rule endpoint has one shared dispatch method.
        // It is deliberately not attributed to an arbitrary source rule;
        // the rule-specific identity begins at the named reaction helper.
        if endpoint.rules.iter().any(|rule| rule.method_def_id == local_def_id) {
            return Some((
                endpoint.endpoint_def_id.map_or(u32::MAX, |id| id.index() as u32),
                local_def_id.index() as u32,
                JoinBodyRole::Dispatch,
                endpoint.declared_arity,
                endpoint.declared_async_rule,
                endpoint.frontend_direct_unary,
                frontend_queue_bound(endpoint.frontend_queue_bound),
                endpoint.endpoint_def_id,
                None,
                None,
            ));
        }

        for (rule_index, rule) in endpoint.rules.iter().enumerate() {
            if rule.method_def_id == local_def_id
                || rule.reaction_method_def_id == Some(local_def_id)
                || rule.body_def_ids.iter().any(|body_id| body_id == local_def_id)
            {
                return Some((
                    endpoint.endpoint_def_id.map_or(u32::MAX, |id| id.index() as u32),
                    rule.method_def_id.index() as u32,
                    if rule.method_def_id == local_def_id {
                        JoinBodyRole::Dispatch
                    } else {
                        JoinBodyRole::ReactionBody
                    },
                    rule.arity,
                    rule.is_async,
                    endpoint.frontend_direct_unary,
                    frontend_queue_bound(endpoint.frontend_queue_bound),
                    endpoint.endpoint_def_id,
                    None,
                    Some(rule_index as u32),
                ));
            }
        }
    }

    // Restricted unary endpoints do not emit a dispatch method.  Their
    // reaction is the nested body of the generated channel method (the outer
    // method constructs the caller-owned future and the nested coroutine owns
    // the reaction body).  Recover that identity through the normal HIR
    // parent chain instead of matching a generated closure name.  This keeps
    // inner channel calls visible to the typed MIR visitor while remaining
    // conservative for unrelated nested closures: only a body below the one
    // direct-unary channel is classified as a reaction.
    let mut ancestor = tcx.opt_parent(local_def_id.to_def_id());
    while let Some(ancestor_local) = ancestor.and_then(|ancestor| ancestor.as_local()) {
        for endpoint in &tcx.join_definitions(()).endpoints {
            if !endpoint.frontend_direct_unary || endpoint.channels.len() != 1 {
                continue;
            }
            let channel = &endpoint.channels[0];
            if channel.method_def_id != ancestor_local {
                continue;
            }
            let endpoint_def_id = endpoint.endpoint_def_id.map_or(u32::MAX, |id| id.index() as u32);
            // There is no generated dispatch DefId in this representation.
            // Use the channel method as the temporary rule anchor; the typed
            // channel/rule indices carried by the next descriptor revision
            // will replace this fallback without changing the parent walk.
            return Some((
                endpoint_def_id,
                channel.method_def_id.index() as u32,
                JoinBodyRole::ReactionBody,
                endpoint.declared_arity,
                endpoint.declared_async_rule,
                endpoint.frontend_direct_unary,
                frontend_queue_bound(endpoint.frontend_queue_bound),
                endpoint.endpoint_def_id,
                Some(channel.index),
                Some(0),
            ));
        }
        ancestor = tcx.opt_parent(ancestor_local.to_def_id());
    }
    None
}

fn frontend_queue_bound(bound: Option<u32>) -> JoinQueueBound {
    match bound {
        Some(0) => JoinQueueBound::Exact(0),
        Some(bound) => JoinQueueBound::AtMost(bound),
        None => JoinQueueBound::Unknown,
    }
}

/// Compute a cheap deterministic identity for the MIR snapshot consumed by
/// the local join proof. This is deliberately structural rather than a hash of
/// pretty-printed MIR: block/statement shape, terminator kinds and all typed
/// extracted facts are enough to reject a stale proof after the transformations
/// that can invalidate locations or ownership flow. It is not a cryptographic
/// certificate and must only be used as a conservative freshness guard.
fn join_mir_fingerprint<'tcx>(
    body: &Body<'tcx>,
    operations: &[JoinMirOperation],
    value_flows: &[JoinValueFlow],
    function_facts: &[JoinCfaFunctionFact],
    unknown_function_locals: &[u32],
    call_edges: &[JoinCallEdge],
) -> u64 {
    let mut hasher = FxHasher::default();
    body.local_decls.len().hash(&mut hasher);
    body.basic_blocks.len().hash(&mut hasher);
    for block in body.basic_blocks.iter() {
        block.statements.len().hash(&mut hasher);
        for statement in &block.statements {
            std::mem::discriminant(&statement.kind).hash(&mut hasher);
        }
        let terminator = block.terminator();
        std::mem::discriminant(&terminator.kind).hash(&mut hasher);
        terminator.successors().count().hash(&mut hasher);
    }
    operations.hash(&mut hasher);
    value_flows.hash(&mut hasher);
    function_facts.hash(&mut hasher);
    unknown_function_locals.hash(&mut hasher);
    call_edges.hash(&mut hasher);
    hasher.finish()
}

struct JoinBodyFacts {
    endpoint_def_id: Option<u32>,
    rule_def_id: Option<u32>,
    channel_index: Option<u32>,
    rule_index: Option<u32>,
    queue_bound: JoinQueueBound,
    operations: Vec<JoinMirOperation>,
    value_flows: Vec<JoinValueFlow>,
    closure_facts: Vec<(u32, Vec<u32>, u32, u32, u32)>,
    function_facts: Vec<JoinCfaFunctionFact>,
    unknown_function_locals: FxIndexSet<u32>,
    callable_locals: Vec<bool>,
    call_edges: Vec<JoinCallEdge>,
    escapes: FxIndexSet<u32>,
    endpoint_escapes: FxIndexSet<JoinEndpointEscape>,
    endpoint_locals: Vec<bool>,
    join_call_targets: FxHashMap<u32, JoinCallTarget>,
    suppress_endpoint_return_escape: bool,
    calls: u32,
    yields: u32,
    unknown_effects: u32,
}

impl JoinBodyFacts {
    fn operation(&mut self, kind: JoinOperationKind, location: Location) {
        self.operation_with_reply_channels(kind, location, std::iter::empty());
    }

    fn operation_with_reply_channels(
        &mut self,
        kind: JoinOperationKind,
        location: Location,
        reply_channel_indices: impl IntoIterator<Item = u32>,
    ) {
        self.operation_with_reply_channels_and_destination(
            kind,
            location,
            reply_channel_indices,
            None,
        );
    }

    fn operation_with_reply_channels_and_destination(
        &mut self,
        kind: JoinOperationKind,
        location: Location,
        reply_channel_indices: impl IntoIterator<Item = u32>,
        destination_local: Option<u32>,
    ) {
        self.operations.push(JoinMirOperation {
            kind,
            block: location.block.index() as u32,
            statement: location.statement_index as u32,
            group_def_id: self.endpoint_def_id,
            channel_index: self.channel_index,
            rule_index: self.rule_index,
            reply_channel_indices: reply_channel_indices.into_iter().collect(),
            queue_bound: self.queue_bound,
            endpoint_def_id: self.endpoint_def_id,
            rule_def_id: self.rule_def_id,
            receiver_local: None,
            destination_local,
            argument_locals: Box::new([]),
        });
    }

    fn operation_with_operands(
        &mut self,
        kind: JoinOperationKind,
        location: Location,
        receiver_local: Option<u32>,
        destination_local: Option<u32>,
        argument_locals: impl IntoIterator<Item = Option<u32>>,
        channel_index: Option<u32>,
        rule_index: Option<u32>,
        queue_bound: JoinQueueBound,
        endpoint_def_id: Option<u32>,
        rule_def_id: Option<u32>,
    ) {
        self.operations.push(JoinMirOperation {
            kind,
            block: location.block.index() as u32,
            statement: location.statement_index as u32,
            group_def_id: endpoint_def_id,
            channel_index,
            rule_index,
            reply_channel_indices: Box::new([]),
            queue_bound,
            endpoint_def_id,
            rule_def_id,
            receiver_local,
            destination_local,
            argument_locals: argument_locals.into_iter().collect(),
        });
    }

    fn record_moved_place<'tcx>(&mut self, place: &Place<'tcx>, kind: JoinEndpointEscapeKind) {
        // A move into a call transfers ownership to code that is outside this
        // body. Projections are intentionally widened to their base local: the
        // first CFA slice needs a sound escape bit, not field-sensitive alias
        // precision. The later solver can refine this with typed projections.
        self.escapes.insert(place.local.index() as u32);
        if place.projection.is_empty()
            && self.endpoint_locals.get(place.local.index()).copied().unwrap_or(false)
        {
            self.endpoint_escapes
                .insert(JoinEndpointEscape { local: place.local.index() as u32, kind });
        }
    }

    fn call_target(&self, callee: Option<LocalDefId>) -> JoinCallTarget {
        match callee {
            Some(def_id) => self
                .join_call_targets
                .get(&(def_id.index() as u32))
                .copied()
                .unwrap_or(JoinCallTarget::ordinary_local()),
            None => JoinCallTarget::unknown(),
        }
    }

    fn finish<'tcx>(
        self,
        body: &Body<'tcx>,
        body_def_id: u32,
        endpoint_def_id: u32,
        rule_def_id: u32,
        rule_index: Option<u32>,
        role: JoinBodyRole,
        arity: u32,
        is_async: bool,
        frontend_direct_unary: bool,
        queue_bound: JoinQueueBound,
        local_count: usize,
        solver_budget: usize,
    ) -> JoinCfaSummary {
        let mir_fingerprint = join_mir_fingerprint(
            body,
            &self.operations,
            &self.value_flows,
            &self.function_facts,
            &self.unknown_function_locals.iter().copied().collect::<Vec<_>>(),
            &self.call_edges,
        );
        let endpoint_escapes = self.endpoint_escapes.iter().copied().collect::<Vec<_>>();
        let closure_facts = self
            .closure_facts
            .into_iter()
            .map(|(destination, captures, closure_body_def_id, block, statement)| {
                JoinCfaClosureFact {
                    destination,
                    body_def_id: closure_body_def_id,
                    captures,
                    block,
                    statement,
                }
            })
            .collect::<Vec<_>>();
        let (local_facts, solver_steps, solver_complete, locally_closed) = solve_local_facts(
            local_count,
            &self.value_flows,
            &self.escapes,
            self.unknown_effects,
            solver_budget,
        );
        let (instance_closedness, instance_closedness_reason) = classify_instance_closedness(
            frontend_direct_unary,
            &endpoint_escapes,
            self.unknown_effects,
            solver_complete,
        );
        let occupancy = solve_body_occupancy(body, &self.operations);
        let channel_occupancy = solve_channel_occupancy(body, &self.operations);
        let rejection = if role != JoinBodyRole::ReactionBody {
            Some(JoinCfaRejection::NotReactionBody)
        } else if arity != 1 {
            Some(JoinCfaRejection::SharedPattern)
        } else if is_async {
            Some(JoinCfaRejection::Async)
        } else if self.yields != 0 {
            Some(JoinCfaRejection::Suspends)
        } else if self.calls != 0 {
            Some(JoinCfaRejection::Calls)
        } else if self.unknown_effects != 0 {
            Some(JoinCfaRejection::UnknownEffects)
        } else if !self.escapes.is_empty() {
            Some(JoinCfaRejection::Escapes)
        } else if !solver_complete {
            Some(JoinCfaRejection::SolverBudget)
        } else if !locally_closed {
            Some(JoinCfaRejection::NotClosed)
        } else {
            None
        };
        let lowering = select_lowering_strategy(frontend_direct_unary, role, rejection);

        JoinCfaSummary {
            body_def_id,
            endpoint_def_id,
            rule_def_id,
            rule_index,
            mir_fingerprint,
            role,
            arity,
            is_async,
            frontend_direct_unary,
            queue_bound,
            lowering,
            occupancy,
            channel_occupancy,
            instance_closedness,
            instance_closedness_reason,
            operations: self.operations,
            value_flows: self.value_flows,
            closure_facts,
            function_facts: self.function_facts,
            unknown_function_locals: self.unknown_function_locals.into_iter().collect(),
            local_facts,
            solver_steps,
            solver_complete,
            locally_closed,
            calls: self.calls,
            call_edges: self.call_edges,
            yields: self.yields,
            unknown_effects: self.unknown_effects,
            escapes: self.escapes.into_iter().collect(),
            endpoint_escapes,
            fusion: None,
            fusion_rejection: None,
            direct_candidate: rejection.is_none(),
            rejection,
        }
    }
}

fn select_lowering_strategy(
    frontend_direct_unary: bool,
    role: JoinBodyRole,
    rejection: Option<JoinCfaRejection>,
) -> JoinLoweringStrategy {
    // The direct future representation is already an ordinary Rust future at
    // the call boundary. Keep the proof gate explicit so a stale frontend
    // marker cannot authorize a lowering for a different body role.
    if frontend_direct_unary
        && role == JoinBodyRole::Channel
        && rejection.is_some_and(|reason| reason == JoinCfaRejection::NotReactionBody)
    {
        return JoinLoweringStrategy::DirectFuture;
    }

    // A body-local event trace does not prove a concrete instance's queue
    // bound: callers, loops, competing rules, and escapes are outside this
    // body. Fixed slots and pair matchers therefore remain unavailable until
    // the interprocedural instance proof is wired into this decision.
    JoinLoweringStrategy::Generic
}

fn is_endpoint_type<'tcx>(endpoint_def_id: LocalDefId, ty: Ty<'tcx>) -> bool {
    matches!(ty.kind(), ty::Adt(adt, _) if adt.did().as_local() == Some(endpoint_def_id))
}

/// Return whether a local can only carry a scalar value in the abstract
/// join domain.  Unknown Rust calls are common in lowered arithmetic and
/// bookkeeping paths; treating every result as an escaping closure is much
/// less precise than JCAM's `Prim` wildcard.  Composite values are scalar-like
/// only when their complete static shape is scalar-like: this covers the
/// tuple/array bookkeeping that Dovetail treats as primitive while still
/// rejecting references, ADTs, closures, function values, and aggregates which
/// may hide a join handle or callable value. Function items are stateless, but
/// an indirect call through one still needs a target-sensitive CFA edge rather
/// than being erased as an unrelated primitive.
fn join_cfa_is_primitive_type<'tcx>(ty: Ty<'tcx>) -> bool {
    match ty.kind() {
        ty::Bool
        | ty::Char
        | ty::Int(..)
        | ty::Uint(..)
        | ty::Float(..)
        | ty::Never => true,
        ty::Tuple(fields) => fields.iter().all(join_cfa_is_primitive_type),
        ty::Array(element, _) => join_cfa_is_primitive_type(*element),
        _ => false,
    }
}

fn join_cfa_is_callable_type<'tcx>(ty: Ty<'tcx>) -> bool {
    matches!(ty.kind(), ty::FnDef(..) | ty::FnPtr(..))
}

fn classify_instance_closedness(
    frontend_direct_unary: bool,
    endpoint_escapes: &[JoinEndpointEscape],
    unknown_effects: u32,
    solver_complete: bool,
) -> (JoinInstanceClosedness, JoinInstanceClosednessReason) {
    if frontend_direct_unary {
        return (JoinInstanceClosedness::Closed, JoinInstanceClosednessReason::FrontendDirectUnary);
    }
    if !endpoint_escapes.is_empty() {
        return (JoinInstanceClosedness::Open, JoinInstanceClosednessReason::EndpointHandleEscapes);
    }
    if !solver_complete {
        return (JoinInstanceClosedness::Unknown, JoinInstanceClosednessReason::SolverBudget);
    }
    if unknown_effects != 0 {
        return (JoinInstanceClosedness::Unknown, JoinInstanceClosednessReason::UnknownEffects);
    }
    (JoinInstanceClosedness::Unknown, JoinInstanceClosednessReason::RequiresInterprocedural)
}

#[derive(Copy, Clone)]
struct JoinCallTarget {
    kind: JoinCallTargetKind,
    endpoint_def_id: Option<u32>,
    channel_index: Option<u32>,
    rule_index: Option<u32>,
    queue_bound: JoinQueueBound,
    rule_def_id: Option<u32>,
    direct_method_def_id: Option<u32>,
}

impl JoinCallTarget {
    fn unknown() -> Self {
        Self {
            kind: JoinCallTargetKind::Unknown,
            endpoint_def_id: None,
            channel_index: None,
            rule_index: None,
            queue_bound: JoinQueueBound::Unknown,
            rule_def_id: None,
            direct_method_def_id: None,
        }
    }

    fn ordinary_local() -> Self {
        Self {
            kind: JoinCallTargetKind::OrdinaryLocal,
            endpoint_def_id: None,
            channel_index: None,
            rule_index: None,
            queue_bound: JoinQueueBound::Unknown,
            rule_def_id: None,
            direct_method_def_id: None,
        }
    }
}

/// Return whether a constructor result reaches a channel receiver through a
/// unique, non-aggregate local-to-local path.  The first result-forwarding
/// rewrite deliberately uses a tiny proof domain: every destination local may
/// have one source, but a branch/overwrite that supplies two different
/// sources rejects the rewrite.  This is stronger than a name-based pattern
/// and cheap enough to run while analysis MIR is still available.
fn unique_alias_reaches(flows: &[JoinValueFlow], source: u32, destination: u32) -> bool {
    let mut incoming = BTreeMap::<u32, u32>::new();
    for flow in flows {
        let Some(flow_source) = flow.source else { continue };
        if !matches!(
            flow.kind,
            JoinValueFlowKind::Copy | JoinValueFlowKind::Move | JoinValueFlowKind::Borrow
        ) {
            continue;
        }
        if let Some(previous) = incoming.insert(flow.destination, flow_source)
            && previous != flow_source
        {
            return false;
        }
    }

    let mut reachable = FxHashSet::default();
    let mut worklist = vec![source];
    while let Some(local) = worklist.pop() {
        if !reachable.insert(local) {
            continue;
        }
        for (&next, &previous) in &incoming {
            if previous == local {
                worklist.push(next);
            }
        }
    }
    reachable.contains(&destination)
}

/// Test reachability with a non-empty path.  This is used to reject only a
/// cycle that can revisit the constructor or channel operation itself; an
/// ordinary async body's poll/resume loop after the request is not a reason to
/// disable a preceding result-forwarding rewrite.
fn cfg_reaches<'tcx>(body: &Body<'tcx>, start: mir::BasicBlock, target: mir::BasicBlock) -> bool {
    let mut visited = FxHashSet::default();
    let mut worklist = body.basic_blocks[start].terminator().successors().collect::<Vec<_>>();
    while let Some(block) = worklist.pop() {
        if block == target {
            return true;
        }
        if !visited.insert(block) {
            continue;
        }
        worklist.extend(body.basic_blocks[block].terminator().successors());
    }
    false
}

/// Return the basic blocks which can reach themselves through a non-empty
/// control-flow path.  This is deliberately a conservative syntactic guard
/// for the first state-token certificate: a channel producer or re-emission
/// in such a block may execute more than once, so `AtMost(1)` cannot be
/// justified until interprocedural multiplicity analysis is available.
fn cfg_cyclic_blocks<'tcx>(body: &Body<'tcx>) -> Vec<u32> {
    body.basic_blocks
        .indices()
        .filter(|&block| cfg_reaches(body, block, block))
        .map(|block| block.index() as u32)
        .collect()
}

fn alias_closure(flows: &[JoinValueFlow], source: u32) -> FxHashSet<u32> {
    let mut outgoing = BTreeMap::<u32, BTreeSet<u32>>::new();
    for flow in flows {
        let Some(flow_source) = flow.source else { continue };
        if matches!(
            flow.kind,
            JoinValueFlowKind::Copy | JoinValueFlowKind::Move | JoinValueFlowKind::Borrow
        ) {
            outgoing.entry(flow_source).or_default().insert(flow.destination);
        }
    }
    let mut aliases = FxHashSet::default();
    let mut worklist = vec![source];
    while let Some(local) = worklist.pop() {
        if !aliases.insert(local) {
            continue;
        }
        if let Some(destinations) = outgoing.get(&local) {
            worklist.extend(destinations.iter().copied());
        }
    }
    aliases
}

/// Prove the reply is transferred directly into Rust's own `.await` lowering.
/// Follow executable moves in order, not just a whole-body alias set. Before
/// the await boundary allow only moves and non-executable bookkeeping. Calls,
/// borrows, projections, stores, branches, drops and returns refuse the proof.
/// After the boundary, polling, suspension and drop remain owned by rustc's
/// ordinary coroutine machinery; no join-specific poll loop is reconstructed.
fn reply_has_immediate_await<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    channel: &JoinCallEdge,
) -> bool {
    let start = mir::BasicBlock::from_usize(channel.block as usize);
    let TerminatorKind::Call { destination, target: Some(mut block), .. } =
        body.basic_blocks[start].terminator().kind
    else {
        return false;
    };
    let Some(mut reply) = destination.as_local() else { return false };
    let reply_ty = body.local_decls[reply].ty;
    let mut visited = FxHashSet::default();
    while visited.insert(block) {
        let data = &body.basic_blocks[block];
        for statement in &data.statements {
            match &statement.kind {
                StatementKind::Assign(assignment) => {
                    let (destination, value) = &**assignment;
                    let Rvalue::Use(Operand::Move(source), _) = value else { return false };
                    let Some(next) = destination.as_local() else { return false };
                    if source.as_local() != Some(reply)
                        || next == RETURN_PLACE
                        || body.local_decls[next].ty != reply_ty
                    {
                        return false;
                    }
                    reply = next;
                }
                StatementKind::StorageLive(local) | StatementKind::StorageDead(local)
                    if *local != reply => {}
                StatementKind::FakeRead(_)
                | StatementKind::PlaceMention(_)
                | StatementKind::AscribeUserType(..)
                | StatementKind::Nop => {}
                _ => return false,
            }
        }
        let terminator = data.terminator();
        match &terminator.kind {
            TerminatorKind::Goto { target } => block = *target,
            TerminatorKind::Call { func, args, destination, target: Some(_), .. } => {
                return terminator
                    .source_info
                    .span
                    .is_desugaring(rustc_span::DesugaringKind::Await)
                    && func.const_fn_def().is_some_and(|(callee, _)| {
                        Some(callee) == tcx.lang_items().into_future_fn()
                    })
                    && args.len() == 1
                    && matches!(&args[0].node, Operand::Move(place) if place.as_local() == Some(reply))
                    && destination
                        .as_local()
                        .is_some_and(|local| body.local_decls[local].ty == reply_ty);
            }
            _ => return false,
        }
    }
    false
}

/// Track whether a proven candidate endpoint is moved into an aggregate that
/// can outlive the current reaction. The coroutine aggregate created by the
/// reaction itself is owned state and is therefore allowed; ordinary closure,
/// tuple, struct and collection aggregates remain an escape until a later
/// interprocedural ownership proof can account for them.
struct CandidateEndpointUseFacts<'tcx> {
    local_types: Vec<Ty<'tcx>>,
    aliases: FxHashSet<u32>,
    captured: bool,
    unsupported: bool,
    allow_alias_flow: bool,
    constructor_location: (u32, u32),
    reaction_body_def_id: DefId,
}

impl<'tcx> Visitor<'tcx> for CandidateEndpointUseFacts<'tcx> {
    fn visit_assign(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>, location: Location) {
        let destination = place.as_local().map(|local| local.index() as u32);
        let source = match rvalue {
            Rvalue::Use(operand, _) => operand.place(),
            Rvalue::Ref(_, _, source) | Rvalue::Reborrow(_, _, source) => Some(*source),
            _ => None,
        };
        let direct_alias_flow = source.is_some_and(|source| {
            source.projection.is_empty()
                && self.aliases.contains(&(source.local.index() as u32))
                && destination.is_some_and(|destination| self.aliases.contains(&destination))
        });
        let aggregate_capture = match rvalue {
            Rvalue::Aggregate(_, operands) => operands.iter().any(|operand| {
                operand.place().is_some_and(|source| {
                    self.aliases.contains(&(source.local.index() as u32))
                        && source.projection.is_empty()
                })
            }),
            _ => false,
        };
        let coroutine_capture = aggregate_capture
            && destination
                .and_then(|destination| self.local_types.get(destination as usize))
                .is_some_and(|ty| {
                    matches!(
                        ty.kind(),
                        ty::Coroutine(def_id, _)
                            if *def_id == self.reaction_body_def_id
                    )
                });
        if aggregate_capture && !coroutine_capture {
            self.captured = true;
        }
        // Only a direct local copy/move/borrow, or the reaction's own
        // coroutine aggregate, is an understood propagation step. Casts,
        // projections, field stores and arbitrary aggregates are rejected
        // rather than being mistaken for a private endpoint alias.
        self.allow_alias_flow = direct_alias_flow || coroutine_capture;
        self.super_assign(place, rvalue, location);
        self.allow_alias_flow = false;
        if source.is_some_and(|source| {
            self.aliases.contains(&(source.local.index() as u32))
                && !direct_alias_flow
                && !coroutine_capture
        }) {
            self.unsupported = true;
        }
    }

    fn visit_local(
        &mut self,
        local: mir::Local,
        context: mir::visit::PlaceContext,
        location: Location,
    ) {
        if self.aliases.contains(&(local.index() as u32)) {
            let allowed = self.allow_alias_flow
                || context.is_drop()
                || context.is_storage_marker()
                || matches!(
                    context,
                    mir::visit::PlaceContext::NonUse(_)
                        | mir::visit::PlaceContext::NonMutatingUse(
                            mir::visit::NonMutatingUseContext::Inspect
                                | mir::visit::NonMutatingUseContext::PlaceMention
                                | mir::visit::NonMutatingUseContext::FakeBorrow
                        )
                );
            if !allowed {
                self.unsupported = true;
            }
        }
        self.super_local(local, context, location);
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: Location) {
        match &terminator.kind {
            // Call arguments are classified with their resolved join target
            // below. Skipping the generic visitor here avoids treating the
            // allowed `&candidate` receiver at the one proven channel call as
            // an escape; unknown/non-join calls are rejected by that edge
            // classification instead.
            TerminatorKind::Call { func, destination, .. } => {
                if func.const_fn_def().is_none()
                    && func
                        .place()
                        .is_some_and(|place| self.aliases.contains(&(place.local.index() as u32)))
                {
                    self.unsupported = true;
                }
                let destination_is_alias =
                    self.aliases.contains(&(destination.local.index() as u32));
                let is_constructor_destination = destination.projection.is_empty()
                    && destination_is_alias
                    && (location.block.index() as u32, location.statement_index as u32)
                        == self.constructor_location;
                // The constructor's own result is the only call result that
                // may introduce the candidate alias. Any later call that
                // overwrites an alias is an unknown replacement and must
                // reject the rewrite; otherwise a channel could be
                // retargeted after the original endpoint was discarded.
                if destination_is_alias && !is_constructor_destination {
                    self.unsupported = true;
                }
                return;
            }
            TerminatorKind::TailCall { func, .. } => {
                if func.const_fn_def().is_none()
                    && func
                        .place()
                        .is_some_and(|place| self.aliases.contains(&(place.local.index() as u32)))
                {
                    self.unsupported = true;
                }
                return;
            }
            TerminatorKind::Return => {
                if self.aliases.contains(&(RETURN_PLACE.index() as u32)) {
                    self.unsupported = true;
                }
            }
            TerminatorKind::Yield { value, .. } => {
                if value
                    .place()
                    .is_some_and(|place| self.aliases.contains(&(place.local.index() as u32)))
                {
                    self.unsupported = true;
                }
            }
            _ => {}
        }
        self.super_terminator(terminator, location);
    }
}

fn is_unscoped_constructor<'tcx>(tcx: TyCtxt<'tcx>, edge: &JoinCallEdge) -> bool {
    let (Some(endpoint_def_id), Some(callee)) = (edge.endpoint_def_id, edge.callee) else {
        return false;
    };
    tcx.join_definitions(()).endpoints.iter().any(|endpoint| {
        endpoint.endpoint_def_id.map(|id| id.index() as u32) == Some(endpoint_def_id)
            && endpoint.constructor_def_id.map(|id| id.index() as u32) == Some(callee)
    })
}

/// Ephemeral representation-selection capability. Holding the exclusive body
/// borrow prevents another pass from invalidating either validated call site
/// between proof construction and application. Never store this in join_info:
/// the serializable JoinFusionFact is an audit record, not this capability.
struct PrivateInstancePlan<'body, 'tcx> {
    body: &'body mut Body<'tcx>,
    channel: (Location, DefId),
    constructor: Option<(Location, DefId)>,
    fact: JoinFusionFact,
}

impl<'tcx> PrivateInstancePlan<'_, 'tcx> {
    fn apply(self, tcx: TyCtxt<'tcx>) -> JoinFusionFact {
        // No fallible proof checks may follow the first mutation. Both sites
        // and ABIs were checked before the exclusive capability was created.
        for (location, target) in self.constructor.into_iter().chain([self.channel]) {
            let data = &mut self.body.basic_blocks_mut()[location.block];
            assert_eq!(location.statement_index, data.statements.len());
            let terminator = data.terminator_mut();
            let TerminatorKind::Call { func, .. } = &mut terminator.kind else {
                unreachable!("validated private-instance call changed under exclusive borrow");
            };
            *func = Operand::function_handle(tcx, target, &[], terminator.source_info.span);
        }
        self.fact
    }
}

/// Proof-gated result forwarding for a private, synchronous unary channel.
///
/// The generated adapter has the same `&self`/payload/`Reply<T>` ABI as the
/// public channel method, but publishes an inline ready reply instead of
/// entering the dynamic matcher.  We only retarget a call when one concrete
/// constructor reaches exactly one channel use through a unique local alias;
/// competing join operations, endpoint escapes, and generic adapters remain on
/// the compatibility matcher path.  This is intentionally a MIR call-target
/// rewrite rather than a runtime symbol pattern match.
fn try_fuse_private_result<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    summary: &JoinCfaSummary,
    reaction_body_def_id: LocalDefId,
) -> (Option<JoinFusionFact>, Option<JoinCfaRejection>) {
    if tcx.sess.opts.unstable_opts.join_cfa != JoinCfaMode::Optimize
        || summary.role != JoinBodyRole::ReactionBody
    {
        return (None, None);
    }
    if !summary.endpoint_escapes.is_empty() {
        return (None, Some(JoinCfaRejection::Escape));
    }
    if summary.mir_fingerprint
        != join_mir_fingerprint(
            body,
            &summary.operations,
            &summary.value_flows,
            &summary.function_facts,
            &summary.unknown_function_locals,
            &summary.call_edges,
        )
    {
        // The proof is tied to the executable snapshot from which its local
        // locations and ownership facts were extracted. Any intervening MIR
        // rewrite must force a fresh analysis instead of consuming stale
        // coordinates.
        return (None, Some(JoinCfaRejection::StaleProof));
    }

    let targets = join_call_target_map(tcx);
    let mut constructors = Vec::new();
    let mut channels = Vec::new();
    let mut known_join_edges = 0usize;
    for edge in &summary.call_edges {
        match edge.target {
            JoinCallTargetKind::Constructor => constructors.push(edge),
            JoinCallTargetKind::Channel => channels.push(edge),
            JoinCallTargetKind::Dispatch | JoinCallTargetKind::ReactionBody => {
                known_join_edges += 1;
            }
            JoinCallTargetKind::Unknown | JoinCallTargetKind::OrdinaryLocal => {}
        }
    }
    if constructors.len() != 1 {
        return (
            None,
            Some(if constructors.is_empty() {
                JoinCfaRejection::UnknownOrigin
            } else {
                JoinCfaRejection::MultipleInstances
            }),
        );
    }
    if channels.len() != 1 {
        return (
            None,
            Some(if channels.is_empty() {
                JoinCfaRejection::UnknownOrigin
            } else {
                JoinCfaRejection::UnsupportedUse
            }),
        );
    }
    if known_join_edges != 0 {
        return (None, Some(JoinCfaRejection::CompetingRule));
    }
    let constructor = constructors[0];
    let channel = channels[0];
    if constructor.endpoint_def_id != channel.endpoint_def_id {
        return (None, Some(JoinCfaRejection::UnknownOrigin));
    }
    if !is_unscoped_constructor(tcx, constructor) {
        // `new_in_scope` has observable executor admission, cancellation and
        // tracing semantics. A ready-reply adapter cannot bypass those
        // effects, so scoped construction remains on the compatibility path.
        return (None, Some(JoinCfaRejection::SharedPolicy));
    }
    let (Some(constructor_destination), Some(channel_receiver), Some(channel_callee)) =
        (constructor.destination_local, channel.receiver_local, channel.callee)
    else {
        return (None, Some(JoinCfaRejection::UnsupportedUse));
    };
    if !unique_alias_reaches(&summary.value_flows, constructor_destination, channel_receiver) {
        return (None, Some(JoinCfaRejection::UnsupportedUse));
    }
    let candidate_aliases = alias_closure(&summary.value_flows, constructor_destination);
    for edge in &summary.call_edges {
        for (argument_index, local) in edge.argument_locals.iter().enumerate() {
            let Some(local) = local else { continue };
            if !candidate_aliases.contains(local) {
                continue;
            }
            let is_candidate_channel_receiver = edge.block == channel.block
                && edge.statement == channel.statement
                && edge.target == JoinCallTargetKind::Channel
                && argument_index == 0;
            if is_candidate_channel_receiver {
                continue;
            }
            let reason = match edge.target {
                JoinCallTargetKind::Dispatch | JoinCallTargetKind::ReactionBody => {
                    JoinCfaRejection::CompetingRule
                }
                JoinCallTargetKind::Unknown => JoinCfaRejection::UnknownCallee,
                JoinCallTargetKind::Constructor => JoinCfaRejection::MultipleInstances,
                JoinCallTargetKind::Channel | JoinCallTargetKind::OrdinaryLocal => {
                    JoinCfaRejection::Escape
                }
            };
            return (None, Some(reason));
        }
    }
    let endpoint_captured = {
        let mut endpoint_uses = CandidateEndpointUseFacts {
            local_types: body.local_decls.iter().map(|decl| decl.ty).collect(),
            aliases: candidate_aliases,
            captured: false,
            unsupported: false,
            allow_alias_flow: false,
            constructor_location: (constructor.block, constructor.statement),
            reaction_body_def_id: reaction_body_def_id.to_def_id(),
        };
        endpoint_uses.visit_body(&*body);
        endpoint_uses.captured || endpoint_uses.unsupported
    };
    if endpoint_captured {
        return (None, Some(JoinCfaRejection::Escape));
    }
    let constructor_block = mir::BasicBlock::from_usize(constructor.block as usize);
    let channel_block = mir::BasicBlock::from_usize(channel.block as usize);
    let dominators = body.basic_blocks.dominators();
    if !dominators.dominates(constructor_block, channel_block)
        || cfg_reaches(body, constructor_block, constructor_block)
        || cfg_reaches(body, channel_block, channel_block)
        || cfg_reaches(body, channel_block, constructor_block)
    {
        // A constructor that does not dominate its use, or any reachable
        // back-edge in the body, needs path-sensitive/loop reasoning that the
        // first certificate does not provide.
        return (None, Some(JoinCfaRejection::RecursiveOrCyclic));
    }

    if !reply_has_immediate_await(tcx, body, channel) {
        return (None, Some(JoinCfaRejection::UnsupportedUse));
    }

    let Some(target) = targets.get(&channel_callee) else {
        return (None, Some(JoinCfaRejection::UnknownCallee));
    };
    let Some(direct_method) = target.direct_method_def_id else {
        return (None, Some(JoinCfaRejection::UnknownCallee));
    };
    // Generic adapters need substitutions from the endpoint instance.  Keep
    // this first transform monomorphic until the typed generic argument map
    // is carried in JoinCall; rejecting them is safe and observable in CFA.
    let direct_def_id =
        DefId::local(rustc_span::def_id::DefIndex::from_usize(direct_method as usize));
    if tcx.generics_of(direct_def_id).count() != 0 {
        return (None, Some(JoinCfaRejection::UnsupportedUse));
    }
    // Representation selection is a paired rewrite. The empty endpoint is
    // valid only when its sole channel use is retargeted to the guarded
    // adapter. Validate both calls before mutating either of them.
    let definition = tcx.join_definitions(()).endpoints.iter().find(|endpoint| {
        endpoint.endpoint_def_id.map(|id| id.index() as u32) == constructor.endpoint_def_id
    });
    let Some(definition) = definition else {
        return (None, Some(JoinCfaRejection::UnknownOrigin));
    };
    if definition.endpoint_def_id.is_some_and(|id| tcx.adt_def(id).has_dtor(tcx)) {
        // A user destructor may observe the endpoint's representation. It is
        // not sufficient that the only channel invocation is private.
        return (None, Some(JoinCfaRejection::UnsupportedUse));
    }
    let private_constructor = definition
        .channels
        .iter()
        .find(|candidate| candidate.method_def_id.index() as u32 == channel_callee)
        .and_then(|candidate| candidate.private_constructor_def_id);
    if let Some(private) = private_constructor {
        if tcx.generics_of(private).count() != 0 {
            return (None, Some(JoinCfaRejection::UnsupportedUse));
        }
        let data = &body.basic_blocks[constructor_block];
        let TerminatorKind::Call { func, args, destination, target: Some(_), .. } =
            &data.terminator().kind
        else {
            return (None, Some(JoinCfaRejection::StaleProof));
        };
        if constructor.statement as usize != data.statements.len()
            || !args.is_empty()
            || destination.as_local().map(|local| local.index() as u32)
                != constructor.destination_local
            || func.const_fn_def().is_none_or(|(callee, args)| {
                callee.as_local() != definition.constructor_def_id || !args.is_empty()
            })
        {
            return (None, Some(JoinCfaRejection::StaleProof));
        }
    }
    let block = mir::BasicBlock::from_usize(channel.block as usize);
    let statement = channel.statement as usize;
    let Some(block_data) = body.basic_blocks.get(block) else {
        return (None, Some(JoinCfaRejection::StaleProof));
    };
    if statement != block_data.statements.len() {
        return (None, Some(JoinCfaRejection::StaleProof));
    }
    let terminator = block_data.terminator();
    let TerminatorKind::Call { func, args, destination, .. } = &terminator.kind else {
        return (None, Some(JoinCfaRejection::StaleProof));
    };
    // Check the concrete executable operands again at the consumption point.
    // The structural fingerprint deliberately remains cheap; it is not a
    // substitute for validating the callee, argument positions and result
    // destination that the proof actually reasoned about.
    let current_callee = func
        .const_fn_def()
        .and_then(|(def_id, _)| def_id.as_local())
        .map(|def_id| def_id.index() as u32);
    let current_destination = destination.as_local().map(|local| local.index() as u32);
    let current_arguments =
        args.iter().map(|arg| arg.node.place().map(|place| place.local.index() as u32));
    if current_callee != Some(channel_callee)
        || current_destination != channel.destination_local
        || current_arguments.ne(channel.argument_locals.iter().copied())
    {
        return (None, Some(JoinCfaRejection::StaleProof));
    }
    let plan = PrivateInstancePlan {
        body,
        channel: (Location { block, statement_index: statement }, direct_def_id),
        constructor: private_constructor.map(|id| {
            (
                Location {
                    block: constructor_block,
                    statement_index: constructor.statement as usize,
                },
                id.to_def_id(),
            )
        }),
        fact: JoinFusionFact {
            constructor_block: constructor.block,
            constructor_statement: constructor.statement,
            channel_block: channel.block,
            channel_statement: channel.statement,
            channel_method_def_id: channel_callee,
            direct_method_def_id: direct_method,
            private_constructor_def_id: private_constructor.map(|id| id.index() as u32),
            rewritten: true,
        },
    };
    (Some(plan.apply(tcx)), None)
}

fn join_call_target_map(tcx: TyCtxt<'_>) -> FxHashMap<u32, JoinCallTarget> {
    let mut targets = FxHashMap::default();
    for endpoint in &tcx.join_definitions(()).endpoints {
        let endpoint_def_id = endpoint.endpoint_def_id.map(|id| id.index() as u32);
        if let Some(constructor) = endpoint.constructor_def_id {
            targets.insert(
                constructor.index() as u32,
                JoinCallTarget {
                    kind: JoinCallTargetKind::Constructor,
                    endpoint_def_id,
                    channel_index: None,
                    rule_index: None,
                    queue_bound: frontend_queue_bound(endpoint.frontend_queue_bound),
                    rule_def_id: None,
                    direct_method_def_id: None,
                },
            );
        }
        if let Some(constructor) = endpoint.scoped_constructor_def_id {
            targets.insert(
                constructor.index() as u32,
                JoinCallTarget {
                    kind: JoinCallTargetKind::Constructor,
                    endpoint_def_id,
                    channel_index: None,
                    rule_index: None,
                    queue_bound: frontend_queue_bound(endpoint.frontend_queue_bound),
                    rule_def_id: None,
                    direct_method_def_id: None,
                },
            );
        }
        for channel in &endpoint.channels {
            targets.insert(
                channel.method_def_id.index() as u32,
                JoinCallTarget {
                    kind: JoinCallTargetKind::Channel,
                    endpoint_def_id,
                    channel_index: Some(channel.index),
                    rule_index: None,
                    queue_bound: frontend_queue_bound(endpoint.frontend_queue_bound),
                    rule_def_id: None,
                    direct_method_def_id: channel.direct_method_def_id.map(|id| id.index() as u32),
                },
            );
        }
        let mut dispatch_inserted = false;
        for (rule_index, rule) in endpoint.rules.iter().enumerate() {
            let rule_def_id = Some(rule.method_def_id.index() as u32);
            if !dispatch_inserted {
                // A shared dispatch method is one executable entry point for
                // the endpoint, not one rule-specific callee. Keeping a
                // source rule index here would make the last rule overwrite
                // the previous entries in this identity map.
                targets.insert(
                    rule.method_def_id.index() as u32,
                    JoinCallTarget {
                        kind: JoinCallTargetKind::Dispatch,
                        endpoint_def_id,
                        channel_index: None,
                        rule_index: None,
                        queue_bound: frontend_queue_bound(endpoint.frontend_queue_bound),
                        rule_def_id: None,
                        direct_method_def_id: None,
                    },
                );
                dispatch_inserted = true;
            }
            if let Some(reaction) = rule.reaction_method_def_id {
                targets.insert(
                    reaction.index() as u32,
                    JoinCallTarget {
                        kind: JoinCallTargetKind::ReactionBody,
                        endpoint_def_id,
                        channel_index: None,
                        rule_index: Some(rule_index as u32),
                        queue_bound: frontend_queue_bound(endpoint.frontend_queue_bound),
                        rule_def_id,
                        direct_method_def_id: None,
                    },
                );
            }
            for body in rule.body_def_ids {
                targets.insert(
                    body.index() as u32,
                    JoinCallTarget {
                        kind: JoinCallTargetKind::ReactionBody,
                        endpoint_def_id,
                        channel_index: None,
                        rule_index: Some(rule_index as u32),
                        queue_bound: frontend_queue_bound(endpoint.frontend_queue_bound),
                        rule_def_id,
                        direct_method_def_id: None,
                    },
                );
            }
        }
    }
    targets
}

/// Join the effects introduced by two context paths.  This is the same
/// monotone union used by the standalone Dovetail-shaped oracle: once an
/// unknown call, suspension or escape is observed it cannot disappear when
/// another path reaches the same bounded context.
fn join_context_effects(left: JoinCfaEffects, right: JoinCfaEffects) -> JoinCfaEffects {
    JoinCfaEffects {
        may_suspend: left.may_suspend || right.may_suspend,
        may_escape: left.may_escape || right.may_escape,
        may_external: left.may_external || right.may_external,
    }
}

fn context_effects_for_body(body: &JoinCfaBodyRecord) -> JoinCfaEffects {
    let mut effects = JoinCfaEffects {
        may_suspend: body.yields != 0,
        // `unknown_effects` is a body-local extraction fallback.  It includes
        // ordinary projection/rvalue shapes and calls which are unrelated to
        // the join protocol, so treating the counter as an endpoint escape
        // would make every real-world caller look open.  Endpoint ownership
        // is represented by the typed escape records below; opaque calls are
        // widened only when their extracted edge is associated with a join
        // endpoint.
        may_escape: !body.endpoint_escapes.is_empty(),
        may_external: false,
    };
    // A statically unresolved edge is an opaque operation even if the MIR
    // visitor did not need it to classify the body as a join reaction.  Keep
    // the distinction in the graph so a context reached through an unknown
    // callback cannot accidentally look private.
    for edge in &body.call_edges {
        // Generated endpoint/channel/reaction bodies contain calls into the
        // runtime adapter whose symbols are intentionally outside the join
        // declaration graph.  Treating those ABI calls as user-level
        // escapes would reject every generated witness.  Ordinary source
        // bodies, however, must be widened when they call through an unknown
        // function pointer, trait object, or unavailable body.
        if body.role == JoinBodyRole::Ordinary
            && edge.endpoint_def_id.is_some()
            && (edge.callee.is_none() || edge.target == JoinCallTargetKind::Unknown)
        {
            effects.may_external = true;
            effects.may_escape = true;
        }
    }
    effects
}

fn context_is_optimizable(
    local: JoinCfaEffects,
    inherited: JoinCfaEffects,
    truncated: bool,
) -> bool {
    !truncated
        && !local.may_suspend
        && !local.may_escape
        && !local.may_external
        && !inherited.may_suspend
        && !inherited.may_escape
        && !inherited.may_external
}

/// Run a bounded, compiler-owned semantic-history CFA over the typed MIR graph.
///
/// The earlier instance pass follows aliases to a concrete constructor, but
/// it has no notion of which call path reached a helper or reaction.  This
/// solver is the natural next layer: it reuses the already extracted typed
/// call edges/value-flow summaries, retains `k` MIR call-site frames, joins
/// effects at merged states and terminates under the same explicit work
/// budget used by the local analysis.  It deliberately does not ask LLVM to
/// rediscover protocol facts; LLVM sees neither the source channel graph nor
/// the dynamic instance identity after lowering.
#[allow(rustc::potential_query_instability)]
fn solve_context_cfa(
    bodies: &[JoinCfaBodyRecord],
    context_depth: usize,
    budget: usize,
) -> JoinCfaContextSummary {
    let by_id = bodies.iter().map(|body| (body.body_def_id, body)).collect::<FxHashMap<_, _>>();
    let local_effects = bodies
        .iter()
        .map(|body| (body.body_def_id, context_effects_for_body(body)))
        .collect::<FxHashMap<_, _>>();

    // A body with a known direct caller is not independently rooted.  Parent
    // identities cover generated nested reaction bodies whose closure call is
    // indirect in MIR; treating those as roots would lose the caller's
    // escape/suspension effects and make the proof unsound.
    let mut incoming = FxHashSet::default();
    let mut children = FxHashMap::<u32, Vec<u32>>::default();
    for body in bodies {
        if let Some(parent) = body.parent_body_def_id
            && by_id.contains_key(&parent)
        {
            incoming.insert(body.body_def_id);
            children.entry(parent).or_default().push(body.body_def_id);
        }
        for edge in &body.call_edges {
            if let Some(callee) = edge.callee {
                if by_id.contains_key(&callee) {
                    incoming.insert(callee);
                }
            }
        }
    }
    for body_ids in children.values_mut() {
        body_ids.sort_unstable();
    }

    type ContextKey = (u32, Vec<JoinCfaContextFrame>);
    let mut keys = FxHashMap::<ContextKey, usize>::default();
    let mut instances = Vec::<JoinCfaContextInstance>::new();
    let mut work = VecDeque::<usize>::new();
    let mut transitions = 0u32;
    let mut complete = budget != 0;

    let insert = |body_def_id: u32,
                  context: Vec<JoinCfaContextFrame>,
                  truncated: bool,
                  inherited: JoinCfaEffects,
                  keys: &mut FxHashMap<ContextKey, usize>,
                  instances: &mut Vec<JoinCfaContextInstance>,
                  work: &mut VecDeque<usize>,
                  complete: &mut bool|
     -> Option<usize> {
        let Some(local) = local_effects.get(&body_def_id).copied() else {
            *complete = false;
            return None;
        };
        let key = (body_def_id, context.clone());
        if let Some(&index) = keys.get(&key) {
            let instance = &mut instances[index];
            let joined = join_context_effects(instance.inherited_effects, inherited);
            let became_truncated = truncated && !instance.truncated;
            if joined != instance.inherited_effects || became_truncated {
                instance.inherited_effects = joined;
                instance.truncated |= truncated;
                instance.closed = !local.may_suspend
                    && !local.may_escape
                    && !local.may_external
                    && !joined.may_suspend
                    && !joined.may_escape
                    && !joined.may_external;
                instance.optimization_safe =
                    context_is_optimizable(local, joined, instance.truncated);
                work.push_back(index);
            }
            return Some(index);
        }
        if instances.len() >= budget {
            *complete = false;
            return None;
        }
        let closed = !local.may_suspend
            && !local.may_escape
            && !local.may_external
            && !inherited.may_suspend
            && !inherited.may_escape
            && !inherited.may_external;
        let optimization_safe = context_is_optimizable(local, inherited, truncated);
        let index = instances.len();
        keys.insert(key, index);
        instances.push(JoinCfaContextInstance {
            body_def_id,
            context,
            truncated,
            local_effects: local,
            inherited_effects: inherited,
            closed,
            optimization_safe,
        });
        work.push_back(index);
        Some(index)
    };

    let roots = bodies
        .iter()
        .filter(|body| !incoming.contains(&body.body_def_id))
        .map(|body| body.body_def_id)
        .collect::<Vec<_>>();
    for body_def_id in roots {
        insert(
            body_def_id,
            Vec::new(),
            false,
            JoinCfaEffects::default(),
            &mut keys,
            &mut instances,
            &mut work,
            &mut complete,
        );
    }

    // A graph can contain a recursive SCC with no path from an ordinary root
    // even when another unrelated component does have a root. Seed each such
    // component with unknown inherited effects instead of silently omitting
    // it. This is the finite-CFA equivalent of an unknown external entry: the
    // component is analysed, but none of its truncated/unknown contexts can
    // authorize a specialization.
    loop {
        while let Some(index) = work.pop_front() {
            let Some(instance) = instances.get(index).cloned() else { continue };
            let Some(body) = by_id.get(&instance.body_def_id).copied() else {
                complete = false;
                continue;
            };
            let inherited =
                join_context_effects(instance.inherited_effects, instance.local_effects);
            for edge in &body.call_edges {
                if transitions as usize >= budget {
                    complete = false;
                    break;
                }
                transitions = transitions.saturating_add(1);
                let Some(callee) = edge.callee else {
                    // The current state itself is not safe when it can execute an
                    // unresolved callback.  Widening the local instance records
                    // the negative fact even when there is no callee state to
                    // enqueue.
                    if body.role == JoinBodyRole::Ordinary
                        && edge.endpoint_def_id.is_some()
                        && let Some(current) = instances.get_mut(index)
                    {
                        current.inherited_effects = join_context_effects(
                            current.inherited_effects,
                            JoinCfaEffects {
                                may_suspend: false,
                                may_escape: true,
                                may_external: true,
                            },
                        );
                        current.closed = false;
                        current.optimization_safe = false;
                    }
                    continue;
                };
                if !by_id.contains_key(&callee) {
                    if body.role == JoinBodyRole::Ordinary {
                        complete = false;
                    }
                    if body.role == JoinBodyRole::Ordinary
                        && edge.endpoint_def_id.is_some()
                        && let Some(current) = instances.get_mut(index)
                    {
                        current.inherited_effects = join_context_effects(
                            current.inherited_effects,
                            JoinCfaEffects {
                                may_suspend: false,
                                may_escape: true,
                                may_external: true,
                            },
                        );
                        current.closed = false;
                        current.optimization_safe = false;
                    }
                    continue;
                }
                // Count source-level semantic events, not every generated ABI
                // call. JCAM's bounded history is made from construction and
                // emission events because JCAM has no ordinary function-call
                // graph. Rust also has ordinary local calls, so those are tagged
                // separately in the same bounded history. Dispatch and reaction
                // bodies are implementation plumbing: the Register/CreateGroup
                // event which led to them is propagated without another frame.
                let callee_body = by_id.get(&callee).copied();
                // A result-bearing unary call can be represented by the shared
                // rule/dispatch DefId even though its callee body is the typed
                // Channel body. Treat that edge as the source Register event;
                // the dispatch body reached after it remains transparent.
                let dispatch_is_channel_registration = edge.target == JoinCallTargetKind::Dispatch
                    && callee_body.is_some_and(|body| body.role == JoinBodyRole::Channel);
                let frame_kind = match edge.target {
                    JoinCallTargetKind::OrdinaryLocal => Some(JoinCfaContextFrameKind::RustCall),
                    JoinCallTargetKind::Constructor => Some(JoinCfaContextFrameKind::JoinCreate),
                    JoinCallTargetKind::Channel => Some(JoinCfaContextFrameKind::JoinRegister),
                    JoinCallTargetKind::Dispatch if dispatch_is_channel_registration => {
                        Some(JoinCfaContextFrameKind::JoinRegister)
                    }
                    JoinCallTargetKind::Dispatch
                    | JoinCallTargetKind::ReactionBody
                    | JoinCallTargetKind::Unknown => None,
                };
                let (context, truncated) = if let Some(kind) = frame_kind {
                    let semantic_group = if dispatch_is_channel_registration {
                        callee_body.and_then(|body| body.endpoint_def_id)
                    } else {
                        edge.group_def_id
                    };
                    let semantic_channel = if dispatch_is_channel_registration {
                        callee_body.and_then(|body| body.channel_index)
                    } else {
                        edge.channel_index
                    };
                    let frame = JoinCfaContextFrame {
                        kind,
                        caller_body_def_id: instance.body_def_id,
                        block: edge.block,
                        statement: edge.statement,
                        callee_body_def_id: callee,
                        group_def_id: semantic_group,
                        channel_index: semantic_channel,
                        rule_index: edge.rule_index,
                    };
                    let mut context = instance.context.clone();
                    let mut truncated = instance.truncated;
                    if context_depth == 0 {
                        truncated = true;
                        context.clear();
                    } else {
                        if context.len() == context_depth {
                            context.remove(0);
                            truncated = true;
                        }
                        context.push(frame);
                    }
                    (context, truncated)
                } else {
                    (instance.context.clone(), instance.truncated)
                };
                if insert(
                    callee,
                    context,
                    truncated,
                    inherited,
                    &mut keys,
                    &mut instances,
                    &mut work,
                    &mut complete,
                )
                .is_none()
                    && !complete
                {
                    break;
                }
            }
            // Closure/nested MIR bodies carry a parent identity even when the
            // closure construction is lowered without a direct typed call edge.
            // Preserve that ownership boundary as a synthetic CFA transition so
            // the child is not silently omitted from the graph. It is not a
            // semantic source event, so it does not consume one of the bounded
            // history frames.
            if let Some(child_ids) = children.get(&instance.body_def_id) {
                for &callee in child_ids {
                    if transitions as usize >= budget {
                        complete = false;
                        break;
                    }
                    transitions = transitions.saturating_add(1);
                    // Constructor/channel/dispatch shims are ABI adapters. Their
                    // endpoint receiver and reply plumbing are intentionally
                    // visible as escapes in the local MIR facts, but that does
                    // not mean a nested source reaction inherits an escaping
                    // application handle. Preserve suspension from a real body;
                    // discard adapter-only ownership effects at this synthetic
                    // parent edge.
                    let child_inherited = match body.role {
                        JoinBodyRole::Constructor
                        | JoinBodyRole::Channel
                        | JoinBodyRole::Dispatch => JoinCfaEffects {
                            may_suspend: inherited.may_suspend,
                            may_escape: false,
                            may_external: false,
                        },
                        JoinBodyRole::ReactionBody | JoinBodyRole::Ordinary => inherited,
                    };
                    if insert(
                        callee,
                        instance.context.clone(),
                        instance.truncated,
                        child_inherited,
                        &mut keys,
                        &mut instances,
                        &mut work,
                        &mut complete,
                    )
                    .is_none()
                        && !complete
                    {
                        break;
                    }
                }
            }
            if !complete && transitions as usize >= budget {
                break;
            }
        }
        if !complete {
            break;
        }
        let missing = bodies
            .iter()
            .map(|body| body.body_def_id)
            .find(|body_def_id| !keys.keys().any(|(id, _)| id == body_def_id));
        let Some(body_def_id) = missing else { break };
        if insert(
            body_def_id,
            Vec::new(),
            false,
            JoinCfaEffects { may_suspend: false, may_escape: true, may_external: true },
            &mut keys,
            &mut instances,
            &mut work,
            &mut complete,
        )
        .is_none()
        {
            break;
        }
    }

    instances.sort_by_key(|instance| {
        (instance.body_def_id, instance.context.len(), instance.context.clone())
    });
    JoinCfaContextSummary {
        context_depth: context_depth.min(u32::MAX as usize) as u32,
        instances,
        transitions,
        complete,
    }
}

// The high bit distinguishes synthetic channel variables from `(body, local)`
// variables. Body and local indices are both 32-bit in the compiler's local
// crate representation, so the remaining bits are sufficient for a channel
// coordinate without allocating an arena or exposing a runtime pointer.
const JOIN_CFA_CHANNEL_TAG: u64 = 1 << 63;

fn join_cfa_local_variable(body_def_id: u32, local: u32) -> u64 {
    ((body_def_id as u64) << 32) | local as u64
}

fn join_cfa_channel_variable(endpoint_def_id: u32, channel_index: Option<u32>) -> u64 {
    JOIN_CFA_CHANNEL_TAG
        | ((endpoint_def_id as u64) << 31)
        | channel_index.unwrap_or(u32::MAX) as u64
}

fn join_cfa_history(
    record: &JoinCfaBodyRecord,
    edge: &JoinCallEdge,
    depth: u32,
) -> Box<[JoinCfaContextFrame]> {
    if depth == 0 {
        return Vec::new().into_boxed_slice();
    }
    let Some(callee_body_def_id) = edge.callee else {
        return Vec::new().into_boxed_slice();
    };
    let kind = match edge.target {
        JoinCallTargetKind::Constructor => JoinCfaContextFrameKind::JoinCreate,
        JoinCallTargetKind::Channel
        | JoinCallTargetKind::Dispatch
        | JoinCallTargetKind::ReactionBody => JoinCfaContextFrameKind::JoinRegister,
        JoinCallTargetKind::OrdinaryLocal | JoinCallTargetKind::Unknown => {
            JoinCfaContextFrameKind::RustCall
        }
    };
    vec![JoinCfaContextFrame {
        kind,
        caller_body_def_id: record.body_def_id,
        block: edge.block,
        statement: edge.statement,
        callee_body_def_id,
        group_def_id: edge.group_def_id,
        channel_index: edge.channel_index,
        rule_index: edge.rule_index,
    }]
    .into_boxed_slice()
}

/// Extract the JCAM-style constraint graph from the typed MIR graph.
///
/// This is intentionally separate from `solve_context_cfa`: the latter
/// computes bounded call-string effects, while this graph carries abstract
/// channel/closure values and `Emit` edges. Keeping both views means the `k`
/// history is not lost when an ordinary Rust helper sits between two join
/// operations. In particular, a join registration is a semantic emission in
/// the graph even though its executable MIR is an ordinary call terminator.
#[allow(rustc::potential_query_instability)]
fn build_join_cfa_constraints(
    bodies: &[JoinCfaBodyRecord],
    context_depth: u32,
) -> Vec<JoinCfaConstraint> {
    let mut constraints = Vec::new();
    let mut seeded_channels = FxHashSet::default();

    for record in bodies {
        let variable = |local| join_cfa_local_variable(record.body_def_id, local);
        let primitive_local = |local: u32| record.primitive_locals.binary_search(&local).is_ok();
        let closure_destinations = record
            .closure_facts
            .iter()
            .map(|closure| closure.destination)
            .collect::<FxHashSet<_>>();
        for flow in &record.value_flows {
            let destination = variable(flow.destination);
            match (flow.kind, flow.source) {
                (
                    JoinValueFlowKind::Copy | JoinValueFlowKind::Move | JoinValueFlowKind::Borrow,
                    Some(source),
                ) => constraints.push(JoinCfaConstraint {
                    body_def_id: record.body_def_id,
                    block: flow.block,
                    statement: flow.statement,
                    kind: JoinCfaConstraintKind::Succ {
                        destination,
                        state: None,
                        source: variable(source),
                    },
                }),
                (JoinValueFlowKind::Aggregate, _) => {
                    // A typed closure aggregate is represented by the
                    // separate `Closure` constraint below.  Seeding it with
                    // `PRIM` as well would merge a callable value with an
                    // unrelated primitive and make every Emit look escaped;
                    // only non-callable aggregates receive the primitive
                    // approximation.
                    if !closure_destinations.contains(&flow.destination) {
                        constraints.push(JoinCfaConstraint {
                            body_def_id: record.body_def_id,
                            block: flow.block,
                            statement: flow.statement,
                            kind: JoinCfaConstraintKind::In {
                                destination,
                                state: JoinCfaFlowState::Foreground,
                                value: JoinCfaValue::Wildcard(JoinCfaSide::Primitive),
                            },
                        });
                    }
                }
                (JoinValueFlowKind::Unknown, _) | (_, None) => {
                    constraints.push(JoinCfaConstraint {
                        body_def_id: record.body_def_id,
                        block: flow.block,
                        statement: flow.statement,
                        kind: JoinCfaConstraintKind::In {
                            destination,
                            state: JoinCfaFlowState::Foreground,
                            value: JoinCfaValue::Wildcard(if primitive_local(flow.destination) {
                                JoinCfaSide::Primitive
                            } else {
                                JoinCfaSide::Outer
                            }),
                        },
                    });
                }
            }
        }

        for closure in &record.closure_facts {
            constraints.push(JoinCfaConstraint {
                body_def_id: record.body_def_id,
                block: closure.block,
                statement: closure.statement,
                kind: JoinCfaConstraintKind::Closure {
                    destination: variable(closure.destination),
                    body_def_id: closure.body_def_id,
                    captures: closure
                        .captures
                        .iter()
                        .copied()
                        .map(variable)
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                },
            });
        }

        for function in &record.function_facts {
            constraints.push(JoinCfaConstraint {
                body_def_id: record.body_def_id,
                block: function.block,
                statement: function.statement,
                kind: JoinCfaConstraintKind::In {
                    destination: variable(function.destination),
                    state: JoinCfaFlowState::Foreground,
                    value: JoinCfaValue::Function {
                        body_def_id: function.body_def_id,
                        origin: join_cfa_closure_origin(
                            record.body_def_id,
                            function.block,
                            function.statement,
                            function.body_def_id,
                        ),
                    },
                },
            });
        }

        for escape in &record.endpoint_escapes {
            constraints.push(JoinCfaConstraint {
                body_def_id: record.body_def_id,
                block: u32::MAX,
                statement: u32::MAX,
                kind: JoinCfaConstraintKind::Escape { source: variable(escape.local) },
            });
        }

        for edge in &record.call_edges {
            let destination = edge.destination_local.map(variable);
            let dispatch_channel_index = edge.callee.and_then(|callee| {
                bodies
                    .iter()
                    .find(|body| body.body_def_id == callee)
                    .filter(|body| body.role == JoinBodyRole::Channel)
                    .and_then(|body| body.channel_index)
            });
            // The direct-unary lowering can call the generated channel body
            // through the shared dispatch identity.  In an ordinary source
            // body that is still one semantic registration; in a generated
            // Channel body it is only the ABI hand-off to the matcher.
            let source_dispatch = edge.target == JoinCallTargetKind::Dispatch
                && record.role == JoinBodyRole::Ordinary
                && dispatch_channel_index.is_some();
            match edge.target {
                JoinCallTargetKind::Constructor => {
                    if let (Some(destination), Some(endpoint)) = (destination, edge.endpoint_def_id)
                    {
                        constraints.push(JoinCfaConstraint {
                            body_def_id: record.body_def_id,
                            block: edge.block,
                            statement: edge.statement,
                            kind: JoinCfaConstraintKind::In {
                                destination,
                                state: JoinCfaFlowState::Foreground,
                                value: JoinCfaValue::Channel {
                                    endpoint_def_id: endpoint,
                                    channel_index: None,
                                },
                            },
                        });
                    }
                }
                JoinCallTargetKind::Channel | JoinCallTargetKind::Dispatch
                    if edge.target == JoinCallTargetKind::Channel || source_dispatch =>
                {
                    let Some(endpoint) = edge.endpoint_def_id else { continue };
                    let channel_index = if source_dispatch {
                        dispatch_channel_index
                    } else {
                        edge.channel_index
                    };
                    let target = join_cfa_channel_variable(endpoint, channel_index);
                    if seeded_channels.insert(target) {
                        constraints.push(JoinCfaConstraint {
                            body_def_id: record.body_def_id,
                            block: edge.block,
                            statement: edge.statement,
                            kind: JoinCfaConstraintKind::In {
                                destination: target,
                                state: JoinCfaFlowState::Foreground,
                                value: JoinCfaValue::Channel {
                                    endpoint_def_id: endpoint,
                                    // A direct unary registration is often
                                    // classified as `Dispatch` by the call
                                    // target table even though its concrete
                                    // callee is the generated Channel body.
                                    // Preserve the recovered source channel
                                    // coordinate in the value as well as in
                                    // the target/history; leaving this as
                                    // `None` merges background gamma facts
                                    // from distinct channels.
                                    channel_index: channel_index,
                                },
                            },
                        });
                    }
                    let start = usize::from(edge.receiver_local.is_some());
                    let inputs = edge
                        .argument_locals
                        .iter()
                        .skip(start)
                        .flatten()
                        .map(|local| variable(*local))
                        .collect::<Vec<_>>()
                        .into_boxed_slice();
                    let history = if source_dispatch {
                        let mut history = join_cfa_history(record, edge, context_depth).into_vec();
                        if let Some(frame) = history.first_mut() {
                            frame.channel_index = channel_index;
                        }
                        history.into_boxed_slice()
                    } else {
                        join_cfa_history(record, edge, context_depth)
                    };
                    constraints.push(JoinCfaConstraint {
                        body_def_id: record.body_def_id,
                        block: edge.block,
                        statement: edge.statement,
                        kind: JoinCfaConstraintKind::Emit {
                            inputs,
                            target,
                            history,
                        },
                    });
                    if let Some(destination) = destination {
                        constraints.push(JoinCfaConstraint {
                            body_def_id: record.body_def_id,
                            block: edge.block,
                            statement: edge.statement,
                            kind: JoinCfaConstraintKind::In {
                                destination,
                                state: JoinCfaFlowState::Foreground,
                                value: JoinCfaValue::Wildcard(JoinCfaSide::Primitive),
                            },
                        });
                    }
                }
                JoinCallTargetKind::Channel => unreachable!("guarded channel edge was not handled"),
                // A generated dispatch call selects a closure that was
                // already reached from the source channel emission.  A
                // reaction-body call executes that selected transition.
                // Neither is a second JCAM `Emit`; recording either one as
                // such duplicates registration histories and can make the
                // same payload appear to escape through an unrelated rule.
                JoinCallTargetKind::Dispatch | JoinCallTargetKind::ReactionBody => {}
                JoinCallTargetKind::OrdinaryLocal => {
                    let Some(callee) = edge.callee else { continue };
                    for (position, source) in edge.argument_locals.iter().enumerate() {
                        let Some(source) = source else { continue };
                        constraints.push(JoinCfaConstraint {
                            body_def_id: record.body_def_id,
                            block: edge.block,
                            statement: edge.statement,
                            kind: JoinCfaConstraintKind::Succ {
                                destination: join_cfa_local_variable(callee, position as u32 + 1),
                                state: None,
                                source: variable(*source),
                            },
                        });
                    }
                    if let Some(destination) = destination {
                        constraints.push(JoinCfaConstraint {
                            body_def_id: record.body_def_id,
                            block: edge.block,
                            statement: edge.statement,
                            kind: JoinCfaConstraintKind::Succ {
                                destination,
                                state: None,
                                source: join_cfa_local_variable(callee, 0),
                            },
                        });
                    }
                }
                JoinCallTargetKind::Unknown => {
                    for source in edge.argument_locals.iter().flatten() {
                        if primitive_local(*source) {
                            continue;
                        }
                        constraints.push(JoinCfaConstraint {
                            body_def_id: record.body_def_id,
                            block: edge.block,
                            statement: edge.statement,
                            kind: JoinCfaConstraintKind::Escape { source: variable(*source) },
                        });
                    }
                    if let Some(destination) = destination {
                        let value = if edge
                            .destination_local
                            .is_some_and(primitive_local)
                        {
                            JoinCfaValue::Wildcard(JoinCfaSide::Primitive)
                        } else {
                            JoinCfaValue::Wildcard(JoinCfaSide::Outer)
                        };
                        constraints.push(JoinCfaConstraint {
                            body_def_id: record.body_def_id,
                            block: edge.block,
                            statement: edge.statement,
                            kind: JoinCfaConstraintKind::In {
                                destination,
                                state: JoinCfaFlowState::Foreground,
                            value,
                            },
                        });
                    }
                }
            }
        }
    }

    // A channel variable is the JCAM `gamma` value for the corresponding
    // endpoint.  In the expanded Rust frontend the matcher is represented by
    // a shared dispatch body rather than by a source-level closure literal at
    // every registration site.  Seed that typed dispatch closure here so an
    // Emit can instantiate its body exactly as JCAM instantiates a channel's
    // transition.  The old solver seeded only a synthetic `Channel` marker,
    // which carried no executable closure and therefore could never reach the
    // reaction constraints.
    let mut channels_by_endpoint = FxHashMap::<u32, FxHashSet<Option<u32>>>::default();
    for record in bodies {
        for edge in &record.call_edges {
            if matches!(edge.target, JoinCallTargetKind::Channel)
                && let Some(endpoint) = edge.endpoint_def_id
            {
                channels_by_endpoint.entry(endpoint).or_default().insert(edge.channel_index);
            }
        }
    }
    for record in bodies {
        let Some(endpoint) = record.endpoint_def_id else { continue };
        if record.role != JoinBodyRole::Dispatch {
            continue;
        }
        let Some(channels) = channels_by_endpoint.get(&endpoint) else { continue };
        for channel_index in channels {
            constraints.push(JoinCfaConstraint {
                body_def_id: record.body_def_id,
                block: u32::MAX,
                statement: u32::MAX,
                kind: JoinCfaConstraintKind::In {
                    destination: join_cfa_channel_variable(endpoint, *channel_index),
                    state: JoinCfaFlowState::Foreground,
                    value: JoinCfaValue::Closure {
                        body_def_id: record.body_def_id,
                        captures: Box::new([]),
                        origin: join_cfa_channel_variable(endpoint, *channel_index),
                    },
                },
            });
        }
    }
    constraints
}

/// A context-qualified body instance used by the value CFA.
///
/// Dovetail does not execute one global copy of a transition body.  When a
/// `Closure` is emitted, it applies a fresh substitution to the nested
/// constraints, keyed by the retained call history.  The old Rust prototype
/// instead keyed instantiation by `body_def_id`, which silently merged every
/// invocation of a reaction.  Keeping the key here (rather than in a runtime
/// helper) makes the substitution an ordinary compiler data-flow operation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct JoinCfaInstanceKey {
    body_def_id: u32,
    context: Box<[JoinCfaContextFrame]>,
    closure_origin: u64,
}

#[derive(Clone, Debug)]
struct JoinCfaDynamicInstance {
    key: JoinCfaInstanceKey,
}

#[derive(Clone, Debug)]
enum JoinCfaDynamicConstraint {
    Succ { destination: u64, state: Option<JoinCfaFlowState>, source: u64 },
    Emit { inputs: Box<[u64]>, target: u64, history: Box<[JoinCfaContextFrame]>, owner: u32 },
    Escape { source: u64 },
}

/// Variables with bit 62 set are qualified by a dynamic body-instance id.
/// Bit 63 is already reserved for synthetic channel variables, while ordinary
/// `(body_def_id, local)` variables use neither tag.  Thirty bits leave ample
/// room for a bounded compiler analysis and avoid pointer/address-derived
/// identities in the certificate.
const JOIN_CFA_CONTEXT_TAG: u64 = 1 << 62;
const JOIN_CFA_CHANNEL_ARGUMENT_TAG: u64 = 1 << 61;

fn join_cfa_context_variable(instance: u32, local: u32) -> u64 {
    JOIN_CFA_CONTEXT_TAG | ((instance as u64) << 32) | local as u64
}

fn join_cfa_is_channel_variable(variable: u64) -> bool {
    variable & JOIN_CFA_CHANNEL_TAG != 0
}

fn join_cfa_is_context_variable(variable: u64) -> bool {
    variable & JOIN_CFA_CONTEXT_TAG != 0
}

fn join_cfa_is_channel_argument_variable(variable: u64) -> bool {
    variable & JOIN_CFA_CHANNEL_ARGUMENT_TAG != 0
}

fn join_cfa_static_parts(variable: u64) -> Option<(u32, u32)> {
    if join_cfa_is_channel_variable(variable)
        || join_cfa_is_context_variable(variable)
        || join_cfa_is_channel_argument_variable(variable)
    {
        None
    } else {
        Some(((variable >> 32) as u32, variable as u32))
    }
}

fn join_cfa_call_origin(caller: u32, block: u32, statement: u32, callee: u32) -> u64 {
    let mut hasher = FxHasher::default();
    caller.hash(&mut hasher);
    block.hash(&mut hasher);
    statement.hash(&mut hasher);
    callee.hash(&mut hasher);
    hasher.finish()
}

fn join_cfa_closure_origin(owner: u32, block: u32, statement: u32, body: u32) -> u64 {
    let mut hasher = FxHasher::default();
    owner.hash(&mut hasher);
    block.hash(&mut hasher);
    statement.hash(&mut hasher);
    body.hash(&mut hasher);
    hasher.finish()
}

/// Replace the old body-global value solver with a bounded, context-qualified
/// fixed point.  The graph extraction remains deliberately typed and
/// source-positioned; this function only decides which substitution is used
/// when a nested closure is entered.
#[allow(rustc::potential_query_instability)]
fn solve_join_cfa_contextual(
    constraints: &[JoinCfaConstraint],
    bodies: &[JoinCfaBodyRecord],
    context_depth: u32,
    budget: u32,
) -> (Vec<JoinCfaValueFact>, u32, bool) {
    let mut solver = JoinCfaContextualSolver::new(constraints, bodies, context_depth, budget);
    solver.solve()
}

struct JoinCfaContextualSolver {
    by_body: FxHashMap<u32, Vec<JoinCfaConstraint>>,
    body_roles: FxHashMap<u32, JoinBodyRole>,
    body_ids: Vec<u32>,
    context_depth: u32,
    budget: u32,
    facts: FxHashMap<u64, FxHashSet<(JoinCfaFlowState, JoinCfaValue)>>,
    closure_captures: FxHashMap<u64, Vec<u64>>,
    /// Variables which crossed an opaque boundary before their concrete
    /// values were available.  Keeping this marker separate from the value
    /// set lets the solver widen a later channel/closure value, while a
    /// primitive-only argument remains `Primitive` instead of acquiring a
    /// spurious `Outer` wildcard.
    escaped_variables: FxHashSet<u64>,
    channel_arguments: FxHashMap<(u32, Option<u32>, u32), u64>,
    next_channel_argument: u64,
    dynamic_constraints: Vec<JoinCfaDynamicConstraint>,
    instances: Vec<JoinCfaDynamicInstance>,
    instance_keys: FxHashMap<JoinCfaInstanceKey, u32>,
    work: VecDeque<u64>,
    steps: u32,
    complete: bool,
}

#[allow(rustc::potential_query_instability)]
impl JoinCfaContextualSolver {
    fn new(
        constraints: &[JoinCfaConstraint],
        bodies: &[JoinCfaBodyRecord],
        context_depth: u32,
        budget: u32,
    ) -> Self {
        let mut by_body = FxHashMap::<u32, Vec<JoinCfaConstraint>>::default();
        for constraint in constraints {
            by_body.entry(constraint.body_def_id).or_default().push(constraint.clone());
        }
        let body_roles = bodies
            .iter()
            .map(|body| (body.body_def_id, body.role))
            .collect::<FxHashMap<_, _>>();
        let mut body_ids = bodies.iter().map(|body| body.body_def_id).collect::<Vec<_>>();
        body_ids.extend(by_body.keys().copied());
        body_ids.sort_unstable();
        body_ids.dedup();
        Self {
            by_body,
            body_roles,
            body_ids,
            context_depth,
            budget,
            facts: FxHashMap::default(),
            closure_captures: FxHashMap::default(),
            escaped_variables: FxHashSet::default(),
            channel_arguments: FxHashMap::default(),
            next_channel_argument: 1,
            dynamic_constraints: Vec::new(),
            instances: Vec::new(),
            instance_keys: FxHashMap::default(),
            work: VecDeque::new(),
            steps: 0,
            complete: budget != 0,
        }
    }

    fn solve(&mut self) -> (Vec<JoinCfaValueFact>, u32, bool) {
        // Channel values are global gamma variables.  Seed them once before
        // any body instance is entered; an `Emit` can therefore discover the
        // typed dispatch closure without first executing its generated body.
        for constraint in self
            .by_body
            .values()
            .flat_map(|constraints| constraints.iter())
            .cloned()
            .collect::<Vec<_>>()
        {
            if let JoinCfaConstraintKind::In { destination, state, value } = constraint.kind
                && join_cfa_is_channel_variable(destination)
            {
                self.add_fact(destination, state, self.contextualize_value(value, destination));
            }
        }

        // Ordinary source bodies are normally the roots.  A generated body
        // can be reached through a closure seed rather than a direct MIR call,
        // so use incoming static references to avoid making every generated
        // transition an independent external entry.  If an isolated SCC has
        // no discoverable root, seed it as an external entry; that is safe
        // (it only widens facts) and keeps the fixed-point gate honest.
        let incoming = self.incoming_bodies();
        // JCAM starts at constructor/channel transitions, not at every
        // unrelated Rust function in the crate.  Seeding all MIR roots made
        // test harnesses and runtime helpers inject opaque `Outer` facts into
        // an otherwise closed join graph.  Restrict roots to ordinary bodies
        // which contain a semantic channel seed or registration; generated
        // adapters are entered through their typed closure/channel edges.
        let semantic_roots = self
            .body_ids
            .iter()
            .copied()
            .filter(|body| self.body_roles.get(body) == Some(&JoinBodyRole::Ordinary))
            .filter(|body| {
                self.by_body.get(body).is_some_and(|constraints| {
                    constraints.iter().any(|constraint| match &constraint.kind {
                        JoinCfaConstraintKind::In { destination, .. } => {
                            join_cfa_is_channel_variable(*destination)
                        }
                        JoinCfaConstraintKind::Emit { .. } => true,
                        _ => false,
                    })
                })
            })
            .filter(|body| !incoming.contains(body))
            .collect::<Vec<_>>();
        let roots = if semantic_roots.is_empty() {
            self.body_ids
                .iter()
                .copied()
                .filter(|body| !incoming.contains(body))
                .collect::<Vec<_>>()
        } else {
            semantic_roots
        };
        for body in roots {
            self.ensure_instance(body, Vec::new().into_boxed_slice(), 0);
        }

        while let Some(changed_variable) = self.work.pop_front() {
            if self.steps >= self.budget {
                self.complete = false;
                break;
            }
            self.steps = self.steps.saturating_add(1);

            if self.escaped_variables.contains(&changed_variable) {
                self.escape_variable(changed_variable);
            }

            // `ensure_instance` may append constraints while this loop runs;
            // process the snapshot and let newly appended edges observe the
            // next work-list event rather than invalidating the borrow.
            let dynamic_len = self.dynamic_constraints.len();
            for index in 0..dynamic_len {
                let constraint = self.dynamic_constraints[index].clone();
                match constraint {
                    JoinCfaDynamicConstraint::Succ { destination, state, source }
                        if source == changed_variable =>
                    {
                        if let Some(source_values) = self.facts.get(&source).cloned() {
                            for (source_state, value) in source_values {
                                self.add_fact(destination, state.unwrap_or(source_state), value);
                            }
                        }
                    }
                    JoinCfaDynamicConstraint::Emit { inputs, target, history, owner }
                        if target == changed_variable
                            || inputs.iter().any(|input| *input == changed_variable) =>
                    {
                        self.process_emit(&inputs, target, &history, owner);
                    }
                    JoinCfaDynamicConstraint::Escape { source } if source == changed_variable => {
                        self.escape_variable(source)
                    }
                    _ => {}
                }
            }
        }
        if !self.work.is_empty() {
            self.complete = false;
        }

        let mut solution = self
            .facts
            .drain()
            .flat_map(|(variable, values)| {
                values.into_iter().map(move |(state, value)| JoinCfaValueFact {
                    variable,
                    state,
                    value,
                })
            })
            .collect::<Vec<_>>();
        solution.sort();
        (solution, self.steps, self.complete)
    }

    fn incoming_bodies(&self) -> FxHashSet<u32> {
        let mut incoming = FxHashSet::default();
        for constraints in self.by_body.values() {
            for constraint in constraints {
                match &constraint.kind {
                    JoinCfaConstraintKind::Succ { destination, source, .. } => {
                        for variable in [*destination, *source] {
                            if let Some((body, _)) = join_cfa_static_parts(variable)
                                && body != constraint.body_def_id
                            {
                                incoming.insert(body);
                            }
                        }
                    }
                    JoinCfaConstraintKind::Closure { body_def_id, .. } => {
                        incoming.insert(*body_def_id);
                    }
                    JoinCfaConstraintKind::In { value, .. } => {
                        match value {
                            JoinCfaValue::Closure { body_def_id, .. }
                            | JoinCfaValue::Function { body_def_id, .. } => {
                                incoming.insert(*body_def_id);
                            }
                            _ => {}
                        }
                    }
                    JoinCfaConstraintKind::Emit { history, .. } => {
                        if let Some(frame) = history.last() {
                            incoming.insert(frame.callee_body_def_id);
                        }
                    }
                    JoinCfaConstraintKind::Escape { .. } => {}
                }
            }
        }
        incoming
    }

    fn add_fact(&mut self, variable: u64, state: JoinCfaFlowState, value: JoinCfaValue) -> bool {
        let inserted = self.facts.entry(variable).or_default().insert((state, value.clone()));
        if inserted {
            self.work.push_back(variable);
        }
        if self.escaped_variables.contains(&variable)
            && !matches!(value, JoinCfaValue::Primitive | JoinCfaValue::Wildcard(JoinCfaSide::Primitive))
        {
            self.widen_escaped_variable(variable);
        }
        inserted
    }

    fn contextualize_value(&self, value: JoinCfaValue, destination: u64) -> JoinCfaValue {
        match value {
            JoinCfaValue::Closure { body_def_id, captures, origin } => JoinCfaValue::Closure {
                body_def_id,
                captures,
                origin: if join_cfa_is_channel_variable(destination) { destination } else { origin },
            },
            JoinCfaValue::Function { body_def_id, origin } => JoinCfaValue::Function {
                body_def_id,
                origin: if join_cfa_is_channel_variable(destination) { destination } else { origin },
            },
            value => value,
        }
    }

    fn channel_argument_variable(
        &mut self,
        endpoint_def_id: u32,
        channel_index: Option<u32>,
        position: u32,
    ) -> u64 {
        let key = (endpoint_def_id, channel_index, position);
        if let Some(variable) = self.channel_arguments.get(&key).copied() {
            return variable;
        }
        let variable = JOIN_CFA_CHANNEL_ARGUMENT_TAG | self.next_channel_argument;
        self.next_channel_argument = self.next_channel_argument.saturating_add(1);
        self.channel_arguments.insert(key, variable);
        variable
    }

    fn escape_variable(&mut self, variable: u64) {
        self.escaped_variables.insert(variable);
        self.widen_escaped_variable(variable);
    }

    fn widen_escaped_variable(&mut self, variable: u64) {
        let Some(values) = self.facts.get(&variable).cloned() else { return };
        let has_non_primitive = values.iter().any(|(_, value)| {
            !matches!(value, JoinCfaValue::Primitive | JoinCfaValue::Wildcard(JoinCfaSide::Primitive))
        });
        if !has_non_primitive {
            return;
        }
        let outer = JoinCfaValue::Wildcard(JoinCfaSide::Outer);
        let inserted = self
            .facts
            .entry(variable)
            .or_default()
            .insert((JoinCfaFlowState::Foreground, outer.clone()));
        if inserted {
            self.work.push_back(variable);
        }
        for (state, value) in values {
            if matches!(
                value,
                JoinCfaValue::Primitive | JoinCfaValue::Wildcard(JoinCfaSide::Primitive)
            ) {
                continue;
            }
            if let JoinCfaValue::Closure { ref captures, .. } = value {
                for capture in captures.iter().copied() {
                    let inserted = self
                        .facts
                        .entry(capture)
                        .or_default()
                        .insert((JoinCfaFlowState::Foreground, outer.clone()));
                    if inserted {
                        self.work.push_back(capture);
                    }
                }
            }
            if !matches!(value, JoinCfaValue::Wildcard(JoinCfaSide::Outer)) {
                let inserted = self.facts.entry(variable).or_default().insert((state, outer.clone()));
                if inserted {
                    self.work.push_back(variable);
                }
            }
        }
    }

    fn extend_context(
        &self,
        parent: &[JoinCfaContextFrame],
        suffix: &[JoinCfaContextFrame],
    ) -> Box<[JoinCfaContextFrame]> {
        if self.context_depth == 0 {
            return Vec::new().into_boxed_slice();
        }
        let mut context = parent.to_vec();
        context.extend_from_slice(suffix);
        let keep = self.context_depth as usize;
        if context.len() > keep {
            let drop_count = context.len() - keep;
            context.drain(..drop_count);
        }
        context.into_boxed_slice()
    }

    fn ensure_instance(
        &mut self,
        body_def_id: u32,
        context: Box<[JoinCfaContextFrame]>,
        closure_origin: u64,
    ) -> Option<u32> {
        let key = JoinCfaInstanceKey { body_def_id, context, closure_origin };
        if let Some(index) = self.instance_keys.get(&key).copied() {
            return Some(index);
        }
        if !self.body_ids.contains(&body_def_id) {
            self.complete = false;
            return None;
        }
        if self.instances.len() >= self.budget as usize {
            self.complete = false;
            return None;
        }
        let index = self.instances.len() as u32;
        self.instance_keys.insert(key.clone(), index);
        self.instances.push(JoinCfaDynamicInstance { key });
        self.instantiate_body(index);
        Some(index)
    }

    fn map_static_variable(
        &mut self,
        variable: u64,
        owner: u32,
        constraint: &JoinCfaConstraint,
    ) -> u64 {
        if join_cfa_is_channel_variable(variable) || join_cfa_is_context_variable(variable) {
            return variable;
        }
        let Some((body_def_id, local)) = join_cfa_static_parts(variable) else {
            return variable;
        };
        let Some(owner_instance) = self.instances.get(owner as usize).cloned() else {
            self.complete = false;
            return variable;
        };
        if body_def_id == owner_instance.key.body_def_id {
            return join_cfa_context_variable(owner, local);
        }

        // Ordinary Rust calls are not part of JCAM, but they still need a
        // context-qualified callee.  Use the source location as the retained
        // RustCall frame; a later context-depth truncation merges it exactly
        // where the bounded analysis says it may be merged.
        let frame = JoinCfaContextFrame {
            kind: JoinCfaContextFrameKind::RustCall,
            caller_body_def_id: owner_instance.key.body_def_id,
            block: constraint.block,
            statement: constraint.statement,
            callee_body_def_id: body_def_id,
            group_def_id: None,
            channel_index: None,
            rule_index: None,
        };
        let context =
            self.extend_context(&owner_instance.key.context, std::slice::from_ref(&frame));
        let origin = join_cfa_call_origin(
            owner_instance.key.body_def_id,
            constraint.block,
            constraint.statement,
            body_def_id,
        );
        let callee = self.ensure_instance(body_def_id, context, origin);
        callee.map_or(variable, |callee| join_cfa_context_variable(callee, local))
    }

    fn payload_start(&self, body_def_id: u32) -> u32 {
        match self.body_roles.get(&body_def_id) {
            // Generated join methods and reaction closures carry the endpoint
            // receiver/environment in local 1; their first source payload is
            // local 2. Ordinary Rust closures have no join receiver.
            Some(JoinBodyRole::Channel)
            | Some(JoinBodyRole::Dispatch)
            | Some(JoinBodyRole::ReactionBody) => 2,
            _ => 1,
        }
    }

    fn instantiate_body(&mut self, owner: u32) {
        let Some(instance) = self.instances.get(owner as usize).cloned() else { return };
        let static_constraints =
            self.by_body.get(&instance.key.body_def_id).cloned().unwrap_or_default();
        for constraint in static_constraints {
            match &constraint.kind {
                JoinCfaConstraintKind::In { destination, state, value } => {
                    let destination = if join_cfa_is_channel_variable(*destination) {
                        *destination
                    } else {
                        self.map_static_variable(*destination, owner, &constraint)
                    };
                    self.add_fact(
                        destination,
                        *state,
                        self.contextualize_value(value.clone(), destination),
                    );
                }
                JoinCfaConstraintKind::Closure { destination, body_def_id, captures } => {
                    let destination = self.map_static_variable(*destination, owner, &constraint);
                    let captures = captures
                        .iter()
                        .map(|capture| self.map_static_variable(*capture, owner, &constraint))
                        .collect::<Vec<_>>()
                        .into_boxed_slice();
                    self.add_fact(
                        destination,
                        JoinCfaFlowState::Foreground,
                        JoinCfaValue::Closure {
                            body_def_id: *body_def_id,
                            captures: captures.clone(),
                            origin: join_cfa_closure_origin(
                                instance.key.body_def_id,
                                constraint.block,
                                constraint.statement,
                                *body_def_id,
                            ),
                        },
                    );
                    self.closure_captures
                        .entry(destination)
                        .or_default()
                        .extend(captures.iter().copied());
                }
                JoinCfaConstraintKind::Succ { destination, state, source } => {
                    let destination = self.map_static_variable(*destination, owner, &constraint);
                    let source = self.map_static_variable(*source, owner, &constraint);
                    self.dynamic_constraints.push(JoinCfaDynamicConstraint::Succ {
                        destination,
                        state: *state,
                        source,
                    });
                }
                JoinCfaConstraintKind::Emit { inputs, target, history } => {
                    let inputs = inputs
                        .iter()
                        .map(|input| self.map_static_variable(*input, owner, &constraint))
                        .collect::<Vec<_>>()
                        .into_boxed_slice();
                    // `Emit` normally targets a global channel variable, but
                    // source-level closure construction can also leave a
                    // local continuation as the target. Apply the same
                    // context substitution to both sides; keeping a local
                    // target body-global would merge two call sites and lose
                    // the fresh substitution that JCAM assigns to each
                    // retained history.
                    let target = self.map_static_variable(*target, owner, &constraint);
                    self.dynamic_constraints.push(JoinCfaDynamicConstraint::Emit {
                        inputs,
                        target,
                        history: history.clone(),
                        owner,
                    });
                }
                JoinCfaConstraintKind::Escape { source } => {
                    let source = self.map_static_variable(*source, owner, &constraint);
                    self.dynamic_constraints.push(JoinCfaDynamicConstraint::Escape { source });
                }
            }
        }
    }

    fn process_emit(
        &mut self,
        inputs: &[u64],
        target: u64,
        history: &[JoinCfaContextFrame],
        owner: u32,
    ) {
        let target_values = self.facts.get(&target).cloned().unwrap_or_default();
        let target_channels = target_values
            .iter()
            .filter_map(|(_, value)| match value {
                JoinCfaValue::Channel { endpoint_def_id, channel_index } => {
                    Some((*endpoint_def_id, *channel_index))
                }
                _ => None,
            })
            .collect::<FxHashSet<_>>();
        let target_endpoints = target_values
            .iter()
            .filter_map(|(_, value)| match value {
                JoinCfaValue::Channel { endpoint_def_id, .. } => Some(*endpoint_def_id),
                _ => None,
            })
            .collect::<FxHashSet<_>>();
        let target_has_outer_wildcard = target_values.iter().any(|(_, value)| {
            matches!(value, JoinCfaValue::Wildcard(JoinCfaSide::Inner | JoinCfaSide::Outer))
        });
        let mut target_closures = target_values
            .into_iter()
            .filter_map(|(_, value)| match value {
                JoinCfaValue::Closure { body_def_id, captures, origin } => {
                    Some((body_def_id, captures, origin))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        let parent_context = self
            .instances
            .get(owner as usize)
            .map(|instance| instance.key.context.clone())
            .unwrap_or_default();
        if target_closures.is_empty() {
            // Restricted unary endpoints do not have a generated dispatch
            // body.  The channel method itself constructs the reaction
            // closure and returns it through local 0.  Enter that channel
            // body under the same JoinRegister history before declaring the
            // target opaque; this is the Rust equivalent of Dovetail's
            // `gamma(channel)` transition.
            if let Some(frame) = history.last() {
                let channel_context = self.extend_context(&parent_context, history);
                if let Some(channel_instance) =
                    self.ensure_instance(frame.callee_body_def_id, channel_context, target)
                {
                    for (position, input) in inputs.iter().copied().enumerate() {
                        let destination = join_cfa_context_variable(
                            channel_instance,
                            self.payload_start(frame.callee_body_def_id) + position as u32,
                        );
                        if let Some(input_values) = self.facts.get(&input).cloned() {
                            for (_, value) in input_values {
                                self.add_fact(destination, JoinCfaFlowState::Foreground, value);
                            }
                        }
                    }
                    let return_value = join_cfa_context_variable(channel_instance, 0);
                    target_closures.extend(
                        self.facts
                            .get(&return_value)
                            .into_iter()
                            .flatten()
                            .filter_map(|(_, value)| match value {
                                JoinCfaValue::Closure { body_def_id, captures, origin } => {
                                    Some((*body_def_id, captures.clone(), *origin))
                                }
                                _ => None,
                            }),
                    );
                }
            }
        }
        let has_target_closure = !target_closures.is_empty();
        // Dovetail's known closure emission feeds both the selected
        // transition's foreground formals and the channel's background
        // `gamma` variables.  Keep those variables distinct from ordinary
        // `(body, local)` and context-qualified ids so later queue/escape
        // proofs can inspect retention without conflating it with execution.
        for (endpoint_def_id, channel_index) in target_channels {
            for (position, input) in inputs.iter().copied().enumerate() {
                let destination =
                    self.channel_argument_variable(endpoint_def_id, channel_index, position as u32);
                if let Some(input_values) = self.facts.get(&input).cloned() {
                    for (_, value) in input_values {
                        self.add_fact(destination, JoinCfaFlowState::Background, value);
                    }
                }
            }
        }
        for (body_def_id, captures, origin) in target_closures {
            let context = self.extend_context(&parent_context, history);
            let Some(instance) = self.ensure_instance(body_def_id, context, origin) else {
                continue;
            };
            // The generated receiver/environment is local 1. Payloads retain
            // the existing typed-MIR ABI numbering (the first source argument
            // is also local 1 for a reaction method); their facts are kept in
            // the same lattice and therefore remain conservative if an ABI
            // adapter aliases those places.
            let environment = join_cfa_context_variable(instance, 1);
            for capture in captures.iter().copied() {
                if let Some(capture_values) = self.facts.get(&capture).cloned() {
                    for (state, value) in capture_values {
                        self.add_fact(environment, state, value);
                    }
                }
            }
            for (position, input) in inputs.iter().copied().enumerate() {
                let destination = join_cfa_context_variable(
                    instance,
                    self.payload_start(body_def_id) + position as u32,
                );
                if let Some(input_values) = self.facts.get(&input).cloned() {
                    for (_, value) in input_values {
                        // An emitted payload enters the nested transition on
                        // its foreground path, as in Dovetail's
                        // `Succ(sub formal, Some F, actual)`.
                        self.add_fact(destination, JoinCfaFlowState::Foreground, value);
                    }
                }
            }
        }
        // A closure target consumes its inputs as foreground arguments;
        // unlike a wildcard target, passing a channel/closure value to that
        // transition is not itself an outer escape.  The old solver widened
        // every higher-order emission merely because the target lacked a
        // Channel marker.  Retain the wildcard branch only when an actual
        // unknown inner/outer alternative is present.
        if !has_target_closure || target_has_outer_wildcard {
            for input in inputs.iter().copied() {
                let Some(input_values) = self.facts.get(&input).cloned() else { continue };
                for (_, value) in input_values {
                    if matches!(
                        value,
                        JoinCfaValue::Primitive
                            | JoinCfaValue::Wildcard(JoinCfaSide::Primitive)
                    ) {
                        continue;
                    }
                    let internal = match value {
                        JoinCfaValue::Channel { endpoint_def_id, .. } => {
                            target_endpoints.contains(&endpoint_def_id)
                        }
                        JoinCfaValue::Closure { .. } | JoinCfaValue::Function { .. } => false,
                        JoinCfaValue::Wildcard(JoinCfaSide::Inner) => !target_endpoints.is_empty(),
                        JoinCfaValue::Wildcard(JoinCfaSide::Outer) => false,
                        JoinCfaValue::Wildcard(JoinCfaSide::Primitive)
                        | JoinCfaValue::Primitive => true,
                    };
                    if internal {
                        self.add_fact(target, JoinCfaFlowState::Background, value);
                    } else {
                        self.escape_variable(input);
                    }
                }
            }
        }
    }
}

/// Resolve function-item values before any proof-consuming pass runs.  A
/// local function value is precise only when one body identity reaches the
/// callsite through copy/move edges; conflicting assignments remain unknown.
/// This is intentionally a small forward fixed point rather than a pattern
/// match on runtime function-pointer representations.
fn resolve_function_value_edges(bodies: &mut [JoinCfaBodyRecord]) {
    let mut aliases_by_body = FxHashMap::<u32, FxHashMap<u32, FunctionAlias>>::default();
    for body in bodies.iter() {
        let mut aliases = FxHashMap::default();
        for fact in &body.function_facts {
            let current = aliases.get(&fact.destination).copied().unwrap_or(FunctionAlias::None);
            aliases.insert(fact.destination, current.join(FunctionAlias::Unique(fact.body_def_id)));
        }
        for local in &body.unknown_function_locals {
            aliases.insert(*local, FunctionAlias::Multiple);
        }
        let mut changed = true;
        let mut iterations = 0;
        while changed && iterations < 1024 {
            changed = false;
            iterations += 1;
            for flow in &body.value_flows {
                if !matches!(flow.kind, JoinValueFlowKind::Copy | JoinValueFlowKind::Move) {
                    continue;
                }
                let Some(source) = flow.source else { continue };
                let incoming = aliases.get(&source).copied().unwrap_or(FunctionAlias::None);
                if incoming == FunctionAlias::None {
                    continue;
                }
                let current = aliases
                    .get(&flow.destination)
                    .copied()
                    .unwrap_or(FunctionAlias::None);
                let next = current.join(incoming);
                if next != current {
                    aliases.insert(flow.destination, next);
                    changed = true;
                }
            }
        }
        aliases_by_body.insert(body.body_def_id, aliases);
    }

    for body in bodies.iter_mut() {
        let Some(aliases) = aliases_by_body.get(&body.body_def_id) else { continue };
        for edge in &mut body.call_edges {
            if edge.target != JoinCallTargetKind::Unknown {
                continue;
            }
            let Some(function_local) = edge.function_local else { continue };
            let FunctionAlias::Unique(callee) =
                aliases.get(&function_local).copied().unwrap_or(FunctionAlias::None)
            else {
                continue;
            };
            edge.callee = Some(callee);
            edge.target = JoinCallTargetKind::OrdinaryLocal;
        }
    }
}

/// Build the first crate-level instance graph from the summaries attached to
/// pre-cleanup MIR bodies. This deliberately starts with facts that can be
/// proved without guessing through an unknown call: a constructor result is
/// followed through copy/move value-flow edges in the same body and then
/// checked at compiler-known channel/dispatch receivers. The result is a
/// proof input for the next MIR transform, not the transform itself.
pub(crate) fn join_cfa_crate_summary(tcx: TyCtxt<'_>, _: ()) -> JoinCfaCrateSummary {
    let mut bodies = Vec::new();
    let mut ordinary_bodies = FxHashMap::default();
    let mut pending_ordinary = Vec::new();
    let join_call_targets = join_call_target_map(tcx);
    for &def_id in tcx.mir_keys(()).iter() {
        // `mir_keys` also contains consts/statics and tuple constructors. The
        // crate summary must never force `optimized_mir`: that query consumes
        // the `mir_drops_elaborated_and_const_checked` Steal, and another
        // analysis/codegen query may still need to own that body. Snapshot an
        // executable function body from `mir_built` while it is borrowable;
        // const/static and constructor MIR has a different ownership/CTFE
        // contract and is not a join instance.
        if tcx.hir_body_const_context(def_id).is_some()
            || tcx.is_constructor(def_id.to_def_id())
            || !tcx.def_kind(def_id).is_fn_like()
        {
            continue;
        }
        let mut body = tcx.mir_built(def_id).borrow().clone();
        // The regular runtime pipeline installs this summary later in
        // `run_analysis_to_runtime_passes`. Running the same required pass on
        // the owned snapshot gives the crate graph a pre-cleanup view without
        // stealing the query-owned body or depending on optimized MIR.
        if tcx.features().joins() && tcx.sess.opts.unstable_opts.join_cfa != JoinCfaMode::Off {
            JoinSemanticOps.run_pass(tcx, &mut body);
        }
        let parent_body_def_id = tcx
            .parent(def_id.to_def_id())
            .as_local()
            .map(|parent| parent.index() as u32)
            .filter(|parent| *parent != def_id.index() as u32);
        if let Some(summary) = body.join_info.as_ref() {
            let record = JoinCfaBodyRecord {
                body_def_id: def_id.index() as u32,
                parent_body_def_id,
                endpoint_def_id: Some(summary.endpoint_def_id),
                channel_index: summary
                    .operations
                    .iter()
                    .find(|operation| operation.kind == JoinOperationKind::Register)
                    .and_then(|operation| operation.channel_index),
                rule_index: summary.rule_index,
                role: summary.role,
                primitive_locals: body
                    .local_decls
                    .iter_enumerated()
                    .filter_map(|(local, declaration)| {
                        join_cfa_is_primitive_type(declaration.ty).then_some(local.index() as u32)
                    })
                    .collect(),
                value_flows: summary.value_flows.clone(),
                closure_facts: summary.closure_facts.clone(),
                function_facts: summary.function_facts.clone(),
                unknown_function_locals: summary.unknown_function_locals.clone(),
                call_edges: summary.call_edges.clone(),
                calls: summary.calls,
                yields: summary.yields,
                unknown_effects: summary.unknown_effects,
                endpoint_escapes: summary.endpoint_escapes.clone(),
                cyclic_blocks: cfg_cyclic_blocks(&body),
            };
            pending_ordinary.extend(
                record
                    .call_edges
                    .iter()
                    .filter(|edge| edge.target == JoinCallTargetKind::OrdinaryLocal)
                    .filter_map(|edge| edge.callee),
            );
            pending_ordinary.extend(record.function_facts.iter().map(|fact| fact.body_def_id));
            bodies.push(record);
            continue;
        }

        // Ordinary helper bodies are not given a per-body public summary, but
        // retain the same typed visitor facts when they are reachable from a
        // join body. Collecting them here lets the crate solver transfer an
        // endpoint argument into a helper without making every Rust function
        // part of the join dump.
        let mut facts = JoinBodyFacts {
            endpoint_def_id: None,
            rule_def_id: None,
            channel_index: None,
            rule_index: None,
            queue_bound: JoinQueueBound::Unknown,
            operations: Vec::new(),
            value_flows: Vec::new(),
            closure_facts: Vec::new(),
            function_facts: Vec::new(),
            unknown_function_locals: FxIndexSet::default(),
            callable_locals: body
                .local_decls
                .iter()
                .map(|decl| join_cfa_is_callable_type(decl.ty))
                .collect(),
            call_edges: Vec::new(),
            escapes: FxIndexSet::default(),
            endpoint_escapes: FxIndexSet::default(),
            endpoint_locals: vec![false; body.local_decls.len()],
            join_call_targets: join_call_targets.clone(),
            suppress_endpoint_return_escape: false,
            calls: 0,
            yields: 0,
            unknown_effects: 0,
        };
        facts.visit_body(&body);
        // Keep an otherwise empty local helper in the side table. It is not a
        // graph root, but a join reaction may call it through an ordinary MIR
        // edge. Dropping it here made the reachability walk report a missing
        // callee and mark the whole endpoint incomplete, even when the helper
        // had no values, calls, escapes, or effects to analyse. Retaining the
        // empty record gives the fixed point an explicit leaf and distinguishes
        // a known no-op helper from an unavailable or indirect callee. Only
        // selected helpers are copied into `bodies`, so unrelated crate
        // functions do not enter the join graph.
        // Ordinary callers are graph roots too.  Previously the crate graph
        // only started from join-associated bodies, which meant that the
        // constructor and seed emissions in `main` (or in an ordinary helper)
        // were never selected.  That made a perfectly visible one-token
        // protocol look as though it had no unique instance or producer.
        // Include only bodies with a compiler-identified join edge; unrelated
        // Rust functions remain outside the graph.
        if facts.call_edges.iter().any(|edge| {
            edge.endpoint_def_id.is_some()
                && matches!(
                    edge.target,
                    JoinCallTargetKind::Constructor
                        | JoinCallTargetKind::Channel
                        | JoinCallTargetKind::Dispatch
                        | JoinCallTargetKind::ReactionBody
                )
        }) {
            pending_ordinary.push(def_id.index() as u32);
        }
        ordinary_bodies.insert(
            def_id.index() as u32,
            JoinCfaBodyRecord {
                body_def_id: def_id.index() as u32,
                parent_body_def_id,
                endpoint_def_id: None,
                channel_index: None,
                rule_index: None,
                role: JoinBodyRole::Ordinary,
                primitive_locals: body
                    .local_decls
                    .iter_enumerated()
                    .filter_map(|(local, declaration)| {
                        join_cfa_is_primitive_type(declaration.ty).then_some(local.index() as u32)
                    })
                    .collect(),
                value_flows: facts.value_flows,
                closure_facts: facts
                    .closure_facts
                    .into_iter()
                    .map(|(destination, captures, closure_body_def_id, block, statement)| {
                        JoinCfaClosureFact {
                            destination,
                            body_def_id: closure_body_def_id,
                            captures,
                            block,
                            statement,
                        }
                    })
                    .collect(),
                function_facts: facts.function_facts,
                unknown_function_locals: facts.unknown_function_locals.into_iter().collect(),
                call_edges: facts.call_edges,
                calls: facts.calls,
                yields: facts.yields,
                unknown_effects: facts.unknown_effects,
                endpoint_escapes: facts.endpoint_escapes.into_iter().collect(),
                cyclic_blocks: cfg_cyclic_blocks(&body),
            },
        );
    }

    // Keep only ordinary bodies reachable from a join-associated body. This
    // preserves a small graph while still following helper chains and makes
    // an absent local callee an explicit loss of proof precision.
    let mut selected = bodies.iter().map(|record| record.body_def_id).collect::<FxHashSet<_>>();
    let mut complete = true;
    while let Some(body_def_id) = pending_ordinary.pop() {
        if !selected.insert(body_def_id) {
            continue;
        }
        let Some(record) = ordinary_bodies.remove(&body_def_id) else {
            complete = false;
            continue;
        };
        pending_ordinary.extend(
            record
                .call_edges
                .iter()
                .filter(|edge| edge.target == JoinCallTargetKind::OrdinaryLocal)
                .filter_map(|edge| edge.callee),
        );
        pending_ordinary.extend(record.function_facts.iter().map(|fact| fact.body_def_id));
        bodies.push(record);
    }
    bodies.sort_by_key(|record| record.body_def_id);
    resolve_function_value_edges(&mut bodies);

    let mut instances = Vec::<JoinCfaInstanceFact>::new();
    let mut aliases_by_body = FxHashMap::<u32, FxHashMap<u32, InstanceAlias>>::default();
    let mut solver_steps = 0u32;
    for record in &bodies {
        solver_steps = solver_steps.saturating_add(
            (record.value_flows.len() as u32).saturating_add(record.call_edges.len() as u32),
        );
        let mut aliases = FxHashMap::<u32, InstanceAlias>::default();

        // Seed a concrete origin at every known constructor result. Multiple
        // constructor values reaching one local are kept as Multiple rather
        // than being silently collapsed into a declaration-level fact.
        for edge in &record.call_edges {
            let (Some(endpoint_def_id), Some(destination_local)) =
                (edge.endpoint_def_id, edge.destination_local)
            else {
                continue;
            };
            if edge.target != JoinCallTargetKind::Constructor {
                continue;
            }
            let origin = InstanceAlias::Unique {
                endpoint_def_id,
                body_def_id: record.body_def_id,
                block: edge.block,
                statement: edge.statement,
            };
            let merged = aliases
                .get(&destination_local)
                .copied()
                .unwrap_or(InstanceAlias::None)
                .join(origin);
            aliases.insert(destination_local, merged);
            instances.push(JoinCfaInstanceFact {
                body_def_id: record.body_def_id,
                endpoint_def_id,
                allocation_block: edge.block,
                allocation_statement: edge.statement,
                known_uses: 0,
                status: JoinCfaInstanceStatus::Unique,
            });
        }

        // Propagate simple aliases to a fixed point. The visitor emits these
        // edges in source order; joining a destination is conservative when a
        // branch or repeated assignment supplies more than one origin.
        let mut changed = true;
        let mut iterations = 0u32;
        while changed && iterations < 1024 {
            changed = false;
            iterations += 1;
            for flow in &record.value_flows {
                let Some(source) = flow.source else { continue };
                if !matches!(
                    flow.kind,
                    JoinValueFlowKind::Copy | JoinValueFlowKind::Move | JoinValueFlowKind::Borrow
                ) {
                    continue;
                }
                let incoming = aliases.get(&source).copied().unwrap_or(InstanceAlias::None);
                if matches!(incoming, InstanceAlias::None) {
                    continue;
                }
                let destination =
                    aliases.get(&flow.destination).copied().unwrap_or(InstanceAlias::None);
                let merged = destination.join(incoming);
                if merged != destination {
                    aliases.insert(flow.destination, merged);
                    changed = true;
                }
            }
        }
        if iterations >= 1024 {
            complete = false;
        }
        aliases_by_body.insert(record.body_def_id, aliases);
    }

    // Transfer endpoint aliases across direct local calls. MIR arguments are
    // numbered from one, with return place zero; preserving argument slots in
    // JoinCallEdge lets this remain identity-based instead of type- or name-
    // based. A missing local callee or an unknown call is an escape.
    let mut escaped_origins = Vec::new();
    let mut interproc_changed = true;
    let mut interproc_iterations = 0u32;
    while interproc_changed && interproc_iterations < 1024 {
        interproc_changed = false;
        interproc_iterations += 1;
        // A parameter update can unlock a borrow/copy chain inside the callee
        // on the next round. Re-run the local transfer before exporting its
        // calls or return value; otherwise a helper's receiver temporary
        // would remain `None` even though its argument is known.
        for record in &bodies {
            let Some(aliases) = aliases_by_body.get_mut(&record.body_def_id) else { continue };
            let mut local_changed = true;
            let mut local_iterations = 0u32;
            while local_changed && local_iterations < 1024 {
                local_changed = false;
                local_iterations += 1;
                for flow in &record.value_flows {
                    let Some(source) = flow.source else { continue };
                    if !matches!(
                        flow.kind,
                        JoinValueFlowKind::Copy
                            | JoinValueFlowKind::Move
                            | JoinValueFlowKind::Borrow
                    ) {
                        continue;
                    }
                    let incoming = aliases.get(&source).copied().unwrap_or(InstanceAlias::None);
                    if matches!(incoming, InstanceAlias::None) {
                        continue;
                    }
                    let destination =
                        aliases.get(&flow.destination).copied().unwrap_or(InstanceAlias::None);
                    let merged = destination.join(incoming);
                    if merged != destination {
                        aliases.insert(flow.destination, merged);
                        local_changed = true;
                        interproc_changed = true;
                    }
                }
            }
            if local_iterations >= 1024 {
                complete = false;
            }
        }
        let mut updates = Vec::<(u32, u32, InstanceAlias)>::new();
        for record in &bodies {
            let Some(caller_aliases) = aliases_by_body.get(&record.body_def_id) else { continue };
            for edge in &record.call_edges {
                let Some(callee) = edge.callee else { continue };
                if let Some(callee_aliases) = aliases_by_body.get(&callee) {
                    for (position, source) in edge.argument_locals.iter().enumerate() {
                        let Some(source) = source else { continue };
                        let incoming =
                            caller_aliases.get(source).copied().unwrap_or(InstanceAlias::None);
                        if !matches!(incoming, InstanceAlias::None) {
                            updates.push((callee, position as u32 + 1, incoming));
                        }
                    }
                    if let Some(destination) = edge.destination_local {
                        let returned =
                            callee_aliases.get(&0).copied().unwrap_or(InstanceAlias::None);
                        if !matches!(returned, InstanceAlias::None) {
                            updates.push((record.body_def_id, destination, returned));
                        }
                    }
                } else if record.role == JoinBodyRole::Ordinary
                    && matches!(
                        edge.target,
                        JoinCallTargetKind::OrdinaryLocal | JoinCallTargetKind::Unknown
                    )
                {
                    for source in edge.argument_locals.iter().flatten() {
                        let alias =
                            caller_aliases.get(source).copied().unwrap_or(InstanceAlias::None);
                        if !matches!(alias, InstanceAlias::None) {
                            escaped_origins.push(alias);
                        }
                    }
                }
            }
        }
        for (body_def_id, local, incoming) in updates {
            let Some(aliases) = aliases_by_body.get_mut(&body_def_id) else {
                complete = false;
                continue;
            };
            let current = aliases.get(&local).copied().unwrap_or(InstanceAlias::None);
            let merged = current.join(incoming);
            if merged != current {
                aliases.insert(local, merged);
                interproc_changed = true;
            }
        }
    }
    if interproc_iterations >= 1024 {
        complete = false;
    }
    solver_steps = solver_steps.saturating_add(interproc_iterations);

    // A compiler-known use is attached to exactly one constructor origin
    // only when the receiver alias is unique and its endpoint matches the
    // call edge. Unknown/multiple aliases invalidate the crate proof but
    // never manufacture a positive fact.  Generated constructors, channel
    // shims, dispatch adapters and reaction wrappers are part of the
    // compiler's implementation of the same endpoint; their ABI temporaries
    // must not be mistaken for a user-level handle escape.  Only ordinary
    // source bodies are roots for this whole-instance ownership proof.
    for record in &bodies {
        // The generated endpoint bodies receive their handle through an ABI
        // environment and may create further adapter temporaries. Those
        // locals are not source-level aliases and are intentionally not part
        // of the constructor/use proof. Counting them here turns a perfectly
        // private unary endpoint into an incomplete instance merely because
        // its wrapper receiver has no source constructor origin.
        if record.role != JoinBodyRole::Ordinary {
            continue;
        }
        let Some(aliases) = aliases_by_body.get(&record.body_def_id) else { continue };
        for edge in &record.call_edges {
            if !matches!(edge.target, JoinCallTargetKind::Channel | JoinCallTargetKind::Dispatch) {
                continue;
            }
            let Some(receiver_local) = edge.receiver_local else {
                if record.role == JoinBodyRole::Ordinary {
                    complete = false;
                }
                continue;
            };
            let alias = aliases.get(&receiver_local).copied().unwrap_or(InstanceAlias::None);
            match alias {
                InstanceAlias::Unique { endpoint_def_id, body_def_id, block, statement }
                    if Some(endpoint_def_id) == edge.endpoint_def_id =>
                {
                    if let Some(instance) = instances.iter_mut().find(|instance| {
                        instance.body_def_id == body_def_id
                            && instance.endpoint_def_id == endpoint_def_id
                            && instance.allocation_block == block
                            && instance.allocation_statement == statement
                    }) {
                        instance.known_uses = instance.known_uses.saturating_add(1);
                    } else {
                        complete = false;
                    }
                }
                InstanceAlias::Unique { endpoint_def_id, body_def_id, block, statement } => {
                    complete = false;
                    if let Some(instance) = instances.iter_mut().find(|instance| {
                        instance.body_def_id == body_def_id
                            && instance.endpoint_def_id == endpoint_def_id
                            && instance.allocation_block == block
                            && instance.allocation_statement == statement
                    }) {
                        instance.status = JoinCfaInstanceStatus::Multiple;
                    }
                }
                InstanceAlias::None => complete = false,
                InstanceAlias::Multiple | InstanceAlias::Unknown => {
                    complete = false;
                    for instance in instances
                        .iter_mut()
                        .filter(|instance| instance.body_def_id == record.body_def_id)
                    {
                        instance.status = JoinCfaInstanceStatus::Multiple;
                    }
                }
            }
        }
        // Primitive-only opaque MIR operations (array stores, aggregate
        // adapters, application arithmetic, and similar details) do not
        // expose a join handle.  Dovetail's closedness analysis likewise
        // widens a channel value only when that value, or a closure capturing
        // it, crosses the boundary.  Keep the generic `unknown_effects`
        // diagnostic in the body record, but do not reject an otherwise
        // unique endpoint instance merely because its payload computation is
        // opaque.
        //
        // The typed endpoint-escape list is still a hard boundary for source
        // bodies. Generated endpoint plumbing is intentionally transparent:
        // its closures must capture the endpoint to implement recursive
        // re-emission, which is an internal JCAM closure edge rather than an
        // escape from the concrete instance.
        if record.role == JoinBodyRole::Ordinary {
            for escape in &record.endpoint_escapes {
                complete = false;
                match aliases.get(&escape.local).copied().unwrap_or(InstanceAlias::None) {
                    InstanceAlias::Unique { endpoint_def_id, body_def_id, block, statement } => {
                        if let Some(instance) = instances.iter_mut().find(|instance| {
                            instance.body_def_id == body_def_id
                                && instance.endpoint_def_id == endpoint_def_id
                                && instance.allocation_block == block
                                && instance.allocation_statement == statement
                        }) {
                            instance.status = JoinCfaInstanceStatus::Escaped;
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    for escaped in escaped_origins {
        if let InstanceAlias::Unique { endpoint_def_id, body_def_id, block, statement } = escaped {
            if let Some(instance) = instances.iter_mut().find(|instance| {
                instance.body_def_id == body_def_id
                    && instance.endpoint_def_id == endpoint_def_id
                    && instance.allocation_block == block
                    && instance.allocation_statement == statement
            }) {
                instance.status = JoinCfaInstanceStatus::Escaped;
            }
            complete = false;
        }
    }
    instances.sort_by_key(|instance| {
        (
            instance.body_def_id,
            instance.allocation_block,
            instance.allocation_statement,
            instance.endpoint_def_id,
        )
    });

    let context = solve_context_cfa(
        &bodies,
        tcx.sess.opts.unstable_opts.join_cfa_depth,
        tcx.sess.opts.unstable_opts.join_cfa_budget,
    );
    // The context graph above is only the history/effect half of CFA. Build
    // and solve the typed JCAM value constraints independently, then expose
    // both certificates in the crate summary. A context fixed point without
    // this value solution is not sufficient to claim closedness.
    let cfa_constraints = build_join_cfa_constraints(&bodies, context.context_depth);
    let (cfa_solution, cfa_steps, cfa_complete) = solve_join_cfa_contextual(
        &cfa_constraints,
        &bodies,
        context.context_depth,
        tcx.sess.opts.unstable_opts.join_cfa_budget.min(u32::MAX as usize) as u32,
    );
    let state_tokens = prove_state_tokens(tcx, &bodies, &instances, &context);
    // The state-token proof is intentionally local to one conserved channel.
    // Run the endpoint-wide JCAM transition analysis as a separate query
    // product: a finite matcher must account for every competing rule and
    // every compiler-visible re-emission before it can replace per-channel
    // queues with a status mask.
    let state_machines = prove_endpoint_state_machines(tcx, &bodies, &instances);
    // Do not let analysis mode change runtime representation.  Optimize mode
    // consumes only positive certificates and records the selected storage
    // contract for the later LowerJoins/MIR-to-LLVM step.
    let state_token_lowerings = if tcx.sess.opts.unstable_opts.join_cfa == JoinCfaMode::Optimize {
        state_tokens
            .iter()
            .filter(|proof| proof.status == JoinStateTokenStatus::Proven)
            .filter_map(|proof| {
                let endpoint = tcx.join_definitions(()).endpoints.iter().find(|endpoint| {
                    endpoint.endpoint_def_id.map(|id| id.index() as u32)
                        == Some(proof.endpoint_def_id)
                })?;
                let rule = endpoint.rules.get(proof.rule_index as usize)?;
                // The first executable pair slice is intentionally narrow:
                // exactly one synchronous, canonical two-channel rule with
                // no competing pattern.  Reordered/partial/async rules keep
                // the generic matcher even when a token proof exists.
                let canonical_pair = endpoint.channels.len() == 2
                    && endpoint.rules.len() == 1
                    && endpoint.declared_arity == 2
                    && rule.arity == 2
                    && !rule.is_async
                    && rule.channel_indices == [0, 1];
                let exact_atomic_pair = canonical_pair
                    && proof.channel_index == 0
                    && is_exact_atomic_u64_pair(tcx, endpoint, rule);
                let strategy = if exact_atomic_pair {
                    JoinLoweringStrategy::FixedAtomicU64Pair
                } else if canonical_pair {
                    JoinLoweringStrategy::FixedPairMatcher
                } else {
                    JoinLoweringStrategy::FixedUnarySlot
                };
                Some(JoinStateTokenLowering {
                    endpoint_def_id: proof.endpoint_def_id,
                    rule_index: proof.rule_index,
                    channel_index: proof.channel_index,
                    proven_bound: proof.proven_bound,
                    strategy,
                    certificate_id: state_token_certificate_id(proof, strategy),
                })
            })
            .collect()
    } else {
        Vec::new()
    };
    let summary = JoinCfaCrateSummary {
        bodies,
        instances,
        state_tokens,
        state_token_lowerings,
        state_machines,
        context,
        cfa_constraints,
        cfa_solution,
        cfa_steps,
        cfa_complete,
        solver_steps,
        complete: complete && cfa_complete,
    };
    dump_crate_summary(tcx, &summary, &aliases_by_body);
    summary
}

/// Build an endpoint-wide finite-state certificate from the typed rule graph.
///
/// This is the small JCAM-style product that was missing from the previous
/// per-body state-token pass.  A channel is a candidate persistent state bit
/// only when a reaction re-emits it, it has no reply, and callers do not pass
/// a payload to it.  Request/result channels remain queues.  The certificate
/// therefore does not identify an MPSC-shaped protocol and is useful for any
/// join definition with a finite set of conserved one-way state channels.
///
/// The runtime representation selected from this certificate keeps an
/// overflow FIFO for duplicate admissions.  That makes the transition
/// lowering semantics-preserving while the caller-sensitive multiplicity CFA
/// is still being expanded; a later proof may remove that fallback entirely.
#[allow(rustc::potential_query_instability)]
fn prove_endpoint_state_machines(
    tcx: TyCtxt<'_>,
    bodies: &[JoinCfaBodyRecord],
    instances: &[JoinCfaInstanceFact],
) -> Vec<JoinStateMachineProof> {
    let mut proofs = Vec::new();
    for endpoint in &tcx.join_definitions(()).endpoints {
        let Some(endpoint_def_id) = endpoint.endpoint_def_id.map(|id| id.index() as u32) else {
            continue;
        };
        let mut rejection = None;
        if endpoint.channels.len() > u64::BITS as usize {
            rejection = Some(JoinStateTokenRejection::UnsupportedRuleShape);
        }
        let unique_instance = instances
            .iter()
            .filter(|instance| instance.endpoint_def_id == endpoint_def_id)
            .filter(|instance| instance.status == JoinCfaInstanceStatus::Unique)
            .count()
            == 1;
        if !unique_instance {
            rejection.get_or_insert(JoinStateTokenRejection::NoUniqueInstance);
        }

        let mut reply_mask = 0u64;
        for rule in &endpoint.rules {
            for &channel in &rule.reply_channel_indices {
                if channel < u64::BITS as u32 {
                    reply_mask |= 1u64 << channel;
                } else {
                    rejection.get_or_insert(JoinStateTokenRejection::UnsupportedRuleShape);
                }
            }
            // Async reactions still participate in the value/re-emission
            // graph.  Suspension changes when the body runs, but it does not
            // change which typed channel values can flow through the rule.
            // The existing coroutine/future lowering owns the claimed inputs
            // until completion or cancellation, so finite-state storage can
            // be selected from the same transition facts as for a synchronous
            // reaction.  Optimizations which remove the executor or overflow
            // storage require stronger proofs later; they are not prerequisites
            // for this representation choice.
            let mut seen = 0u64;
            for &channel in &rule.channel_indices {
                if channel >= u64::BITS as u32 || (seen & (1u64 << channel)) != 0 {
                    rejection.get_or_insert(JoinStateTokenRejection::UnsupportedRuleShape);
                } else {
                    seen |= 1u64 << channel;
                }
            }
        }

        // A state bit has to be a unit/no-argument one-way channel.  This is
        // checked from the resolved method signature, not from source names
        // or a runtime matcher type.
        let mut state_shape_mask = 0u64;
        for channel in &endpoint.channels {
            if channel.index >= u64::BITS as u32 || (reply_mask & (1u64 << channel.index)) != 0 {
                continue;
            }
            let signature = tcx
                .fn_sig(channel.method_def_id.to_def_id())
                .instantiate_identity()
                .skip_binder();
            if signature.inputs().len() == 1 {
                state_shape_mask |= 1u64 << channel.index;
            }
        }

        let mut rules = Vec::with_capacity(endpoint.rules.len());
        let mut produced_mask = 0u64;
        for (rule_index, rule) in endpoint.rules.iter().enumerate() {
            let mut consume_mask = 0u64;
            for &channel in &rule.channel_indices {
                if channel < u64::BITS as u32 && (state_shape_mask & (1u64 << channel)) != 0 {
                    consume_mask |= 1u64 << channel;
                }
            }

            // The generated reaction helper and any nested adapter carry the
            // same source-rule coordinate. Follow their typed channel edges
            // to recover re-emission transitions without scanning names.
            let mut produce_mask_for_rule = 0u64;
            let mut duplicate_producer = false;
            for body in bodies.iter().filter(|body| {
                body.endpoint_def_id == Some(endpoint_def_id)
                    && body.rule_index == Some(rule_index as u32)
            }) {
                for edge in &body.call_edges {
                    if edge.target != JoinCallTargetKind::Channel
                        || edge.endpoint_def_id != Some(endpoint_def_id)
                    {
                        continue;
                    }
                    let Some(channel) = edge.channel_index else {
                        rejection.get_or_insert(JoinStateTokenRejection::IncompleteAnalysis);
                        continue;
                    };
                    if channel >= u64::BITS as u32 {
                        rejection.get_or_insert(JoinStateTokenRejection::UnsupportedRuleShape);
                        continue;
                    }
                    let bit = 1u64 << channel;
                    if (reply_mask & bit) != 0 {
                        // A result-bearing channel is a request, not a
                        // persistent state token. Its ordinary reply path is
                        // deliberately left untouched by this lowering.
                        continue;
                    }
                    if (state_shape_mask & bit) == 0 {
                        // A one-way channel with a payload is still part of
                        // the endpoint's transition graph, but it is not a
                        // finite state bit.  Keep its FIFO representation and
                        // let this certificate cover only the persistent unit
                        // channels.  In particular, a state reaction may
                        // consume and re-emit a payload token (for example a
                        // counter) while its ready/ownership marker uses a
                        // bit.  Rejecting the whole endpoint here would make
                        // an otherwise valid product depend on the unrelated
                        // queue-backed channel.
                        continue;
                    }
                    if (produce_mask_for_rule & bit) != 0 {
                        duplicate_producer = true;
                    }
                    produce_mask_for_rule |= bit;
                }
            }
            if duplicate_producer {
                rejection.get_or_insert(JoinStateTokenRejection::MultipleReemissions);
            }
            produced_mask |= produce_mask_for_rule;
            let reply_for_rule = rule
                .reply_channel_indices
                .iter()
                .filter_map(|channel| (*channel < u64::BITS as u32).then_some(1u64 << channel))
                .fold(0u64, |mask, bit| mask | bit);
            rules.push(JoinStateMachineRule {
                rule_index: rule_index as u32,
                consume_mask,
                produce_mask: produce_mask_for_rule,
                reply_mask: reply_for_rule,
            });
        }

        // Only channels which are actually re-emitted are persistent state.
        // One-way request channels (such as release messages) retain their
        // ordinary FIFO, so this analysis cannot accidentally turn every
        // one-way input into a capacity-one slot.
        let state_mask = produced_mask & state_shape_mask;
        if state_mask == 0 {
            rejection.get_or_insert(JoinStateTokenRejection::MissingReemission);
        }
        if endpoint.rules.is_empty() || rules.len() != endpoint.rules.len() {
            rejection.get_or_insert(JoinStateTokenRejection::IncompleteAnalysis);
        }
        let status = if rejection.is_none() {
            JoinStateTokenStatus::Proven
        } else {
            JoinStateTokenStatus::Rejected
        };
        let mut hasher = FxHasher::default();
        endpoint_def_id.hash(&mut hasher);
        state_mask.hash(&mut hasher);
        reply_mask.hash(&mut hasher);
        for rule in &rules {
            rule.rule_index.hash(&mut hasher);
            rule.consume_mask.hash(&mut hasher);
            rule.produce_mask.hash(&mut hasher);
            rule.reply_mask.hash(&mut hasher);
        }
        proofs.push(JoinStateMachineProof {
            endpoint_def_id,
            state_mask,
            rules,
            status,
            rejection,
            certificate_id: hasher.finish(),
        });
    }
    proofs.sort_by_key(|proof| proof.endpoint_def_id);
    proofs
}

/// Check the first interprocedural state-token shape without making any
/// representation choice.  The proof intentionally uses only compiler-owned
/// identities: a typed rule must consume one non-reply channel together with
/// another input, one named reaction body must re-emit that channel, and one
/// concrete constructor instance must be visible.  Runtime matcher names,
/// mutexes, atomics and frontend queue hints never participate in this test.
///
/// This is a deliberately small certificate.  It rejects an endpoint when
/// there are competing rules, more than one seed, more than one re-emission,
/// or no unique instance.  A later lowering pass may consume only
/// `JoinStateTokenStatus::Proven` after validating the current MIR snapshots.
#[allow(rustc::potential_query_instability)]
fn prove_state_tokens<'tcx>(
    tcx: TyCtxt<'tcx>,
    bodies: &[JoinCfaBodyRecord],
    instances: &[JoinCfaInstanceFact],
    context: &JoinCfaContextSummary,
) -> Vec<JoinStateTokenProof> {
    let mut proofs = Vec::new();
    for endpoint in &tcx.join_definitions(()).endpoints {
        let Some(endpoint_def_id) = endpoint.endpoint_def_id.map(|id| id.index() as u32) else {
            continue;
        };
        for (rule_index, rule) in endpoint.rules.iter().enumerate() {
            // A state-token rule has a state input and at least one other
            // input. A unary result rule is an ordinary future, not this
            // protocol, even if its body happens to call a channel.
            if rule.channel_indices.len() < 2 {
                continue;
            }
            for &channel_index in &rule.channel_indices {
                if rule.reply_channel_indices.contains(&channel_index) {
                    continue;
                }
                let competing_rules = endpoint
                    .rules
                    .iter()
                    .enumerate()
                    .filter(|(candidate_index, candidate)| {
                        *candidate_index != rule_index
                            && candidate.channel_indices.contains(&channel_index)
                    })
                    .count();
                let mut transitions = Vec::new();
                let mut seed_events: u32 = 0;
                let mut reemit_events: u32 = 0;
                let mut extra_reemit = false;
                let mut candidate_reaction = false;
                let mut loop_multiplicity = false;

                // A body is relevant even when it is an ordinary caller: its
                // endpoint identity is carried by the typed call edge rather
                // than by a per-body join descriptor.  This is the root that
                // supplies the initial token in a closed local witness.
                let endpoint_body = |body: &&JoinCfaBodyRecord| {
                    body.endpoint_def_id == Some(endpoint_def_id)
                        || body
                            .call_edges
                            .iter()
                            .any(|edge| edge.endpoint_def_id == Some(endpoint_def_id))
                };

                for body in bodies.iter().filter(endpoint_body) {
                    let reaction_for_rule = body.role == JoinBodyRole::ReactionBody
                        && body.rule_index == Some(rule_index as u32);
                    for edge in &body.call_edges {
                        if edge.target != JoinCallTargetKind::Channel
                            || edge.endpoint_def_id != Some(endpoint_def_id)
                            || edge.channel_index != Some(channel_index)
                        {
                            continue;
                        }
                        if body.cyclic_blocks.contains(&edge.block) {
                            // A seed or re-emission in a cyclic block can
                            // execute repeatedly.  Keep collecting evidence
                            // for diagnostics, but never turn it into a
                            // fixed slot from this first syntactic proof.
                            loop_multiplicity = true;
                        }
                        if reaction_for_rule {
                            candidate_reaction = true;
                            reemit_events = reemit_events.saturating_add(1);
                            transitions.push(JoinStateTokenTransition {
                                body_def_id: body.body_def_id,
                                role: body.role,
                                kind: JoinStateTokenTransitionKind::Reemit,
                                block: edge.block,
                                statement: edge.statement,
                            });
                        } else if body.role == JoinBodyRole::ReactionBody {
                            // Another reaction can produce this channel. It
                            // is not safe to infer one-token conservation from
                            // a single selected rule in that case.
                            extra_reemit = true;
                        } else if body.role == JoinBodyRole::Ordinary {
                            // Only source-level ordinary callers are seeds.
                            // Channel and dispatch implementation bodies may
                            // contain internal calls to the same endpoint, but
                            // treating those wrappers as independent token
                            // producers would manufacture duplicate seeds.
                            seed_events = seed_events.saturating_add(1);
                            transitions.push(JoinStateTokenTransition {
                                body_def_id: body.body_def_id,
                                role: body.role,
                                kind: JoinStateTokenTransitionKind::Seed,
                                block: edge.block,
                                statement: edge.statement,
                            });
                        } else {
                            // A compiler-generated endpoint body that emits
                            // this channel is not a source-level seed, but it
                            // is still an unmodelled producer.  Preserve the
                            // conservative rejection rather than silently
                            // treating it as part of the one-token protocol.
                            extra_reemit = true;
                        }
                    }
                }

                // A claim is represented by the static complete pattern. The
                // shared dispatch call does not carry a source rule coordinate
                // in MIR yet, so use the reaction owner's sentinel location;
                // this record remains descriptive until a dedicated Match
                // terminator is available.
                if candidate_reaction {
                    let body_def_id = bodies
                        .iter()
                        .find(|body| {
                            body.endpoint_def_id == Some(endpoint_def_id)
                                && body.role == JoinBodyRole::ReactionBody
                                && body.rule_index == Some(rule_index as u32)
                        })
                        .map(|body| body.body_def_id)
                        .unwrap_or(u32::MAX);
                    transitions.push(JoinStateTokenTransition {
                        body_def_id,
                        role: JoinBodyRole::ReactionBody,
                        kind: JoinStateTokenTransitionKind::Claim,
                        block: u32::MAX,
                        statement: rule_index as u32,
                    });
                }

                let endpoint_instances = instances
                    .iter()
                    .filter(|instance| instance.endpoint_def_id == endpoint_def_id)
                    .collect::<Vec<_>>();
                let unique_instance = (endpoint_instances.len() == 1)
                    .then(|| endpoint_instances[0])
                    .filter(|instance| instance.status == JoinCfaInstanceStatus::Unique);
                // A proof rooted in a constructor allocation is only safe
                // when the source-level seed is in that allocation's body.
                // If the seed is hidden behind an ordinary helper, the
                // helper may be called more than once (or from a loop), while
                // this bounded scan would still observe only one static call
                // edge.  Reject that shape until the interprocedural call
                // graph tracks multiplicity explicitly.
                let seed_outside_allocation = unique_instance.is_some_and(|instance| {
                    transitions.iter().any(|transition| {
                        transition.kind == JoinStateTokenTransitionKind::Seed
                            && transition.body_def_id != instance.body_def_id
                            && !unique_ordinary_call_path(
                                instance.body_def_id,
                                transition.body_def_id,
                                bodies,
                            )
                    })
                });
                let endpoint_complete =
                    state_token_endpoint_complete(endpoint_def_id, rule_index as u32, bodies);
                let context_bodies = transitions
                    .iter()
                    .filter(|transition| transition.body_def_id != u32::MAX)
                    .map(|transition| transition.body_def_id)
                    .collect::<FxHashSet<_>>();
                let context_complete = state_token_context_complete(
                    endpoint_def_id,
                    rule_index as u32,
                    channel_index,
                    &context_bodies,
                    bodies,
                    context,
                );
                let rejection = if competing_rules != 0 {
                    Some(JoinStateTokenRejection::CompetingRule)
                } else if !endpoint_complete {
                    Some(JoinStateTokenRejection::IncompleteAnalysis)
                } else if unique_instance.is_none() {
                    Some(JoinStateTokenRejection::NoUniqueInstance)
                } else if loop_multiplicity {
                    Some(JoinStateTokenRejection::LoopMultiplicity)
                } else if seed_outside_allocation {
                    Some(JoinStateTokenRejection::HelperMultiplicity)
                } else if seed_events != 1 {
                    Some(if seed_events > 1 {
                        JoinStateTokenRejection::DuplicateSeed
                    } else {
                        JoinStateTokenRejection::UnknownProducer
                    })
                } else if extra_reemit {
                    Some(JoinStateTokenRejection::EscapingProducer)
                } else if !candidate_reaction || reemit_events == 0 {
                    Some(JoinStateTokenRejection::MissingReemission)
                } else if reemit_events != 1 {
                    Some(JoinStateTokenRejection::MultipleReemissions)
                } else if !context_complete {
                    Some(JoinStateTokenRejection::IncompleteAnalysis)
                } else {
                    None
                };
                let (instance_body_def_id, allocation_block, allocation_statement) =
                    unique_instance.map_or((None, None, None), |instance| {
                        (
                            Some(instance.body_def_id),
                            Some(instance.allocation_block),
                            Some(instance.allocation_statement),
                        )
                    });
                proofs.push(JoinStateTokenProof {
                    endpoint_def_id,
                    instance_body_def_id,
                    allocation_block,
                    allocation_statement,
                    rule_index: rule_index as u32,
                    channel_index,
                    seed_events,
                    claim_events: candidate_reaction as u32,
                    reemit_events,
                    proven_bound: JoinQueueBound::AtMost(1),
                    status: if rejection.is_none() {
                        JoinStateTokenStatus::Proven
                    } else {
                        JoinStateTokenStatus::Rejected
                    },
                    rejection,
                    transitions,
                });
            }
        }
    }
    proofs.sort_by_key(|proof| (proof.endpoint_def_id, proof.rule_index, proof.channel_index));
    proofs
}

/// Return true only when one non-cyclic, compiler-resolved ordinary-call path
/// reaches `target` from the constructor allocation body.  This is the
/// interprocedural refinement of the original helper-multiplicity rejection:
/// a single callable helper may participate in a fixed-slot proof, while two
/// callsites, a loop, recursion, or an unresolved edge still reject it.
fn unique_ordinary_call_path(
    start: u32,
    target: u32,
    bodies: &[JoinCfaBodyRecord],
) -> bool {
    fn visit(
        current: u32,
        target: u32,
        bodies: &FxHashMap<u32, &JoinCfaBodyRecord>,
        stack: &mut FxHashSet<u32>,
    ) -> u8 {
        if current == target {
            return 1;
        }
        if !stack.insert(current) {
            return 0;
        }
        let Some(body) = bodies.get(&current).copied() else {
            stack.remove(&current);
            return 0;
        };
        let mut paths = 0u8;
        for edge in &body.call_edges {
            if edge.target != JoinCallTargetKind::OrdinaryLocal {
                continue;
            }
            let Some(callee) = edge.callee else {
                stack.remove(&current);
                return 0;
            };
            if body.cyclic_blocks.contains(&edge.block) {
                stack.remove(&current);
                return 0;
            }
            paths = paths.saturating_add(visit(callee, target, bodies, stack));
            if paths > 1 {
                break;
            }
        }
        stack.remove(&current);
        paths
    }

    let by_id = bodies.iter().map(|body| (body.body_def_id, body)).collect::<FxHashMap<_, _>>();
    visit(start, target, &by_id, &mut FxHashSet::default()) == 1
}

/// Check the context slice needed by a conserved state-token proof.
///
/// A re-emission is intentionally a semantic CFA edge.  Therefore a
/// closed, one-token protocol naturally creates a bounded-history cycle: the
/// next reaction registers the replacement token and reaches an already
/// retained history at the configured depth.  Treating that truncation as an
/// unconditional proof failure would make the very conservation rule we are
/// trying to optimize impossible to recognize.  Permit only this narrow
/// cycle shape: the truncated body must be one of the selected rule's
/// reaction bodies, all effects must remain closed and internal, and the
/// truncating frame must be the candidate token's typed registration.  Any
/// ordinary/helper/external/truly escaping truncation remains a rejection.
#[allow(rustc::potential_query_instability)]
fn state_token_context_complete(
    endpoint_def_id: u32,
    rule_index: u32,
    channel_index: u32,
    context_bodies: &FxHashSet<u32>,
    bodies: &[JoinCfaBodyRecord],
    context: &JoinCfaContextSummary,
) -> bool {
    if !context.complete {
        return false;
    }
    let reaction_ids = bodies
        .iter()
        .filter(|body| {
            body.endpoint_def_id == Some(endpoint_def_id)
                && body.role == JoinBodyRole::ReactionBody
                && body.rule_index == Some(rule_index)
        })
        .map(|body| body.body_def_id)
        .collect::<FxHashSet<_>>();
    let has_reemit = bodies.iter().any(|body| {
        body.body_def_id != u32::MAX
            && reaction_ids.contains(&body.body_def_id)
            && body.call_edges.iter().any(|edge| {
                edge.target == JoinCallTargetKind::Channel
                    && edge.endpoint_def_id == Some(endpoint_def_id)
                    && edge.channel_index == Some(channel_index)
            })
    });
    for &body_def_id in context_bodies {
        let mut found = false;
        for instance in
            context.instances.iter().filter(|instance| instance.body_def_id == body_def_id)
        {
            found = true;
            if instance.optimization_safe {
                continue;
            }
            let reaction_cycle = has_reemit
                && reaction_ids.contains(&instance.body_def_id)
                && instance.truncated
                && instance.closed
                && !instance.local_effects.may_suspend
                && !instance.local_effects.may_escape
                && !instance.local_effects.may_external
                && !instance.inherited_effects.may_suspend
                && !instance.inherited_effects.may_escape
                && !instance.inherited_effects.may_external
                && instance.context.last().is_some_and(|frame| {
                    frame.kind == JoinCfaContextFrameKind::JoinRegister
                        && frame.group_def_id == Some(endpoint_def_id)
                        && frame.channel_index == Some(channel_index)
                });
            if !reaction_cycle {
                return false;
            }
        }
        if !found {
            return false;
        }
    }
    true
}

/// Check completeness only for the body subgraph which can affect one state
/// token endpoint.  The crate-wide graph may legitimately be incomplete: an
/// unrelated join body can call an ordinary helper whose MIR is unavailable,
/// and that must not disable a proof for a closed local protocol.  Conversely,
/// an unresolved ordinary call in the candidate endpoint's own subgraph is a
/// real soundness boundary, so it keeps the proof rejected.
#[allow(rustc::potential_query_instability)]
fn state_token_endpoint_complete(
    endpoint_def_id: u32,
    rule_index: u32,
    bodies: &[JoinCfaBodyRecord],
) -> bool {
    let by_id = bodies.iter().map(|body| (body.body_def_id, body)).collect::<FxHashMap<_, _>>();
    let mut relevant = FxHashSet::default();
    for body in bodies {
        if body.endpoint_def_id == Some(endpoint_def_id)
            || body.call_edges.iter().any(|edge| edge.endpoint_def_id == Some(endpoint_def_id))
        {
            relevant.insert(body.body_def_id);
        }
    }
    if relevant.is_empty() {
        return false;
    }

    // The generated dynamic dispatcher has an outer reaction wrapper and a
    // nested body for the source reaction.  The wrapper contains compiler
    // plumbing (closure construction and result adaptation) that is not an
    // independent producer; its nested body is the actual source-level
    // reaction whose channel edges are recorded below.  Check only leaf
    // reaction bodies here.  `unknown_effects` counts projected MIR
    // assignments (including result-adapter plumbing), not an unresolved
    // producer.  The sound escape boundary for this proof is the typed
    // endpoint-escape set: an endpoint moved into an unknown call, aggregate,
    // yield, or return remains a negative fact below.
    let reaction_bodies = bodies
        .iter()
        .filter(|body| {
            body.endpoint_def_id == Some(endpoint_def_id)
                && body.role == JoinBodyRole::ReactionBody
                && body.rule_index == Some(rule_index)
        })
        .collect::<Vec<_>>();
    if reaction_bodies.iter().any(|body| {
        let has_nested_reaction = reaction_bodies
            .iter()
            .any(|candidate| candidate.parent_body_def_id == Some(body.body_def_id));
        !has_nested_reaction && !body.endpoint_escapes.is_empty()
    }) {
        return false;
    }

    // An unresolved indirect callable in the endpoint subgraph may invoke a
    // channel method without leaving a typed Channel edge in the extracted
    // graph.  Do not let the visible producers accidentally prove a fixed
    // slot in that case; only a unique `Function` fact may make this edge an
    // ordinary-local call before the proof reaches this boundary.
    if relevant.iter().any(|body_def_id| {
        by_id.get(body_def_id).is_some_and(|body| {
            body.role == JoinBodyRole::Ordinary
                && body.call_edges.iter().any(|edge| {
                    edge.target == JoinCallTargetKind::Unknown && edge.function_local.is_some()
                })
        })
    }) {
        return false;
    }

    // Follow ordinary helper calls from endpoint bodies. The graph builder
    // normally selects these roots already; retaining the check here makes a
    // missing body an explicit negative proof rather than an accidental
    // omission.
    let mut worklist = relevant
        .iter()
        .copied()
        .filter(|body_def_id| {
            by_id.get(body_def_id).is_some_and(|body| body.role == JoinBodyRole::Ordinary)
        })
        .collect::<Vec<_>>();
    while let Some(body_def_id) = worklist.pop() {
        let Some(body) = by_id.get(&body_def_id).copied() else {
            return false;
        };
        for edge in &body.call_edges {
            if edge.target != JoinCallTargetKind::OrdinaryLocal {
                continue;
            }
            let Some(callee) = edge.callee else {
                return false;
            };
            if by_id.contains_key(&callee) && relevant.insert(callee) {
                worklist.push(callee);
            } else if !by_id.contains_key(&callee) {
                return false;
            }
        }
    }

    // Generated constructors, channel wrappers and dispatch bodies naturally
    // contain aggregate-capture escapes.  Those are implementation details,
    // not source-level token producers.  Keep the completeness boundary on
    // ordinary source callers; projected assignments in an ordinary body are
    // likewise bookkeeping unless the typed endpoint-escape set identifies a
    // real handle transfer.  An unknown call which receives an endpoint
    // handle is recorded as such by `record_moved_place` and is rejected by
    // the same escape check.
    relevant
        .into_iter()
        .filter(|body_def_id| {
            by_id.get(body_def_id).is_some_and(|body| body.role == JoinBodyRole::Ordinary)
        })
        .all(|body_def_id| {
            let Some(body) = by_id.get(&body_def_id).copied() else {
                return false;
            };
            body.endpoint_escapes.is_empty()
        })
}

#[allow(rustc::potential_query_instability)]
fn dump_crate_summary(
    tcx: TyCtxt<'_>,
    summary: &JoinCfaCrateSummary,
    aliases_by_body: &FxHashMap<u32, FxHashMap<u32, InstanceAlias>>,
) {
    let Some(directory) = tcx.sess.opts.unstable_opts.join_cfa_dump.as_ref() else { return };
    if let Err(error) = fs::create_dir_all(directory) {
        tracing::warn!(target: "rustc_join", ?error, path = ?directory, "could not create join CFA graph dump directory");
        return;
    }
    let body_records = summary
        .bodies
        .iter()
        .map(|body| {
            let call_edges = body
                .call_edges
                .iter()
                .map(|edge| {
                    let arguments = edge
                        .argument_locals
                        .iter()
                        .map(|local| local.map_or_else(|| "null".to_string(), |local| local.to_string()))
                        .collect::<Vec<_>>()
                        .join(",");
                    format!(
                        "{{\"callee\":{},\"target\":\"{:?}\",\"endpoint\":{},\"receiver\":{},\"destination\":{},\"function_local\":{},\"arguments\":[{}],\"group\":{},\"channel\":{},\"rule_index\":{},\"queue_bound\":\"{:?}\"}}",
                        edge.callee.map_or_else(|| "null".to_string(), |callee| callee.to_string()),
                        edge.target,
                        edge.endpoint_def_id
                            .map_or_else(|| "null".to_string(), |endpoint| endpoint.to_string()),
                        edge.receiver_local
                            .map_or_else(|| "null".to_string(), |local| local.to_string()),
                        edge.destination_local
                            .map_or_else(|| "null".to_string(), |local| local.to_string()),
                        edge.function_local
                            .map_or_else(|| "null".to_string(), |local| local.to_string()),
                        arguments,
                        edge.group_def_id
                            .map_or_else(|| "null".to_string(), |group| group.to_string()),
                        edge.channel_index
                            .map_or_else(|| "null".to_string(), |channel| channel.to_string()),
                        edge.rule_index
                            .map_or_else(|| "null".to_string(), |rule| rule.to_string()),
                        edge.queue_bound,
                    )
                })
                .collect::<Vec<_>>()
                .join(",");
            let value_flows = body
                .value_flows
                .iter()
                .map(|flow| {
                    format!(
                        "{{\"destination\":{},\"source\":{},\"kind\":\"{:?}\"}}",
                        flow.destination,
                        flow.source.map_or_else(|| "null".to_string(), |source| source.to_string()),
                        flow.kind,
                    )
                })
                .collect::<Vec<_>>()
                .join(",");
            let closure_facts = body
                .closure_facts
                .iter()
                .map(|closure| {
                    let captures = closure
                        .captures
                        .iter()
                        .map(u32::to_string)
                        .collect::<Vec<_>>()
                        .join(",");
                    format!(
                        "{{\"destination\":{},\"body\":{},\"captures\":[{}],\"block\":{},\"statement\":{}}}",
                        closure.destination,
                        closure.body_def_id,
                        captures,
                        closure.block,
                        closure.statement,
                    )
                })
                .collect::<Vec<_>>()
                .join(",");
            let function_facts = body
                .function_facts
                .iter()
                .map(|fact| {
                    format!(
                        "{{\"destination\":{},\"body\":{},\"block\":{},\"statement\":{}}}",
                        fact.destination, fact.body_def_id, fact.block, fact.statement
                    )
                })
                .collect::<Vec<_>>()
                .join(",");
            let mut aliases = aliases_by_body
                .get(&body.body_def_id)
                .map(|aliases| aliases.iter().collect::<Vec<_>>())
                .unwrap_or_default();
            aliases.sort_by_key(|(local, _)| **local);
            let aliases = aliases
                .into_iter()
                .map(|(local, alias)| format!("{{\"local\":{},\"alias\":\"{:?}\"}}", local, alias))
                .collect::<Vec<_>>()
                .join(",");
            let cyclic_blocks = body
                .cyclic_blocks
                .iter()
                .map(u32::to_string)
                .collect::<Vec<_>>()
                .join(",");
            let endpoint_escapes = body
                .endpoint_escapes
                .iter()
                .map(|escape| {
                    format!(
                        "{{\"local\":{},\"kind\":\"{:?}\"}}",
                        escape.local, escape.kind
                    )
                })
                .collect::<Vec<_>>()
                .join(",");
            let primitive_locals = body
                .primitive_locals
                .iter()
                .map(u32::to_string)
                .collect::<Vec<_>>()
                .join(",");
            format!(
                "{{\"body\":{},\"parent\":{},\"endpoint\":{},\"channel_index\":{},\"rule_index\":{},\"role\":\"{:?}\",\"primitive_locals\":[{}],\"flows\":[{}],\"closures\":[{}],\"function_facts\":[{}],\"aliases\":[{}],\"cyclic_blocks\":[{}],\"calls_count\":{},\"yields\":{},\"unknown_effects\":{},\"endpoint_escapes\":[{}],\"calls\":[{}]}}",
                body.body_def_id,
                body.parent_body_def_id
                    .map_or_else(|| "null".to_string(), |parent| parent.to_string()),
                body.endpoint_def_id
                    .map_or_else(|| "null".to_string(), |endpoint| endpoint.to_string()),
                body.channel_index
                    .map_or_else(|| "null".to_string(), |channel| channel.to_string()),
                body.rule_index
                    .map_or_else(|| "null".to_string(), |rule| rule.to_string()),
                body.role,
                primitive_locals,
                value_flows,
                closure_facts,
                function_facts,
                aliases,
                cyclic_blocks,
                body.calls,
                body.yields,
                body.unknown_effects,
                endpoint_escapes,
                call_edges,
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let instances = summary
        .instances
        .iter()
        .map(|instance| {
            format!(
                "{{\"body\":{},\"endpoint\":{},\"allocation_block\":{},\"allocation_statement\":{},\"known_uses\":{},\"status\":\"{:?}\"}}",
                instance.body_def_id,
                instance.endpoint_def_id,
                instance.allocation_block,
                instance.allocation_statement,
                instance.known_uses,
                instance.status,
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let state_tokens = summary
        .state_tokens
        .iter()
        .map(|proof| {
            let transitions = proof
                .transitions
                .iter()
                .map(|transition| {
                    format!(
                        "{{\"body\":{},\"role\":\"{:?}\",\"kind\":\"{:?}\",\"block\":{},\"statement\":{}}}",
                        transition.body_def_id,
                        transition.role,
                        transition.kind,
                        transition.block,
                        transition.statement,
                    )
                })
                .collect::<Vec<_>>()
                .join(",");
            format!(
                "{{\"endpoint\":{},\"instance_body\":{},\"allocation_block\":{},\"allocation_statement\":{},\"rule_index\":{},\"channel\":{},\"seed_events\":{},\"claim_events\":{},\"reemit_events\":{},\"bound\":\"{:?}\",\"status\":\"{:?}\",\"rejection\":{},\"transitions\":[{}]}}",
                proof.endpoint_def_id,
                proof.instance_body_def_id
                    .map_or_else(|| "null".to_string(), |value| value.to_string()),
                proof.allocation_block
                    .map_or_else(|| "null".to_string(), |value| value.to_string()),
                proof.allocation_statement
                    .map_or_else(|| "null".to_string(), |value| value.to_string()),
                proof.rule_index,
                proof.channel_index,
                proof.seed_events,
                proof.claim_events,
                proof.reemit_events,
                proof.proven_bound,
                proof.status,
                proof.rejection
                    .map_or_else(|| "null".to_string(), |reason| format!("\"{reason:?}\"")),
                transitions,
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let state_token_lowerings = summary
        .state_token_lowerings
        .iter()
        .map(|lowering| {
            format!(
                "{{\"endpoint\":{},\"rule_index\":{},\"channel\":{},\"bound\":\"{:?}\",\"strategy\":\"{:?}\",\"certificate\":{}}}",
                lowering.endpoint_def_id,
                lowering.rule_index,
                lowering.channel_index,
                lowering.proven_bound,
                lowering.strategy,
                lowering.certificate_id,
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let state_machines = summary
        .state_machines
        .iter()
        .map(|machine| {
            let rules = machine
                .rules
                .iter()
                .map(|rule| {
                    format!(
                        "{{\"rule\":{},\"consume_mask\":{},\"produce_mask\":{},\"reply_mask\":{}}}",
                        rule.rule_index, rule.consume_mask, rule.produce_mask, rule.reply_mask
                    )
                })
                .collect::<Vec<_>>()
                .join(",");
            format!(
                "{{\"endpoint\":{},\"state_mask\":{},\"status\":\"{:?}\",\"rejection\":{},\"certificate\":{},\"rules\":[{}]}}",
                machine.endpoint_def_id,
                machine.state_mask,
                machine.status,
                machine
                    .rejection
                    .map_or_else(|| "null".to_string(), |reason| format!("\"{reason:?}\"")),
                machine.certificate_id,
                rules,
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let context_instances = summary
        .context
        .instances
        .iter()
        .map(|instance| {
            let frames = instance
                .context
                .iter()
                .map(|frame| {
                    format!(
                        "{{\"kind\":\"{:?}\",\"caller\":{},\"block\":{},\"statement\":{},\"callee\":{},\"group\":{},\"channel\":{},\"rule_index\":{}}}",
                        frame.kind,
                        frame.caller_body_def_id,
                        frame.block,
                        frame.statement,
                        frame.callee_body_def_id,
                        frame.group_def_id
                            .map_or_else(|| "null".to_string(), |value| value.to_string()),
                        frame.channel_index
                            .map_or_else(|| "null".to_string(), |value| value.to_string()),
                        frame.rule_index
                            .map_or_else(|| "null".to_string(), |value| value.to_string()),
                    )
                })
                .collect::<Vec<_>>()
                .join(",");
            format!(
                "{{\"body\":{},\"frames\":[{}],\"truncated\":{},\"local_effects\":{{\"suspend\":{},\"escape\":{},\"external\":{}}},\"inherited_effects\":{{\"suspend\":{},\"escape\":{},\"external\":{}}},\"closed\":{},\"optimization_safe\":{}}}",
                instance.body_def_id,
                frames,
                instance.truncated,
                instance.local_effects.may_suspend,
                instance.local_effects.may_escape,
                instance.local_effects.may_external,
                instance.inherited_effects.may_suspend,
                instance.inherited_effects.may_escape,
                instance.inherited_effects.may_external,
                instance.closed,
                instance.optimization_safe,
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    // Keep the compiler-owned static definition beside the dynamic instance
    // graph.  The body records above intentionally contain only the facts
    // observed at MIR call sites; this descriptor is where a consumer can
    // recover the exact source channel order, reply mapping, and selected
    // execution policy without inspecting generated names or source text.
    let definitions = tcx
        .join_definitions(())
        .endpoints
        .iter()
        .map(|endpoint| {
            let channels = endpoint
                .channels
                .iter()
                .map(|channel| {
                    format!(
                        "{{\"index\":{},\"name\":{}}}",
                        channel.index,
                        format!("{:?}", channel.name.as_str()),
                    )
                })
                .collect::<Vec<_>>()
                .join(",");
            let rules = endpoint
                .rules
                .iter()
                .enumerate()
                .map(|(index, rule)| {
                    let input_channels = rule
                        .channel_indices
                        .iter()
                        .map(u32::to_string)
                        .collect::<Vec<_>>()
                        .join(",");
                    let reply_channels = rule
                        .reply_channel_indices
                        .iter()
                        .map(u32::to_string)
                        .collect::<Vec<_>>()
                        .join(",");
                    let nested_bodies = rule
                        .body_def_ids
                        .iter()
                        .map(|body| body.index().to_string())
                        .collect::<Vec<_>>()
                        .join(",");
                    format!(
                        "{{\"index\":{},\"arity\":{},\"async\":{},\"channels\":[{}],\"replies\":[{}],\"body_index\":{},\"body\":{},\"reaction_method\":{},\"nested_bodies\":[{}]}}",
                        index,
                        rule.arity,
                        rule.is_async,
                        input_channels,
                        reply_channels,
                        rule.body_index
                            .map_or_else(|| "null".to_string(), |value| value.to_string()),
                        rule.body_def_id
                            .map_or_else(|| "null".to_string(), |value| value.index().to_string()),
                        rule.reaction_method_def_id
                            .map_or_else(|| "null".to_string(), |value| value.index().to_string()),
                        nested_bodies,
                    )
                })
                .collect::<Vec<_>>()
                .join(",");
            format!(
                "{{\"impl\":{},\"endpoint\":{},\"policy\":\"{:?}\",\"channels\":[{}],\"rules\":[{}]}}",
                endpoint.impl_def_id.index(),
                endpoint
                    .endpoint_def_id
                    .map_or_else(|| "null".to_string(), |value| value.index().to_string()),
                endpoint.policy,
                channels,
                rules,
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let cfa_constraints = summary
        .cfa_constraints
        .iter()
        .map(|constraint| {
            format!(
                "{{\"body\":{},\"block\":{},\"statement\":{},\"kind\":\"{:?}\"}}",
                constraint.body_def_id, constraint.block, constraint.statement, constraint.kind
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let cfa_solution = summary
        .cfa_solution
        .iter()
        .map(|fact| {
            format!(
                "{{\"variable\":{},\"state\":\"{:?}\",\"value\":\"{:?}\"}}",
                fact.variable, fact.state, fact.value
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let json = format!(
        "{{\"bodies\":{},\"body_records\":[{}],\"instances\":[{}],\"state_tokens\":[{}],\"state_token_lowerings\":[{}],\"state_machines\":[{}],\"context\":{{\"depth\":{},\"transitions\":{},\"complete\":{},\"instances\":[{}]}},\"definitions\":[{}],\"cfa_constraints\":[{}],\"cfa_solution\":[{}],\"cfa_steps\":{},\"cfa_complete\":{},\"solver_steps\":{},\"complete\":{}}}\n",
        summary.bodies.len(),
        body_records,
        instances,
        state_tokens,
        state_token_lowerings,
        state_machines,
        summary.context.context_depth,
        summary.context.transitions,
        summary.context.complete,
        context_instances,
        definitions,
        cfa_constraints,
        cfa_solution,
        summary.cfa_steps,
        summary.cfa_complete,
        summary.solver_steps,
        summary.complete,
    );
    let crate_tag = tcx.stable_crate_id(LOCAL_CRATE).as_u64();
    let path = directory.join(format!("join-cfa-graph-{crate_tag:016x}.json"));
    if let Err(error) = fs::write(&path, json) {
        tracing::warn!(target: "rustc_join", ?error, path = ?path, "could not write join CFA graph summary");
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct OccupancyInterval {
    min: u32,
    max: Option<u32>,
}

const OCCUPANCY_ITERATION_LIMIT: u32 = 1024;

/// Propagate an interval through the MIR control-flow graph rather than
/// sorting events by block number.  A block-order sort is not a sound proof
/// for branches or loops: it can claim a small queue for one path while
/// ignoring a backedge that accumulates registrations.  Merging intervals at
/// CFG joins preserves every reachable path; an unbounded upper end widens to
/// `None` and disables proof-consuming transforms.
fn solve_body_occupancy<'tcx>(
    body: &Body<'tcx>,
    operations: &[JoinMirOperation],
) -> JoinOccupancyFact {
    solve_body_occupancy_for_channel(body, operations, None)
}

/// Compute the same conservative interval transfer for each channel that has
/// a typed source-declaration coordinate.  Operations without a channel
/// coordinate (notably a shared-rule `Match` before rule-pattern metadata is
/// available) are intentionally excluded from a per-channel result rather
/// than guessed onto the first endpoint channel.  Such facts remain useful
/// diagnostics, but their `complete` bit is not an authorization to choose a
/// fixed slot.
fn solve_channel_occupancy<'tcx>(
    body: &Body<'tcx>,
    operations: &[JoinMirOperation],
) -> Vec<JoinChannelOccupancyFact> {
    let channels =
        operations.iter().filter_map(|operation| operation.channel_index).collect::<BTreeSet<_>>();
    let mut result = channels
        .into_iter()
        .map(|channel_index| JoinChannelOccupancyFact {
            channel_index,
            occupancy: solve_body_occupancy_for_channel(body, operations, Some(channel_index)),
        })
        .collect::<Vec<_>>();
    result.sort_by_key(|fact| fact.channel_index);
    result
}

fn solve_body_occupancy_for_channel<'tcx>(
    body: &Body<'tcx>,
    operations: &[JoinMirOperation],
    channel_filter: Option<u32>,
) -> JoinOccupancyFact {
    let block_count = body.basic_blocks.len();
    if block_count == 0 {
        return JoinOccupancyFact {
            proven_peak: None,
            proven_final: None,
            events: 0,
            complete: false,
        };
    }

    let mut operations_by_block = vec![Vec::<JoinMirOperation>::new(); block_count];
    let mut events = 0u32;
    for operation in operations {
        if channel_filter.is_some() && operation.channel_index != channel_filter {
            continue;
        }
        if matches!(
            operation.kind,
            JoinOperationKind::Register
                | JoinOperationKind::Match
                | JoinOperationKind::WithdrawOrAbandon
                | JoinOperationKind::CancelScope
        ) {
            events = events.saturating_add(1);
        }
        if let Some(bucket) = operations_by_block.get_mut(operation.block as usize) {
            bucket.push(operation.clone());
        }
    }
    for bucket in &mut operations_by_block {
        bucket.sort_by_key(|operation| {
            (operation.statement, occupancy_operation_priority(operation.kind))
        });
    }

    let mut entry_states = vec![None::<OccupancyInterval>; block_count];
    entry_states[mir::START_BLOCK.index()] = Some(OccupancyInterval { min: 0, max: Some(0) });
    let mut worklist = std::collections::VecDeque::from([mir::START_BLOCK.index()]);
    let mut queued = vec![false; block_count];
    queued[mir::START_BLOCK.index()] = true;
    let mut visits = vec![0u32; block_count];
    let mut peak = 0u32;
    let mut complete = true;
    let mut exit_state = None::<OccupancyInterval>;

    while let Some(block_index) = worklist.pop_front() {
        queued[block_index] = false;
        visits[block_index] = visits[block_index].saturating_add(1);
        let Some(mut state) = entry_states[block_index] else { continue };
        if visits[block_index] > OCCUPANCY_ITERATION_LIMIT {
            complete = false;
            state.max = None;
        }

        for operation in &operations_by_block[block_index] {
            match operation.kind {
                JoinOperationKind::Register => {
                    let Some(next_min) = state.min.checked_add(1) else {
                        complete = false;
                        state.max = None;
                        continue;
                    };
                    let next_max = match state.max {
                        Some(max) => match max.checked_add(1) {
                            Some(next) if next <= OCCUPANCY_ITERATION_LIMIT => Some(next),
                            _ => {
                                complete = false;
                                None
                            }
                        },
                        None => {
                            complete = false;
                            None
                        }
                    };
                    state = OccupancyInterval { min: next_min, max: next_max };
                    if let Some(max) = state.max {
                        peak = peak.max(max);
                    }
                }
                JoinOperationKind::Match | JoinOperationKind::WithdrawOrAbandon => {
                    if state.min == 0 {
                        // The body is consuming an input supplied by a caller
                        // or a different body. This path has unknown starting
                        // occupancy, so it cannot yield a hard bound.
                        complete = false;
                        state.max = None;
                    } else {
                        state.min -= 1;
                        state.max = state.max.map(|max| max.saturating_sub(1));
                    }
                }
                JoinOperationKind::CancelScope => {
                    // Cancellation can drain an arbitrary number of pending
                    // inputs unless the scope contract is represented in MIR.
                    complete = false;
                    state = OccupancyInterval { min: 0, max: None };
                }
                JoinOperationKind::CreateGroup
                | JoinOperationKind::Demand
                | JoinOperationKind::CompleteReplies
                | JoinOperationKind::OrdinaryCall
                | JoinOperationKind::Yield
                | JoinOperationKind::Return
                | JoinOperationKind::Escape => {}
            }
        }

        let block = mir::BasicBlock::from_usize(block_index);
        let successors = body.basic_blocks[block].terminator().successors().collect::<Vec<_>>();
        if successors.is_empty() {
            merge_occupancy_interval(&mut exit_state, state);
        }
        for successor in successors {
            let successor_index = successor.index();
            if merge_occupancy_interval(&mut entry_states[successor_index], state)
                && !queued[successor_index]
            {
                queued[successor_index] = true;
                worklist.push_back(successor_index);
            }
        }
    }

    let proven_final = exit_state.and_then(|state| match state.max {
        Some(max) if max == state.min => Some(max),
        _ => None,
    });
    if exit_state.is_none() {
        complete = false;
    }
    JoinOccupancyFact {
        proven_peak: complete.then_some(peak),
        proven_final: complete.then_some(proven_final).flatten(),
        events,
        complete,
    }
}

fn merge_occupancy_interval(
    current: &mut Option<OccupancyInterval>,
    incoming: OccupancyInterval,
) -> bool {
    let merged = match *current {
        None => incoming,
        Some(existing) => OccupancyInterval {
            min: existing.min.min(incoming.min),
            max: match (existing.max, incoming.max) {
                (Some(left), Some(right)) => Some(left.max(right)),
                _ => None,
            },
        },
    };
    if *current == Some(merged) {
        false
    } else {
        *current = Some(merged);
        true
    }
}

fn occupancy_operation_priority(kind: JoinOperationKind) -> u8 {
    match kind {
        JoinOperationKind::Register => 0,
        JoinOperationKind::Match | JoinOperationKind::WithdrawOrAbandon => 1,
        JoinOperationKind::CancelScope => 2,
        JoinOperationKind::CreateGroup
        | JoinOperationKind::Demand
        | JoinOperationKind::CompleteReplies
        | JoinOperationKind::OrdinaryCall
        | JoinOperationKind::Yield
        | JoinOperationKind::Return
        | JoinOperationKind::Escape => 3,
    }
}

/// Solve the local value-flow lattice to a bounded fixed point.
///
/// The visitor emits a finite graph, while this routine supplies the
/// monotone propagation that the later interprocedural solver will reuse.
/// Every edge is revisited only when its source changes. A zero budget is a
/// deliberate incomplete result, never an optimistic proof.
fn solve_local_facts(
    local_count: usize,
    flows: &[JoinValueFlow],
    escapes: &FxIndexSet<u32>,
    unknown_effects: u32,
    budget: usize,
) -> (Vec<JoinLocalFact>, u32, bool, bool) {
    let mut states = vec![JoinValueState::Internal; local_count];
    let mut outgoing = vec![Vec::<usize>::new(); local_count];
    let mut incoming = vec![Vec::<usize>::new(); local_count];
    for (edge, flow) in flows.iter().enumerate() {
        if let Some(source) = flow.source {
            if let Some(edges) = outgoing.get_mut(source as usize) {
                edges.push(edge);
            }
            if let Some(edges) = incoming.get_mut(flow.destination as usize) {
                edges.push(edge);
            }
        }
    }

    let mut work = std::collections::VecDeque::new();
    for local in escapes {
        if let Some(state) = states.get_mut(*local as usize) {
            *state = JoinValueState::Escapes;
            work.push_back(*local as usize);
        }
    }
    // Seed edges whose RHS does not have a single source. This includes
    // references and aggregates, so they are visible even if no local later
    // changes.
    for flow in flows {
        let incoming_state = match flow.kind {
            JoinValueFlowKind::Borrow => JoinValueState::Borrowed,
            JoinValueFlowKind::Aggregate => JoinValueState::Aggregate,
            JoinValueFlowKind::Unknown => JoinValueState::Unknown,
            JoinValueFlowKind::Copy | JoinValueFlowKind::Move => flow
                .source
                .and_then(|source| states.get(source as usize).copied())
                .unwrap_or(JoinValueState::Unknown),
        };
        if let Some(state) = states.get_mut(flow.destination as usize) {
            let next = widen(*state, incoming_state);
            if next != *state {
                *state = next;
                work.push_back(flow.destination as usize);
            }
        }
    }

    let mut steps = 0usize;
    let mut complete = budget != 0;
    while let Some(local) = work.pop_front() {
        if steps >= budget {
            complete = false;
            break;
        }
        steps += 1;

        for &edge_index in outgoing.get(local).into_iter().flatten() {
            let flow = &flows[edge_index];
            let incoming_state = match flow.kind {
                JoinValueFlowKind::Copy | JoinValueFlowKind::Move => states[local],
                JoinValueFlowKind::Borrow => JoinValueState::Borrowed,
                JoinValueFlowKind::Aggregate => JoinValueState::Aggregate,
                JoinValueFlowKind::Unknown => JoinValueState::Unknown,
            };
            if let Some(destination) = states.get_mut(flow.destination as usize) {
                let next = widen(*destination, incoming_state);
                if next != *destination {
                    *destination = next;
                    work.push_back(flow.destination as usize);
                }
            }
        }

        // If an alias/aggregate that originated at this local escapes, widen
        // the origin too. This reverse step is what prevents a copied channel
        // handle from looking private merely because the returned local has a
        // different index.
        if states[local] == JoinValueState::Escapes {
            for &edge_index in incoming.get(local).into_iter().flatten() {
                let flow = &flows[edge_index];
                if let Some(source) = flow.source {
                    if let Some(state) = states.get_mut(source as usize) {
                        let next = widen(*state, JoinValueState::Escapes);
                        if next != *state {
                            *state = next;
                            work.push_back(source as usize);
                        }
                    }
                }
            }
        }
    }
    if !work.is_empty() {
        complete = false;
    }
    if unknown_effects != 0 {
        complete = complete && budget != 0;
    }

    let local_facts = states
        .into_iter()
        .enumerate()
        .map(|(local, state)| JoinLocalFact { local: local as u32, state })
        .collect::<Vec<_>>();
    let locally_closed = complete
        && unknown_effects == 0
        && local_facts
            .iter()
            .all(|fact| !matches!(fact.state, JoinValueState::Escapes | JoinValueState::Unknown));
    (local_facts, steps as u32, complete, locally_closed)
}

fn widen(current: JoinValueState, incoming: JoinValueState) -> JoinValueState {
    use JoinValueState::*;
    if current == incoming {
        return current;
    }
    match (current, incoming) {
        (Unknown, _) | (_, Unknown) => Unknown,
        (Escapes, _) | (_, Escapes) => Escapes,
        (Internal, state) | (state, Internal) => state,
        (Borrowed, Borrowed) => Borrowed,
        (Aggregate, Aggregate) => Aggregate,
        // An aggregate may contain a borrow without making the aggregate
        // externally visible. Preserve the more precise non-escaping state;
        // an actual escape is widened separately by the reverse edge pass.
        (Borrowed, Aggregate) | (Aggregate, Borrowed) => Aggregate,
    }
}

impl<'tcx> Visitor<'tcx> for JoinBodyFacts {
    fn visit_assign(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>, location: Location) {
        let Some(destination) = place.as_local() else {
            self.unknown_effects += 1;
            self.super_assign(place, rvalue, location);
            return;
        };
        let destination_callable = self
            .callable_locals
            .get(destination.index())
            .copied()
            .unwrap_or(false);
        // A function item is a zero-sized typed value in MIR, but it is not a
        // primitive payload for join CFA. Preserve its statically known body
        // identity when it is assigned to a local, including the explicit
        // FnDef -> fn-pointer reification coercion. Later call edges can use
        // this fact to turn an otherwise opaque indirect call into the same
        // ordinary-local edge that a direct call already exposes.
        let function_body_def_id = match rvalue {
            Rvalue::Use(Operand::Constant(constant), _) => match *constant.const_.ty().kind() {
                ty::FnDef(def_id, _) => def_id.as_local().map(|id| id.index() as u32),
                _ => None,
            },
            Rvalue::Cast(
                CastKind::PointerCoercion(
                    PointerCoercion::ReifyFnPointer(_) | PointerCoercion::UnsafeFnPointer,
                    _,
                ),
                operand,
                _,
            ) => operand
                .const_fn_def()
                .and_then(|(def_id, _)| def_id.as_local())
                .map(|id| id.index() as u32),
            _ => None,
        };
        if let Some(body_def_id) = function_body_def_id {
            self.function_facts.push(JoinCfaFunctionFact {
                destination: destination.index() as u32,
                body_def_id,
                block: location.block.index() as u32,
                statement: location.statement_index as u32,
            });
            self.super_assign(place, rvalue, location);
            return;
        }
        let (kind, source) = match rvalue {
            Rvalue::Use(Operand::Copy(source), _) => {
                // Keep the base local for projected copies. The projection is
                // a typed path within the same value; dropping it here would
                // turn every ordinary field read into an artificial Unknown
                // state and would prevent direct unary candidates.
                (JoinValueFlowKind::Copy, Some(source.local))
            }
            Rvalue::Use(Operand::Move(source), _) => (JoinValueFlowKind::Move, Some(source.local)),
            Rvalue::Ref(_, _, source) | Rvalue::Reborrow(_, _, source) => {
                (JoinValueFlowKind::Borrow, Some(source.local))
            }
            Rvalue::Cast(_, operand, _) => {
                let source = operand.place().map(|place| place.local);
                (JoinValueFlowKind::Copy, source)
            }
            Rvalue::Aggregate(kind, operands) => {
                // A closure/coroutine may capture an endpoint handle without
                // moving the aggregate's final value directly at the call
                // site. Record the *actual nested body owner* from the typed
                // aggregate.  The previous implementation used the enclosing
                // body id here, which made every aggregate look like a
                // recursive closure of its creator and prevented CFA from
                // instantiating the right body.  Ordinary tuples/ADTs are not
                // callable closures and must not enter the closure domain.
                let closure_body_def_id = match kind.as_ref() {
                    AggregateKind::Closure(def_id, _)
                    | AggregateKind::Coroutine(def_id, _)
                    | AggregateKind::CoroutineClosure(def_id, _) => {
                        def_id.as_local().map(|id| id.index() as u32)
                    }
                    _ => None,
                };
                let captures = operands
                    .iter()
                    .filter_map(|operand| match operand {
                        Operand::Move(source) | Operand::Copy(source) => {
                            Some(source.local.index() as u32)
                        }
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                if let Some(closure_body_def_id) = closure_body_def_id {
                    self.closure_facts.push((
                        destination.index() as u32,
                        captures,
                        closure_body_def_id,
                        location.block.index() as u32,
                        location.statement_index as u32,
                    ));
                }
                // Constructing a closure is not itself an external escape.
                // The closure may remain inside the join group; the typed
                // `Closure` fact lets CFA mark its captures only if the
                // closure later crosses a return/unknown-call boundary.  A
                // previous eager `AggregateCapture` escape made all
                // generated matcher adapters look externally owned.
                if closure_body_def_id.is_none() {
                    for operand in operands {
                        if let Operand::Move(source) | Operand::Copy(source) = operand {
                            self.record_moved_place(
                                source,
                                JoinEndpointEscapeKind::AggregateCapture,
                            );
                        }
                    }
                }
                (JoinValueFlowKind::Aggregate, None)
            }
            _ => {
                if destination_callable {
                    self.unknown_function_locals.insert(destination.index() as u32);
                }
                return self.super_assign(place, rvalue, location);
            }
        };
        if destination_callable
            && !matches!(kind, JoinValueFlowKind::Copy | JoinValueFlowKind::Move)
        {
            self.unknown_function_locals.insert(destination.index() as u32);
        }
        self.value_flows.push(JoinValueFlow {
            destination: destination.index() as u32,
            source: source.map(|local| local.index() as u32),
            kind,
            block: location.block.index() as u32,
            statement: location.statement_index as u32,
        });
        self.super_assign(place, rvalue, location);
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: Location) {
        match &terminator.kind {
            TerminatorKind::Call { func, args, .. }
            | TerminatorKind::TailCall { func, args, .. } => {
                self.calls += 1;
                let callee_def_id = func.const_fn_def().and_then(|(def_id, _)| def_id.as_local());
                let target = self.call_target(callee_def_id);
                let function_local = func
                    .place()
                    .and_then(|place| place.as_local())
                    .map(|local| local.index() as u32);
                let receiver_local = matches!(
                    target.kind,
                    JoinCallTargetKind::Channel
                        | JoinCallTargetKind::Dispatch
                        | JoinCallTargetKind::ReactionBody
                )
                .then(|| args.first().and_then(|arg| arg.node.place()))
                .flatten()
                .map(|place| place.local.index() as u32);
                let destination_local = match &terminator.kind {
                    TerminatorKind::Call { destination, .. } => {
                        destination.as_local().map(|local| local.index() as u32)
                    }
                    TerminatorKind::TailCall { .. } => None,
                    _ => None,
                };
                if destination_local.is_some_and(|local| {
                    self.callable_locals.get(local as usize).copied().unwrap_or(false)
                }) {
                    // Returning a callable from a call is not yet tracked
                    // interprocedurally. Keep the destination conservative;
                    // a function-item fact from another path must not win
                    // over this opaque assignment.
                    if let Some(destination_local) = destination_local {
                        self.unknown_function_locals.insert(destination_local);
                    }
                }
                let argument_locals = args
                    .iter()
                    .map(|arg| arg.node.place().map(|place| place.local.index() as u32))
                    .collect::<Vec<_>>();
                self.operation_with_operands(
                    JoinOperationKind::OrdinaryCall,
                    location,
                    receiver_local,
                    destination_local,
                    argument_locals.iter().copied(),
                    target.channel_index,
                    target.rule_index,
                    target.queue_bound,
                    target.endpoint_def_id,
                    target.rule_def_id,
                );
                match target.kind {
                    JoinCallTargetKind::Constructor => self.operation_with_operands(
                        JoinOperationKind::CreateGroup,
                        location,
                        receiver_local,
                        destination_local,
                        argument_locals.iter().copied(),
                        target.channel_index,
                        target.rule_index,
                        target.queue_bound,
                        target.endpoint_def_id,
                        target.rule_def_id,
                    ),
                    JoinCallTargetKind::Channel => self.operation_with_operands(
                        JoinOperationKind::Register,
                        location,
                        receiver_local,
                        destination_local,
                        argument_locals.iter().copied(),
                        target.channel_index,
                        target.rule_index,
                        target.queue_bound,
                        target.endpoint_def_id,
                        target.rule_def_id,
                    ),
                    JoinCallTargetKind::Dispatch => self.operation_with_operands(
                        JoinOperationKind::Match,
                        location,
                        receiver_local,
                        destination_local,
                        argument_locals.iter().copied(),
                        target.channel_index,
                        target.rule_index,
                        target.queue_bound,
                        target.endpoint_def_id,
                        target.rule_def_id,
                    ),
                    JoinCallTargetKind::Unknown
                    | JoinCallTargetKind::OrdinaryLocal
                    | JoinCallTargetKind::ReactionBody => {}
                }
                self.call_edges.push(JoinCallEdge {
                    block: location.block.index() as u32,
                    statement: location.statement_index as u32,
                    callee: callee_def_id.map(|def_id| def_id.index() as u32),
                    target: target.kind,
                    group_def_id: target.endpoint_def_id,
                    channel_index: target.channel_index,
                    rule_index: target.rule_index,
                    queue_bound: target.queue_bound,
                    endpoint_def_id: target.endpoint_def_id,
                    rule_def_id: target.rule_def_id,
                    receiver_local,
                    destination_local,
                    argument_locals,
                    function_local,
                });
                let preserves_endpoint = matches!(
                    target.kind,
                    JoinCallTargetKind::Constructor
                        | JoinCallTargetKind::Channel
                        | JoinCallTargetKind::Dispatch
                        | JoinCallTargetKind::ReactionBody
                        | JoinCallTargetKind::OrdinaryLocal
                ) && callee_def_id.is_some();
                for arg in args {
                    if !preserves_endpoint && let Operand::Move(place) = &arg.node {
                        self.record_moved_place(place, JoinEndpointEscapeKind::CallArgument);
                    }
                }
            }
            TerminatorKind::Yield { value, .. } => {
                self.yields += 1;
                self.operation(JoinOperationKind::Yield, location);
                if let Operand::Move(place) = value {
                    self.record_moved_place(place, JoinEndpointEscapeKind::Yield);
                }
            }
            TerminatorKind::Return => {
                self.operation(JoinOperationKind::Return, location);
                if !self.suppress_endpoint_return_escape
                    && self.endpoint_locals.get(RETURN_PLACE.index()).copied().unwrap_or(false)
                {
                    self.endpoint_escapes.insert(JoinEndpointEscape {
                        local: RETURN_PLACE.index() as u32,
                        kind: JoinEndpointEscapeKind::Return,
                    });
                }
            }
            _ => {}
        }
        self.super_terminator(terminator, location);
    }
}

/// Emit a per-body JSON-lines-free record. A directory of one file per stable
/// local body identity avoids concurrent append ordering and makes a dump
/// reproducible after sorting filenames. The caller is responsible for using
/// a fresh directory for a fresh compilation.
fn dump_summary(
    tcx: TyCtxt<'_>,
    local_def_id: LocalDefId,
    mode: JoinCfaMode,
    summary: &JoinCfaSummary,
) {
    let Some(directory) = tcx.sess.opts.unstable_opts.join_cfa_dump.as_ref() else {
        return;
    };
    if let Err(error) = fs::create_dir_all(directory) {
        tracing::warn!(
            target: "rustc_join",
            ?error,
            path = ?directory,
            "could not create join CFA dump directory"
        );
        return;
    }

    let operation_kinds = summary
        .operations
        .iter()
        .map(|operation| {
            format!(
                "{{\"kind\":\"{:?}\",\"block\":{},\"statement\":{},\"group\":{},\"channel\":{},\"rule_index\":{},\"reply_channels\":[{}],\"queue_bound\":\"{:?}\",\"endpoint\":{},\"rule\":{},\"receiver\":{},\"destination\":{},\"arguments\":[{}]}}",
                operation.kind,
                operation.block,
                operation.statement,
                operation
                    .group_def_id
                    .map_or_else(|| "null".to_string(), |id| id.to_string()),
                operation
                    .channel_index
                    .map_or_else(|| "null".to_string(), |id| id.to_string()),
                operation
                    .rule_index
                    .map_or_else(|| "null".to_string(), |id| id.to_string()),
                operation
                    .reply_channel_indices
                    .iter()
                    .map(u32::to_string)
                    .collect::<Vec<_>>()
                    .join(","),
                operation.queue_bound,
                operation
                    .endpoint_def_id
                    .map_or_else(|| "null".to_string(), |id| id.to_string()),
                operation
                    .rule_def_id
                    .map_or_else(|| "null".to_string(), |id| id.to_string()),
                operation
                    .receiver_local
                    .map_or_else(|| "null".to_string(), |id| id.to_string()),
                operation
                    .destination_local
                    .map_or_else(|| "null".to_string(), |id| id.to_string()),
                operation
                    .argument_locals
                    .iter()
                    .map(|id| id.map_or_else(|| "null".to_string(), |id| id.to_string()))
                    .collect::<Vec<_>>()
                    .join(","),
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let escapes = summary.escapes.iter().map(u32::to_string).collect::<Vec<_>>().join(",");
    let value_flows = summary
        .value_flows
        .iter()
        .map(|flow| {
            format!(
                "{{\"destination\":{},\"source\":{},\"kind\":\"{:?}\",\"block\":{},\"statement\":{}}}",
                flow.destination,
                flow.source.map_or_else(|| "null".to_string(), |source| source.to_string()),
                flow.kind,
                flow.block,
                flow.statement,
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let local_facts = summary
        .local_facts
        .iter()
        .map(|fact| format!("{{\"local\":{},\"state\":\"{:?}\"}}", fact.local, fact.state))
        .collect::<Vec<_>>()
        .join(",");
    let call_edges = summary
        .call_edges
        .iter()
        .map(|edge| {
            format!(
                "{{\"block\":{},\"statement\":{},\"callee\":{},\"target\":\"{:?}\",\"endpoint\":{},\"rule\":{},\"receiver\":{},\"destination\":{},\"function_local\":{},\"arguments\":[{}],\"group\":{},\"channel\":{},\"rule_index\":{},\"queue_bound\":\"{:?}\"}}",
                edge.block,
                edge.statement,
                edge.callee.map_or_else(|| "null".to_string(), |callee| callee.to_string()),
                edge.target,
                edge.endpoint_def_id
                    .map_or_else(|| "null".to_string(), |endpoint| endpoint.to_string()),
                edge.rule_def_id
                    .map_or_else(|| "null".to_string(), |rule| rule.to_string()),
                edge.receiver_local
                    .map_or_else(|| "null".to_string(), |local| local.to_string()),
                edge.destination_local
                    .map_or_else(|| "null".to_string(), |local| local.to_string()),
                edge.function_local
                    .map_or_else(|| "null".to_string(), |local| local.to_string()),
                edge.argument_locals
                    .iter()
                    .map(|local| local.map_or_else(|| "null".to_string(), |local| local.to_string()))
                    .collect::<Vec<_>>()
                    .join(","),
                edge.group_def_id
                    .map_or_else(|| "null".to_string(), |group| group.to_string()),
                edge.channel_index
                    .map_or_else(|| "null".to_string(), |channel| channel.to_string()),
                edge.rule_index
                    .map_or_else(|| "null".to_string(), |rule| rule.to_string()),
                edge.queue_bound,
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let function_facts = summary
        .function_facts
        .iter()
        .map(|fact| {
            format!(
                "{{\"destination\":{},\"body\":{},\"block\":{},\"statement\":{}}}",
                fact.destination, fact.body_def_id, fact.block, fact.statement
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let rejection =
        summary.rejection.map_or_else(|| "null".to_string(), |reason| format!("\"{reason:?}\""));
    let fusion = summary.fusion.map_or_else(
        || "null".to_string(),
        |fact| {
            format!(
                "{{\"constructor_block\":{},\"constructor_statement\":{},\"channel_block\":{},\"channel_statement\":{},\"channel_method\":{},\"direct_method\":{},\"private_constructor\":{},\"rewritten\":{}}}",
                fact.constructor_block,
                fact.constructor_statement,
                fact.channel_block,
                fact.channel_statement,
                fact.channel_method_def_id,
                fact.direct_method_def_id,
                fact.private_constructor_def_id.map_or_else(|| "null".to_string(), |id| id.to_string()),
                fact.rewritten,
            )
        },
    );
    let fusion_rejection = summary
        .fusion_rejection
        .map_or_else(|| "null".to_string(), |reason| format!("\"{reason:?}\""));
    let endpoint_escapes = summary
        .endpoint_escapes
        .iter()
        .map(|escape| format!("{{\"local\":{},\"kind\":\"{:?}\"}}", escape.local, escape.kind))
        .collect::<Vec<_>>()
        .join(",");
    let channel_occupancy = summary
        .channel_occupancy
        .iter()
        .map(|fact| {
            format!(
                "{{\"channel\":{},\"proven_peak\":{},\"proven_final\":{},\"events\":{},\"complete\":{}}}",
                fact.channel_index,
                fact.occupancy
                    .proven_peak
                    .map_or_else(|| "null".to_string(), |value| value.to_string()),
                fact.occupancy
                    .proven_final
                    .map_or_else(|| "null".to_string(), |value| value.to_string()),
                fact.occupancy.events,
                fact.occupancy.complete,
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let json = format!(
        "{{\"def_id\":{},\"endpoint\":{},\"rule\":{},\"mir_fingerprint\":{},\"role\":\"{:?}\",\"arity\":{},\"is_async\":{},\"frontend_direct_unary\":{},\"queue_bound\":\"{:?}\",\"lowering\":\"{:?}\",\"occupancy\":{{\"proven_peak\":{},\"proven_final\":{},\"events\":{},\"complete\":{}}},\"channel_occupancy\":[{}],\"instance_closedness\":\"{:?}\",\"instance_closedness_reason\":\"{:?}\",\"mode\":\"{:?}\",\"calls\":{},\"call_edges\":[{}],\"function_facts\":[{}],\"yields\":{},\"unknown_effects\":{},\"solver_steps\":{},\"solver_complete\":{},\"locally_closed\":{},\"escapes\":[{}],\"endpoint_escapes\":[{}],\"value_flows\":[{}],\"local_facts\":[{}],\"operations\":[{}],\"direct_candidate\":{},\"fusion\":{},\"fusion_rejection\":{},\"rejection\":{}}}\n",
        local_def_id.index(),
        summary.endpoint_def_id,
        summary.rule_def_id,
        summary.mir_fingerprint,
        summary.role,
        summary.arity,
        summary.is_async,
        summary.frontend_direct_unary,
        summary.queue_bound,
        summary.lowering,
        summary.occupancy.proven_peak.map_or_else(|| "null".to_string(), |value| value.to_string()),
        summary
            .occupancy
            .proven_final
            .map_or_else(|| "null".to_string(), |value| value.to_string()),
        summary.occupancy.events,
        summary.occupancy.complete,
        channel_occupancy,
        summary.instance_closedness,
        summary.instance_closedness_reason,
        mode,
        summary.calls,
        call_edges,
        function_facts,
        summary.yields,
        summary.unknown_effects,
        summary.solver_steps,
        summary.solver_complete,
        summary.locally_closed,
        escapes,
        endpoint_escapes,
        value_flows,
        local_facts,
        operation_kinds,
        summary.direct_candidate,
        fusion,
        fusion_rejection,
        rejection,
    );
    // Local indices repeat in every compilation unit. Include the stable
    // crate identity so a shared dump directory never silently overwrites a
    // different crate's body.
    let crate_tag = tcx.stable_crate_id(LOCAL_CRATE).as_u64();
    let path = directory.join(format!("body-{crate_tag:016x}-{}.json", local_def_id.index()));
    if let Err(error) = fs::write(&path, json) {
        tracing::warn!(target: "rustc_join", ?error, path = ?path, "could not write join CFA summary");
    }
}

/// Materialize the typed operation stream in analysis MIR.
///
/// A call-site operation is attached to the ordinary `Call` terminator. That
/// terminator already owns the function, argument and destination operands, so
/// no second statement is needed (or permitted) to describe their uses. The
/// remaining body-boundary operations are represented by operand-free legacy
/// intrinsics until their dedicated MIR forms are implemented. All of this
/// metadata remains available through optimized MIR and is consumed only at
/// the backend boundary.
fn join_call_kind(kind: JoinOperationKind) -> Option<JoinOperationKind> {
    match kind {
        JoinOperationKind::CreateGroup
        | JoinOperationKind::Register
        | JoinOperationKind::Demand
        | JoinOperationKind::Match
        | JoinOperationKind::CompleteReplies
        | JoinOperationKind::WithdrawOrAbandon
        | JoinOperationKind::CancelScope => Some(kind),
        JoinOperationKind::OrdinaryCall
        | JoinOperationKind::Yield
        | JoinOperationKind::Return
        | JoinOperationKind::Escape => None,
    }
}

fn local_join_def_id(index: Option<u32>) -> Option<DefId> {
    index
        .filter(|index| *index != u32::MAX)
        .map(|index| DefId::local(rustc_span::def_id::DefIndex::from_usize(index as usize)))
}

/// Attach compiler-owned descriptors to known join calls in any body.
///
/// Join bodies also receive the body-boundary marker stream below, but callers
/// such as an ordinary or async function may contain the only observable
/// registration site. Keeping the call descriptor on the real terminator lets
/// later MIR passes see the typed group/channel/rule identity without requiring
/// the caller itself to be classified as a join body.
fn install_join_call_descriptors<'tcx>(body: &mut Body<'tcx>, operations: &[JoinMirOperation]) {
    if body.basic_blocks.is_empty() {
        return;
    }

    let mut call_descriptors = BTreeMap::new();
    for operation in operations {
        let Some(kind) = join_call_kind(operation.kind) else { continue };
        if operation.block == u32::MAX {
            continue;
        }
        let block = mir::BasicBlock::from_usize(operation.block as usize);
        let Some(block_data) = body.basic_blocks.get(block) else { continue };
        let statement = operation.statement as usize;
        if statement != block_data.statements.len()
            || !matches!(block_data.terminator().kind, TerminatorKind::Call { .. })
        {
            continue;
        }
        call_descriptors.entry((block.index(), statement)).or_insert(JoinCall {
            kind,
            lowering: JoinLoweringStrategy::Generic,
            certificate_id: None,
            group_def_id: local_join_def_id(operation.group_def_id),
            channel_index: operation.channel_index,
            rule_index: operation.rule_index,
            queue_bound: operation.queue_bound,
            endpoint_def_id: local_join_def_id(operation.endpoint_def_id),
            rule_def_id: local_join_def_id(operation.rule_def_id),
        });
    }

    for ((block, statement), descriptor) in call_descriptors {
        let block = mir::BasicBlock::from_usize(block);
        if statement != body.basic_blocks[block].statements.len() {
            continue;
        }
        if let TerminatorKind::Call { join, .. } =
            &mut body.basic_blocks_mut()[block].terminator_mut().kind
        {
            if join.is_none() {
                *join = Some(descriptor);
            }
        }
    }
}

fn install_join_intrinsics<'tcx>(body: &mut Body<'tcx>, summary: &JoinCfaSummary) {
    if body.basic_blocks.is_empty() {
        return;
    }
    install_join_call_descriptors(body, &summary.operations);
    if body.basic_blocks.iter().any(|block| {
        block.statements.iter().any(|statement| {
            matches!(
                &statement.kind,
                StatementKind::Intrinsic(intrinsic)
                    if matches!(intrinsic.as_ref(), rustc_middle::mir::NonDivergingIntrinsic::Join(_))
            )
        })
    }) {
        return;
    }

    let mut pending = Vec::new();
    for operation in &summary.operations {
        // Escape is a fact about ownership, not an executable event, and has
        // no valid MIR location. Keep it in the summary only.
        if operation.block == u32::MAX {
            continue;
        }
        let block = mir::BasicBlock::from_usize(operation.block as usize);
        let Some(block_data) = body.basic_blocks.get(block) else { continue };
        let statement = operation.statement as usize;

        // The location immediately after a block's statements denotes its
        // terminator. Preserve the join identity on that terminator instead
        // of materialising a duplicate operand-bearing statement beside it.
        if statement == block_data.statements.len()
            && matches!(block_data.terminator().kind, TerminatorKind::Call { .. })
        {
            continue;
        }

        // Ordinary calls have their complete semantics in the terminator and
        // do not need a marker at all. A TailCall is intentionally unsupported
        // by this first descriptor slice; its operation remains in the CFA
        // summary for diagnostics and future lowering.
        if operation.kind == JoinOperationKind::OrdinaryCall {
            continue;
        }
        // Completion is a body effect, not an entry marker. The compatibility
        // expansion currently records it at START_BLOCK, but materialising
        // that location would falsely claim that replies were published
        // before the reaction body executes. Keep it in the summary until a
        // real completion operation is available.
        if operation.kind == JoinOperationKind::CompleteReplies
            && statement != block_data.statements.len()
        {
            continue;
        }
        let source_info = block_data
            .statements
            .get(statement)
            .map(|statement| statement.source_info)
            .unwrap_or(block_data.terminator().source_info);

        let marker = JoinIntrinsic {
            kind: operation.kind,
            block: operation.block,
            statement: operation.statement,
            group_def_id: operation.group_def_id,
            channel_index: operation.channel_index,
            rule_index: operation.rule_index,
            reply_channel_indices: operation.reply_channel_indices.clone(),
            queue_bound: operation.queue_bound,
            endpoint_def_id: operation.endpoint_def_id,
            rule_def_id: operation.rule_def_id,
            receiver: None,
            destination: operation
                .destination_local
                .map(|local| Place::from(mir::Local::from_usize(local as usize))),
            arguments: Box::new([]),
        };
        pending.push((block, statement.min(block_data.statements.len()), source_info, marker));
    }

    // Insert backwards so the source locations recorded in the operation
    // summary continue to denote the original MIR terminator/statement.
    pending.sort_by_key(|(block, statement, _, _)| (block.index(), *statement));
    for (block, statement, source_info, marker) in pending.into_iter().rev() {
        body.basic_blocks_mut()[block].statements.insert(
            statement,
            Statement::new(
                source_info,
                StatementKind::Intrinsic(Box::new(rustc_middle::mir::NonDivergingIntrinsic::Join(
                    marker,
                ))),
            ),
        );
    }
}

/// Select the deliberately narrow atomic-token ABI.  The state-token proof
/// establishes boundedness and uniqueness; this additional typed check keeps
/// the runtime representation honest: channel zero must be the one-way
/// `u64` token, and the sole rule must complete channel one.
fn is_exact_atomic_u64_pair<'tcx>(
    tcx: TyCtxt<'tcx>,
    endpoint: &rustc_middle::middle::joins::JoinDefinition<'tcx>,
    rule: &rustc_middle::middle::joins::JoinRule<'tcx>,
) -> bool {
    // The runtime ABI uses an AtomicU8 state machine around an AtomicU64
    // payload.  Do not select it for targets which cannot provide both
    // widths; those targets retain the ordinary fixed-pair mutex path.
    if !tcx.sess.target.atomic_cas
        || tcx.sess.target.min_atomic_width() > 8
        || tcx.sess.target.max_atomic_width() < 64
    {
        return false;
    }
    if rule.reply_channel_indices != [1] || endpoint.channels.len() != 2 {
        return false;
    }
    let Some(token) = endpoint.channels.first() else { return false };
    let signature =
        tcx.fn_sig(token.method_def_id.to_def_id()).instantiate_identity().skip_binder();
    signature.inputs().len() == 2
        && signature.inputs().get(1) == Some(&tcx.types.u64)
        && signature.output() == tcx.types.unit
}

/// Give each positive state-token proof a deterministic identity which can be
/// carried through MIR.  This deliberately hashes compiler-owned coordinates
/// and transition evidence only; source spans, generated names, and runtime
/// implementation details are excluded so the identity remains useful after
/// lowering and across equivalent generated bodies.
fn state_token_certificate_id(proof: &JoinStateTokenProof, strategy: JoinLoweringStrategy) -> u64 {
    let mut hasher = FxHasher::default();
    proof.endpoint_def_id.hash(&mut hasher);
    proof.instance_body_def_id.hash(&mut hasher);
    proof.allocation_block.hash(&mut hasher);
    proof.allocation_statement.hash(&mut hasher);
    proof.rule_index.hash(&mut hasher);
    proof.channel_index.hash(&mut hasher);
    proof.seed_events.hash(&mut hasher);
    proof.claim_events.hash(&mut hasher);
    proof.reemit_events.hash(&mut hasher);
    proof.proven_bound.hash(&mut hasher);
    proof.status.hash(&mut hasher);
    proof.rejection.hash(&mut hasher);
    for transition in &proof.transitions {
        transition.body_def_id.hash(&mut hasher);
        transition.role.hash(&mut hasher);
        transition.kind.hash(&mut hasher);
        transition.block.hash(&mut hasher);
        transition.statement.hash(&mut hasher);
    }
    strategy.hash(&mut hasher);
    hasher.finish()
}

/// One endpoint-wide lowering decision.  Every generated constructor,
/// channel adapter, and dispatch body for an endpoint consumes this same
/// plan; a body-local pass must not independently decide that only one part
/// of a shared instance can use the fixed representation.
#[derive(Copy, Clone, Debug)]
struct JoinEndpointLoweringPlan {
    endpoint_def_id: u32,
    inline_mask: u64,
    strategy: JoinLoweringStrategy,
    certificate_id: u64,
}

/// Validate and combine all positive state-token records for one concrete
/// endpoint instance.  The returned certificate binds the endpoint identity,
/// unique allocation, proof identities, mask, and selected strategy.  Any
/// ambiguity (multiple instances, mismatched proof origins, mixed strategies,
/// or an unsupported bound) retains the generic representation.
fn validated_endpoint_lowering_plan(
    endpoint: &rustc_middle::middle::joins::JoinDefinition<'_>,
    summary: &rustc_middle::middle::joins::JoinCfaCrateSummary,
) -> Option<JoinEndpointLoweringPlan> {
    let endpoint_def_id = endpoint.endpoint_def_id?.index() as u32;
    let mut instances =
        summary.instances.iter().filter(|instance| instance.endpoint_def_id == endpoint_def_id);
    let instance = instances.next()?;
    if instances.next().is_some() || instance.status != JoinCfaInstanceStatus::Unique {
        return None;
    }

    // Endpoint-wide JCAM transition certificates take precedence over the
    // older single-token proof. They describe a finite set of persistent
    // one-way state bits while leaving result/request channels dynamic.
    // The runtime representation retains a correctness-preserving overflow
    // queue until caller-sensitive multiplicity is proved, so selecting this
    // plan does not depend on recognizing a particular lock or queue library.
    if let Some(machine) = summary.state_machines.iter().find(|machine| {
        machine.endpoint_def_id == endpoint_def_id
            && machine.status == JoinStateTokenStatus::Proven
    }) {
        let mut certificate = FxHasher::default();
        endpoint_def_id.hash(&mut certificate);
        instance.body_def_id.hash(&mut certificate);
        instance.allocation_block.hash(&mut certificate);
        instance.allocation_statement.hash(&mut certificate);
        machine.certificate_id.hash(&mut certificate);
        machine.state_mask.hash(&mut certificate);
        return Some(JoinEndpointLoweringPlan {
            endpoint_def_id,
            inline_mask: machine.state_mask,
            strategy: JoinLoweringStrategy::FiniteStateMask,
            certificate_id: certificate.finish(),
        });
    }

    let mut lowerings = summary
        .state_token_lowerings
        .iter()
        .filter(|lowering| {
            lowering.endpoint_def_id == endpoint_def_id
                && matches!(
                    lowering.strategy,
                    JoinLoweringStrategy::FixedUnarySlot
                        | JoinLoweringStrategy::FixedPairMatcher
                        | JoinLoweringStrategy::FixedAtomicU64Pair
                )
                && lowering.proven_bound == JoinQueueBound::AtMost(1)
        })
        .collect::<Vec<_>>();
    if lowerings.is_empty() {
        return None;
    }
    lowerings.sort_by_key(|lowering| (lowering.rule_index, lowering.channel_index));
    let strategy = lowerings[0].strategy;
    if lowerings.iter().any(|lowering| lowering.strategy != strategy) {
        return None;
    }

    let mut inline_mask = 0u64;
    let mut certificate = FxHasher::default();
    endpoint_def_id.hash(&mut certificate);
    instance.body_def_id.hash(&mut certificate);
    instance.allocation_block.hash(&mut certificate);
    instance.allocation_statement.hash(&mut certificate);
    strategy.hash(&mut certificate);
    for lowering in lowerings {
        if lowering.channel_index >= u64::BITS as u32 {
            return None;
        }
        let mut proofs = summary.state_tokens.iter().filter(|proof| {
            proof.endpoint_def_id == endpoint_def_id
                && proof.rule_index == lowering.rule_index
                && proof.channel_index == lowering.channel_index
                && proof.status == JoinStateTokenStatus::Proven
                && proof.proven_bound == JoinQueueBound::AtMost(1)
                && proof.instance_body_def_id == Some(instance.body_def_id)
                && proof.allocation_block == Some(instance.allocation_block)
                && proof.allocation_statement == Some(instance.allocation_statement)
        });
        let proof = proofs.next()?;
        if proofs.next().is_some() {
            return None;
        }
        // The per-channel certificate is part of the endpoint certificate;
        // later MIR consumers can use either identity when diagnosing a
        // rejected or stale rewrite.
        lowering.certificate_id.hash(&mut certificate);
        proof.rule_index.hash(&mut certificate);
        proof.channel_index.hash(&mut certificate);
        inline_mask |= 1u64 << lowering.channel_index;
    }
    inline_mask.hash(&mut certificate);
    Some(JoinEndpointLoweringPlan {
        endpoint_def_id,
        inline_mask,
        strategy,
        certificate_id: certificate.finish(),
    })
}

/// Return the source rule/channel lowering which is safe to apply to one
/// concrete generated endpoint constructor.  A lowering record is not enough
/// by itself: the proof must also identify exactly one unscoped constructor
/// allocation and the current constructor body must still contain the
/// compiler-emitted policy call with its conservative literals.
fn state_token_constructor_lowering<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    endpoint: &rustc_middle::middle::joins::JoinDefinition<'tcx>,
    summary: &rustc_middle::middle::joins::JoinCfaCrateSummary,
) -> Option<JoinEndpointLoweringPlan> {
    let plan = validated_endpoint_lowering_plan(endpoint, summary)?;
    let endpoint_def_id = plan.endpoint_def_id;
    let constructor_def_id = endpoint.constructor_def_id?;
    let constructor_u32 = constructor_def_id.index() as u32;
    if plan.strategy == JoinLoweringStrategy::FiniteStateMask {
        // The endpoint-wide certificate has already validated the concrete
        // instance.  Reuse the same constructor literal check as the older
        // state-token path, but do not require a per-rule token record.
        if endpoint.scoped_constructor_def_id == Some(constructor_def_id)
            || endpoint.constructor_def_id != Some(constructor_def_id)
        {
            return None;
        }
        let typing_env = body.typing_env(tcx);
        let expected_channels = endpoint.declared_channels as u64;
        let matches = body
            .basic_blocks
            .iter_enumerated()
            .filter(|(_, block_data)| {
                let TerminatorKind::Call { func, args, .. } = &block_data.terminator().kind
                else {
                    return false;
                };
                let Some((callee, _)) = func.const_fn_def() else { return false };
                if !is_join_mask_constructor(tcx, callee) || args.len() != 2 {
                    return false;
                }
                let channels = args[0]
                    .node
                    .constant()
                    .and_then(|constant| constant.const_.try_eval_target_usize(tcx, typing_env));
                let mask = args[1]
                    .node
                    .constant()
                    .and_then(|constant| constant.const_.try_eval_target_usize(tcx, typing_env));
                channels == Some(expected_channels) && mask == Some(0)
            })
            .count();
        if matches != 1 {
            return None;
        }
        return Some(plan);
    }
    let lowerings = summary
        .state_token_lowerings
        .iter()
        .filter(|lowering| {
            lowering.endpoint_def_id == endpoint_def_id
                && matches!(
                    lowering.strategy,
                    JoinLoweringStrategy::FixedUnarySlot
                        | JoinLoweringStrategy::FixedPairMatcher
                        | JoinLoweringStrategy::FixedAtomicU64Pair
                )
                && lowering.proven_bound == JoinQueueBound::AtMost(1)
        })
        .collect::<Vec<_>>();
    for lowering in lowerings {
        let proof = summary.state_tokens.iter().find(|proof| {
            proof.endpoint_def_id == endpoint_def_id
                && proof.rule_index == lowering.rule_index
                && proof.channel_index == lowering.channel_index
                && proof.status == JoinStateTokenStatus::Proven
        })?;
        let allocation_block = proof.allocation_block?;
        let allocation_statement = proof.allocation_statement?;
        let instance_body_def_id = proof.instance_body_def_id?;
        let allocation_record =
            summary.bodies.iter().find(|record| record.body_def_id == instance_body_def_id)?;
        let allocation = allocation_record.call_edges.iter().find(|edge| {
            edge.target == JoinCallTargetKind::Constructor
                && edge.endpoint_def_id == Some(endpoint_def_id)
                && edge.callee == Some(constructor_u32)
                && edge.block == allocation_block
                && edge.statement == allocation_statement
        })?;
        let _ = allocation;
    }
    // A scoped constructor has different cancellation/tracing ownership and
    // cannot be replaced by the unscoped per-channel policy constructor.
    if endpoint.scoped_constructor_def_id == Some(constructor_def_id)
        || endpoint.constructor_def_id != Some(constructor_def_id)
    {
        return None;
    }
    // The current bridge uses an exact compiler-owned marker call emitted by
    // the builtin macro.  Its name is checked together with the argument
    // types/values below; no source-level endpoint or runtime symbol is
    // searched in ordinary callers.
    let typing_env = body.typing_env(tcx);
    let expected_channels = endpoint.declared_channels as u64;
    let mut matches = Vec::new();
    for (block, block_data) in body.basic_blocks.iter_enumerated() {
        let TerminatorKind::Call { func, args, .. } = &block_data.terminator().kind else {
            continue;
        };
        let Some((callee, _)) = func.const_fn_def() else { continue };
        if !is_join_mask_constructor(tcx, callee) {
            continue;
        }
        if args.len() != 2 {
            continue;
        }
        let Some(channels) = args[0]
            .node
            .constant()
            .and_then(|constant| constant.const_.try_eval_target_usize(tcx, typing_env))
        else {
            continue;
        };
        let Some(inline_mask) = args[1]
            .node
            .constant()
            .and_then(|constant| constant.const_.try_eval_target_usize(tcx, typing_env))
        else {
            continue;
        };
        if channels == expected_channels && inline_mask == 0 {
            matches.push(block);
        }
    }
    if matches.len() == 1 { Some(plan) } else { None }
}

/// Resolve the compiler-owned typed pair constructor beside the generic mask
/// constructor.  The generated endpoint still starts on
/// `new_with_channel_mask`, which is the safe fallback in every mode.  A
/// positive proof may retarget only a `PairMatcher` call to this distinct
/// runtime entry point; no runtime lock implementation is inspected or
/// selected here.
fn fixed_pair_constructor<'tcx>(
    tcx: TyCtxt<'tcx>,
    generic: DefId,
    generic_args: GenericArgsRef<'tcx>,
) -> Option<DefId> {
    fixed_pair_constructor_named(tcx, generic, generic_args, "new_with_fixed_pair_mask")
}

fn fixed_atomic_pair_constructor<'tcx>(
    tcx: TyCtxt<'tcx>,
    generic: DefId,
    generic_args: GenericArgsRef<'tcx>,
) -> Option<DefId> {
    fixed_pair_constructor_named(tcx, generic, generic_args, "new_with_fixed_atomic_u64_pair_mask")
}

/// Resolve the endpoint-wide finite-state constructor. Its ABI is identical
/// to the generic dynamic constructor; only the runtime representation policy
/// changes. Keeping this as an ABI-checked shim makes the proof consumer
/// independent of the library's internal state layout.
fn finite_state_constructor<'tcx>(
    tcx: TyCtxt<'tcx>,
    generic: DefId,
    generic_args: GenericArgsRef<'tcx>,
) -> Option<DefId> {
    if tcx.crate_name(generic.krate).as_str() != "joins_runtime"
        || tcx.item_name(generic).as_str() != "new_with_channel_mask"
    {
        return None;
    }
    let signature = tcx.fn_sig(generic).instantiate(tcx, generic_args).skip_binder();
    let ty::Adt(output, _) = signature.output().kind() else { return None };
    if tcx.crate_name(output.did().krate).as_str() != "joins_runtime"
        || tcx.item_name(output.did()).as_str() != "DynamicMatcher"
    {
        return None;
    }
    let mut containers = vec![tcx.parent(generic)];
    containers.extend(tcx.inherent_impls(output.did()).iter().copied());
    containers
        .into_iter()
        .flat_map(|container| {
            tcx.associated_items(container).in_definition_order().filter(|item| item.is_fn())
        })
        .filter(|item| tcx.item_name(item.def_id).as_str() == "new_with_finite_state_mask")
        .map(|item| item.def_id)
        .find(|target| {
            let target_signature = tcx.fn_sig(*target).instantiate(tcx, generic_args).skip_binder();
            same_join_abi(tcx, signature, target_signature)
        })
}

fn fixed_pair_constructor_named<'tcx>(
    tcx: TyCtxt<'tcx>,
    generic: DefId,
    generic_args: GenericArgsRef<'tcx>,
    target_name: &str,
) -> Option<DefId> {
    if tcx.crate_name(generic.krate).as_str() != "joins_runtime"
        || tcx.item_name(generic).as_str() != "new_with_channel_mask"
    {
        return None;
    }
    let signature = tcx.fn_sig(generic).instantiate(tcx, generic_args).skip_binder();
    let ty::Adt(output, _) = signature.output().kind() else { return None };
    if tcx.crate_name(output.did().krate).as_str() != "joins_runtime"
        || tcx.item_name(output.did()).as_str() != "PairMatcher"
    {
        return None;
    }
    let mut containers = vec![tcx.parent(generic)];
    containers.extend(tcx.inherent_impls(output.did()).iter().copied());
    containers
        .into_iter()
        .flat_map(|container| {
            tcx.associated_items(container).in_definition_order().filter(|item| item.is_fn())
        })
        .filter(|item| tcx.item_name(item.def_id).as_str() == target_name)
        .map(|item| item.def_id)
        .find(|target| {
            let target_signature = tcx.fn_sig(*target).instantiate(tcx, generic_args).skip_binder();
            same_join_abi(tcx, signature, target_signature)
                && matches!(target_signature.output().kind(), ty::Adt(..))
        })
}

/// Compare the complete instantiated function ABI before a compiler-owned
/// runtime shim is selected. Arity/output checks alone are insufficient: two
/// generic methods can have the same shape while moving different payload
/// types, safety modes, variadic conventions, or Rust/C ABIs. The call is
/// still validated by MIR type checking after replacement, but this predicate
/// is the proof gate that prevents a malformed or unrelated helper from being
/// selected in the first place.
fn same_join_abi<'tcx>(tcx: TyCtxt<'tcx>, lhs: ty::FnSig<'tcx>, rhs: ty::FnSig<'tcx>) -> bool {
    tcx.erase_and_anonymize_regions(lhs.inputs_and_output)
        == tcx.erase_and_anonymize_regions(rhs.inputs_and_output)
        && lhs.abi() == rhs.abi()
        && lhs.safety() == rhs.safety()
        && lhs.c_variadic() == rhs.c_variadic()
        && lhs.splatted() == rhs.splatted()
}

/// Operation shims are methods, so their receiver lifetime may have a
/// distinct late-bound identity even when it denotes the same
/// `PairMatcher<...>`. Compare every payload and result type after erasing
/// those region identities; the receiver's ADT is already restricted to the
/// proven endpoint's inherent impl below.
fn same_join_operation_abi<'tcx>(
    tcx: TyCtxt<'tcx>,
    lhs: ty::FnSig<'tcx>,
    rhs: ty::FnSig<'tcx>,
) -> bool {
    let lhs_inputs = lhs.inputs();
    let rhs_inputs = rhs.inputs();
    lhs_inputs.len() == rhs_inputs.len()
        && lhs_inputs.iter().skip(1).zip(rhs_inputs.iter().skip(1)).all(|(lhs, rhs)| {
            tcx.erase_and_anonymize_regions(*lhs) == tcx.erase_and_anonymize_regions(*rhs)
        })
        && tcx.erase_and_anonymize_regions(lhs.output())
            == tcx.erase_and_anonymize_regions(rhs.output())
        && lhs.abi() == rhs.abi()
        && lhs.safety() == rhs.safety()
        && lhs.c_variadic() == rhs.c_variadic()
        && lhs.splatted() == rhs.splatted()
}

/// Resolve one of the compiler-owned fixed-pair operation shims beside the
/// generic runtime method. The caller has already matched the generated HIR
/// body to the proven endpoint/channel, so this identity check does not infer
/// anything from a user lock or from a source spelling.
fn fixed_pair_method<'tcx>(
    tcx: TyCtxt<'tcx>,
    generic: DefId,
    generic_args: GenericArgsRef<'tcx>,
    fixed_name: &str,
) -> Option<DefId> {
    if tcx.crate_name(generic.krate).as_str() != "joins_runtime"
        || !matches!(
            tcx.item_name(generic).as_str(),
            "submit_left_at"
                | "submit_left_oneway_at"
                | "submit_right_at"
                | "submit_right_and_dispatch_at"
                | "submit_right_oneway_at"
                | "__join_dispatch_once_at"
        )
    {
        return None;
    }
    let signature = tcx.fn_sig(generic).instantiate(tcx, generic_args).skip_binder();
    let receiver_def = signature.inputs().first().and_then(|ty| ty.peel_refs().ty_adt_def());
    let mut containers = vec![tcx.parent(generic)];
    if let Some(receiver_def) = receiver_def {
        containers.extend(tcx.inherent_impls(receiver_def.did()).iter().copied());
    }
    containers
        .into_iter()
        .flat_map(|container| {
            tcx.associated_items(container).in_definition_order().filter(|item| item.is_fn())
        })
        .filter(|item| tcx.item_name(item.def_id).as_str() == fixed_name)
        .map(|item| item.def_id)
        .find(|target| {
            let target_signature = tcx.fn_sig(*target).instantiate(tcx, generic_args).skip_binder();
            // Generated fixed shims are compiler-owned ABI twins. Compare all
            // payload/result types and ABI flags while ignoring only receiver
            // lifetime identities; MIR validation still checks the final call.
            same_join_operation_abi(tcx, signature, target_signature)
        })
}

/// Return the single endpoint-wide representation selected for a generated
/// channel or dispatch body. Constructor lowering adds the stricter
/// literal/unique-call-site checks; all other endpoint methods consume this
/// same validated plan.
fn proven_endpoint_lowering<'tcx>(
    endpoint: &rustc_middle::middle::joins::JoinDefinition<'tcx>,
    summary: &rustc_middle::middle::joins::JoinCfaCrateSummary,
) -> Option<JoinEndpointLoweringPlan> {
    validated_endpoint_lowering_plan(endpoint, summary)
}

/// Proof-consuming bridge from the compiler's per-channel state-token record
/// to the runtime's mixed queue representation.  The generated constructor
/// starts with a zero mask.  Only optimize mode with positive certificates
/// replaces that scalar with the proven channel bits; off/analyze leave the
/// exact same generic constructor path untouched.
impl<'tcx> crate::MirPass<'tcx> for JoinStorageLowering {
    fn policy(&self, _ctx: &crate::PassCtx<'_>) -> PassPolicy {
        PassPolicy::Required
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        if !tcx.features().joins() || tcx.sess.opts.unstable_opts.join_cfa != JoinCfaMode::Optimize
        {
            return;
        }
        let Some(local_def_id) = body.source.def_id().as_local() else { return };
        let Some(endpoint) = tcx.join_definitions(()).endpoints.iter().find(|endpoint| {
            endpoint.constructor_def_id == Some(local_def_id)
                || endpoint.channels.iter().any(|channel| channel.method_def_id == local_def_id)
                || endpoint.rules.iter().any(|rule| rule.method_def_id == local_def_id)
        }) else {
            return;
        };
        let is_constructor = endpoint.constructor_def_id == Some(local_def_id);
        let channel_index = endpoint
            .channels
            .iter()
            .find(|channel| channel.method_def_id == local_def_id)
            .map(|channel| channel.index);
        let is_dispatch = endpoint.rules.iter().any(|rule| rule.method_def_id == local_def_id);
        let summary = tcx.join_cfa_crate_summary(());
        let lowering = if is_constructor {
            state_token_constructor_lowering(tcx, body, endpoint, summary)
        } else {
            proven_endpoint_lowering(endpoint, summary)
        };
        let Some(plan) = lowering else { return };
        let inline_mask = plan.inline_mask;
        let strategy = plan.strategy;
        let pair_strategy = matches!(
            strategy,
            JoinLoweringStrategy::FixedPairMatcher | JoinLoweringStrategy::FixedAtomicU64Pair
        );
        let finite_state_strategy = strategy == JoinLoweringStrategy::FiniteStateMask;
        if !is_constructor && !pair_strategy && !finite_state_strategy {
            return;
        }
        // The first fixed-pair runtime representation has an inline left
        // token and a FIFO right side. Do not select it for a certificate
        // whose only bounded channel is the right side; retain the generic
        // matcher until a symmetric representation is implemented.
        if pair_strategy && inline_mask != 1 {
            return;
        }
        let typing_env = body.typing_env(tcx);
        let expected_channels = endpoint.declared_channels as u64;
        let mask_size = tcx
            .layout_of(body.typing_env(tcx).as_query_input(tcx.types.u64))
            .unwrap_or_else(|_| bug!("could not lay out u64 for join storage lowering"))
            .size;
        // Preflight every rewrite before mutating the body.  A proof-selected
        // endpoint has several generated shims (constructor, admissions and
        // dispatch); changing the first call and discovering a missing ABI
        // twin at a later call would leave a fixed matcher reachable through
        // its generic operation path.  Keep the plan immutable until every
        // compiler/runtime identity and literal has been checked.
        let mut planned = Vec::new();
        for (block, block_data) in body.basic_blocks.iter_enumerated() {
            let span = block_data.terminator().source_info.span;
            let TerminatorKind::Call { func, args, .. } = &block_data.terminator().kind else {
                continue;
            };
            let Some((callee, generic_args)) = func.const_fn_def() else { continue };
            if is_constructor {
                if !is_join_mask_constructor(tcx, callee) {
                    continue;
                }
                if args.len() != 2 {
                    // A recognized policy call with a changed shape is not a
                    // safe candidate.  Do not rewrite another call in this
                    // body and leave this one on an incompatible ABI.
                    return;
                }
                let channels = args[0]
                    .node
                    .constant()
                    .and_then(|constant| constant.const_.try_eval_target_usize(tcx, typing_env));
                let mask = args[1]
                    .node
                    .constant()
                    .and_then(|constant| constant.const_.try_eval_target_usize(tcx, typing_env));
                if channels != Some(expected_channels) || mask != Some(0) {
                    return;
                }
                let target = if pair_strategy {
                    let target = match strategy {
                        JoinLoweringStrategy::FixedAtomicU64Pair => {
                            fixed_atomic_pair_constructor(tcx, callee, generic_args)
                        }
                        JoinLoweringStrategy::FixedPairMatcher => {
                            fixed_pair_constructor(tcx, callee, generic_args)
                        }
                        _ => None,
                    };
                    let Some(target) = target else {
                        // The positive proof is not permission to guess an
                        // ABI twin.  If the runtime/compiler pair contract is
                        // absent, leave this body entirely generic.
                        return;
                    };
                    Some(target)
                } else if finite_state_strategy {
                    let Some(target) = finite_state_constructor(tcx, callee, generic_args) else {
                        return;
                    };
                    Some(target)
                } else {
                    None
                };
                planned.push((
                    block,
                    target,
                    generic_args,
                    span,
                    Some(inline_mask),
                    JoinOperationKind::CreateGroup,
                    None,
                ));
                continue;
            }

            // The finite-state policy is selected at the constructor. The
            // ordinary DynamicMatcher entry points consult that policy and
            // take the masked claim path; unlike the fixed-pair ABI they need
            // no per-method shim or call-target rewrite. Still carry the
            // proof on those real MIR calls, so a later typed claim lowering
            // can consume the same endpoint certificate instead of recovering
            // it from the constructor or a runtime symbol name.
            if finite_state_strategy {
                let item_symbol = tcx.item_name(callee);
                let item_name = item_symbol.as_str();
                let is_finite_operation = tcx.crate_name(callee.krate).as_str()
                    == "joins_runtime"
                    && matches!(
                        item_name,
                        "submit_at"
                            | "submit_oneway_at"
                            | "submit_and_dispatch_at"
                            | "__join_dispatch_once_at"
                            | "__join_dispatch_all_once_at"
                    );
                if is_finite_operation {
                    let operation_kind = if item_name.starts_with("__join_dispatch") {
                        JoinOperationKind::Match
                    } else {
                        JoinOperationKind::Register
                    };
                    planned.push((
                        block,
                        None,
                        generic_args,
                        span,
                        None,
                        operation_kind,
                        channel_index,
                    ));
                }
                continue;
            }
            if !pair_strategy {
                continue;
            }
            let item_symbol = tcx.item_name(callee);
            let item_name = item_symbol.as_str();
            let is_generic_fixed_operation = tcx.crate_name(callee.krate).as_str()
                == "joins_runtime"
                && matches!(
                    item_name,
                    "submit_left_at"
                        | "submit_left_oneway_at"
                        | "submit_right_at"
                        | "submit_right_and_dispatch_at"
                        | "submit_right_oneway_at"
                        | "__join_dispatch_once_at"
                );
            // Channel/dispatch bodies contain ordinary helper calls (for
            // example source-location construction) which are not part of
            // the fixed ABI.  Only a recognized generic runtime operation
            // enters the all-or-nothing shim preflight below.
            if !is_generic_fixed_operation {
                continue;
            }
            let fixed_name = if is_dispatch && item_name == "__join_dispatch_once_at" {
                Some(match strategy {
                    JoinLoweringStrategy::FixedAtomicU64Pair => {
                        "__join_dispatch_once_atomic_u64_at"
                    }
                    _ => "__join_dispatch_once_fixed_at",
                })
            } else if let Some(index) = channel_index {
                if strategy == JoinLoweringStrategy::FixedAtomicU64Pair {
                    match (index, item_name) {
                        (0, "submit_left_oneway_at") => Some("submit_left_atomic_u64_oneway_at"),
                        (1, "submit_right_and_dispatch_at") => {
                            Some("submit_right_atomic_u64_and_dispatch_at")
                        }
                        _ => None,
                    }
                } else {
                    match (index, item_name) {
                        (0, "submit_left_at") => Some("submit_left_fixed_at"),
                        (0, "submit_left_oneway_at") => Some("submit_left_oneway_fixed_at"),
                        (1, "submit_right_at") => Some("submit_right_fixed_at"),
                        (1, "submit_right_and_dispatch_at") => {
                            Some("submit_right_fixed_and_dispatch_at")
                        }
                        (1, "submit_right_oneway_at") => Some("submit_right_oneway_fixed_at"),
                        _ => None,
                    }
                }
            } else {
                None
            };
            let Some(fixed_name) = fixed_name else {
                // A generated endpoint operation that has no corresponding
                // fixed shim invalidates the whole body.  Returning before
                // the apply phase prevents a partial retarget.
                return;
            };
            let Some(target) = fixed_pair_method(tcx, callee, generic_args, fixed_name) else {
                // A missing compiler/runtime fixed method is a conservative
                // rejection, never a reason to mutate an earlier call.
                return;
            };
            let operation_kind = if item_name == "__join_dispatch_once_at" {
                JoinOperationKind::Match
            } else {
                JoinOperationKind::Register
            };
            planned.push((
                block,
                Some(target),
                generic_args,
                span,
                None,
                operation_kind,
                channel_index,
            ));
        }

        if planned.is_empty() {
            return;
        }

        // The complete preflight succeeded.  Apply all planned changes in a
        // separate pass; no ABI lookup or shape validation remains on this
        // mutation path.
        for (block, target, generic_args, span, mask, kind, channel_index) in planned {
            let block_data = &mut body.basic_blocks_mut()[block];
            let TerminatorKind::Call { func, args, join, .. } =
                &mut block_data.terminator_mut().kind
            else {
                // The body cannot change between the two passes, but retain a
                // conservative guard if a future MIR pass invalidates that
                // assumption.
                return;
            };
            if let Some(target) = target {
                *func = Operand::function_handle(tcx, target, generic_args.as_slice(), span);
            }
            // The selected strategy is part of the compiler-owned MIR
            // operation, not an inference that later passes should repeat
            // from the rewritten runtime symbol.  The call remains an
            // ordinary typed call; this field is the proof result that makes
            // a future direct state-transition lowering possible.
            if let Some(join) = join {
                join.lowering = strategy;
                join.certificate_id = Some(plan.certificate_id);
            } else {
                // Runtime adapter calls are generated after the source-level
                // channel/dispatch operation has been identified, so they do
                // not always have a frontend descriptor of their own. Attach
                // the proof result to the actual typed call rather than
                // forcing later MIR passes to infer it from the selected
                // helper symbol.
                *join = Some(JoinCall {
                    kind,
                    lowering: strategy,
                    certificate_id: Some(plan.certificate_id),
                    group_def_id: endpoint.endpoint_def_id.map(|id| id.to_def_id()),
                    channel_index,
                    rule_index: None,
                    queue_bound: frontend_queue_bound(endpoint.frontend_queue_bound),
                    endpoint_def_id: endpoint.endpoint_def_id.map(|id| id.to_def_id()),
                    rule_def_id: None,
                });
            }
            if let Some(inline_mask) = mask {
                // Both the generic and fixed constructors receive the proven
                // channel mask. The fixed ABI distinguishes the representation;
                // the mask still carries the per-channel occupancy decision.
                let Some(mask_arg) = args.get_mut(1) else { return };
                *mask_arg = Spanned {
                    span,
                    node: Operand::const_from_scalar(
                        tcx,
                        tcx.types.u64,
                        Scalar::from_uint(inline_mask as u128, mask_size),
                        span,
                    ),
                };
            }
        }
    }
}

/// Identify the compiler-owned runtime policy constructor by crate, symbol,
/// and signature.  The builtin macro emits an absolute `joins_runtime` path,
/// but a name-only check would still allow an unrelated same-named function
/// to be rewritten if generated MIR changes in the future.
fn is_join_mask_constructor(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    if tcx.crate_name(callee.krate).as_str() != "joins_runtime"
        || tcx.item_name(callee).as_str() != "new_with_channel_mask"
    {
        return false;
    }
    let signature = tcx.fn_sig(callee).instantiate_identity().skip_binder();
    if signature.inputs().len() != 2 || signature.c_variadic() {
        return false;
    }
    matches!(
        signature.output().kind(),
        ty::Adt(def, _) if tcx.crate_name(def.did().krate).as_str() == "joins_runtime"
            && matches!(
                tcx.item_name(def.did()).as_str(),
                "DynamicMatcher" | "PairMatcher"
            )
    )
}

impl<'tcx> crate::MirPass<'tcx> for JoinSemanticOps {
    fn policy(&self, _ctx: &crate::PassCtx<'_>) -> PassPolicy {
        // Keeping this pass required makes the pre-coroutine observation
        // independent of optimization level. A future implementation may
        // mutate MIR here, but it must retain the same semantic boundary.
        PassPolicy::Required
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        if !tcx.features().joins() {
            return;
        }
        let cfa_mode = tcx.sess.opts.unstable_opts.join_cfa;

        let Some(local_def_id) = body.source.def_id().as_local() else {
            return;
        };
        let Some((
            endpoint_def_id,
            rule_def_id,
            role,
            arity,
            is_async,
            frontend_direct_unary,
            queue_bound,
            endpoint_def_id_local,
            channel_index,
            rule_index,
        )) = body_descriptor(tcx, local_def_id)
        else {
            // A caller need not itself be generated by the join frontend. It
            // can still contain the source-level registration or demand that
            // must remain visible to later MIR analyses. Visit such bodies
            // with an unclassified fact collector and install only the typed
            // descriptors on their real call terminators.
            let mut facts = JoinBodyFacts {
                endpoint_def_id: None,
                rule_def_id: None,
                channel_index: None,
                rule_index: None,
                queue_bound: JoinQueueBound::Unknown,
                operations: Vec::new(),
                value_flows: Vec::new(),
                closure_facts: Vec::new(),
                function_facts: Vec::new(),
                unknown_function_locals: FxIndexSet::default(),
                callable_locals: body
                    .local_decls
                    .iter()
                    .map(|decl| join_cfa_is_callable_type(decl.ty))
                    .collect(),
                call_edges: Vec::new(),
                escapes: FxIndexSet::default(),
                endpoint_escapes: FxIndexSet::default(),
                endpoint_locals: vec![false; body.local_decls.len()],
                join_call_targets: join_call_target_map(tcx),
                suppress_endpoint_return_escape: false,
                calls: 0,
                yields: 0,
                unknown_effects: 0,
            };
            facts.visit_body(body);
            install_join_call_descriptors(body, &facts.operations);
            return;
        };

        let mut facts = JoinBodyFacts {
            endpoint_def_id: Some(endpoint_def_id),
            rule_def_id: Some(rule_def_id),
            channel_index,
            rule_index,
            queue_bound,
            operations: Vec::new(),
            value_flows: Vec::new(),
            closure_facts: Vec::new(),
            function_facts: Vec::new(),
            unknown_function_locals: FxIndexSet::default(),
            callable_locals: body
                .local_decls
                .iter()
                .map(|decl| join_cfa_is_callable_type(decl.ty))
                .collect(),
            call_edges: Vec::new(),
            escapes: FxIndexSet::default(),
            endpoint_escapes: FxIndexSet::default(),
            endpoint_locals: endpoint_def_id_local
                .map(|endpoint| {
                    body.local_decls
                        .iter()
                        .map(|decl| is_endpoint_type(endpoint, decl.ty))
                        .collect()
                })
                .unwrap_or_default(),
            join_call_targets: join_call_target_map(tcx),
            suppress_endpoint_return_escape: role == JoinBodyRole::Constructor,
            calls: 0,
            yields: 0,
            unknown_effects: 0,
        };
        facts.visit_body(body);

        // Resolve the source rule's reply map once from the typed endpoint
        // descriptor. Completion metadata must carry these channel indices
        // through MIR; a later lowering pass should not reconstruct them from
        // the generated reaction helper's name or tuple layout.
        let reply_channel_indices = if role == JoinBodyRole::ReactionBody {
            endpoint_def_id_local
                .and_then(|endpoint_id| {
                    tcx.join_definitions(())
                        .endpoints
                        .iter()
                        .find(|endpoint| endpoint.endpoint_def_id == Some(endpoint_id))
                })
                .and_then(|endpoint| {
                    rule_index.and_then(|index| endpoint.rules.get(index as usize))
                })
                .map(|rule| rule.reply_channel_indices.clone())
                .unwrap_or_default()
        } else {
            Vec::new()
        };

        // Add the semantic operation at the boundary that generated methods
        // currently represent. These entries are typed and descriptor-backed;
        // they are not a claim that the runtime helper itself is the semantic
        // representation. A later lowering pass will replace the compatibility
        // expansion once native construction/demand operations exist.
        match role {
            JoinBodyRole::Constructor => facts.operation(
                JoinOperationKind::CreateGroup,
                Location { block: mir::START_BLOCK, statement_index: 0 },
            ),
            JoinBodyRole::Channel => facts.operation(
                JoinOperationKind::Register,
                Location { block: mir::START_BLOCK, statement_index: 0 },
            ),
            JoinBodyRole::Dispatch => {
                facts.operation(
                    JoinOperationKind::Match,
                    Location { block: mir::START_BLOCK, statement_index: 0 },
                );
                if is_async {
                    facts.operation(
                        JoinOperationKind::Demand,
                        Location { block: mir::START_BLOCK, statement_index: 0 },
                    );
                }
            }
            JoinBodyRole::ReactionBody => {
                if is_async || facts.yields != 0 {
                    facts.operation(
                        JoinOperationKind::Demand,
                        Location { block: mir::START_BLOCK, statement_index: 0 },
                    );
                }
                // A synchronous reaction completes its replies at each real
                // return edge. Keeping the operation at that boundary makes
                // the marker useful to later typed MIR lowering without
                // claiming that completion happened before the body ran.
                // Async reactions are different: their generated body first
                // returns a coroutine and the reply is completed only when
                // that coroutine's output is delivered by the executor. Do
                // not invent an entry-point completion marker for them; the
                // coroutine lowering slice will add it at the output edge.
                if !is_async && facts.yields == 0 && !reply_channel_indices.is_empty() {
                    for (block, block_data) in body.basic_blocks.iter_enumerated() {
                        if matches!(block_data.terminator().kind, TerminatorKind::Return) {
                            facts.operation_with_reply_channels_and_destination(
                                JoinOperationKind::CompleteReplies,
                                Location { block, statement_index: block_data.statements.len() },
                                reply_channel_indices.iter().copied(),
                                Some(RETURN_PLACE.index() as u32),
                            );
                        }
                    }
                }
            }
            JoinBodyRole::Ordinary => {}
        }

        for local in facts.escapes.iter().copied() {
            facts.operations.push(JoinMirOperation {
                kind: JoinOperationKind::Escape,
                block: u32::MAX,
                statement: local,
                group_def_id: Some(endpoint_def_id),
                channel_index: None,
                rule_index: None,
                reply_channel_indices: Box::new([]),
                queue_bound,
                endpoint_def_id: Some(endpoint_def_id),
                rule_def_id: Some(rule_def_id),
                receiver_local: None,
                destination_local: None,
                argument_locals: Box::new([]),
            });
        }

        let summary = facts.finish(
            body,
            local_def_id.index() as u32,
            endpoint_def_id,
            rule_def_id,
            rule_index,
            role,
            arity,
            is_async,
            frontend_direct_unary,
            queue_bound,
            body.local_decls.len(),
            tcx.sess.opts.unstable_opts.join_cfa_budget,
        );
        let (fusion, fusion_rejection) = try_fuse_private_result(tcx, body, &summary, local_def_id);
        let mut summary = summary;
        summary.fusion = fusion;
        summary.fusion_rejection = fusion_rejection;
        let rejection = summary.rejection;
        let direct_candidate = summary.direct_candidate;
        let operations = summary.operations.len();
        let calls = summary.calls;
        let call_edges = summary.call_edges.len();
        let yields = summary.yields;
        let unknown_effects = summary.unknown_effects;
        let solver_steps = summary.solver_steps;
        let solver_complete = summary.solver_complete;
        let locally_closed = summary.locally_closed;
        let lowering = summary.lowering;
        let instance_closedness = summary.instance_closedness;
        let instance_closedness_reason = summary.instance_closedness_reason;
        let occupancy = summary.occupancy;
        let escapes = summary.escapes.len();
        let endpoint_escapes = summary.endpoint_escapes.len();
        let value_flows = summary.value_flows.len();
        let operation_kinds = summary.operations.iter().map(|op| op.kind).collect::<Vec<_>>();
        install_join_intrinsics(body, &summary);
        body.join_info = Some(Box::new(summary));
        dump_summary(
            tcx,
            local_def_id,
            cfa_mode,
            body.join_info.as_ref().expect("join summary just installed"),
        );

        tracing::info!(
            target: "rustc_join",
            def_id = ?body.source.def_id(),
            endpoint = endpoint_def_id,
            rule = rule_def_id,
            ?role,
            arity,
            is_async,
            frontend_direct_unary,
            ?queue_bound,
            ?lowering,
            ?instance_closedness,
            ?instance_closedness_reason,
            ?occupancy,
            operations,
            calls,
            call_edges,
            yields,
            value_flows,
            unknown_effects,
            solver_steps,
            solver_complete,
            locally_closed,
            escapes,
            endpoint_escapes,
            operation_kinds = ?operation_kinds,
            direct_candidate,
            ?rejection,
            fusion = ?fusion,
            ?cfa_mode,
            "join CFA summary"
        );
    }
}
