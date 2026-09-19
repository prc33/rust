//! The compiler-owned join boundary in MIR.
//!
//! Join syntax is currently expanded into ordinary Rust methods. This pass
//! runs while MIR is still in the initial analysis phase, before cleanup and
//! coroutine state transformation, and ties those bodies back to the resolved
//! `JoinDefinitions` descriptor. It records a small, typed operation stream
//! and conservative value-flow facts on the MIR body. The stream is the
//! hand-off point for a future lowering/fusion pass; it deliberately does not
//! infer semantics from generated method names or call into the library
//! runtime.

use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxHasher, FxIndexSet};
use rustc_hir::def_id::{DefId, LOCAL_CRATE, LocalDefId};
use rustc_index::Idx;
use rustc_middle::middle::joins::{
    JoinBodyRole, JoinCall, JoinCallEdge, JoinCallTargetKind, JoinCfaBodyRecord, JoinCfaCrateSummary,
    JoinCfaInstanceFact, JoinCfaInstanceStatus, JoinCfaRejection, JoinCfaSummary, JoinFusionFact,
    JoinEndpointEscape, JoinEndpointEscapeKind, JoinInstanceClosedness,
    JoinInstanceClosednessReason, JoinLocalFact, JoinMirOperation, JoinChannelOccupancyFact,
    JoinOccupancyFact,
    JoinLoweringStrategy, JoinOperationKind, JoinQueueBound, JoinValueFlow, JoinValueFlowKind,
    JoinValueState, JoinStateTokenProof, JoinStateTokenRejection, JoinStateTokenStatus,
    JoinStateTokenTransition, JoinStateTokenTransitionKind,
};
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{
    self, Body, JoinIntrinsic, Location, Operand, Place, RETURN_PLACE, Rvalue, Statement,
    StatementKind, TerminatorKind,
};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_session::config::JoinCfaMode;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::hash::{Hash, Hasher};

use crate::{MirPass, PassPolicy};

pub(super) struct JoinSemanticOps;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum InstanceAlias {
    None,
    Unique {
        endpoint_def_id: u32,
        body_def_id: u32,
        block: u32,
        statement: u32,
    },
    Multiple,
    Unknown,
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
                && left_statement == right_statement => self,
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
        if let Some(channel) = endpoint
            .channels
            .iter()
            .find(|channel| channel.method_def_id == local_def_id)
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
        self.operations.push(JoinMirOperation {
            kind,
            block: location.block.index() as u32,
            statement: location.statement_index as u32,
            group_def_id: self.endpoint_def_id,
            channel_index: self.channel_index,
            rule_index: self.rule_index,
            queue_bound: self.queue_bound,
            endpoint_def_id: self.endpoint_def_id,
            rule_def_id: self.rule_def_id,
            receiver_local: None,
            destination_local: None,
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
            &self.call_edges,
        );
        let endpoint_escapes = self.endpoint_escapes.iter().copied().collect::<Vec<_>>();
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
        let lowering = select_lowering_strategy(
            frontend_direct_unary,
            role,
            rejection,
        );

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
fn unique_alias_reaches(
    flows: &[JoinValueFlow],
    source: u32,
    destination: u32,
) -> bool {
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
                return terminator.source_info.span.is_desugaring(rustc_span::DesugaringKind::Await)
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

    fn visit_local(&mut self, local: mir::Local, context: mir::visit::PlaceContext, location: Location) {
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
                let destination_is_alias = self
                    .aliases
                    .contains(&(destination.local.index() as u32));
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
        != join_mir_fingerprint(body, &summary.operations, &summary.value_flows, &summary.call_edges)
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
    let (Some(constructor_destination), Some(channel_receiver), Some(channel_callee)) = (
        constructor.destination_local,
        channel.receiver_local,
        channel.callee,
    ) else {
        return (None, Some(JoinCfaRejection::UnsupportedUse));
    };
    if !unique_alias_reaches(
        &summary.value_flows,
        constructor_destination,
        channel_receiver,
    ) {
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
                JoinCallTargetKind::Channel
                | JoinCallTargetKind::OrdinaryLocal => JoinCfaRejection::Escape,
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
    let direct_def_id = DefId::local(rustc_span::def_id::DefIndex::from_usize(
        direct_method as usize,
    ));
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
    let private_constructor = definition.channels.iter()
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
    let current_arguments = args
        .iter()
        .map(|arg| arg.node.place().map(|place| place.local.index() as u32));
    if current_callee != Some(channel_callee)
        || current_destination != channel.destination_local
        || current_arguments.ne(channel.argument_locals.iter().copied())
    {
        return (None, Some(JoinCfaRejection::StaleProof));
    }
    let plan = PrivateInstancePlan {
        body,
        channel: (Location { block, statement_index: statement }, direct_def_id),
        constructor: private_constructor.map(|id| (
            Location { block: constructor_block, statement_index: constructor.statement as usize },
            id.to_def_id(),
        )),
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
                    direct_method_def_id: channel
                        .direct_method_def_id
                        .map(|id| id.index() as u32),
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
        if tcx.features().joins()
            && tcx.sess.opts.unstable_opts.join_cfa != JoinCfaMode::Off
        {
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
                rule_index: summary.rule_index,
                role: summary.role,
                value_flows: summary.value_flows.clone(),
                call_edges: summary.call_edges.clone(),
                unknown_effects: summary.unknown_effects,
                endpoint_escapes: summary.endpoint_escapes.clone(),
            };
            pending_ordinary.extend(
                record
                    .call_edges
                    .iter()
                    .filter(|edge| edge.target == JoinCallTargetKind::OrdinaryLocal)
                    .filter_map(|edge| edge.callee),
            );
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
        if facts.value_flows.is_empty() && facts.call_edges.is_empty() {
            continue;
        }
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
                rule_index: None,
                role: JoinBodyRole::Ordinary,
                value_flows: facts.value_flows,
                call_edges: facts.call_edges,
                unknown_effects: facts.unknown_effects,
                endpoint_escapes: facts.endpoint_escapes.into_iter().collect(),
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
        bodies.push(record);
    }
    bodies.sort_by_key(|record| record.body_def_id);

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
                        let incoming = caller_aliases
                            .get(source)
                            .copied()
                            .unwrap_or(InstanceAlias::None);
                        if !matches!(incoming, InstanceAlias::None) {
                            updates.push((callee, position as u32 + 1, incoming));
                        }
                    }
                    if let Some(destination) = edge.destination_local {
                        let returned = callee_aliases
                            .get(&0)
                            .copied()
                            .unwrap_or(InstanceAlias::None);
                        if !matches!(returned, InstanceAlias::None) {
                            updates.push((record.body_def_id, destination, returned));
                        }
                    }
                } else if matches!(edge.target, JoinCallTargetKind::OrdinaryLocal | JoinCallTargetKind::Unknown) {
                    for source in edge.argument_locals.iter().flatten() {
                        let alias = caller_aliases.get(source).copied().unwrap_or(InstanceAlias::None);
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
    // never manufacture a positive fact.
    for record in &bodies {
        let Some(aliases) = aliases_by_body.get(&record.body_def_id) else { continue };
        for edge in &record.call_edges {
            if !matches!(edge.target, JoinCallTargetKind::Channel | JoinCallTargetKind::Dispatch) {
                continue;
            }
            let Some(receiver_local) = edge.receiver_local else {
                complete = false;
                continue;
            };
            let alias = aliases.get(&receiver_local).copied().unwrap_or(InstanceAlias::None);
            match alias {
                InstanceAlias::Unique {
                    endpoint_def_id,
                    body_def_id,
                    block,
                    statement,
                } if Some(endpoint_def_id) == edge.endpoint_def_id => {
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
                InstanceAlias::Unique {
                    endpoint_def_id,
                    body_def_id,
                    block,
                    statement,
                } => {
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
                    for instance in instances.iter_mut().filter(|instance| {
                        instance.body_def_id == record.body_def_id
                    }) {
                        instance.status = JoinCfaInstanceStatus::Multiple;
                    }
                }
            }
        }
        if record.unknown_effects != 0 {
            complete = false;
            for instance in instances.iter_mut().filter(|instance| {
                instance.body_def_id == record.body_def_id
            }) {
                instance.status = JoinCfaInstanceStatus::Escaped;
            }
        }
        for escape in &record.endpoint_escapes {
            complete = false;
            match aliases.get(&escape.local).copied().unwrap_or(InstanceAlias::None) {
                InstanceAlias::Unique {
                    endpoint_def_id,
                    body_def_id,
                    block,
                    statement,
                } => {
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
    for escaped in escaped_origins {
        if let InstanceAlias::Unique {
            endpoint_def_id,
            body_def_id,
            block,
            statement,
        } = escaped
        {
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

    let state_tokens = prove_state_tokens(tcx, &bodies, &instances);
    let summary = JoinCfaCrateSummary {
        bodies,
        instances,
        state_tokens,
        solver_steps,
        complete,
    };
    dump_crate_summary(tcx, &summary, &aliases_by_body);
    summary
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
fn prove_state_tokens<'tcx>(
    tcx: TyCtxt<'tcx>,
    bodies: &[JoinCfaBodyRecord],
    instances: &[JoinCfaInstanceFact],
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

                // A body is relevant even when it is an ordinary caller: its
                // endpoint identity is carried by the typed call edge rather
                // than by a per-body join descriptor.  This is the root that
                // supplies the initial token in a closed local witness.
                let endpoint_body = |body: &&JoinCfaBodyRecord| {
                    body.endpoint_def_id == Some(endpoint_def_id)
                        || body.call_edges.iter().any(|edge| {
                            edge.endpoint_def_id == Some(endpoint_def_id)
                        })
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
                let endpoint_complete = state_token_endpoint_complete(endpoint_def_id, bodies);
                let rejection = if competing_rules != 0 {
                    Some(JoinStateTokenRejection::CompetingRule)
                } else if !endpoint_complete {
                    Some(JoinStateTokenRejection::IncompleteAnalysis)
                } else if unique_instance.is_none() {
                    Some(JoinStateTokenRejection::NoUniqueInstance)
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
    proofs.sort_by_key(|proof| {
        (
            proof.endpoint_def_id,
            proof.rule_index,
            proof.channel_index,
        )
    });
    proofs
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
    bodies: &[JoinCfaBodyRecord],
) -> bool {
    let by_id = bodies
        .iter()
        .map(|body| (body.body_def_id, body))
        .collect::<FxHashMap<_, _>>();
    let mut relevant = FxHashSet::default();
    for body in bodies {
        if body.endpoint_def_id == Some(endpoint_def_id)
            || body
                .call_edges
                .iter()
                .any(|edge| edge.endpoint_def_id == Some(endpoint_def_id))
        {
            relevant.insert(body.body_def_id);
        }
    }
    if relevant.is_empty() {
        return false;
    }

    // Follow ordinary helper calls from endpoint bodies. The graph builder
    // normally selects these roots already; retaining the check here makes a
    // missing body an explicit negative proof rather than an accidental
    // omission.
    let mut worklist = relevant.iter().copied().collect::<Vec<_>>();
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

    relevant.into_iter().all(|body_def_id| {
        let Some(body) = by_id.get(&body_def_id).copied() else {
            return false;
        };
        body.unknown_effects == 0 && body.endpoint_escapes.is_empty()
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
                        "{{\"callee\":{},\"target\":\"{:?}\",\"endpoint\":{},\"receiver\":{},\"destination\":{},\"arguments\":[{}],\"group\":{},\"channel\":{},\"rule_index\":{},\"queue_bound\":\"{:?}\"}}",
                        edge.callee.map_or_else(|| "null".to_string(), |callee| callee.to_string()),
                        edge.target,
                        edge.endpoint_def_id
                            .map_or_else(|| "null".to_string(), |endpoint| endpoint.to_string()),
                        edge.receiver_local
                            .map_or_else(|| "null".to_string(), |local| local.to_string()),
                        edge.destination_local
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
            format!(
                "{{\"body\":{},\"parent\":{},\"endpoint\":{},\"rule_index\":{},\"role\":\"{:?}\",\"flows\":[{}],\"aliases\":[{}],\"calls\":[{}]}}",
                body.body_def_id,
                body.parent_body_def_id
                    .map_or_else(|| "null".to_string(), |parent| parent.to_string()),
                body.endpoint_def_id
                    .map_or_else(|| "null".to_string(), |endpoint| endpoint.to_string()),
                body.rule_index
                    .map_or_else(|| "null".to_string(), |rule| rule.to_string()),
                body.role,
                value_flows,
                aliases,
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
    let json = format!(
        "{{\"bodies\":{},\"body_records\":[{}],\"instances\":[{}],\"state_tokens\":[{}],\"definitions\":[{}],\"solver_steps\":{},\"complete\":{}}}\n",
        summary.bodies.len(),
        body_records,
        instances,
        state_tokens,
        definitions,
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
    let channels = operations
        .iter()
        .filter_map(|operation| operation.channel_index)
        .collect::<BTreeSet<_>>();
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
            Rvalue::Aggregate(_, operands) => {
                // A closure/aggregate may capture an endpoint handle without
                // moving the aggregate's final value directly at the call
                // site. Record those typed captures before the ordinary
                // value-flow summary widens the aggregate.
                for operand in operands {
                    if let Operand::Move(source) | Operand::Copy(source) = operand {
                        self.record_moved_place(source, JoinEndpointEscapeKind::AggregateCapture);
                    }
                }
                (JoinValueFlowKind::Aggregate, None)
            }
            _ => return self.super_assign(place, rvalue, location),
        };
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
                "{{\"kind\":\"{:?}\",\"block\":{},\"statement\":{},\"group\":{},\"channel\":{},\"rule_index\":{},\"queue_bound\":\"{:?}\",\"endpoint\":{},\"rule\":{},\"receiver\":{},\"destination\":{},\"arguments\":[{}]}}",
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
                "{{\"block\":{},\"statement\":{},\"callee\":{},\"target\":\"{:?}\",\"endpoint\":{},\"rule\":{},\"receiver\":{},\"destination\":{},\"arguments\":[{}],\"group\":{},\"channel\":{},\"rule_index\":{},\"queue_bound\":\"{:?}\"}}",
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
    let fusion_rejection = summary.fusion_rejection.map_or_else(
        || "null".to_string(),
        |reason| format!("\"{reason:?}\""),
    );
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
        "{{\"def_id\":{},\"endpoint\":{},\"rule\":{},\"mir_fingerprint\":{},\"role\":\"{:?}\",\"arity\":{},\"is_async\":{},\"frontend_direct_unary\":{},\"queue_bound\":\"{:?}\",\"lowering\":\"{:?}\",\"occupancy\":{{\"proven_peak\":{},\"proven_final\":{},\"events\":{},\"complete\":{}}},\"channel_occupancy\":[{}],\"instance_closedness\":\"{:?}\",\"instance_closedness_reason\":\"{:?}\",\"mode\":\"{:?}\",\"calls\":{},\"call_edges\":[{}],\"yields\":{},\"unknown_effects\":{},\"solver_steps\":{},\"solver_complete\":{},\"locally_closed\":{},\"escapes\":[{}],\"endpoint_escapes\":[{}],\"value_flows\":[{}],\"local_facts\":[{}],\"operations\":[{}],\"direct_candidate\":{},\"fusion\":{},\"fusion_rejection\":{},\"rejection\":{}}}\n",
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
fn install_join_call_descriptors<'tcx>(
    body: &mut Body<'tcx>,
    operations: &[JoinMirOperation],
) {
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
        if let TerminatorKind::Call { join, .. } = &mut body.basic_blocks_mut()[block]
            .terminator_mut()
            .kind
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
            queue_bound: operation.queue_bound,
            endpoint_def_id: operation.endpoint_def_id,
            rule_def_id: operation.rule_def_id,
            receiver: None,
            destination: None,
            arguments: Box::new([]),
        };
        pending.push((block, statement.min(block_data.statements.len()), source_info, marker));
    }

    // Insert backwards so the source locations recorded in the operation
    // summary continue to denote the original MIR terminator/statement.
    pending.sort_by_key(|(block, statement, _, _)| (block.index(), *statement));
    for (block, statement, source_info, marker) in pending.into_iter().rev() {
        body.basic_blocks_mut()[block]
            .statements
            .insert(statement, Statement::new(source_info, StatementKind::Intrinsic(Box::new(
                rustc_middle::mir::NonDivergingIntrinsic::Join(marker),
            ))));
    }
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
        )) = body_descriptor(tcx, local_def_id) else {
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
                facts.operation(
                    JoinOperationKind::CompleteReplies,
                    Location { block: mir::START_BLOCK, statement_index: 0 },
                );
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
        let (fusion, fusion_rejection) =
            try_fuse_private_result(tcx, body, &summary, local_def_id);
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
