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

use rustc_data_structures::fx::FxIndexSet;
use rustc_hir::def_id::{LOCAL_CRATE, LocalDefId};
use rustc_index::Idx;
use rustc_middle::middle::joins::{
    JoinBodyRole, JoinCallEdge, JoinCfaRejection, JoinCfaSummary, JoinEndpointEscape,
    JoinEndpointEscapeKind, JoinInstanceClosedness, JoinInstanceClosednessReason, JoinLocalFact,
    JoinMirOperation, JoinOperationKind, JoinQueueBound, JoinValueFlow, JoinValueFlowKind,
    JoinValueState,
};
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{
    self, Body, Location, Operand, Place, RETURN_PLACE, Rvalue, TerminatorKind,
};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_session::config::JoinCfaMode;
use std::fs;

use crate::PassPolicy;

pub(super) struct JoinSemanticOps;

/// Locate the compiler descriptor for one body without consulting any later
/// MIR query. Returning the role separately keeps the generated frontend
/// shape out of the analysis itself.
fn body_descriptor<'tcx>(
    tcx: TyCtxt<'tcx>,
    local_def_id: LocalDefId,
) -> Option<(u32, u32, JoinBodyRole, u32, bool, bool, JoinQueueBound, Option<LocalDefId>)> {
    for endpoint in &tcx.join_definitions(()).endpoints {
        if endpoint.channels.iter().any(|channel| channel.method_def_id == local_def_id) {
            return Some((
                endpoint.endpoint_def_id.map_or(u32::MAX, |id| id.index() as u32),
                0,
                JoinBodyRole::Channel,
                endpoint.declared_arity,
                endpoint.declared_async_rule,
                endpoint.frontend_direct_unary,
                frontend_queue_bound(endpoint.frontend_queue_bound),
                endpoint.endpoint_def_id,
            ));
        }

        for rule in &endpoint.rules {
            if rule.method_def_id == local_def_id
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
                ));
            }
        }
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

struct JoinBodyFacts {
    operations: Vec<JoinMirOperation>,
    value_flows: Vec<JoinValueFlow>,
    call_edges: Vec<JoinCallEdge>,
    escapes: FxIndexSet<u32>,
    endpoint_escapes: FxIndexSet<JoinEndpointEscape>,
    endpoint_locals: Vec<bool>,
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

    fn finish(
        self,
        endpoint_def_id: u32,
        rule_def_id: u32,
        role: JoinBodyRole,
        arity: u32,
        is_async: bool,
        frontend_direct_unary: bool,
        queue_bound: JoinQueueBound,
        local_count: usize,
        solver_budget: usize,
    ) -> JoinCfaSummary {
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

        JoinCfaSummary {
            endpoint_def_id,
            rule_def_id,
            role,
            arity,
            is_async,
            frontend_direct_unary,
            queue_bound,
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
            direct_candidate: rejection.is_none(),
            rejection,
        }
    }
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
            Rvalue::Ref(..) => (JoinValueFlowKind::Borrow, None),
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
                self.operation(JoinOperationKind::OrdinaryCall, location);
                self.call_edges.push(JoinCallEdge {
                    block: location.block.index() as u32,
                    statement: location.statement_index as u32,
                    callee: func
                        .const_fn_def()
                        .and_then(|(def_id, _)| def_id.as_local())
                        .map(|def_id| def_id.index() as u32),
                });
                for arg in args {
                    if let Operand::Move(place) = &arg.node {
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
                if self.endpoint_locals.get(RETURN_PLACE.index()).copied().unwrap_or(false) {
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
        .map(|operation| format!("\"{:?}\"", operation.kind))
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
                "{{\"block\":{},\"statement\":{},\"callee\":{}}}",
                edge.block,
                edge.statement,
                edge.callee.map_or_else(|| "null".to_string(), |callee| callee.to_string()),
            )
        })
        .collect::<Vec<_>>()
        .join(",");
    let rejection =
        summary.rejection.map_or_else(|| "null".to_string(), |reason| format!("\"{reason:?}\""));
    let endpoint_escapes = summary
        .endpoint_escapes
        .iter()
        .map(|escape| format!("{{\"local\":{},\"kind\":\"{:?}\"}}", escape.local, escape.kind))
        .collect::<Vec<_>>()
        .join(",");
    let json = format!(
        "{{\"def_id\":{},\"endpoint\":{},\"rule\":{},\"role\":\"{:?}\",\"arity\":{},\"is_async\":{},\"frontend_direct_unary\":{},\"queue_bound\":\"{:?}\",\"instance_closedness\":\"{:?}\",\"instance_closedness_reason\":\"{:?}\",\"mode\":\"{:?}\",\"calls\":{},\"call_edges\":[{}],\"yields\":{},\"unknown_effects\":{},\"solver_steps\":{},\"solver_complete\":{},\"locally_closed\":{},\"escapes\":[{}],\"endpoint_escapes\":[{}],\"value_flows\":[{}],\"local_facts\":[{}],\"operations\":[{}],\"direct_candidate\":{},\"rejection\":{}}}\n",
        local_def_id.index(),
        summary.endpoint_def_id,
        summary.rule_def_id,
        summary.role,
        summary.arity,
        summary.is_async,
        summary.frontend_direct_unary,
        summary.queue_bound,
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
        if cfa_mode == JoinCfaMode::Off {
            return;
        }

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
        )) = body_descriptor(tcx, local_def_id)
        else {
            return;
        };

        let mut facts = JoinBodyFacts {
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
        }

        for local in facts.escapes.iter().copied() {
            facts.operations.push(JoinMirOperation {
                kind: JoinOperationKind::Escape,
                block: u32::MAX,
                statement: local,
            });
        }

        let summary = facts.finish(
            endpoint_def_id,
            rule_def_id,
            role,
            arity,
            is_async,
            frontend_direct_unary,
            queue_bound,
            body.local_decls.len(),
            tcx.sess.opts.unstable_opts.join_cfa_budget,
        );
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
        let instance_closedness = summary.instance_closedness;
        let instance_closedness_reason = summary.instance_closedness_reason;
        let escapes = summary.escapes.len();
        let endpoint_escapes = summary.endpoint_escapes.len();
        let value_flows = summary.value_flows.len();
        let operation_kinds = summary.operations.iter().map(|op| op.kind).collect::<Vec<_>>();
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
            ?instance_closedness,
            ?instance_closedness_reason,
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
            ?cfa_mode,
            "join CFA summary"
        );
    }
}
