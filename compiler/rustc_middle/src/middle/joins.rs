//! Compiler-owned descriptions of expanded `join impl` endpoints.
//!
//! The frontend currently lowers the experimental syntax through a builtin
//! macro, but it leaves a parsed `join_endpoint` contract on the
//! generated impl. This module is the typed seam between that expansion and
//! later CFA/MIR work: identities are local `DefId`s and channel signatures
//! are rustc's resolved types rather than source strings.

use rustc_hir::def_id::LocalDefId;
use rustc_macros::{StableHash, TyDecodable, TyEncodable, TypeFoldable, TypeVisitable};
use rustc_span::{Span, Symbol};

use crate::ty::PolyFnSig;

/// All join endpoints discovered in a local crate.
#[derive(Debug, StableHash)]
pub struct JoinDefinitions<'tcx> {
    pub endpoints: Vec<JoinDefinition<'tcx>>,
}

/// A single expanded endpoint and its compiler identities.
#[derive(Debug, StableHash)]
pub struct JoinDefinition<'tcx> {
    /// The generated inherent impl carrying the join contract marker.
    pub impl_def_id: LocalDefId,
    /// The generated storage struct, when its self type resolved to a local
    /// definition. This is optional to keep diagnostics recoverable after a
    /// type error.
    pub endpoint_def_id: Option<LocalDefId>,
    /// Shape declared by the frontend marker.
    pub declared_channels: u32,
    pub declared_rules: u32,
    pub declared_arity: u32,
    pub declared_async_rule: bool,
    /// Whether the frontend selected the restricted caller-owned unary future
    /// representation for this endpoint. The later CFA pass still validates
    /// the body; this bit records the representation choice in compiler IR.
    pub frontend_direct_unary: bool,
    /// Frontend queue bound for restricted unary storage: `0` means the
    /// caller-owned direct future has no queue, `1` means the generated
    /// matcher is allowed to use a single slot, and `None` means unknown.
    pub frontend_queue_bound: Option<u32>,
    /// Span of the generated endpoint contract. This points back through the
    /// builtin expansion to the source `join impl` declaration.
    pub span: Span,
    /// Generated channel methods with their resolved function signatures.
    pub channels: Vec<JoinChannel<'tcx>>,
    /// The generated constructors are allocation-site anchors for the
    /// interprocedural instance analysis.  `new` creates an endpoint with the
    /// default runtime scope; `new_in_scope` creates one owned by an explicit
    /// `QueryScope`.  Keeping both identities avoids treating a constructor
    /// call as an opaque ordinary function when the later solver connects
    /// concrete instances to channel calls.
    pub constructor_def_id: Option<LocalDefId>,
    pub scoped_constructor_def_id: Option<LocalDefId>,
    /// Generated dispatch method(s). The first compiler slice emits one
    /// dispatch body for the restricted unary/pair forms.
    pub rules: Vec<JoinRule<'tcx>>,
}

/// A channel endpoint represented by its resolved associated function.
#[derive(Debug, StableHash)]
pub struct JoinChannel<'tcx> {
    pub method_def_id: LocalDefId,
    /// Position in the source declaration. This remains stable even when the
    /// generated method has a hygienic name or the declaration is generic.
    pub index: u32,
    pub name: Symbol,
    pub signature: PolyFnSig<'tcx>,
}

/// A reaction dispatch body and the shape known at expansion time.
#[derive(Debug, StableHash)]
pub struct JoinRule<'tcx> {
    pub method_def_id: LocalDefId,
    pub arity: u32,
    pub is_async: bool,
    /// All nested body owners in the generated dispatch method, in rustc's
    /// post-order. Keeping these identities lets pre-coroutine MIR analysis
    /// find the actual reaction closures without matching source strings.
    pub body_def_ids: &'tcx crate::ty::List<LocalDefId>,
    pub span: Span,
}

/// The compiler-owned role of a MIR body that belongs to a join endpoint.
///
/// This is deliberately independent of generated method names.  The current
/// frontend still expands through ordinary methods, but the descriptor query
/// records the identities and this role is what later MIR analyses consume.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinBodyRole {
    Constructor,
    Channel,
    Dispatch,
    ReactionBody,
    /// An ordinary body that is retained by a future interprocedural join
    /// summary because it reaches a compiler-known join operation.
    Ordinary,
}

/// Typed operations that are preserved at the join/MIR boundary.
///
/// These are an analysis vocabulary, not runtime calls.  The first vertical
/// slice records them in the body side table; a later lowering pass will map
/// the surviving operations to the selected runtime or to a specialised
/// direct future.  Keeping the vocabulary here prevents CFA from having to
/// infer semantics from a queue helper's symbol name.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinOperationKind {
    CreateGroup,
    Register,
    Demand,
    Match,
    CompleteReplies,
    WithdrawOrAbandon,
    CancelScope,
    OrdinaryCall,
    Yield,
    Return,
    Escape,
}

/// A source-positioned operation in the pre-coroutine MIR view.
///
/// MIR locations are body-local and are intentionally represented as compact
/// indices so this metadata can be encoded with the body.  The actual MIR
/// remains authoritative; this is an index for diagnostics and transform
/// decisions, not a second control-flow graph.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinMirOperation {
    pub kind: JoinOperationKind,
    pub block: u32,
    pub statement: u32,
}

/// A typed local-to-local value-flow edge extracted from MIR.  `source` is
/// absent when the RHS is a constant, aggregate or otherwise does not have a
/// single local origin.  This is the seed domain for the interprocedural CFA;
/// it is intentionally more precise than treating every MIR statement as an
/// opaque external operation.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinValueFlow {
    pub destination: u32,
    pub source: Option<u32>,
    pub kind: JoinValueFlowKind,
    pub block: u32,
    pub statement: u32,
}

/// The intrabody value state used by the first compiler-native CFA solver.
///
/// The lattice is deliberately small. `Internal` is the optimistic seed for
/// locals that are fully described by MIR; the other states only widen that
/// seed. `Unknown` is the top element and is never treated as a proof of
/// closedness.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinValueState {
    Internal,
    Borrowed,
    Aggregate,
    Escapes,
    Unknown,
}

/// A solved local value fact, keyed by the body-local MIR local index.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinLocalFact {
    pub local: u32,
    pub state: JoinValueState,
}

/// A direct call edge extracted from typed MIR. `callee` is present only for
/// a statically resolved local `FnDef`; trait objects, function pointers and
/// external definitions remain unknown and must widen an interprocedural
/// proof. The source location lets a later solver attach a context frame
/// without reparsing generated names.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinCallEdge {
    pub block: u32,
    pub statement: u32,
    pub callee: Option<u32>,
    pub target: JoinCallTargetKind,
    /// Compiler-owned endpoint identity for a known join call target.  This
    /// is populated for channel, dispatch, reaction-body and constructor
    /// calls; ordinary and unknown calls remain `None`.
    pub endpoint_def_id: Option<u32>,
    /// Compiler-owned rule identity for dispatch and reaction-body calls.
    pub rule_def_id: Option<u32>,
    /// Base MIR local carrying the receiver for a known channel/dispatch
    /// method.  It is intentionally a local index rather than a guessed
    /// source name; value-flow facts can connect aliases to this local later.
    pub receiver_local: Option<u32>,
    /// Base MIR local receiving the result of a known constructor/channel/
    /// dispatch call, when the call has a local destination.
    pub destination_local: Option<u32>,
    /// Base MIR locals for the call operands, preserving argument position.
    /// `None` represents a constant or other operand without a local place;
    /// preserving the slot is what lets the crate solver map a caller value
    /// to the callee's MIR argument local without guessing through types.
    pub argument_locals: Vec<Option<u32>>,
}

/// Semantic target classification for a typed direct call edge.
///
/// `Unknown` covers function pointers, trait dispatch and foreign/external
/// calls. `OrdinaryLocal` is a known local function that is not itself a join
/// declaration. The join-specific variants (including constructors) are
/// resolved from compiler-owned descriptor identities, never from generated
/// symbol names.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinCallTargetKind {
    Unknown,
    OrdinaryLocal,
    Constructor,
    Channel,
    Dispatch,
    ReactionBody,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinValueFlowKind {
    Copy,
    Move,
    Borrow,
    Aggregate,
    Unknown,
}

/// Conservative occupancy fact for one compiler-described join endpoint.
/// This is deliberately separate from local value closedness: a channel can
/// be closed over values while still receiving an unbounded producer stream.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinQueueBound {
    Exact(u32),
    AtMost(u32),
    Unknown,
}

/// Body-local occupancy transfer facts for semantic register/match events.
///
/// These facts describe only the event interval visible in one MIR body. A
/// `complete` result is not a queue proof for a concrete group instance: the
/// solver has not yet connected callers, allocation sites, loops, competing
/// rules, or external producers. `None` is therefore used whenever the local
/// event sequence begins with an externally supplied match/withdraw or a
/// cancellation whose drain is not represented in this body.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinOccupancyFact {
    pub proven_peak: Option<u32>,
    pub proven_final: Option<u32>,
    pub events: u32,
    pub complete: bool,
}

/// Closedness of the concrete join state represented by a body.
///
/// `Closed` is intentionally reserved for the caller-owned direct unary
/// representation, where each invocation owns its input and reaction future
/// and no shared channel state participates. `Open` is a definite typed
/// endpoint-handle escape from the analyzed body; it is useful negative
/// evidence, but is not a whole-program allocation proof. Matcher-backed
/// endpoints without such a witness remain `Unknown` until an
/// interprocedural instance analysis accounts for every channel handle,
/// producer, consumer and escape.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinInstanceClosedness {
    Closed,
    Open,
    Unknown,
}

/// Why the compiler assigned the current whole-instance closedness fact.
///
/// The reason is part of the proof record rather than a diagnostic string so
/// later transforms can require the exact fact they need.  In particular,
/// `RequiresInterprocedural` must never be treated as an optimistic closedness
/// result merely because a body-local solver reached a fixed point.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinInstanceClosednessReason {
    FrontendDirectUnary,
    EndpointHandleEscapes,
    UnknownEffects,
    SolverBudget,
    RequiresInterprocedural,
}

/// A typed escape of a concrete endpoint handle from a join-associated body.
///
/// Ordinary payload moves remain in `escapes`; this side table only records a
/// move whose MIR type is the endpoint's own ADT.  That distinction is what
/// lets closed-instance analysis reject a returned/captured group handle
/// without confusing it with an application value moved to a reaction.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinEndpointEscape {
    pub local: u32,
    pub kind: JoinEndpointEscapeKind,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinEndpointEscapeKind {
    CallArgument,
    AggregateCapture,
    Yield,
    Return,
}

/// Conservative facts produced for one join-associated MIR body.
///
/// `direct_candidate` is intentionally only a candidate bit.  It is true for
/// a non-suspending, call-free reaction body; ownership, panic and instance
/// proofs still have to be supplied before a fusion pass may rewrite it.
/// `rejection` explains why a candidate was not eligible for that restricted
/// shape.  Counts and local indices make the result deterministic and cheap
/// to dump in compiler tests.
#[derive(Clone, Debug, PartialEq, Eq)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinCfaSummary {
    /// MIR body identity within the local crate.  The endpoint/rule IDs below
    /// identify the declaration; this field identifies the concrete body that
    /// can be reached through ordinary helpers or generated closures.
    pub body_def_id: u32,
    pub endpoint_def_id: u32,
    pub rule_def_id: u32,
    pub role: JoinBodyRole,
    pub arity: u32,
    pub is_async: bool,
    pub frontend_direct_unary: bool,
    pub queue_bound: JoinQueueBound,
    pub occupancy: JoinOccupancyFact,
    pub instance_closedness: JoinInstanceClosedness,
    pub instance_closedness_reason: JoinInstanceClosednessReason,
    pub operations: Vec<JoinMirOperation>,
    pub value_flows: Vec<JoinValueFlow>,
    /// Monotone intrabody solution for the locals touched by the extracted
    /// value-flow edges. This is compiler-owned CFA state, not a second MIR.
    pub local_facts: Vec<JoinLocalFact>,
    /// Number of lattice propagation steps consumed by this body.
    pub solver_steps: u32,
    /// Whether the local solution reached a fixed point before the configured
    /// work budget. An incomplete solution disables proof-consuming passes.
    pub solver_complete: bool,
    /// A closedness fact for this body only. It does not imply a concrete
    /// channel instance or a closed protocol across call boundaries.
    pub locally_closed: bool,
    pub calls: u32,
    pub call_edges: Vec<JoinCallEdge>,
    pub yields: u32,
    pub unknown_effects: u32,
    pub escapes: Vec<u32>,
    pub endpoint_escapes: Vec<JoinEndpointEscape>,
    pub direct_candidate: bool,
    pub rejection: Option<JoinCfaRejection>,
}

/// A body summary retained by the crate-level instance analysis.
///
/// `JoinCfaSummary` is installed on the pre-cleanup body while that body is
/// being prepared.  Keeping the parent identity beside a cloned summary lets
/// the crate query relate generated closure bodies to the body that created
/// them without using generated names.
#[derive(Clone, Debug, PartialEq, Eq)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinCfaBodyRecord {
    pub body_def_id: u32,
    pub parent_body_def_id: Option<u32>,
    pub endpoint_def_id: Option<u32>,
    pub role: JoinBodyRole,
    pub value_flows: Vec<JoinValueFlow>,
    pub call_edges: Vec<JoinCallEdge>,
    pub unknown_effects: u32,
    pub endpoint_escapes: Vec<JoinEndpointEscape>,
}

/// Result of the first compiler-owned instance/context propagation slice.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinCfaInstanceStatus {
    Unique,
    Multiple,
    Escaped,
    Unknown,
}

/// A constructor allocation and the known uses reached from that allocation.
///
/// `Unique` is only emitted when the current bounded graph has one constructor
/// origin and all observed compiler-known channel/dispatch uses resolve to it.
/// Missing caller/closure flow, unknown calls and competing origins widen the
/// status; no transform may treat an absent fact as proof.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinCfaInstanceFact {
    pub body_def_id: u32,
    pub endpoint_def_id: u32,
    pub allocation_block: u32,
    pub allocation_statement: u32,
    pub known_uses: u32,
    pub status: JoinCfaInstanceStatus,
}

/// Crate-level join facts.  This query is deliberately `eval_always` while the
/// representation is experimental: it consumes pre-cleanup summaries and is
/// not yet a stable incremental artifact.
#[derive(Clone, Debug, PartialEq, Eq)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinCfaCrateSummary {
    pub bodies: Vec<JoinCfaBodyRecord>,
    pub instances: Vec<JoinCfaInstanceFact>,
    pub solver_steps: u32,
    pub complete: bool,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinCfaRejection {
    NotReactionBody,
    SharedPattern,
    Async,
    Suspends,
    Calls,
    UnknownEffects,
    Escapes,
    SolverBudget,
    NotClosed,
}
