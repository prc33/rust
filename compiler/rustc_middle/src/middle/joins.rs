//! Compiler-owned descriptions of expanded `join impl` endpoints.
//!
//! The frontend currently lowers the experimental syntax through a builtin
//! macro, but it leaves a parsed `join_endpoint` contract on the
//! generated impl. This module is the typed seam between that expansion and
//! later CFA/MIR work: identities are local `DefId`s and channel signatures
//! are rustc's resolved types rather than source strings.

use rustc_hir::def_id::{DefId, LocalDefId};
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
    /// Compiler-selected semantic contract for this generated endpoint. The
    /// values are facts about the lowering, not optimization hints supplied
    /// by the programmer; later CFA may only consume a representation whose
    /// requirements are implied by these policies.
    pub policy: JoinPolicy,
}

/// Semantic policy selected by the builtin lowering and retained in typed
/// compiler IR. Keeping these dimensions separate prevents a proof of one
/// property (for example caller-driven execution) from being mistaken for a
/// proof of another (for example bounded storage).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinPolicy {
    pub admission: JoinAdmissionPolicy,
    pub demand: JoinDemandPolicy,
    pub execution: JoinExecutionPolicy,
    pub cancellation: JoinCancellationPolicy,
    pub lifetime: JoinLifetimePolicy,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinAdmissionPolicy {
    Immediate,
    Fallible,
    Unknown,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinDemandPolicy {
    DemandGated,
    EagerCompatibility,
    Unknown,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinExecutionPolicy {
    CallerDriven,
    GroupDriven,
    Unknown,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinCancellationPolicy {
    OwnedFuture,
    IndependentReplies,
    ScopeBound,
    Unknown,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinLifetimePolicy {
    CallerOwned,
    OwnedShared,
    Unknown,
}

/// A channel endpoint represented by its resolved associated function.
#[derive(Debug, StableHash)]
pub struct JoinChannel<'tcx> {
    pub method_def_id: LocalDefId,
    /// Compiler-private direct reply adapter, when the frontend generated a
    /// proof-eligible unary reaction helper.  This is a target identity, not
    /// a promise that the helper may be called: the MIR CFA consumer must
    /// still prove a private unique instance before retargeting a channel
    /// call to it.
    pub direct_method_def_id: Option<LocalDefId>,
    /// Allocation-free private representation constructor, paired with the
    /// direct adapter. Only a whole-instance MIR proof may select this target.
    pub private_constructor_def_id: Option<LocalDefId>,
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
    /// Named executable helper emitted for this source rule.  This is the
    /// authoritative reaction owner; `body_def_ids` retains nested closure or
    /// coroutine identities below it for reachability analysis.
    pub reaction_method_def_id: Option<LocalDefId>,
    /// Exact source-declaration channel order for this reaction. This is
    /// recovered from the per-rule compiler marker, not from generated names.
    pub channel_indices: Vec<u32>,
    /// Source channels whose result expressions are completed by this rule.
    pub reply_channel_indices: Vec<u32>,
    /// Defining body owner for this generated reaction. A dynamic endpoint
    /// keeps all rule closures under one dispatch owner, so `body_index` is
    /// the source-rule coordinate within that owner rather than an assumed
    /// ordinal in the nested-body list (async rules can contain nested
    /// coroutines of their own).
    pub body_def_id: Option<LocalDefId>,
    pub body_index: Option<u32>,
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
/// These are a compiler vocabulary, not runtime calls. The first vertical
/// slice records them in the body side table and materializes them as typed
/// MIR markers; a later proof-gated lowering can map surviving operations to
/// the selected runtime or a specialised direct future. Keeping the vocabulary
/// here prevents CFA from having to infer semantics from a queue helper's
/// symbol name.
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

/// Metadata attached directly to an ordinary MIR call that the join CFA has
/// classified as a join operation.
///
/// The call already owns the function operand, argument operands and return
/// destination.  Keeping only the semantic identity here avoids introducing a
/// second, metadata-only statement which would make ordinary MIR visitors see
/// every argument twice.  This descriptor is not an executable operation and
/// is stripped at the backend boundary after MIR optimisations have had a
/// chance to consume it.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinCall {
    pub kind: JoinOperationKind,
    /// Representation selected by the compiler for this call site.  The
    /// descriptor is initialized to `Generic` while the frontend operation
    /// is being classified, then upgraded only after the interprocedural CFA
    /// certificate has been consumed by the MIR lowering pass.  Keeping this
    /// on the real call makes the selected state visible to later MIR passes
    /// without asking them to infer it from a runtime symbol name.
    pub lowering: JoinLoweringStrategy,
    /// Stable identity of the whole-instance CFA certificate consumed at
    /// this call. `None` means that the call is only classified by the
    /// frontend; an optimized call must carry the certificate which selected
    /// its representation so later MIR/LLVM passes never have to infer proof
    /// provenance from a runtime symbol.
    pub certificate_id: Option<u64>,
    /// Typed group identity. For local definitions this is the endpoint
    /// `DefId`; when metadata is imported the crate number remains part of the
    /// identity rather than being reconstructed from a local index.
    pub group_def_id: Option<DefId>,
    /// Source-declaration channel index, when this call is a channel
    /// registration. This is stable within the typed group definition and is
    /// intentionally independent of generated method names.
    pub channel_index: Option<u32>,
    /// Source-declaration rule index, when this call targets a dispatch or
    /// reaction body. This is stable within the typed group definition.
    pub rule_index: Option<u32>,
    /// Static queue/storage bound carried by the group definition. Unknown is
    /// the safe fallback; this fact is descriptive until a later proof
    /// validates the concrete instance.
    pub queue_bound: JoinQueueBound,
    /// Transitional endpoint identity retained for diagnostics and old dump
    /// readers. New consumers should use `group_def_id`.
    /// Cross-crate definition identity for the endpoint/group. Keeping the
    /// crate number here prevents local index collisions in downstream MIR.
    pub endpoint_def_id: Option<DefId>,
    /// Cross-crate definition identity for the selected rule, when known.
    pub rule_def_id: Option<DefId>,
}

/// A source-positioned operation in the pre-coroutine MIR view.
///
/// MIR locations are body-local and are intentionally represented as compact
/// indices so this metadata can be encoded with the body.  The operation also
/// carries the resolved endpoint/rule identity and the MIR locals used by the
/// operation. This is the typed seam consumed by future MIR/codegen lowering:
/// transforms do not have to reconstruct a channel from a generated method
/// name or a runtime helper symbol. `None` operands represent constants or
/// projections that do not have a single local base.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinMirOperation {
    pub kind: JoinOperationKind,
    pub block: u32,
    pub statement: u32,
    pub group_def_id: Option<u32>,
    pub channel_index: Option<u32>,
    pub rule_index: Option<u32>,
    /// Source channels whose result slots are completed by this reaction.
    /// This is populated for `CompleteReplies`; other operations keep it
    /// empty rather than making later passes rediscover the reply map from a
    /// generated helper name.
    pub reply_channel_indices: Box<[u32]>,
    pub queue_bound: JoinQueueBound,
    pub endpoint_def_id: Option<u32>,
    pub rule_def_id: Option<u32>,
    pub receiver_local: Option<u32>,
    pub destination_local: Option<u32>,
    pub argument_locals: Box<[Option<u32>]>,
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

/// A closure/aggregate value and the MIR locals it captures. Keeping this
/// separate from `JoinValueFlow` is important: an aggregate can be a tuple,
/// a coroutine frame, or a closure, and only the latter needs the recursive
/// capture edge used by the JCAM escape solver. The MIR visitor records the
/// exact operands; the solver decides whether the resulting closure crosses a
/// join boundary.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinCfaClosureFact {
    pub destination: u32,
    pub body_def_id: u32,
    pub captures: Vec<u32>,
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
    /// Typed group/channel/rule coordinates recovered from the compiler-owned
    /// descriptor. These remain meaningful after generated method identities
    /// are remapped across MIR transformations.
    pub group_def_id: Option<u32>,
    pub channel_index: Option<u32>,
    pub rule_index: Option<u32>,
    pub queue_bound: JoinQueueBound,
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

/// Representation selected by the CFA/lowering boundary for one join body.
///
/// The value is a proof result, not a user annotation. `Generic` means that
/// the compatibility matcher remains necessary. The fixed representations
/// are reserved for a later interprocedural instance proof; body-local event
/// counts must never select them.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinLoweringStrategy {
    Generic,
    DirectFuture,
    FixedUnarySlot,
    FixedPairMatcher,
    /// Safe atomic token storage for an exact `u64` one-way state channel.
    /// This is deliberately narrower than `FixedPairMatcher`; no generic
    /// payload is reinterpreted as an integer by the lowering.
    FixedAtomicU64Pair,
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

/// Body-local occupancy facts for one source-declaration channel.
///
/// The existing `JoinOccupancyFact` deliberately summarizes all semantic
/// register/match events in a body.  That aggregate is useful for detecting
/// loops, but it cannot distinguish a state token from an unrelated reply
/// queue.  Keep the channel coordinate beside the interval so an
/// interprocedural proof can later join producer, matcher, and re-emission
/// facts without reconstructing the pattern from generated method names.
/// These are still body-local facts: a complete bit here never authorizes a
/// fixed representation by itself.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinChannelOccupancyFact {
    pub channel_index: u32,
    pub occupancy: JoinOccupancyFact,
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

/// A compiler-owned proof witness for a result-channel forwarding rewrite.
///
/// The locations are body-local indices in the same pre-cleanup MIR snapshot
/// as the enclosing summary.  Definition identities are compact local
/// indices here because the enclosing `JoinCfaSummary` already carries the
/// endpoint/body identity; a future cross-crate certificate can replace them
/// with `DefId`s without changing the operation carrier.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinFusionFact {
    pub constructor_block: u32,
    pub constructor_statement: u32,
    pub channel_block: u32,
    pub channel_statement: u32,
    pub channel_method_def_id: u32,
    pub direct_method_def_id: u32,
    pub private_constructor_def_id: Option<u32>,
    pub rewritten: bool,
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
    /// Source-rule coordinate, when this body belongs to a named dynamic
    /// reaction helper. Dispatch and ordinary endpoint bodies leave it unset.
    pub rule_index: Option<u32>,
    /// Fingerprint of the executable MIR snapshot plus the extracted typed
    /// facts. A proof consumer must compare this with the current body before
    /// rewriting; a changed CFG or operation stream invalidates the snapshot.
    pub mir_fingerprint: u64,
    pub role: JoinBodyRole,
    pub arity: u32,
    pub is_async: bool,
    pub frontend_direct_unary: bool,
    pub queue_bound: JoinQueueBound,
    pub lowering: JoinLoweringStrategy,
    pub occupancy: JoinOccupancyFact,
    /// Per-channel body-local occupancy facts.  The list is sorted by source
    /// channel index before it is installed in the summary and dump.
    pub channel_occupancy: Vec<JoinChannelOccupancyFact>,
    pub instance_closedness: JoinInstanceClosedness,
    pub instance_closedness_reason: JoinInstanceClosednessReason,
    pub operations: Vec<JoinMirOperation>,
    pub value_flows: Vec<JoinValueFlow>,
    pub closure_facts: Vec<JoinCfaClosureFact>,
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
    /// Present only when the proof consumer found and rewrote a private
    /// result-forwarding edge in this body.  A missing value is not a proof of
    /// rejection; it means that no eligible forwarding edge was discovered.
    pub fusion: Option<JoinFusionFact>,
    /// The explicit reason a proof-consuming fusion attempt was declined.
    /// `None` means the pass was not applicable (for example in off/analyze
    /// mode) or the rewrite succeeded. This is separate from `rejection`,
    /// which classifies the reaction body itself.
    pub fusion_rejection: Option<JoinCfaRejection>,
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
    /// Source channel identity for a generated channel body. This lets the
    /// solver recover the semantic registration event when the frontend call
    /// is represented by a shared dispatch method rather than a
    /// channel-specific DefId.
    pub channel_index: Option<u32>,
    /// Source-rule coordinate for reaction bodies.  The generated dynamic
    /// endpoint has one shared dispatch owner, so the method DefId alone is
    /// not enough to relate a re-emission to the rule that consumed it.
    pub rule_index: Option<u32>,
    pub role: JoinBodyRole,
    pub value_flows: Vec<JoinValueFlow>,
    pub closure_facts: Vec<JoinCfaClosureFact>,
    pub call_edges: Vec<JoinCallEdge>,
    /// Number of MIR call and yield events in this body.  Keeping these
    /// effects on the crate graph lets the context solver distinguish a
    /// caller-driven, non-suspending path from a body that may schedule or
    /// suspend when it is reached through another call site.
    pub calls: u32,
    pub yields: u32,
    pub unknown_effects: u32,
    pub endpoint_escapes: Vec<JoinEndpointEscape>,
    /// Basic blocks which are part of a control-flow cycle in this body.
    /// State-token proofs must reject a producer/re-emission edge located in
    /// one of these blocks until interprocedural multiplicity is modelled.
    pub cyclic_blocks: Vec<u32>,
}

/// Effects propagated by the compiler-owned bounded CFA.  This is deliberately
/// smaller than MIR's complete effect system: it records exactly the facts
/// that can invalidate a private/local join specialization.  A missing or
/// unresolved dependency widens the corresponding bit instead of being
/// treated as a proof of absence.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinCfaEffects {
    pub may_suspend: bool,
    pub may_escape: bool,
    pub may_external: bool,
}

/// The kind of source-level event represented by a bounded CFA frame.
///
/// JCAM's history contains join construction/emission events because it has
/// no ordinary function-call graph. Rust has both kinds of edges, so the
/// compiler keeps them tagged in one history. Generated dispatch/reaction
/// adapters are not frames: the semantic event is recorded once at the
/// source-level constructor or channel registration and then propagated
/// through those adapters.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinCfaContextFrameKind {
    RustCall,
    JoinCreate,
    JoinRegister,
}

/// One retained semantic call/history frame in the rustc-owned CFA. The
/// source location and resolved identities are retained so the frame remains
/// meaningful after generated method bodies are introduced or remapped.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinCfaContextFrame {
    pub kind: JoinCfaContextFrameKind,
    pub caller_body_def_id: u32,
    pub block: u32,
    pub statement: u32,
    pub callee_body_def_id: u32,
    /// Endpoint/group identity for semantic join frames. Ordinary Rust call
    /// frames leave these coordinates absent.
    pub group_def_id: Option<u32>,
    pub channel_index: Option<u32>,
    pub rule_index: Option<u32>,
}

/// A bounded context-sensitive instance of a MIR body.  Multiple concrete
/// call paths merge only when their retained call strings are equal; effects
/// are joined monotonically at the merged state.
#[derive(Clone, Debug, PartialEq, Eq)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinCfaContextInstance {
    pub body_def_id: u32,
    pub context: Vec<JoinCfaContextFrame>,
    pub truncated: bool,
    pub local_effects: JoinCfaEffects,
    pub inherited_effects: JoinCfaEffects,
    pub closed: bool,
    pub optimization_safe: bool,
}

/// Result of the compiler-native bounded context analysis.  `complete` is the
/// only authority for proof-consuming transforms: a partial graph is useful
/// for diagnostics but must not enable a representation change.
#[derive(Clone, Debug, PartialEq, Eq)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinCfaContextSummary {
    pub context_depth: u32,
    pub instances: Vec<JoinCfaContextInstance>,
    pub transitions: u32,
    pub complete: bool,
}

/// The two control-flow states used by the JCAM abstract interpreter.
///
/// Rust still has ordinary function calls in addition to join emissions, so
/// this state is carried by the compiler's value facts rather than being
/// encoded in a generated runtime helper.  `Foreground` is the caller's
/// currently demanded path; `Background` is a value which may be retained by
/// a channel or closure and reached again by a later emission.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinCfaFlowState {
    Background,
    Foreground,
}

/// The side of a wildcard in the JCAM abstract value domain.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinCfaSide {
    Inner,
    Outer,
    Primitive,
}

/// A compiler-owned abstract value.  Unlike the old `JoinValueState` lattice,
/// this records *what* flows, not only whether a MIR local looks opaque.
/// `Channel` and `Closure` preserve the identities needed by `Emit` to decide
/// whether a value stays inside one join group or crosses its boundary.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinCfaValue {
    Wildcard(JoinCfaSide),
    Primitive,
    Channel {
        endpoint_def_id: u32,
        channel_index: Option<u32>,
    },
    Closure {
        body_def_id: u32,
        /// Values captured by this closure aggregate, in the typed MIR
        /// capture-field order. Keeping the actual values on the abstract
        /// closure preserves the substitution inputs; the solver uses them
        /// when entering the nested body at an Emit site.
        captures: Box<[u64]>,
        /// The context-qualified creation site of this closure value.  A
        /// body identity alone is not enough: Dovetail's `Closure(f, cs, is)`
        /// value is instantiated separately for each retained emission
        /// history.  This origin keeps two otherwise identical zero-capture
        /// closures distinct until the bounded-context solver has decided
        /// that their histories may be merged.
        origin: u64,
    },
}

/// One solved abstract value at a semantic variable.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinCfaValueFact {
    /// Locals use `(body_def_id << 32) | local`; the high-bit tagged values
    /// used for synthetic channel variables are documented in rustc_mir.
    pub variable: u64,
    pub state: JoinCfaFlowState,
    pub value: JoinCfaValue,
}

/// A JCAM-style constraint extracted from typed MIR.  Constraints remain
/// source-positioned and typed until the fixed-point solver has consumed
/// them, so later lowering does not need to reverse engineer queue helpers.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinCfaConstraintKind {
    /// `destination >= state(source)`; `None` preserves the source state.
    Succ {
        destination: u64,
        state: Option<JoinCfaFlowState>,
        source: u64,
    },
    /// Seed a variable with an abstract value.
    In {
        destination: u64,
        state: JoinCfaFlowState,
        value: JoinCfaValue,
    },
    /// Emit the input values to a channel/continuation variable.  The bounded
    /// call history includes ordinary calls as well as join construction and
    /// registration, matching the Rust interpretation of JCAM's `k` history.
    Emit {
        inputs: Box<[u64]>,
        target: u64,
        history: Box<[JoinCfaContextFrame]>,
    },
    /// Construct a closure-like value and retain explicit capture edges.
    Closure {
        destination: u64,
        body_def_id: u32,
        captures: Box<[u64]>,
    },
    /// A typed value crossed an external boundary.
    Escape {
        source: u64,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinCfaConstraint {
    pub body_def_id: u32,
    pub block: u32,
    pub statement: u32,
    pub kind: JoinCfaConstraintKind,
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

/// A transition observed while checking a compiler-described state-token
/// protocol.  These are evidence records only: they identify the concrete
/// MIR edge which supplied, consumed, or re-emitted the token.  A proof
/// consumer must still validate the current MIR fingerprint before changing
/// representation.
#[derive(Clone, Debug, PartialEq, Eq)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinStateTokenTransition {
    pub body_def_id: u32,
    pub role: JoinBodyRole,
    pub kind: JoinStateTokenTransitionKind,
    pub block: u32,
    pub statement: u32,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinStateTokenTransitionKind {
    Seed,
    Claim,
    Reemit,
}

/// Why a candidate state-token protocol was not proved.  The reasons are
/// intentionally semantic rather than frontend-shape based: a generated
/// queue implementation or a user annotation can never manufacture a proof.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinStateTokenRejection {
    NoUniqueInstance,
    DuplicateSeed,
    EscapingProducer,
    UnknownProducer,
    CompetingRule,
    MissingReemission,
    MultipleReemissions,
    LoopMultiplicity,
    HelperMultiplicity,
    UnsupportedRuleShape,
    IncompleteAnalysis,
}

/// Cross-body proof for a state channel whose token count is statically
/// bounded by one.  `status == Proven` is the only value that may eventually
/// authorize inline storage; all other records are explicit negative evidence
/// and must retain the generic matcher.  Pending requests on other channels
/// are deliberately not included in this bound.
#[derive(Clone, Debug, PartialEq, Eq)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinStateTokenProof {
    pub endpoint_def_id: u32,
    pub instance_body_def_id: Option<u32>,
    pub allocation_block: Option<u32>,
    pub allocation_statement: Option<u32>,
    pub rule_index: u32,
    pub channel_index: u32,
    pub seed_events: u32,
    pub claim_events: u32,
    pub reemit_events: u32,
    pub proven_bound: JoinQueueBound,
    pub status: JoinStateTokenStatus,
    pub rejection: Option<JoinStateTokenRejection>,
    pub transitions: Vec<JoinStateTokenTransition>,
}

/// The first proof consumer for a state-token channel.  This is an explicit
/// compiler decision, separate from the evidence record: only a `Proven`
/// state-token proof in optimize mode can produce one.  The decision is still
/// a lowering contract rather than a runtime hint; the eventual MIR/LLVM
/// lowering must validate the referenced fingerprints and materialize the
/// inline storage before this record is treated as executable.
#[derive(Clone, Debug, PartialEq, Eq)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinStateTokenLowering {
    pub endpoint_def_id: u32,
    pub rule_index: u32,
    pub channel_index: u32,
    pub proven_bound: JoinQueueBound,
    pub strategy: JoinLoweringStrategy,
    /// Deterministic identity of the positive proof record which selected
    /// this lowering. This is evidence identity, not a runtime pointer or a
    /// user-visible token.
    pub certificate_id: u64,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub enum JoinStateTokenStatus {
    Proven,
    Rejected,
}

/// Crate-level join facts.  This query is deliberately `eval_always` while the
/// representation is experimental: it consumes pre-cleanup summaries and is
/// not yet a stable incremental artifact.
#[derive(Clone, Debug, PartialEq, Eq)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinCfaCrateSummary {
    pub bodies: Vec<JoinCfaBodyRecord>,
    pub instances: Vec<JoinCfaInstanceFact>,
    pub state_tokens: Vec<JoinStateTokenProof>,
    pub state_token_lowerings: Vec<JoinStateTokenLowering>,
    pub context: JoinCfaContextSummary,
    /// The fixed-point JCAM value constraints and their solved facts.  These
    /// are deliberately separate from the effect/context summary above: a
    /// context graph without abstract values is not a complete CFA.
    pub cfa_constraints: Vec<JoinCfaConstraint>,
    pub cfa_solution: Vec<JoinCfaValueFact>,
    pub cfa_steps: u32,
    pub cfa_complete: bool,
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
    /// No unique constructor origin could be connected to the request.
    UnknownOrigin,
    /// More than one live constructor origin reaches the candidate use.
    MultipleInstances,
    /// A handle, reply or body value escapes the private proof boundary.
    Escape,
    /// Another rule or join operation can observe the same protocol.
    CompetingRule,
    /// An explicit shared executor/scope policy is outside caller-owned fusion.
    SharedPolicy,
    /// Admission is fallible or otherwise observable by the caller.
    AdmissionEffect,
    /// Group creation/destruction or tracing effects would be removed.
    ObservableGroupEffect,
    /// The use shape cannot be represented by the current rewrite.
    UnsupportedUse,
    /// A cycle or recursive helper would require path-sensitive reasoning.
    RecursiveOrCyclic,
    /// A callee or compiler-owned adapter could not be resolved.
    UnknownCallee,
    /// The configured CFA budget did not cover a required dependency.
    Budget,
    /// The body changed after the proof snapshot was produced.
    StaleProof,
}
