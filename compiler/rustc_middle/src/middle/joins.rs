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
    Channel,
    Dispatch,
    ReactionBody,
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
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[derive(StableHash, TyEncodable, TyDecodable, TypeFoldable, TypeVisitable)]
pub struct JoinCallEdge {
    pub block: u32,
    pub statement: u32,
    pub callee: Option<u32>,
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
    pub endpoint_def_id: u32,
    pub rule_def_id: u32,
    pub role: JoinBodyRole,
    pub arity: u32,
    pub is_async: bool,
    pub frontend_direct_unary: bool,
    pub queue_bound: JoinQueueBound,
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
    pub direct_candidate: bool,
    pub rejection: Option<JoinCfaRejection>,
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
