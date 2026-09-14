//! Compiler-owned descriptions of expanded `join impl` endpoints.
//!
//! The frontend currently lowers the experimental syntax through a builtin
//! macro, but it leaves a parsed `join_endpoint` contract on the
//! generated impl. This module is the typed seam between that expansion and
//! later CFA/MIR work: identities are local `DefId`s and channel signatures
//! are rustc's resolved types rather than source strings.

use rustc_hir::def_id::LocalDefId;
use rustc_macros::StableHash;
use rustc_span::Symbol;

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
    /// Generated channel methods with their resolved function signatures.
    pub channels: Vec<JoinChannel<'tcx>>,
    /// Generated dispatch method(s). The first compiler slice emits one
    /// dispatch body for the restricted unary/pair forms.
    pub rules: Vec<JoinRule>,
}

/// A channel endpoint represented by its resolved associated function.
#[derive(Debug, StableHash)]
pub struct JoinChannel<'tcx> {
    pub method_def_id: LocalDefId,
    pub name: Symbol,
    pub signature: PolyFnSig<'tcx>,
}

/// A reaction dispatch body and the shape known at expansion time.
#[derive(Debug, StableHash)]
pub struct JoinRule {
    pub method_def_id: LocalDefId,
    pub arity: u32,
    pub is_async: bool,
}
