// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC declaration and type-codegen subsystem facade.
//!
//! This keeps the declaration family behind a real `decl/` module boundary
//! while preserving the historical `super::...` imports used by the
//! already-split leaf modules.

// Re-export chc-level items so that leaf modules can keep their `use super::...` imports.
pub(super) use super::{
    ChcCtx, RefTarget, chc_fresh_name, codegen_ctx, codegen_expr_constant, codegen_expr_heap,
    codegen_rules_entry, codegen_rules_helpers, declare_pending_var, fragment, names,
    push_pending_datatype_sort, record_type_sort_fallback,
};

mod codegen_decl;
mod codegen_decl_cleanup_seed;
mod codegen_decl_datatypes;
mod codegen_decl_deref;
pub(in crate::codegen_ay::chc) mod codegen_decl_flatten;
mod codegen_decl_heap;
mod codegen_decl_liveness;
pub(in crate::codegen_ay::chc) mod codegen_decl_panic_filter;
mod codegen_decl_ref_const_discriminant;
mod codegen_decl_ref_const_extract;
mod codegen_decl_ref_const_extract_adt;
mod codegen_decl_ref_const_extract_seq;
mod codegen_decl_ref_const_values;
mod codegen_decl_ref_numeric;
mod codegen_decl_state_vars;
mod codegen_decl_state_vars_arg_pointees;
mod codegen_decl_state_vars_array_solver_aux;
mod codegen_decl_state_vars_collections;
pub(in crate::codegen_ay) mod codegen_decl_state_vars_enum_layout;
mod codegen_decl_state_vars_locals;
mod codegen_decl_state_vars_locals_flatten;
pub(in crate::codegen_ay::chc) mod codegen_decl_static;
mod codegen_decl_static_alloc;
mod codegen_decl_static_callee;
mod codegen_decl_static_init;
mod codegen_decl_static_metadata;
mod codegen_decl_stub_internal;
mod codegen_decl_stub_internal_spawn;
mod codegen_decl_vtable;
pub(in crate::codegen_ay::chc) mod codegen_types;
pub(in crate::codegen_ay::chc) mod codegen_types_adt;
pub(in crate::codegen_ay::chc) mod codegen_types_adt_sort;
