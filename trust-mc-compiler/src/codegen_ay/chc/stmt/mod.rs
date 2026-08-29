// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Statement codegen — CHC encoding of MIR statements and assignments.
//!
//! Converted from `#[path = "stmt/..."]` directives in `chc/mod.rs` to a proper
//! directory module per #3254.

// Re-export items from parent (chc) that stmt files access via `super::`.
// Children can see parent private items, so these resolve through chc's
// private `use` imports.
use super::CHC_DEBUG_FLAG;
use super::ChcCtx;
use super::ChcDebugMode;
use super::MemPromoteAction;
use super::POINTER_WIDTH;
use super::UNDEF_COUNTER;
use super::chc_debug_enabled;
use super::chc_fresh_name;
use super::codegen_ctx::RefTarget;
use super::codegen_ctx::types::ChcConfig;
use super::declare_pending_var;
use super::push_pending_var_decl;

// Re-export sibling modules from chc that stmt files access via
// `super::module::item` paths.
use super::codegen_call_cmp_string;
use super::codegen_call_coerce;
use super::codegen_call_vec;
use super::codegen_ctx;
use super::codegen_decl_flatten;
use super::codegen_expr_heap;
use super::codegen_expr_signedness;
use super::codegen_rules;
use super::codegen_types;
use super::codegen_types_adt_sort;
use super::pointer_step;
use super::stubs_option_helpers;

// Preserve the historical `super::codegen_expr_array_eq` path for leaf modules
// that have not yet moved to the chc-level import.
mod codegen_expr_array_eq {
    use ay_bindings::Expr;
    use rustc_public::mir::{LocalDecl, Operand};

    pub(super) use super::super::codegen_expr_array_eq::{
        build_spec_array_eq, recover_spec_array_eq_len,
    };

    type BuildSpecArrayEq = fn(&Expr, &Expr, Option<usize>) -> Option<Expr>;
    type RecoverSpecArrayEqLen = fn(Option<&str>, Option<&Operand>, &[LocalDecl]) -> Option<usize>;

    const _: (BuildSpecArrayEq, RecoverSpecArrayEqLen) =
        (build_spec_array_eq, recover_spec_array_eq_len);
}

// --- Statement submodules ---
// pub(super): accessed from chc via re-export (expr/, call/, tests/)
// pub(crate): accessed externally via crate:: paths (statement/)

pub(super) mod codegen_stmt;
pub(crate) mod codegen_stmt_aggregate_adt;
mod codegen_stmt_aggregate_adt_option;
mod codegen_stmt_aggregate_adt_special;
mod codegen_stmt_aggregate_adt_struct_enum;
pub(super) mod codegen_stmt_flatten;
pub(super) mod codegen_stmt_memory_bridge;
pub(super) mod codegen_stmt_mirror;
pub(super) mod codegen_stmt_output;
pub(super) mod codegen_stmt_projection;
pub(super) mod codegen_stmt_store;
pub(in crate::codegen_ay::chc) use codegen_stmt_store::deref_mem::ProvDef;
pub(super) mod codegen_stmt_store_ref;
pub(super) mod stmt_accumulator;

mod codegen_stmt_aggregate;
mod codegen_stmt_aggregate_closure;
mod codegen_stmt_aggregate_discr;
mod codegen_stmt_aggregate_discr_adt;
mod codegen_stmt_aggregate_discr_literal_opt;
mod codegen_stmt_aggregate_wrapper;
mod codegen_stmt_arithmetic;
mod codegen_stmt_arithmetic_coerce;
mod codegen_stmt_arithmetic_ops;
mod codegen_stmt_assign_cleanup;
mod codegen_stmt_assign_projection;
mod codegen_stmt_assign_projection_field;
mod codegen_stmt_assign_simple;
mod codegen_stmt_assign_simple_collection;
mod codegen_stmt_assign_simple_single_assign;
mod codegen_stmt_assign_simple_vtable;
mod codegen_stmt_const_ref_assign;
mod codegen_stmt_copy;
mod codegen_stmt_copy_intrinsic;
mod codegen_stmt_flatten_constrain;
pub(super) mod codegen_stmt_flatten_copy;
mod codegen_stmt_flatten_dt_ite;
mod codegen_stmt_flatten_enum_bv;
mod codegen_stmt_ptr_metadata;
mod codegen_stmt_ptr_metadata_copy_trace;
mod codegen_stmt_ptr_metadata_mir_trace;
mod codegen_stmt_ptr_metadata_mir_trace_util;
mod codegen_stmt_rvalue;
mod codegen_stmt_rvalue_binop;
mod codegen_stmt_rvalue_box;
mod codegen_stmt_rvalue_len;
mod codegen_stmt_rvalue_offset;
mod codegen_stmt_rvalue_pun_scan;
mod codegen_stmt_rvalue_ref;
pub(crate) mod codegen_stmt_slice_metadata;
mod codegen_stmt_store_array;
mod codegen_stmt_store_ref_array;
mod codegen_stmt_store_ref_array_compound;
mod codegen_stmt_store_ref_collection;
pub(super) mod codegen_stmt_vtable_tracking;

// Re-export inter-stmt items used by stmt files via `super::`.
use codegen_stmt_projection::FieldProjection;
use codegen_stmt_projection::UnknownProjectionPolicy;
use codegen_stmt_projection::collect_field_projections;
use codegen_stmt_projection::constant_index_offset;
