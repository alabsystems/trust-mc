// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC expression codegen subsystem facade.
//!
//! This keeps the expression codegen family behind a real `expr/` module
//! boundary while preserving the historical `super::...` imports used by the
//! already-split leaf modules.

// Re-export chc-level items so that leaf modules can keep their `use super::...` imports.
pub(super) use super::{
    ChcCtx, FieldProjection, UnknownProjectionPolicy, chc_debug_enabled, codegen_ctx,
    codegen_decl_flatten, codegen_stmt_aggregate_adt, codegen_stmt_projection, codegen_types,
    codegen_types_adt_sort, collect_field_projections, constant_index_offset, memory_model, names,
};

pub(super) mod codegen_expr;
pub(super) mod codegen_expr_array_eq;
pub(super) mod codegen_expr_assert;
pub(super) mod codegen_expr_assert_simplify;
pub(super) mod codegen_expr_constant;
pub(in crate::codegen_ay) mod codegen_expr_constant_payload;
pub(super) mod codegen_expr_deref;
pub(super) mod codegen_expr_deref_field;
pub(super) mod codegen_expr_deref_field_offset;
pub(super) mod codegen_expr_deref_field_validity;
pub(super) mod codegen_expr_deref_null_check;
pub(super) mod codegen_expr_deref_projection;
pub(super) mod codegen_expr_deref_resolve;
pub(super) mod codegen_expr_deref_slice_index;
pub(super) mod codegen_expr_deref_static;
pub(super) mod codegen_expr_deref_subslice;
pub(super) mod codegen_expr_detect;
pub(super) mod codegen_expr_env;
pub(super) mod codegen_expr_flattened;
pub(super) mod codegen_expr_flattened_coroutine;
pub(super) mod codegen_expr_flattened_index;
pub(super) mod codegen_expr_heap;
pub(super) mod codegen_expr_heap_bv_eval;
pub(super) mod codegen_expr_heap_span;
pub(super) mod codegen_expr_reconstruct;
pub(super) mod codegen_expr_reconstruct_flattened;
pub(super) mod codegen_expr_signedness;
