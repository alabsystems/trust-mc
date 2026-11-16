// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC call-terminator codegen subsystem facade.
//!
//! This keeps the call dispatch, inline, and pointer-handling family behind a
//! real `call/` module boundary while preserving the historical `super::...`
//! imports used by the already-split leaf modules.

// ── Re-export chc-level items so leaf modules can keep `use super::...` ──

pub(in crate::codegen_ay::chc) use super::{
    AllocCallResult, ChcCtx, FieldProjection, KaniHook, KaniIntrinsic, KaniModel, RelationApp,
    Rule, RuleBody, UnknownProjectionPolicy, chc_debug_enabled, chc_fresh_name, codegen_ctx,
    codegen_expr_assert, codegen_expr_constant, codegen_expr_heap, codegen_expr_signedness,
    codegen_rules, codegen_rules_helpers, codegen_stmt_flatten, codegen_types,
    collect_field_projections, constant_index_offset, dyn_coercion, dyn_dispatch_scope,
    heap_store_chains, pointer_step, quantifier_encoding, stmt_accumulator, stubs_option_helpers,
    ty_signedness,
};

// Re-export decl submodule (used as `super::codegen_decl_flatten` by leaf modules)
pub(in crate::codegen_ay::chc) use super::decl::codegen_decl_flatten;

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

// ── Modules accessed from outside call/ ──

pub(in crate::codegen_ay::chc) mod chc_call_context;
pub(in crate::codegen_ay::chc) mod codegen_call;
pub(in crate::codegen_ay::chc) mod codegen_call_coerce;
pub(in crate::codegen_ay::chc) mod codegen_call_vtable_intrinsic;

// ── Internal modules ──

pub(in crate::codegen_ay::chc) mod call_accumulator;
pub(in crate::codegen_ay::chc) mod codegen_call_alloc;
mod codegen_call_alloc_payload;
pub(in crate::codegen_ay::chc) mod codegen_call_array_solver_shadow;
mod codegen_call_array_solver_shadow_resolve;
mod codegen_call_array_solver_shadow_state;
mod codegen_call_array_solver_visible_state;
pub(in crate::codegen_ay) mod codegen_call_atomic;
mod codegen_call_atomic_from_ptr;
mod codegen_call_atomic_mem;
pub(in crate::codegen_ay::chc) mod codegen_call_atomic_rmw;
mod codegen_call_bigint_preroute;
pub(in crate::codegen_ay::chc) mod codegen_call_block_on;
mod codegen_call_block_on_body_helpers;
mod codegen_call_block_on_spawn;
mod codegen_call_block_on_specialize;
mod codegen_call_catch_unwind;
pub(in crate::codegen_ay::chc) mod codegen_call_cell;
mod codegen_call_cell_register;
pub(in crate::codegen_ay) mod codegen_call_static_atomic_address;
#[cfg(all(trust_toolchain, version("1.101")))]
mod native_box_into_raw;
mod native_box_uninit;
#[cfg(all(trust_toolchain, version("1.101")))]
mod native_init_capability;
#[cfg(all(trust_toolchain, version("1.101")))]
mod native_init_custody;
#[cfg(all(trust_toolchain, version("1.101")))]
mod native_init_domain;
#[cfg(all(trust_toolchain, version("1.101")))]
pub(in crate::codegen_ay::chc) mod native_init_handoff;
#[cfg(all(trust_toolchain, version("1.101")))]
mod native_init_memory;
#[cfg(all(trust_toolchain, version("1.101")))]
mod native_init_observers;
#[cfg(all(trust_toolchain, version("1.101")))]
mod native_init_shadow;
#[cfg(all(trust_toolchain, version("1.101")))]
mod native_init_values;
#[cfg(all(trust_toolchain, version("1.101")))]
mod native_init_write;
#[cfg(all(trust_toolchain, version("1.101")))]
mod native_maybe_access;
pub(in crate::codegen_ay::chc) use codegen_call_cell_register::substitute_vars;
pub(in crate::codegen_ay::chc) mod codegen_call_closure;
mod codegen_call_cmp;
mod codegen_call_cmp_array_stub;
mod codegen_call_cmp_operand;
mod codegen_call_cmp_ord;
mod codegen_call_cmp_semantic;
pub(in crate::codegen_ay) mod codegen_call_cmp_string;
pub(in crate::codegen_ay::chc) mod codegen_call_collections;
pub(in crate::codegen_ay::chc) mod codegen_call_coroutine;
pub(in crate::codegen_ay::chc) mod codegen_call_dispatch_collections;
mod codegen_call_dispatch_dyn;
mod codegen_call_dispatch_dyn_rc;
pub(in crate::codegen_ay::chc) mod codegen_call_dispatch_kani;
pub(in crate::codegen_ay::chc) mod codegen_call_dispatch_misc;
pub(in crate::codegen_ay::chc) mod codegen_call_dispatch_option_ptr;
mod codegen_call_dispatch_overapprox;
mod codegen_call_dispatch_overapprox_kani_mem;
mod codegen_call_dispatch_overapprox_kani_mem_ssa;
mod codegen_call_fallback_emit;
pub(in crate::codegen_ay::chc) mod codegen_call_fn_inline;
pub(in crate::codegen_ay::chc) mod codegen_call_fn_inline_emit;
mod codegen_call_fn_inline_specialization;
mod codegen_call_fn_ptr;
pub(in crate::codegen_ay::chc) mod codegen_call_hashmap_iter;
mod codegen_call_index_range_len;
mod codegen_call_iter_collect_method;
pub(in crate::codegen_ay::chc) mod codegen_call_iterator_adapter;
mod codegen_call_kani;
pub(crate) mod codegen_call_kani_any_vec;
mod codegen_call_kani_hooks;
mod codegen_call_kani_hooks_model;
mod codegen_call_kani_hooks_pointer;
pub(in crate::codegen_ay::chc) mod codegen_call_kani_model;
pub(in crate::codegen_ay::chc) mod codegen_call_kani_model_dst;
mod codegen_call_kani_model_dyn;
mod codegen_call_kani_model_mem_init;
mod codegen_call_kani_model_zst;
mod codegen_call_model_unwind;
pub(in crate::codegen_ay::chc) mod fn_ptr_targets;
pub(in crate::codegen_ay::chc) use self::codegen_call_kani_model_zst::{
    canonical_zst_expr, canonical_zst_expr_for_sort,
};
pub(in crate::codegen_ay::chc) use self::codegen_call_slice_helpers::SLICE_BACKING_REBASE_MAX_ELEMS;
pub(in crate::codegen_ay::chc) mod codegen_call_misc;
mod codegen_call_numeric;
pub(in crate::codegen_ay::chc) mod codegen_call_option_result;
mod codegen_call_option_result_emit;
mod codegen_call_promoted_option_predicate;
pub(in crate::codegen_ay::chc) mod codegen_call_ptr;
mod codegen_call_ptr_helpers;
pub(in crate::codegen_ay::chc) mod codegen_call_ptr_identity;
mod codegen_call_ptr_identity_cast;
mod codegen_call_ptr_identity_ref_target;
mod codegen_call_ptr_nonnull;
mod codegen_call_ptr_offset_metadata;
mod codegen_call_ptr_offset_metadata_helpers;
mod codegen_call_raw_ptr_as_ref;
pub(in crate::codegen_ay::chc) mod codegen_call_result_mem;
mod codegen_call_simd;
mod codegen_call_simd_lib;
mod codegen_call_simd_ops;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(in crate::codegen_ay::chc) use codegen_call_simd::SimdIntrinsicKind;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(in crate::codegen_ay::chc) use codegen_call_simd::{
    SimdLayoutInfo, extract_simd_layout, resolve_simd_array,
};
#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(in crate::codegen_ay::chc) use codegen_call_simd_lib::try_dispatch_simd_lib_call;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(in crate::codegen_ay::chc) use codegen_call_simd_ops::{
    SimdBinopOrigin, codegen_simd_elementwise_binop, codegen_simd_shift, codegen_simd_shuffle,
    divisor_lanes_nonzero,
};
mod codegen_call_slice;
mod codegen_call_slice_get;
mod codegen_call_slice_helpers;
mod codegen_call_slice_index;
mod codegen_call_slice_index_capture;
mod codegen_call_slice_provenance;
mod codegen_call_slice_query;
mod codegen_call_slice_range;
mod codegen_call_slice_repeat;
mod codegen_call_slice_zst_eq;
mod codegen_call_spine_helpers;
mod codegen_call_string;
pub(in crate::codegen_ay::chc) mod codegen_call_struct_clone;
pub(in crate::codegen_ay::chc) mod codegen_call_struct_map_constructor;
mod codegen_call_struct_method_passthrough;
mod codegen_call_struct_vec_accessor;
pub(in crate::codegen_ay::chc) mod codegen_call_struct_vec_constructor;
mod codegen_call_unsafe_cell;
pub(in crate::codegen_ay::chc) mod codegen_call_vec;
mod codegen_call_vec_append;
mod codegen_call_vec_array_iter;
#[cfg(test)]
mod codegen_call_vec_array_iter_tests;
mod codegen_call_vec_builder;
mod codegen_call_vec_builder_pattern;
mod codegen_call_vec_element;
mod codegen_call_vec_element_pop_struct;
mod codegen_call_vec_element_pop_struct_array_solver;
mod codegen_call_vec_element_struct;
mod codegen_call_vec_empty_pointer;
mod codegen_call_vec_into;
mod codegen_call_vec_iter;
mod codegen_call_vec_iter_next;
mod codegen_call_vec_mutation_state;
pub(crate) mod codegen_call_vec_ops;
mod codegen_call_vec_ops_extend_internal;
mod codegen_call_vec_ops_extend_range;
mod codegen_call_vec_ops_is_empty;
mod codegen_call_vec_ops_len;
mod codegen_call_vec_ops_mutate;
mod codegen_call_vec_ops_struct_resize;
mod codegen_call_vec_ops_views;
mod codegen_call_vec_resolve;
mod codegen_call_virtual;
pub(in crate::codegen_ay::chc) mod codegen_call_virtual_inline;
mod codegen_call_virtual_utils;
pub(in crate::codegen_ay::chc) mod codegen_slice_op;
pub(in crate::codegen_ay::chc) mod dispatch_helpers;
mod inline_aggregate;
pub(in crate::codegen_ay::chc) mod inline_alias_writeback;
mod inline_array_semantic_eq;
pub(in crate::codegen_ay::chc) mod inline_body;
mod inline_bool_return;
pub(in crate::codegen_ay::chc) mod inline_budget;
mod inline_const_origin;
pub(in crate::codegen_ay::chc) mod inline_field_map;
pub(in crate::codegen_ay::chc) mod inline_field_map_reconstruct;
mod inline_iterator_eq;
pub(in crate::codegen_ay::chc) mod inline_known_calls;
mod inline_known_calls_math;
mod inline_known_calls_raw_ptr;
mod inline_known_calls_simd;
pub(in crate::codegen_ay::chc) mod inline_mut_ref_owner;
mod inline_readonly_capture;
pub(in crate::codegen_ay::chc) mod inline_readonly_ref;
pub(in crate::codegen_ay::chc) mod inline_ref_arg_binding;
mod inline_result_shared;
pub(in crate::codegen_ay::chc) mod inline_shared;
mod inline_storage_address;
mod inline_str_chars;
pub(in crate::codegen_ay::chc) mod inline_walk_guard;
pub(in crate::codegen_ay::chc) mod inline_work_budget;
pub(in crate::codegen_ay::chc) mod native_drop_memory;
pub(in crate::codegen_ay::chc) mod native_dyn_drop;
pub(in crate::codegen_ay::chc) mod native_dyn_origin;
mod ptr_offset_common;
pub(in crate::codegen_ay::chc) mod ptr_receiver_mem;
pub(in crate::codegen_ay::chc) mod range_span;

#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(in crate::codegen_ay::chc) fn try_inline_nested_call_step(
    ctx: &mut ChcCtx<'_, '_>,
    func: &rustc_public::mir::Operand,
    args: &[rustc_public::mir::Operand],
    outer_body: &rustc_public::mir::Body,
    local_exprs: &std::collections::HashMap<usize, ay_bindings::Expr>,
    resolver: &inline_shared::PlaceResolver<'_>,
    inline_vtable_ids: &std::collections::HashMap<usize, ay_bindings::Expr>,
    inline_alloc_ids: &std::collections::HashMap<usize, u32>,
    destination: &rustc_public::mir::Place,
    inline_depth: usize,
) -> Option<inline_body::InlineReturn> {
    codegen_call_virtual_inline::try_inline_nested_call_step(
        ctx,
        func,
        args,
        outer_body,
        local_exprs,
        resolver,
        inline_vtable_ids,
        inline_alloc_ids,
        destination,
        inline_depth,
    )
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(in crate::codegen_ay::chc) fn build_nested_call_fallback_expr_for_test(
    effective_sort: ay_bindings::Sort,
    is_pointer_like: bool,
) -> ay_bindings::Expr {
    codegen_call_virtual_inline::build_nested_call_fallback_expr_for_test(
        effective_sort,
        is_pointer_like,
    )
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(in crate::codegen_ay::chc) fn unprojected_inline_drop_arg_base_local_for_test(
    outer_body: &rustc_public::mir::Body,
    arg: &rustc_public::mir::Operand,
) -> Option<usize> {
    codegen_call_virtual_inline::unprojected_inline_drop_arg_base_local_for_test(outer_body, arg)
}

#[cfg(test)]
#[allow(dead_code)]
pub(in crate::codegen_ay::chc) fn build_dispatch_ite_chain_for_test(
    ctx: &mut ChcCtx<'_, '_>,
    concrete_bodies: &[super::dyn_coercion::ResolvedDispatchBody],
    param_exprs: &[ay_bindings::Expr],
    vtable_disc: ay_bindings::Expr,
    bb_idx: usize,
    caller_vtable_ids: &std::collections::HashMap<usize, ay_bindings::Expr>,
) -> Option<inline_body::InlineReturn> {
    codegen_call_virtual_inline::build_dispatch_ite_chain(
        ctx,
        concrete_bodies,
        param_exprs,
        vtable_disc,
        bb_idx,
        caller_vtable_ids,
        &super::dyn_dispatch_scope::DynDispatchScope::unknown(),
    )
}
