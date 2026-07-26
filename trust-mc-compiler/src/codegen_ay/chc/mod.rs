// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC (Constrained Horn Clause) code generation from MIR.
//!
//! This module translates MIR basic blocks and terminators into CHC relations and rules,
//! enabling unbounded verification via AY's PDR-based CHC engine.
//!
//! Refactored per #1508: original 4816-line codegen.rs split into module families
//! (codegen_ctx, decl, rules, expr, stmt, call, heap, stub_codegen, etc.). Commit 0bb7fc2b.
//!
//! ## CHC Encoding Strategy
//!
//! CHC encoding strategy:
//!
//! - Each basic block `B` becomes a relation `B(state_params...)`
//! - Each CFG edge `B → S` becomes a Horn rule: `B(in) ∧ T(in,out) ∧ cond → S(out)`
//! - Assertions become error rules: `B(s) ∧ violation → error()`
//! - Query `error()` to check for reachable violations
//!
//! ## Example
//!
//! ```text
//! fn foo(x: bool) {
//!     let y = if x { 1 } else { 2 };
//!     assert!(y != 2);
//! }
//! ```
//!
//! Becomes:
//! ```text
//! (declare-rel entry (Bool Int))
//! (declare-rel then_bb (Bool Int))
//! (declare-rel else_bb (Bool Int))
//! (declare-rel join_bb (Bool Int))
//! (declare-rel error ())
//!
//! (rule (=> (and (entry x y) x) (then_bb x 1)))
//! (rule (=> (and (entry x y) (not x)) (else_bb x 2)))
//! (rule (=> (then_bb x y) (join_bb x y)))
//! (rule (=> (else_bb x y) (join_bb x y)))
//! (rule (=> (and (join_bb x y) (= y 2)) error))
//!
//! (query error)
//! ```

/// Declarative stub dispatch table macro (D3, Part of #2304).
///
/// Generates a match-based dispatch from a table of `(StubKind, handler_method)`
/// entries. This keeps the table-style callsite shape while avoiding generic
/// lifetime constraints from const fn-pointer tables on `ChcCtx<'tcx, 'body>`.
macro_rules! stub_dispatch {
    ($self:expr, $stub:expr, $ctx:expr, $trace_name:literal,
     $( $kind:pat => $handler:ident ),+ $(,)?) => {
        match $stub {
            $( $kind => $self.$handler($ctx), )+
            _other => { // partial dispatch: StubKind
                tracing::trace!(stub = ?_other, concat!($trace_name, ": unhandled stub kind"));
                None
            }
        }
    };
}

// Call-terminator codegen — proper directory module (Part of #3254)
pub(crate) mod call;
use call::chc_call_context;
use call::codegen_call;
use call::codegen_call_coerce;
use call::codegen_call_vtable_intrinsic;
// Re-export call/ submodules needed by non-call chc modules (quantifier_encoding, stmt, rules)
use call::codegen_call_cmp_string;
use call::codegen_call_vec;
use call::inline_known_calls;
use call::inline_shared;
// Re-export call/ submodules for test access (tests use super::super::codegen_call_*)
#[cfg(test)]
#[allow(unused_imports)]
use call::{
    call_accumulator, codegen_call_alloc, codegen_call_atomic, codegen_call_atomic_rmw,
    codegen_call_closure, codegen_call_collections, codegen_call_coroutine,
    codegen_call_dispatch_collections, codegen_call_dispatch_kani, codegen_call_dispatch_misc,
    codegen_call_dispatch_option_ptr, codegen_call_fn_inline, codegen_call_hashmap_iter,
    codegen_call_iterator_adapter, codegen_call_kani_model, codegen_call_kani_model_dst,
    codegen_call_misc, codegen_call_option_result, codegen_call_ptr, codegen_call_ptr_identity,
    codegen_call_struct_clone, codegen_call_struct_map_constructor,
    codegen_call_struct_vec_constructor, codegen_slice_op, inline_body, inline_budget,
    inline_field_map,
};
pub(in crate::codegen_ay) mod expr;
use expr::codegen_expr_array_eq;
use expr::codegen_expr_constant;
use expr::codegen_expr_env;
use expr::codegen_expr_signedness;
mod rules;
use rules::codegen_rules;
use rules::codegen_rules_entry;
use rules::codegen_rules_helpers;
// Statement codegen — proper directory module (Part of #3254)
mod stmt;
// Re-export stmt modules used by other chc children (expr/, call/, tests/)
use stmt::codegen_stmt_flatten;
use stmt::codegen_stmt_projection;
// Only used by chc::tests (codegen_stmt_mirror and codegen_stmt_store_ref are
// accessed by stmt children directly via their own super:: paths).
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use stmt::codegen_stmt_store_ref;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use stmt::codegen_stmt_vtable_tracking;
use stmt::stmt_accumulator;
// pub(crate) for external consumers (statement/*.rs, call/virtual_inline/)
pub(crate) use stmt::codegen_stmt_aggregate_adt;
mod decl;
use decl::codegen_decl_flatten;
use decl::codegen_decl_panic_filter;
use decl::codegen_types;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use decl::codegen_types_adt;
use decl::codegen_types_adt_sort;
mod dyn_coercion;
mod dyn_coercion_resolve;
mod error_property;
mod fieldless_constructor_cmp;
mod float_assertion_patterns;
mod float_binop_table;
mod float_fast_math_patterns;
mod float_floor_direction_patterns;
mod float_roundtrip_patterns;
mod fragment;
mod loop_modifies_frame;
mod modifies_frame;
mod pointer_step;
pub(in crate::codegen_ay) mod quantifier_encoding;
mod shadow_mem_state;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
mod tests;
use codegen_call::CallTerminator;
use codegen_call_coerce::CallCoerce;
#[cfg(test)]
pub(in crate::codegen_ay) use codegen_call_coerce::clear_chc_coerce_eq_dropped_constraint_counts_by_fn;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(super) use codegen_call_coerce::get_chc_coerce_eq_dropped_constraint_counts_by_fn;
#[cfg(test)]
pub(in crate::codegen_ay) use codegen_call_coerce::set_chc_coerce_eq_dropped_constraint_count_for_test;
pub(in crate::codegen_ay) use codegen_call_coerce::take_chc_coerce_eq_dropped_constraint_count;
pub(in crate::codegen_ay) use codegen_call_coerce::take_chc_coerce_eq_dropped_constraint_counts_by_fn;
#[cfg(test)]
pub(super) use codegen_expr::set_place_translation_drop_count_for_test;
pub(in crate::codegen_ay) use codegen_expr::take_place_translation_drop_count;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use codegen_expr_constant::ExprConstant;
#[cfg(test)]
pub(super) use codegen_expr_constant::set_constant_translation_drop_count_for_test;
pub(in crate::codegen_ay) use codegen_expr_constant::take_constant_translation_drop_count;
pub(in crate::codegen_ay) use codegen_expr_env::ExprEnv;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use codegen_expr_signedness::ExprSignedness;
use codegen_expr_signedness::ty_signedness;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use codegen_rules::CodegenRules;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use codegen_rules_entry::CodegenRulesEntry;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use codegen_rules_helpers::CodegenRulesHelpers;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use codegen_types_adt_sort::CodegenTypesAdtSort;
use stmt::codegen_stmt_projection::FieldProjection;
use stmt::codegen_stmt_projection::UnknownProjectionPolicy;
use stmt::codegen_stmt_projection::collect_constructor_guards;
use stmt::codegen_stmt_projection::collect_field_projections;
use stmt::codegen_stmt_projection::constant_index_offset;
#[cfg(test)]
pub(super) use stmt::codegen_stmt_projection::set_unsupported_field_projection_count_for_test;
pub(in crate::codegen_ay) use stmt::codegen_stmt_projection::take_unsupported_field_projection_count;
pub(in crate::codegen_ay) use stmt::codegen_stmt_store::get_chc_store_dropped_transition_count;

mod codegen_ctx;
mod heap;
use super::names;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use super::stubs::StubRegistry;
use super::types::POINTER_WIDTH;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use crate::args::ChcTrackLevel;
use crate::kani_middle::kani_functions::{KaniHook, KaniIntrinsic, KaniModel};
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use ay_bindings::Sort;
use codegen_ctx::CHC_DEBUG_FLAG;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use codegen_ctx::ChcCollectionLenState;
pub(in crate::codegen_ay) use codegen_ctx::ChcCtx;
pub(in crate::codegen_ay) use codegen_ctx::ChcDebugMode;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use codegen_ctx::PENDING_FRESH_VAR_DECLS;
use codegen_ctx::UNDEF_COUNTER;
pub(in crate::codegen_ay) use codegen_ctx::WideMemMode;
use codegen_ctx::chc_debug_enabled;
use codegen_ctx::chc_fresh_name;
#[cfg(test)]
pub(in crate::codegen_ay) use codegen_ctx::clear_chc_fallback_counts;
use codegen_ctx::declare_pending_var;
#[cfg(test)]
pub(in crate::codegen_ay) use codegen_ctx::diagnostics::GLOBAL_COUNTERS;
pub(in crate::codegen_ay) use codegen_ctx::get_aggregate_encoding_gap_count;
#[cfg(test)]
use codegen_ctx::get_chc_fallback_counts;
#[cfg(test)]
pub(in crate::codegen_ay) use codegen_ctx::get_chc_unhandled_call_count;
pub(in crate::codegen_ay) use codegen_ctx::get_fp_bitvector_encoding_count;
pub(in crate::codegen_ay) use codegen_ctx::get_inferable_predicate_count;
pub(in crate::codegen_ay) use codegen_ctx::get_ptr_metadata_unconstrained_count;
pub(in crate::codegen_ay) use codegen_ctx::get_rounding_assertion_bypass_count;
pub(in crate::codegen_ay) use codegen_ctx::get_static_init_incomplete_count;
pub(in crate::codegen_ay) use codegen_ctx::get_stub_approximation_count;
#[allow(unused_imports)] // W1:3920: caller not yet committed
pub(in crate::codegen_ay) use codegen_ctx::globals::get_chc_fallback_count_for_fn;
pub(in crate::codegen_ay) use codegen_ctx::globals::set_chc_fallback_count_for_fn;
pub(in crate::codegen_ay) use codegen_ctx::globals::take_aggregate_encoding_gap_by_fn;
pub(in crate::codegen_ay) use codegen_ctx::globals::take_aggregate_encoding_gap_count;
pub(in crate::codegen_ay) use codegen_ctx::globals::take_rounding_assertion_bypass_count;
pub(in crate::codegen_ay) use codegen_ctx::globals::take_stub_approximation_by_fn;
pub(in crate::codegen_ay) use codegen_ctx::globals::take_stub_approximation_count;
use codegen_ctx::push_pending_datatype_sort;
use codegen_ctx::push_pending_var_decl;
use codegen_ctx::record_type_sort_fallback;
#[cfg(test)]
pub(in crate::codegen_ay) use codegen_ctx::set_chc_fallback_count_for_test;
#[cfg(test)]
pub(in crate::codegen_ay) use codegen_ctx::set_chc_unhandled_call_count_for_test;
#[cfg(test)]
pub(in crate::codegen_ay) use codegen_ctx::set_type_sort_fallback_count_for_test;
pub(in crate::codegen_ay) use codegen_ctx::take_chc_diverging_call_drop_count;
pub(in crate::codegen_ay) use codegen_ctx::take_chc_fallback_counts;
pub(in crate::codegen_ay) use codegen_ctx::take_chc_offset_provenance_unresolved_count;
pub(in crate::codegen_ay) use codegen_ctx::take_chc_unhandled_call_count;
pub(in crate::codegen_ay) use codegen_ctx::take_drop_fallback_reasons_by_fn;
pub(in crate::codegen_ay) use codegen_ctx::take_error_blocked_fmt_count;
pub(in crate::codegen_ay) use codegen_ctx::take_fp_bitvector_encoding_by_fn;
pub(in crate::codegen_ay) use codegen_ctx::take_fp_bitvector_encoding_count;
pub(in crate::codegen_ay) use codegen_ctx::take_inferable_predicate_count;
pub(in crate::codegen_ay) use codegen_ctx::take_kani_mem_overapprox_by_fn;
pub(in crate::codegen_ay) use codegen_ctx::take_kani_mem_overapprox_count;
pub(in crate::codegen_ay) use codegen_ctx::take_offset_provenance_unresolved_by_fn;
pub(in crate::codegen_ay) use codegen_ctx::take_known_stdlib_unconstrained_count;
pub(in crate::codegen_ay) use codegen_ctx::take_ptr_metadata_unconstrained_by_fn;
pub(in crate::codegen_ay) use codegen_ctx::take_ptr_metadata_unconstrained_count;
pub(in crate::codegen_ay) use codegen_ctx::take_signedness_fallback_by_fn;
pub(in crate::codegen_ay) use codegen_ctx::take_sound_havoc_drop_by_fn;
pub(in crate::codegen_ay) use codegen_ctx::take_static_init_incomplete_by_fn;
pub(in crate::codegen_ay) use codegen_ctx::take_static_init_incomplete_count;
pub(in crate::codegen_ay) use codegen_ctx::take_store_dropped_by_fn;
pub(in crate::codegen_ay) use codegen_ctx::take_translation_drop_by_fn;
pub(in crate::codegen_ay) use codegen_ctx::take_translation_drop_site_reasons_by_fn;
pub(in crate::codegen_ay) use codegen_ctx::take_type_sort_fallback_by_fn;
pub(in crate::codegen_ay) use codegen_ctx::take_type_sort_fallback_count;
pub(in crate::codegen_ay) use codegen_ctx::take_unhandled_call_by_fn;
pub(in crate::codegen_ay) use codegen_ctx::types::ChcConfig;
use codegen_ctx::{AllocCallResult, CollectionCallResult, RefTarget, StubTranslateArgs};
pub(in crate::codegen_ay::chc) use heap::heap_state;
pub(in crate::codegen_ay::chc) use heap::heap_store_chains;
pub(in crate::codegen_ay::chc) use heap::memory_model;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(in crate::codegen_ay::chc) use heap::memory_type_key_tables;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use heap_state::ChcHeapState;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use rustc_public::mir::{ProjectionElem, Rvalue, StatementKind, TerminatorKind};
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use std::collections::HashMap;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use trust_mc_core::chc::{ChcQuery, ChcVc, VarDecl};
use trust_mc_core::chc::{RelationApp, Rule, RuleBody};
mod codegen_ctx_dead_locals;
pub(in crate::codegen_ay) use codegen_expr_assert::get_chc_assert_untranslatable_count;
pub(in crate::codegen_ay) use codegen_expr_assert::get_chc_assume_dropped_transition_count;
pub(in crate::codegen_ay) use codegen_expr_heap::get_chc_heap_check_unknown_layout_count;
pub(in crate::codegen_ay) use codegen_expr_heap::get_chc_heap_check_untranslatable_count;
use expr::codegen_expr;
use expr::codegen_expr_assert;
use expr::codegen_expr_heap;
// Statement codegen — now a proper directory module (Part of #3254)
// Re-export stmt::codegen_stmt_output items for codegen_ay consumers
#[allow(unused_imports)]
pub(in crate::codegen_ay) use stmt::codegen_stmt_output::mir_to_chc;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
pub(in crate::codegen_ay) use stmt::codegen_stmt_output::mir_to_chc_skip_tic;
pub(in crate::codegen_ay) use stmt::codegen_stmt_output::mir_to_chc_with_instance;
// Stub interception and translation — proper module boundary (Part of #3254)
mod stub_codegen;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use stub_codegen::stub_method_tables;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use stub_codegen::stubs_numeric_arg;
use stub_codegen::stubs_option_helpers;
use stub_codegen::stubs_util;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use stub_codegen::stubs_util_collections;
// Re-export for test access via super::common::* glob
pub(in crate::codegen_ay) use stub_codegen::stubs_iterators::get_chc_iterator_unsound_skip_count;
pub(in crate::codegen_ay) use stub_codegen::stubs_math::get_chc_bigint_unsound_skip_count;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use stub_method_tables::{
    BIGINT_METHOD_STUBS, BIGRATIONAL_METHOD_STUBS, MethodStubSpec, lookup_method_stub,
};
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use stubs_option_helpers::make_option_sort;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use stubs_option_helpers::option_empty_variant_name;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use stubs_option_helpers::option_payload_variant_name;
#[cfg(all(test, feature = "compiler-corpus-tests"))]
use stubs_option_helpers::option_value_sort;
// Post-codegen unused type array pruning (Part of #3184)
mod prune_arrays;
mod prune_relation_args;
pub(in crate::codegen_ay) use prune_relation_args::prune_dead_array_relation_args;
// Post-pruning constant-index array scalarization (Part of #4050)
mod scalarize_arrays;
pub(in crate::codegen_ay) use scalarize_arrays::scalarize_vc;
mod straightline_proof;
#[cfg(test)]
pub(in crate::codegen_ay) use straightline_proof::set_straightline_discharge_disabled;
pub(in crate::codegen_ay) use straightline_proof::{
    discharge_straightline_safety, straightline_discharge_disabled,
};

// Note: All diagnostic counters are consolidated in GLOBAL_COUNTERS
// (codegen_ctx::diagnostics::GlobalDiagnosticCounters, Part of #2906).
// Submodule get_*/take_* wrapper functions provide the public API and
// are re-exported into this module's namespace.

#[allow(dead_code)] // Call site wired in W1:4385 INCOMPLETE
pub(in crate::codegen_ay) fn get_recursive_unwind_count_for_fn(fn_name: &str) -> usize {
    codegen_ctx::globals::get_recursive_unwind_count_for_fn(fn_name)
}

#[allow(dead_code)] // Call site wired in W1:4385 INCOMPLETE
pub(in crate::codegen_ay) fn take_inferable_summary_names_by_fn()
-> std::collections::BTreeMap<String, std::collections::BTreeMap<String, usize>> {
    codegen_ctx::take_inferable_summary_names_by_fn()
}

// translate.rs — MIR-to-CHC entry point: translate(), MemPromoteAction, reset_chc_session_counters
mod translate;
pub(super) use translate::MemPromoteAction;
pub(in crate::codegen_ay) use translate::block_relation_apps_consistent;
pub(in crate::codegen_ay) use translate::block_relation_slot_names_consistent;
pub(in crate::codegen_ay) use translate::canonicalize_block_relation_apps;
pub(in crate::codegen_ay) use translate::fixup_relation_app_arities;
pub(in crate::codegen_ay) use translate::reset_chc_session_counters;
