// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! AY Backend for trust_mc Verification.

mod abstraction_boundary;
/// Guard (b) of the `--c-lib` front-end: check a C prototype against the Rust
/// `extern` declaration before any C body may speak for a call.
mod c_ffi_check;
pub(crate) mod chc;
mod codegen_file_io;
mod codegen_function;
mod codegen_results;
mod compiler_interface;
mod context;
mod coroutine_layout;
pub(crate) mod diagnostics;
mod emitter;
// The per-datatype field-role table (`docs/addr-vs-value-conversion-queue.md`
// §4 item 7): the declaration records which fields hold ADDRESSES, from the MIR
// type it was built out of, so consumers read the fact instead of guessing it
// off the field's sort.
mod field_roles;
mod float_arithmetic;
mod float_arithmetic_pure;
mod float_compare;
#[allow(dead_code)] // BMC-path functions not yet wired into dispatch
mod float_math_ops;
mod float_range_check;
mod foreign_defs;
mod loop_invariant;
mod obligation_free_walk;
mod loop_unroll;
mod names;
mod option_like_eq;
// Wave 1 of the address-vs-value conversion converted its first entry points;
// the remaining accessors stay allowed until the later waves consume them.
#[allow(dead_code)]
mod provenance;
// Wave 3 of the address-vs-value conversion: the fat-pointer decoder. A wide
// pointer is an address AND a value packed together, and the packed form is
// bit-identical to a widened thin one — `Val`/`Loc` alone cannot express that,
// so `PtrRepr` decodes it structurally, once.
mod ptr_repr;
mod shadow_mem;
mod shared;
mod statement;
mod store_coercion;
// stubs extracted to trust_mc-codegen-stubs crate (Part of #2997).
// Re-export as module alias to preserve all existing import paths.
pub(crate) use trust_mc_codegen_stubs as stubs;
mod target_config;
mod type_depth_guard;
mod types;
mod unsoundness_fields;
mod unsoundness_fields_collectors;
mod unsoundness_per_harness;

#[cfg(test)]
#[allow(clippy::panic)]
mod emitter_tests;

pub(crate) use compiler_interface::AYCodegenBackend;
pub(crate) use unsoundness_fields::collect_unsoundness_fields;

// Internal APIs used within the crate for MIR codegen
pub(in crate::codegen_ay) use emitter::emit_bmc;
pub(in crate::codegen_ay) use emitter::emit_chc;

// Programmatic CHC emission APIs for callers that already have a trust_mc_core::ChcVc.
#[allow(dead_code)]
pub(crate) fn emit_chc_program(vc: &trust_mc_core::ChcVc) -> ay_bindings::AYProgram {
    emitter::emit_chc_program(vc)
}

#[allow(dead_code)]
pub(crate) fn emit_chc_smt2(vc: &trust_mc_core::ChcVc) -> String {
    emitter::emit_chc_smt2(vc)
}

// Iterator unsoundness counter accessors (#1929)
// These are used by compiler_interface to populate metadata.
pub(in crate::codegen_ay) use chc::get_chc_iterator_unsound_skip_count;
pub(in crate::codegen_ay) use statement::get_bmc_iterator_unsound_skip_count;
pub(in crate::codegen_ay) use statement::take_constant_zero_fallback_count;

#[cfg(test)]
pub(in crate::codegen_ay) use statement::set_constant_zero_fallback_count_for_test;

// BigInt unsoundness counter accessors (#1989)
// These are used by compiler_interface to populate metadata.
pub(in crate::codegen_ay) use chc::get_chc_bigint_unsound_skip_count;

// Coercion drop counter accessors (#2235)
// Used by metadata/reporting to surface silently dropped destination constraints.
pub(in crate::codegen_ay) use chc::take_chc_coerce_eq_dropped_constraint_count;
pub(in crate::codegen_ay) use chc::take_chc_coerce_eq_dropped_constraint_counts_by_fn;

// Assume dropped transition counter accessor (#2239)
// Used by metadata/reporting to surface dropped kani::assume transitions.
pub(in crate::codegen_ay) use chc::get_chc_assume_dropped_transition_count;

// Assert untranslatable counter accessor (#2251)
// Used by metadata/reporting to surface conservative error rules for untranslatable assertions.
pub(in crate::codegen_ay) use chc::get_chc_assert_untranslatable_count;

// Store dropped transition counter accessor (#2236)
// Used by metadata/reporting to surface dropped store transitions.
pub(in crate::codegen_ay) use chc::get_chc_store_dropped_transition_count;

// CHC type/size fallback metric accessor (#2234)
// Used by metadata/reporting to emit per-harness fallback counts.
pub(in crate::codegen_ay) use chc::take_chc_fallback_counts;

// Heap check untranslatable counter accessor (#2314)
// Used by metadata/reporting to surface conservative heap safety error rules.
pub(in crate::codegen_ay) use chc::get_chc_heap_check_untranslatable_count;

// Heap check unknown layout counter accessor (#2501)
// Used by metadata/reporting to surface fail-closed heap checks for unknown-layout types.
pub(in crate::codegen_ay) use chc::get_chc_heap_check_unknown_layout_count;

// Unhandled call counter accessor (#2573)
// Used by metadata/reporting to surface over-approximated call returns.
pub(in crate::codegen_ay) use chc::take_chc_unhandled_call_count;

// Diverging call drop counter accessor (#3164)
// Used by metadata/reporting to surface silently dropped diverging calls.
pub(in crate::codegen_ay) use chc::take_chc_diverging_call_drop_count;

// Offset-provenance-unresolved counter accessor: surfaces pointer-offset/deref
// alloc-bound checks skipped on symbolic obj_id (fail-open) so they demote.
pub(in crate::codegen_ay) use chc::take_chc_offset_provenance_unresolved_count;

// Dispatch sub-classification counters (#3379)
// Used by metadata/reporting for CTREX recovery roadmapping.
pub(in crate::codegen_ay) use chc::get_inferable_predicate_count;
pub(in crate::codegen_ay) use chc::take_error_blocked_fmt_count;
pub(in crate::codegen_ay) use chc::take_inferable_predicate_count;
pub(in crate::codegen_ay) use chc::take_known_stdlib_unconstrained_count;

// kani::mem over-approximation counter accessor (#3165)
// Used by metadata/reporting to surface memory safety predicates approximated as true.
pub(in crate::codegen_ay) use chc::take_kani_mem_overapprox_by_fn;
pub(in crate::codegen_ay) use chc::take_kani_mem_overapprox_count;
pub(in crate::codegen_ay) use chc::take_offset_provenance_unresolved_by_fn;

// #3447 CTREX diagnostic counters: PtrMetadata, static init, FP-as-BV, aggregate, stub
pub(in crate::codegen_ay) use chc::get_aggregate_encoding_gap_count;
pub(in crate::codegen_ay) use chc::get_fp_bitvector_encoding_count;
pub(in crate::codegen_ay) use chc::get_ptr_metadata_unconstrained_count;
pub(in crate::codegen_ay) use chc::get_rounding_assertion_bypass_count;
pub(in crate::codegen_ay) use chc::get_static_init_incomplete_count;
pub(in crate::codegen_ay) use chc::get_stub_approximation_count;
pub(in crate::codegen_ay) use chc::take_aggregate_encoding_gap_by_fn;
pub(in crate::codegen_ay) use chc::take_aggregate_encoding_gap_count;
pub(in crate::codegen_ay) use chc::take_aggregate_gap_reasons_by_fn;
pub(in crate::codegen_ay) use chc::take_fp_bitvector_encoding_by_fn;
pub(in crate::codegen_ay) use chc::take_fp_bitvector_encoding_count;
pub(in crate::codegen_ay) use chc::take_ptr_metadata_unconstrained_by_fn;
pub(in crate::codegen_ay) use chc::take_ptr_metadata_unconstrained_count;
pub(in crate::codegen_ay) use chc::take_rounding_assertion_bypass_count;
pub(in crate::codegen_ay) use chc::take_static_init_incomplete_by_fn;
pub(in crate::codegen_ay) use chc::take_static_init_incomplete_count;
pub(in crate::codegen_ay) use chc::take_stub_approximation_by_fn;
pub(in crate::codegen_ay) use chc::take_stub_approximation_count;

// Type-sort fallback counter accessor (#2705)
// Used by metadata/reporting to surface hardcoded sort fallbacks.
pub(in crate::codegen_ay) use chc::take_type_sort_fallback_count;
pub(in crate::codegen_ay) use shared::take_signedness_fallback_count;
// Per-function signedness/type-sort fallback maps (Part of #2959)
pub(in crate::codegen_ay) use chc::take_signedness_fallback_by_fn;
// Per-function store-dropped-transition map (Part of #2966)
pub(in crate::codegen_ay) use chc::take_store_dropped_by_fn;
// Per-function unhandled-call and translation-drop maps (Part of #2966)
pub(in crate::codegen_ay) use chc::take_drop_fallback_reasons_by_fn;
pub(in crate::codegen_ay) use chc::take_sound_havoc_drop_by_fn;
pub(in crate::codegen_ay) use chc::take_translation_drop_by_fn;
pub(in crate::codegen_ay) use chc::take_translation_drop_site_reasons_by_fn;
pub(in crate::codegen_ay) use chc::take_type_sort_fallback_by_fn;
pub(in crate::codegen_ay) use chc::take_unhandled_call_by_fn;

// CHC translation-drop counters (#2770)
// Used by metadata/reporting to surface immutable/static None-drop paths.
pub(in crate::codegen_ay) use chc::take_constant_translation_drop_count;
pub(in crate::codegen_ay) use chc::take_place_translation_drop_count;
pub(in crate::codegen_ay) use chc::take_unsupported_field_projection_count;
pub(in crate::codegen_ay) use shared::take_into_option_dropped_count;

// Vec field fallback counter accessor (#2733)
// Used by metadata/reporting to surface Vec non-datatype symbolic fallbacks.
pub(in crate::codegen_ay) use statement::take_vec_field_fallback_counter;

// Dispatch counter accessors (#2597 Phase 3)
// Used by metadata/reporting to surface pre-inlined collection and stdlib fallbacks.
pub(in crate::codegen_ay) use statement::take_abstracted_fallback_count;
pub(in crate::codegen_ay) use statement::take_internal_workaround_count;

// Pointee synthesis fallback counter accessor (#3013)
// Used by metadata/reporting to surface unconstrained symbolic pointee creation.
pub(in crate::codegen_ay) use statement::take_pointee_synthesis_fallback_count;

// Unsupported construct fallback counter accessor (#3017)
// Used by metadata/reporting to surface proceed-with-fallback unsupported constructs.
pub(in crate::codegen_ay) use context::take_unsupported_construct_fallback_count;

// Unconstrained assignment counter accessors (#3192)
// Distinct from unsupported_construct_fallback — tracks when codegen_rvalue returns None
// and the LHS SSA variable is left unconstrained.
pub(in crate::codegen_ay) use context::get_unconstrained_assignment_count;
pub(in crate::codegen_ay) use context::take_unconstrained_assignment_count;

// Non-destructive read accessors for per-harness snapshot deltas (Part of #3080).
// These allow compiler_interface to snapshot counter values before/after each harness
// codegen to compute per-harness demotion counts without draining the counters.
pub(in crate::codegen_ay) use context::get_unsupported_construct_fallback_count;
pub(in crate::codegen_ay) use shared::get_into_option_dropped_count;
pub(in crate::codegen_ay) use statement::get_abstracted_fallback_count;
pub(in crate::codegen_ay) use statement::get_constant_zero_fallback_count;
pub(in crate::codegen_ay) use statement::get_internal_workaround_count;
pub(in crate::codegen_ay) use statement::get_pointee_synthesis_fallback_count;
pub(in crate::codegen_ay) use statement::get_sort_harmonize_fresh_var_count;
pub(in crate::codegen_ay) use statement::get_vec_field_fallback_count;
pub(in crate::codegen_ay) use statement::take_sort_harmonize_fresh_var_count;

// Test setters for statement-level unsoundness counters (Part of #3369)
#[cfg(test)]
#[allow(unused_imports)]
pub(in crate::codegen_ay) use context::set_unconstrained_assignment_count_for_test;
#[cfg(test)]
#[allow(unused_imports)]
pub(in crate::codegen_ay) use context::set_unsupported_construct_fallback_count_for_test;
#[cfg(test)]
#[allow(unused_imports)]
pub(in crate::codegen_ay) use statement::set_abstracted_fallback_count_for_test;
#[cfg(test)]
#[allow(unused_imports)]
pub(in crate::codegen_ay) use statement::set_internal_workaround_count_for_test;
#[cfg(test)]
#[allow(unused_imports)]
pub(in crate::codegen_ay) use statement::set_pointee_synthesis_fallback_count_for_test;
#[cfg(test)]
#[allow(unused_imports)]
pub(in crate::codegen_ay) use statement::set_sort_harmonize_fresh_var_count_for_test;
#[cfg(test)]
#[allow(unused_imports)]
pub(in crate::codegen_ay) use statement::set_vec_field_fallback_count_for_test;
#[cfg(test)]
#[allow(unused_imports)]
pub(in crate::codegen_ay) use store_coercion::set_bmc_store_coercion_fallback_count_for_test;

#[cfg(test)]
mod test_fixtures;
#[cfg(test)]
mod test_types;
#[cfg(test)]
mod test_types_enum;
