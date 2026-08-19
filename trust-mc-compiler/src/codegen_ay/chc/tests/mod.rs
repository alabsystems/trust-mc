// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;
mod test_active_variant;
mod test_aggregate;
mod test_arithmetic;
mod test_codegen_types;
mod test_collections_bigint;
mod test_collections_btreemap;
mod test_collections_hashmap;
mod test_collections_result;
mod test_collections_vec;
mod test_core_vc;
mod test_coroutine_root_map;
mod test_ctx;

mod test_decl;
mod test_decl_ref_const_discriminant;
mod test_decl_ref_const_option_registration;
mod test_decl_ref_const_values;
mod test_decl_state_vars;
mod test_discriminant_aggregate;
mod test_discriminant_flattened_tuple;
mod test_discriminant_infer;
mod test_expr;
mod test_expr_assert;
mod test_expr_deref;
mod test_expr_env;
mod test_expr_env_len;
mod test_heap;
mod test_mem_promote;
mod test_projection;
mod test_projection_bv_update;
mod test_quantifier_closure_body;
mod test_quantifier_encoding;
mod test_signedness;
mod test_solver;
mod test_static_byte_backing;
mod test_stubs_math;
mod test_stubs_util;
mod test_types;

mod test_assert_encoding;
mod test_assert_encoding_fallback;
mod test_bigrational_translate;
mod test_bootstrap_arrays_tier3;
mod test_bootstrap_arrays_tier3_option_gaps;
mod test_bootstrap_pdr_frame;
mod test_bootstrap_xor_dpll_regressions;
mod test_btreeset;
mod test_call_alloc;
mod test_call_alloc_extra;
mod test_call_alloc_layout_helpers;
mod test_call_any_where_semantics;
mod test_call_any_where_vec_len_bridge;
mod test_call_array_intoiter_identity;
mod test_call_array_iter_noncopy;
mod test_call_block_on;
mod test_call_block_on_with_spawn;
mod test_call_block_on_with_spawn_loop_fuel;
mod test_call_block_on_with_spawn_round_robin;
mod test_call_block_on_with_spawn_task_slot;
mod test_call_cell;
mod test_call_cell_identity;
mod test_call_closure_float_predicate;
mod test_call_closure_vec_index_polarity;
mod test_call_closure_vec_len;
mod test_call_cmp;
mod test_call_cmp_fallback;
mod test_call_cmp_raw_expr_bv128;
mod test_call_cmp_string;
mod test_call_cmp_string_fallback;
mod test_call_coerce;
mod test_call_collections;
mod test_call_coroutine;
mod test_call_coroutine_iterator;
mod test_call_coroutine_iterator_native;
mod test_call_coroutine_reentry;
mod test_call_dispatch;
mod test_call_dispatch_collections;
mod test_call_dispatch_dyn_matchers;
mod test_call_dispatch_dyn_rc_codegen;
mod test_call_dispatch_dyn_vtable_capture;
mod test_call_dispatch_helpers;
mod test_call_dispatch_misc;
mod test_call_dispatch_misc_box_wrappers;
mod test_call_dispatch_misc_pointer_wrapper_common;
mod test_call_dispatch_misc_range_len;
mod test_call_dispatch_misc_rc_wrappers;
mod test_call_dispatch_option_ptr;
mod test_call_dispatch_overapprox;
mod test_call_dispatch_overapprox_kani_mem;
mod test_call_dispatch_rc_from_inner;
mod test_call_drop_terminator;
mod test_call_fn_ptr_function_symbols;
mod test_call_inline_alloc_metadata;
mod test_call_inline_field_map_scope;
mod test_call_iterator_adapter;
mod test_call_layout_semantic;
mod test_call_libc_mem;
mod test_call_mem_swap;
mod test_call_misc_intrinsics_fallback;
mod test_call_numeric;
mod test_call_option_result;
mod test_call_option_result_metadata;
mod test_call_primitive_clone;
mod test_call_primitive_ops_fallback;
mod test_call_ptr;
mod test_call_ptr_fallback;
mod test_call_ptr_offset_method_dispatch;
mod test_call_ptr_offset_sub;
mod test_call_range_contains;
mod test_call_raw_eq;
mod test_call_raw_ptr_as_ref;
mod test_call_rawvec_try;
mod test_call_referent_resolve;
mod test_call_result_mem;
mod test_call_simd_shuffle;
mod test_call_slice_fallback;
mod test_call_sound_fallback_invariants;
mod test_call_step_wrapping;
mod test_call_string;
mod test_call_string_nth;
mod test_call_string_raw_ptr;
mod test_call_string_utf8;
mod test_call_unsafe_cell_recovery;
mod test_call_vec;
mod test_call_vec_is_empty_fallback;
mod test_call_zero_valid;
mod test_edge_cases;
mod test_hashmap_translate;
mod test_hashset;
mod test_memory_addr;
mod test_memory_impl;
mod test_memory_layout;
mod test_memory_model;
mod test_memory_ptr_alias;
mod test_memory_type_keys;
mod test_option_helpers;
mod test_perf_patterns;
mod test_proptest;
mod test_ref_analysis;
mod test_rules;
mod test_stmt_arithmetic;
mod test_stmt_copy;
mod test_stmt_copy_harness;
mod test_stmt_copy_swap_diagnostics;
mod test_stmt_flatten;
mod test_stmt_ref_metadata;
mod test_stmt_rvalue;
mod test_stmt_rvalue_zst_repeat;
mod test_stmt_store;
mod test_stubs_alloc;
mod test_stubs_alloc_heap_ops;
mod test_stubs_alloc_layout_validity;
mod test_stubs_alloc_realloc_stale_ptr;
mod test_stubs_alloc_std_alloc_shapes;
mod test_stubs_collections;
mod test_stubs_dispatch;
mod test_stubs_impl;
mod test_stubs_intrinsics;
mod test_stubs_intrinsics_generic_fallback;
mod test_stubs_iterators;
mod test_stubs_iterators_fail_closed;

mod test_decl_ref_numeric;
mod test_hashset_translate;
mod test_rules_entry;
mod test_stmt_fallback_counter;
mod test_stmt_float_assertion_patterns;
mod test_stmt_float_copysign;
mod test_stmt_output;
mod test_stmt_store_array;
mod test_stmt_store_deref;
mod test_stmt_store_ref;
mod test_stubs_bigint;
mod test_stubs_iterators_hashmap;

mod test_call_closure;
mod test_call_closure_alias_updates;
mod test_call_dispatch_kani;
mod test_call_iterator_adapter_helpers;

mod test_ctx_dead_locals;
mod test_flattened_enum;
mod test_rules_helpers;
mod test_stmt_aggregate_adt;
mod test_stmt_aggregate_adt_wide_payload;
mod test_stmt_arithmetic_ops;
mod test_stmt_dispatch;
mod test_stubs_hashmap_detect;

mod test_decl_deref;
mod test_decl_static;
mod test_decl_static_aliasing;
mod test_decl_static_fat_ptr;
mod test_decl_static_mirror;
mod test_projection_extract;
mod test_ptr_translate;
mod test_stubs_iterators_vec;
mod test_types_adt;

mod test_alloc_id_overflow_callers;
mod test_call_kani;
mod test_heap_state;
mod test_inline_body;
mod test_quantifier_exists;
mod test_slice_ops_parity;
mod test_stmt_sort_mismatch;

mod test_assign_projection_fallback;
mod test_assign_projection_happy;
mod test_call_collections_hashmap_flatten;
mod test_call_hashmap_iter;
mod test_call_hashset_direct;
mod test_expr_constant;
mod test_expr_heap;
mod test_heap_regions;
mod test_heap_store_chains;
mod test_rules_emit;
mod test_stmt_aggregate;
mod test_stmt_store_decompose;
mod test_stub_method_tables;

mod test_memory_type_key_tables;
mod test_stubs_set_common;
mod test_stubs_util_collections;

mod test_call_bv_concat_extract;
mod test_call_iterator_adapter_dispatch;
mod test_call_iterator_adapter_range;
mod test_call_iterator_adapter_try_fold;
mod test_call_kani_model;
mod test_call_slice;
mod test_call_slice_zst_first;
mod test_call_vec_aggregate_wrappers;
mod test_call_vec_element;
mod test_call_vec_ops;
mod test_call_vec_ops_len;
mod test_call_vec_ops_resize;
mod test_check_disabling_config;
mod test_codegen_stmt;
mod test_ctx_globals;
mod test_ctx_types;
mod test_stmt_flatten_core;
mod test_stubs_collection_projection;

mod test_call_vec_ops_views;
mod test_expr_deref_field;
mod test_expr_deref_null_check;
mod test_stmt_store_ref_array;
mod test_stubs_numeric_arg;

mod test_call_kani_hooks;

mod test_ctx_clusters;
mod test_diagnostics_counters;
mod test_expr_detect;

mod test_stmt_float_casts;
mod test_stmt_mirror_invariant;
mod test_stmt_store_array_update;

mod test_expr_reconstruct;

mod test_large_step;

mod test_call_struct_clone;
mod test_call_struct_map_constructor;
mod test_kani_mem_ssa_ambiguous;
mod test_kani_mem_validity;

mod test_call_slice_range;
mod test_dispatch_ordering;
mod test_fragment_gen;
mod test_lemma_linearize;
mod test_math_intrinsic_dispatch;
mod test_math_intrinsic_folding;
mod test_transition_gen;

mod test_call_atomic;
mod test_call_atomic_cache_invalidation;
mod test_call_atomic_cxchg;
mod test_call_atomic_ptr;
mod test_call_enum_partial_eq;
mod test_call_fn_inline_alias_updates;
mod test_call_fn_inline_ptr_comparison_helpers;
mod test_call_fn_inline_rotate_helpers;
mod test_call_tuple_partial_eq;
mod test_call_union_find_bounded_find;
mod test_call_virtual;
mod test_call_virtual_inline;
mod test_call_virtual_inline_assume_switchint;
mod test_call_virtual_inline_box_dyn_drop;
mod test_call_virtual_inline_solver;
mod test_call_virtual_inline_vec_pop_alias_updates;
mod test_call_virtual_result_epilogue;
mod test_dyn_coercion;
mod test_lemma_hint;
mod test_prune_arrays;
mod test_rules_helpers_boxed_str;
mod test_template_check;
mod test_translation_drop_array_compare;
mod test_translation_drop_bootstrap_lra;
mod test_translation_drop_dyn_vtable;
mod test_translation_drop_flattened_array_struct;
mod test_translation_drop_newtype;

mod test_call_rc_dyn_value;
mod test_call_slice_is_empty;
mod test_decl_stub_internal_type_arrays;
mod test_deref_mem_trace;
mod test_dyn_tail_callee_layout;
mod test_float_rounding;
mod test_inline_rvalue_len;
mod test_stmt_flatten_copy_env;
mod test_stmt_ptr_metadata;
mod test_stmt_set_discriminant;
mod test_translation_drop_simd_arbitrary;

mod test_bootstrap_nia_tangent_plane;
mod test_bootstrap_packed_row_identity;
mod test_call_fn_inline_widen_fat_ptr;
mod test_dt_solver_gap_diagnostic;
mod test_dt_solver_gap_diagnostic_full;
mod test_sound_fallback_guard;
mod test_thread_local_current_head;

mod test_ay_version_guards;
mod test_call_coroutine_state;
mod test_call_coroutine_support;
mod test_call_struct_vec_constructor;
mod test_hashmap_contains_compiletest_parity;
mod test_smt_expr_encoding_path_guards;
mod test_smt_expr_regression_guards;
mod test_stmt_ptr_metadata_copy_trace;
mod test_stmt_ptr_metadata_mir_trace;

// All Mutex<()> counter serialization statics removed (Part of #2906):
// - COERCE_COUNTER_MUTEX — tests read per-ctx ChcDiagnostics
// - HEAP_COUNTER_MUTEX — tests read per-ctx ChcDiagnostics
// - STORE_DROP_COUNTER_MUTEX — no remaining references
// - TYPE_SORT_FALLBACK_MUTEX — tests use return-value assertions or per-ctx diagnostics
// - SIGNEDNESS_FALLBACK_MUTEX — tests use return-value assertions or snapshot-delta
// - FALLBACK_COUNTER_MUTEX — tests use per-function-name overwrite semantics
