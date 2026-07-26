// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC stub-codegen subsystem facade.
//!
//! This keeps the stub interception and translation family behind a real
//! `stub_codegen/` module boundary while preserving the historical
//! `super::...` imports used by the already-split leaf modules.

// Re-export codegen_ay-level items so leaf modules can keep `use super::...`.
pub(super) use super::super::{names, stubs, types};

// Re-export chc-level items so leaf modules can keep `use super::...`.
pub(super) use super::{
    AllocCallResult, ChcCtx, CollectionCallResult, StubTranslateArgs, UNDEF_COUNTER,
    UnknownProjectionPolicy, chc_call_context, chc_fresh_name, codegen_call_coerce,
    codegen_call_vtable_intrinsic, codegen_ctx, codegen_decl_flatten, codegen_expr_heap,
    codegen_expr_signedness, codegen_rules, codegen_types, collect_field_projections,
    declare_pending_var, pointer_step, push_pending_datatype_sort, record_type_sort_fallback,
    ty_signedness,
};

// --- Modules accessed from outside stub_codegen ---

pub(in crate::codegen_ay::chc) mod stub_method_tables;
pub(in crate::codegen_ay::chc) mod stubs_impl;
pub(in crate::codegen_ay::chc) mod stubs_iterators;
pub(in crate::codegen_ay::chc) mod stubs_math;
pub(in crate::codegen_ay::chc) mod stubs_numeric_arg;
pub(in crate::codegen_ay::chc) mod stubs_option_helpers;
pub(in crate::codegen_ay::chc) mod stubs_util_collections;

// --- Internal modules ---

mod layout_trace;
mod stubs_alloc;
mod stubs_alloc_dealloc;
mod stubs_alloc_heap_ops;
mod stubs_alloc_overlay_helpers;
mod stubs_alloc_realloc;
mod stubs_btreeset;
mod stubs_collection_projection;
mod stubs_hashmap_detect;
mod stubs_hashmap_resolve;
mod stubs_hashmap_sorts;
mod stubs_hashmap_translate;
mod stubs_hashset_translate;
mod stubs_iterators_hashmap;
mod stubs_iterators_vec;
mod stubs_iterators_vec_array;
mod stubs_math_bigint;
mod stubs_math_bigrational;
mod stubs_ptr_ops;
mod stubs_ptr_overflow;
mod stubs_set_common;
pub(in crate::codegen_ay::chc) mod stubs_util;
mod stubs_util_flattened_enum;
mod stubs_util_intrinsics;
mod stubs_util_pointer;
