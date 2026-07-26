// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared naming helpers for SMT sorts and identifiers.
//!
//! Decomposed from monolith names.rs (621 prod LOC) into 6 submodules:
//! - `adt_names`: ADT sort name generation and sanitization
//! - `sort_constructors`: Field layout builders for collection and enum sorts
//! - `sort_type_names`: SMT sort name strings for Rust types
//! - `chc_state_names`: CHC encoding variable and memory array names
//! - `field_names`: ADT field, constructor, and collection accessor names
//! - `mir_symbolic_names`: MIR local names and discriminant/undef symbolics
//! - `sort_short_name`: Human-readable sort name generation
//!
//! Part of #2408, #2304.

mod adt_names;
mod chc_state_names;
mod field_names;
mod mir_symbolic_names;
mod sort_constructors;
mod sort_short_name;
mod sort_type_names;

// Re-export everything at the `names` module level to preserve existing import paths.
pub use adt_names::{adt_sort_name, sanitize_adt_suffix};
pub use chc_state_names::{
    addr_name, alloc_obj_size_name, collection_cap_var_name, collection_len_var_name,
    collection_present_var_name, mem_array_name, mem_array_name_pair, out_name, pointee_var_name,
    region_array_name, region_array_name_pair, region_key, state_var_addr_name, state_var_name,
    state_var_name_pair, static_var_name, store_coerce_name,
};
pub use field_names::{
    adt_struct_field_name, base_variant_field_name, cons_name, coroutine_direct_fields_name,
    coroutine_discriminant_field_name, coroutine_field_index, coroutine_field_name,
    coroutine_variant_field_name, discrim_name, indexed_field_name, len_name, meta_name,
    payload_name, resolve_ctor_name, tuple_field_name, variant_field_name,
};
pub use mir_symbolic_names::{
    alloc_discr_name, discr_sym_name, discriminant_name, local_name, undef_sym_name,
};
pub use sort_constructors::{
    RUST_STRING_CONS, RUST_STRING_SORT, btree_entry_fields, enum_sort, hashmap_iter_fields,
    hashset_iter_fields, index_range_sort, is_err_constructor, is_none_constructor,
    is_ok_constructor, is_some_constructor, layout_fields, option_constructors,
    option_none_constructor_name, option_some_constructor_name, option_value_field_name,
    rawvec_fields, scope_option_ctor, string_fields, struct_sort, vec_fields,
    vec_into_iter_bmc_fields, vec_into_iter_fields, vec_layout,
};
// These are used by trust_mc-compiler test code (chc/tests/test_collections_result.rs).
// Always exported so dependent crates can use them in their tests.
pub use sort_constructors::{result_err_constructor_name, result_ok_constructor_name};
pub use sort_short_name::sort_short_name;
pub use sort_type_names::{
    capture_field_name, closure_sort_name, coroutine_sort_name, dyn_sort_name,
    hashmap_into_iter_sort_name, hashset_into_iter_sort_name, into_iter_sort_name,
    option_sort_name, polymorphic_iter_sort_name, slice_sort_name, vec_into_iter_sort_name,
    vec_sort_name,
};
