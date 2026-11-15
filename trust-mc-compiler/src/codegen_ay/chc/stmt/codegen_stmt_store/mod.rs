// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Store helpers for CHC block statement encoding.
//!
//! Handles Mem-level deref stores (`*ptr = value`), sort coercion for array
//! store values, and local array updates when writing through references.
//!
//! ## Submodules
//!
//! - `counter`: dropped-store transition counter (#2236)
//! - `coerce`: sort coercion for array store values (#2244)
//! - `deref_elem_store`: element store through a pointer to an array with no
//!   register referent (`(*p)[i] = v`)
//! - `deref_mem`: Mem-level deref store handler (#905, #1100)
//! - `pointer_field_escape`: whether a pointer field's bytes may change
//!   without a typed pointer store (`pointer_field_value_source`)
//! - `static_image`: a `static mut` store reaches the static's memory image
//! - `untyped_view_scan`: memory rewritten or read under a type it was not
//!   written as (pointer bytes rewritten untyped, a static read under an
//!   unseeded view)
//! - `deref_mem_mirror`: mirror-store helpers for scalar/datatype/flattened (#2278)
//! - `deref_mem_mirror_struct`: exact mirror of a Field path into a flattened
//!   struct owner, and the ref_target join check every mirror arm needs
//! - `array_update`: local array update via ref_targets (#1957)
//! - `struct_decompose`: per-field struct store decomposition (#1739)
//! - `store_pointer_offset`: the constant byte offset of a store pointer from
//!   its ref target's referent, read off the pointer's definition chain
//!
//! Array element stores are handled by `StmtStoreArray` in `codegen_stmt_store_array.rs`.
//! Reg-level ref_target stores are handled by `StmtStoreRef` in `codegen_stmt_store_ref.rs`.

mod array_update;
mod coerce;
pub(in crate::codegen_ay) mod counter;
pub(in crate::codegen_ay::chc) mod deref_elem_store;
pub(in crate::codegen_ay::chc) mod deref_mem;
mod deref_mem_mirror;
pub(in crate::codegen_ay::chc) use deref_mem_mirror::{OUT_OF_BOUNDS_MESSAGE, RefStoreReinterpretation};
mod deref_mem_mirror_struct;
mod store_pointer_offset;
mod pointer_field_escape;
mod static_image;
mod untyped_view_flow;
mod untyped_view_scan;
pub(in crate::codegen_ay::chc) use untyped_view_scan::model_object_literal_lane;
mod struct_decompose;

pub(in crate::codegen_ay) use counter::get_chc_store_dropped_transition_count;
