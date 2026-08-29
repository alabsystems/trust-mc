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
//! - `deref_mem`: Mem-level deref store handler (#905, #1100)
//! - `deref_mem_mirror`: mirror-store helpers for scalar/datatype/flattened (#2278)
//! - `array_update`: local array update via ref_targets (#1957)
//! - `struct_decompose`: per-field struct store decomposition (#1739)
//!
//! Array element stores are handled by `StmtStoreArray` in `codegen_stmt_store_array.rs`.
//! Reg-level ref_target stores are handled by `StmtStoreRef` in `codegen_stmt_store_ref.rs`.

mod array_update;
mod coerce;
pub(in crate::codegen_ay) mod counter;
pub(in crate::codegen_ay::chc) mod deref_mem;
mod deref_mem_mirror;
mod struct_decompose;

pub(in crate::codegen_ay) use counter::get_chc_store_dropped_transition_count;
