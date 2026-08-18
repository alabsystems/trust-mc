// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC heap-model subsystem facade.
//!
//! This keeps the abstract-heap family behind a real `heap/` module boundary
//! while preserving the historical `super::...` imports used by the
//! already-split leaf modules.

pub(super) use super::super::{names, types};
pub(super) use super::{
    ChcCtx, UNDEF_COUNTER, codegen_ctx, codegen_types, declare_pending_var, dyn_coercion,
    record_type_sort_fallback,
};

mod heap_regions;
pub(in crate::codegen_ay::chc) mod heap_state;
mod heap_state_alloc;
pub(in crate::codegen_ay::chc) mod heap_store_chains;
mod memory_impl;
mod memory_impl_addr;
mod memory_impl_addr_normalize;
// The predicate moved next to the `Loc` tag it guards (`codegen_ay::provenance`)
// so the BMC statement path can make the same refusal; re-exported here so the
// existing `super::super::heap::is_value_widened_into_address` imports still resolve.
pub(in crate::codegen_ay::chc) use crate::codegen_ay::provenance::is_value_widened_into_address;
mod memory_impl_addr_stack;
mod memory_impl_layout;
mod memory_impl_layout_query;
mod memory_impl_ptr_alias;
mod memory_impl_region;
mod memory_impl_type_keys;
pub(in crate::codegen_ay::chc) mod memory_model;
pub(in crate::codegen_ay::chc) mod memory_type_key_tables;
