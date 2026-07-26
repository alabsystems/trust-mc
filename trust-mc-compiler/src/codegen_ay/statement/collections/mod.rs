// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Collection semantic models for AY codegen.
//!
//! This module contains **semantic models** (NOT stubs) that translate Rust
//! standard library collection operations into SMT constraints for verification.
//! These are real implementations that encode collection semantics in AY's
//! theory solvers:
//!
//! - [`bigint`]: BigInt/BigUint operations modeled with SMT Int theory
//! - [`hashmap`]: HashMap/TrustMcMap modeled with SMT Array theory
//! - [`vec`]: Vec operations modeled with struct (ptr, len, cap)
//! - [`string`]: String operations modeled with struct (ptr, len, cap)
//! - [`btreeset`]: BTreeSet modeled with SMT Array theory (presence map)
//! - [`hashset`]: HashSet modeled with SMT Array theory (presence map)
//!
//! Part of #1354: Statement module refactoring.

mod bigint;
mod bigint_shift;
mod btreemap;
mod btreeset;
mod hashmap;
mod hashset;
mod iter;
mod iter_adapters;
mod iter_collection_next;
mod iter_filter_map_replay;
mod iter_flatten;
mod iter_helpers;
mod set_common;
mod string;
mod string_convert;
mod vec;
mod vec_fields;
mod vec_ops;
mod vec_view;

// Re-export iterator unsoundness counter accessor (#1929)
pub(in crate::codegen_ay) use iter::get_bmc_iterator_unsound_skip_count;
pub(in crate::codegen_ay::statement) use iter::take_bmc_iterator_unsound_skip_count;
pub(in crate::codegen_ay) use vec_fields::get_vec_field_fallback_count;
#[cfg(test)]
#[allow(unused_imports)]
pub(in crate::codegen_ay) use vec_fields::set_vec_field_fallback_count_for_test;
pub(in crate::codegen_ay) use vec_fields::take_vec_field_fallback_counter;
