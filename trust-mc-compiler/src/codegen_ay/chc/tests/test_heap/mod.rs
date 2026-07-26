// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test code: unwrap is acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::names::RUST_STRING_SORT;

mod address_and_naming;
mod alloc_preconditions_and_regions;
mod allocator_intrinsics_core;
mod allocator_intrinsics_semantics;
mod error_rule_fallbacks;
mod heap_access_checks;
mod heap_state_accumulation;
mod memory_impl_edges;
mod phase2_heap_model;
