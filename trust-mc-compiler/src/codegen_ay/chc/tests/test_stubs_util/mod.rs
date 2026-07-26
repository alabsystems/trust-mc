// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC stubs_util.rs — Option/Result predicates, unwrap variants,
//! combinators, pointer utilities, and collection predicates.
//!
//! Split from monolithic test_stubs_util.rs (2184 LOC) into thematic submodules.
//! Part of #2016, #2413.

mod collections_ptr;
mod kani_mem;
mod option_result;
mod primitive_cmp_vec;
mod ptr_ops;
mod raw_eq_pipeline;
mod std_types;
mod translate_edge_cases;
