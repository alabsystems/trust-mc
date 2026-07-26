// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Sort-polymorphic helpers for CHC numeric sorts — re-exported from the
//! library-lane implementation (`crate::chc_auto_hints`), which is the single
//! source shared with the native typed-CHC runner. See that module's doc.
//!
//! Part of #2875: BV-aware detection.

#[allow(unused_imports)]
pub(super) use crate::chc_auto_hints::{
    is_add_op, is_comparison_op, is_const_one, is_le_direction, is_numeric_sort, is_sub_op,
    make_ge, make_le, make_zero,
};
