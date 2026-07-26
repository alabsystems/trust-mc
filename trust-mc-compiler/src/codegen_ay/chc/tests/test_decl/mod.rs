// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test code: unwrap is acceptable for assertions
#![allow(clippy::unwrap_used)]

//! MIR-driven tests for CHC codegen_decl.rs declaration functions.
//!
//! Tests cover:
//! - declare_block_relations: creates relations for each basic block
//! - collect_state_vars: translates MIR locals to AY sorts
//! - declare_datatype_sorts: declares nested datatype sorts
//! - collect_nested_datatypes: recursively finds datatypes in sorts
//! - collect_numeric_ref_targets: identifies BigInt/BigRational references
//!
//! Part of #2016 (test coverage for codegen_ay/chc/codegen_decl.rs).

use super::common::*;

// ═══════════════════════════════════════════════════════════════════════
// Probe sources for declaration tests
// ═══════════════════════════════════════════════════════════════════════

pub(super) const DECL_PROBE_SOURCE: &str = r#"
pub fn simple_fn(x: u32) -> u32 {
    x + 1
}

pub fn multi_local(a: i32, b: u64, flag: bool) -> i32 {
    if flag { a } else { b as i32 }
}

pub fn branching_fn(x: u32) -> u32 {
    if x > 10 {
        x * 2
    } else if x > 5 {
        x + 3
    } else {
        1
    }
}

pub fn loop_fn(n: u32) -> u32 {
    let mut sum: u32 = 0;
    let mut i: u32 = 0;
    while i < n {
        sum = sum.wrapping_add(i);
        i = i.wrapping_add(1);
    }
    sum
}

pub fn tuple_fn(x: u32, y: bool) -> (u32, bool) {
    (x + 1, !y)
}

pub fn no_args_fn() -> u32 {
    42
}

pub struct Point {
    pub x: i32,
    pub y: i32,
}

pub fn struct_fn(p: Point) -> i32 {
    p.x + p.y
}
"#;

pub(super) const CLEANUP_ONLY_LOCAL_SOURCE: &str = r#"
#![allow(dead_code)]

struct CleanupMarker(u8);

impl Drop for CleanupMarker {
    fn drop(&mut self) {
        assert!(self.0 == 0);
    }
}

pub fn probe_cleanup_only_local(flag: bool) -> u8 {
    if flag {
        let marker = CleanupMarker(0);
        unimplemented!("panic after creating cleanup-only local");
    }
    1
}
"#;

mod block_relations;
mod deref_type_arrays;
mod flattening_option_tuple;
mod flattening_range;
mod flattening_result_and_fallback;
mod heap_region;
mod local_type_arrays;
mod nested_datatypes_and_vc;
mod state_vars;
mod static_and_collection;
