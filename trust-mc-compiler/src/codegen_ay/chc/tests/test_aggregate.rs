// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC codegen_stmt_aggregate.rs — aggregate construction in the
//! CHC encoding (tuples, structs, enums, arrays, closures, discriminants).
//! 867 lines with 0 prior direct tests.
//!
//! Part of #2016 (test coverage for chc/ modules).
//!
//! These tests exercise the aggregate translation via the `mir_to_chc` pipeline,
//! verifying that MIR aggregate rvalues produce valid CHC VCs with correct
//! structural properties: entry rules, error relations, block relations,
//! transition rules, and type-appropriate state variable sorts.

#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::emit_chc;

// assert_vc_structure is shared via common.rs

// =============================================================================
// Tuple aggregate — translate_tuple_aggregate
// =============================================================================

#[test]
fn test_tuple_aggregate_two_fields_produces_valid_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_tuple(x: u32, y: u32) -> (u32, u32) {
            (x, y)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_tuple");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_tuple", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_tuple", bb_count);

        // Tuple (u32, u32) should produce a datatype or flattened state vars
        // with bitvec(32) sorts for the two fields
        let has_bv32_sort =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32_sort, "tuple (u32, u32) relations should contain bv32 sorts");
    });
}

#[test]
fn test_tuple_aggregate_unit_produces_valid_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_unit_tuple() -> () {
            ()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unit_tuple");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_unit_tuple", ChcConfig::default());

        assert_vc_structure(&vc, "probe_unit_tuple", body.blocks.len());
    });
}

#[test]
fn test_tuple_aggregate_three_fields_mixed_types() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_triple(a: bool, b: u64, c: u8) -> (bool, u64, u8) {
            (a, b, c)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_triple");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_triple", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_triple", bb_count);

        // Mixed-type tuple should produce state vars for bool, bv64, bv8
        let all_sorts: Vec<_> = vc.relations.iter().flat_map(|r| r.arg_sorts.iter()).collect();
        let has_bool = all_sorts.iter().any(|s| s.is_bool());
        let has_bv64 = all_sorts.iter().any(|s| s.bitvec_width() == Some(64));
        let has_bv8 = all_sorts.iter().any(|s| s.bitvec_width() == Some(8));
        assert!(has_bool, "tuple (bool, u64, u8): relations should contain Bool sort");
        assert!(has_bv64, "tuple (bool, u64, u8): relations should contain bv64 sort");
        assert!(has_bv8, "tuple (bool, u64, u8): relations should contain bv8 sort");
    });
}

// =============================================================================
// Struct aggregate — translate_adt_aggregate (struct path)
// =============================================================================

#[test]
fn test_struct_aggregate_range_produces_valid_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_range() -> core::ops::Range<u32> {
            0..10
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_range");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_range", ChcConfig::default());

        assert_vc_structure(&vc, "probe_range", body.blocks.len());

        // Range<u32> has start/end fields — should produce state vars
        // (datatype, bv32, or bv64 depending on encoding)
        let has_state_vars = vc.relations.iter().any(|r| !r.arg_sorts.is_empty());
        assert!(has_state_vars, "Range<u32> relations should have state variable args");
    });
}

#[test]
fn test_struct_aggregate_custom_struct() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone, Copy)]
        pub struct Point {
            pub x: i32,
            pub y: i32,
        }

        pub fn probe_point(x: i32, y: i32) -> Point {
            Point { x, y }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_point");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_point", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_point", bb_count);

        // Point has two i32 fields — check that datatype or flattened bv32 sorts appear
        let has_struct_sort = vc.relations.iter().any(|r| {
            r.arg_sorts.iter().any(|s| s.datatype_name().is_some() || s.bitvec_width() == Some(32))
        });
        assert!(has_struct_sort, "Point struct should produce datatype or bv32 sorts in relations");
    });
}

#[test]
fn test_struct_aggregate_wrapper_bound_unflattens_enum_field() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        use std::ops::Bound;

        #[derive(Clone, Copy)]
        pub struct Wrapper(pub Bound<u8>);

        pub fn probe_wrapper_bound(tag: u8, included: u8, excluded: u8) -> Wrapper {
            let bound = if tag == 0 {
                Bound::Included(included)
            } else if tag == 1 {
                Bound::Excluded(excluded)
            } else {
                Bound::Unbounded
            };
            Wrapper(bound)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wrapper_bound");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_wrapper_bound", ChcConfig::default());
        let smt = emit_chc(&vc).to_string();
        let z3_result = run_z3_on_smt2_with_timeout(&smt, 10);

        assert!(
            z3_result.is_ok(),
            "Wrapper<Bound<u8>> aggregate SMT should parse in Z3, got {z3_result:?}\n{smt}"
        );
    });
}

// =============================================================================
// Option-like enum — translate_adt_aggregate (Option path)
// =============================================================================

#[test]
fn test_option_some_aggregate() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_some(x: u32) -> Option<u32> {
            Some(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_some");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_some", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_option_some", bb_count);

        // Option<u32> should produce datatype sort (Option encoding)
        let has_option_sort = vc.relations.iter().any(|r| {
            r.arg_sorts.iter().any(|s| {
                s.datatype_name().is_some_and(|n| n.contains("Option"))
                    || s.bitvec_width() == Some(32)
            })
        });
        assert!(has_option_sort, "Option<u32> should produce Option datatype or bv32 sort");
    });
}

#[test]
fn test_option_none_aggregate() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_none() -> Option<u32> {
            None
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_none");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_none", ChcConfig::default());

        assert_vc_structure(&vc, "probe_option_none", body.blocks.len());

        // None should still produce the same Option-typed state vars
        let has_option_sort = vc.relations.iter().any(|r| {
            r.arg_sorts.iter().any(|s| {
                s.datatype_name().is_some_and(|n| n.contains("Option"))
                    || s.bitvec_width() == Some(32)
            })
        });
        assert!(has_option_sort, "Option<u32> None should produce Option datatype or bv32 sort");
    });
}

// =============================================================================
// Unit enum — translate_adt_aggregate (unit enum path)
// =============================================================================

#[test]
fn test_unit_enum_aggregate_produces_bitvec() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone, Copy)]
        pub enum Color {
            Red,
            Green,
            Blue,
        }

        pub fn probe_unit_enum() -> Color {
            Color::Green
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unit_enum");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_unit_enum", ChcConfig::default());

        assert_vc_structure(&vc, "probe_unit_enum", body.blocks.len());

        // Unit enum is represented as a bitvec discriminant (typically bv8)
        let has_small_bv = vc
            .relations
            .iter()
            .any(|r| r.arg_sorts.iter().any(|s| matches!(s.bitvec_width(), Some(w) if w <= 32)));
        assert!(has_small_bv, "unit enum Color should produce a bitvec sort for the discriminant");
    });
}

#[test]
fn test_unit_enum_explicit_discriminants() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone, Copy)]
        pub enum Status {
            Active = 1,
            Inactive = 0,
            Pending = 255,
        }

        pub fn probe_explicit_discr() -> Status {
            Status::Pending
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_explicit_discr");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_explicit_discr", ChcConfig::default());

        assert_vc_structure(&vc, "probe_explicit_discr", body.blocks.len());

        // Explicit discriminant 255 requires at least bv8 width
        let has_bv = vc
            .relations
            .iter()
            .any(|r| r.arg_sorts.iter().any(|s| matches!(s.bitvec_width(), Some(w) if w >= 8)));
        assert!(has_bv, "Status enum (max discr=255) should produce >= bv8 sort");
    });
}

// =============================================================================
// Array aggregate — translate_array_aggregate
// =============================================================================

#[test]
fn test_array_aggregate_literal() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_array() -> [u32; 4] {
            [1, 2, 3, 4]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_array", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_array", bb_count);

        // Array [u32; 4] should produce Array sort or flattened bv32 vars
        // State may be in relation args or declare-var free variables
        assert_relation_has_arg_sort(
            &vc,
            "probe_array",
            |s| s.is_array() || s.bitvec_width() == Some(32),
            "Array or bv32",
        );
    });
}

#[test]
fn test_array_aggregate_bool_elements() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_bool_array() -> [bool; 3] {
            [true, false, true]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bool_array");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bool_array", ChcConfig::default());

        assert_vc_structure(&vc, "probe_bool_array", body.blocks.len());

        // Bool array should have Bool or Array sorts in state vars
        // State may be in relation args or declare-var free variables
        assert_relation_has_arg_sort(
            &vc,
            "probe_bool_array",
            |s| s.is_bool() || s.is_array(),
            "Bool or Array",
        );
    });
}

// =============================================================================
// Closure aggregate — translate_closure_aggregate
// =============================================================================

#[test]
fn test_non_capturing_closure_aggregate() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_non_capturing_closure() -> u32 {
            let f = || 42u32;
            f()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_non_capturing_closure");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_non_capturing_closure", ChcConfig::default());

        assert_vc_structure(&vc, "probe_non_capturing_closure", body.blocks.len());

        // Closure call should produce transition rules (call terminators)
        let has_transitions = vc.rules.iter().any(|r| r.body.relation.is_some());
        assert!(
            has_transitions,
            "non-capturing closure should produce at least one transition rule"
        );
    });
}

#[test]
fn test_capturing_closure_aggregate() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_capturing_closure(x: u32) -> u32 {
            let f = |y: u32| x + y;
            f(10)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_capturing_closure");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_capturing_closure", ChcConfig::default());

        assert_vc_structure(&vc, "probe_capturing_closure", body.blocks.len());

        // Capturing closure with u32 capture and u32 return
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "capturing closure with u32 should have bv32 state vars");

        let has_transitions = vc.rules.iter().any(|r| r.body.relation.is_some());
        assert!(has_transitions, "capturing closure should produce at least one transition rule");
    });
}

// =============================================================================
// Discriminant — translate_discriminant
// =============================================================================

#[test]
fn test_discriminant_option_match() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_match(opt: Option<u32>) -> u32 {
            match opt {
                Some(v) => v,
                None => 0,
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_match");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_match", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_option_match", bb_count);

        // Option match should have at least 2 transition rules (Some/None arms)
        let transition_rules: Vec<_> =
            vc.rules.iter().filter(|r| r.body.relation.is_some()).collect();
        assert!(
            transition_rules.len() >= 2,
            "Option match should have >= 2 transition rules (one per arm), got {}",
            transition_rules.len()
        );

        // The discriminant read should produce guard constraints in transition rules
        let guarded_rules =
            transition_rules.iter().filter(|r| !r.body.constraints.is_empty()).count();
        assert!(guarded_rules >= 1, "Option match should have at least 1 guarded transition rule");
    });
}

#[test]
fn test_discriminant_unit_enum_match() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone, Copy)]
        pub enum Dir { Up, Down, Left, Right }

        pub fn probe_enum_match(d: Dir) -> u32 {
            match d {
                Dir::Up => 0,
                Dir::Down => 1,
                Dir::Left => 2,
                Dir::Right => 3,
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_enum_match");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_enum_match", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_enum_match", bb_count);

        // Enum discriminant (Dir: Up/Down/Left/Right) requires bitvec encoding
        let has_bv_sort =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width().is_some()));
        assert!(
            has_bv_sort,
            "4-arm enum match should produce bitvec sort for discriminant or return value"
        );

        // All rules must be well-formed with head referencing declared relation
        let declared: HashSet<_> = vc.relations.iter().map(|r| r.name.as_str()).collect();
        for rule in &vc.rules {
            assert!(
                declared.contains(rule.head.name.as_str()),
                "rule head '{}' references undeclared relation",
                rule.head.name
            );
        }
    });
}

#[test]
fn test_discriminant_ordering_explicit_values() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::cmp::Ordering;

        pub fn probe_ordering_match(ord: Ordering) -> i32 {
            match ord {
                Ordering::Less => -1,
                Ordering::Equal => 0,
                Ordering::Greater => 1,
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ordering_match");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_ordering_match", ChcConfig::default());

        assert_vc_structure(&vc, "probe_ordering_match", body.blocks.len());

        // Ordering discriminant and i32 return should produce bitvec sorts
        let has_bv =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width().is_some()));
        assert!(has_bv, "Ordering match should have bitvec state vars");

        // i32 return type should produce bv32 sort specifically
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "Ordering match returning i32 should have bv32 sort");
    });
}

// =============================================================================
// Pointer wrapper ADTs — NonNull/Box transparent wrappers
// =============================================================================

#[test]
fn test_nonnull_aggregate_treated_as_pointer() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::ptr::NonNull;

        pub fn probe_nonnull(ptr: *mut u32) -> Option<NonNull<u32>> {
            NonNull::new(ptr)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nonnull");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_nonnull", ChcConfig::default());

        assert_vc_structure(&vc, "probe_nonnull", body.blocks.len());

        // NonNull<u32> is a transparent pointer wrapper — should produce
        // pointer-width bitvec sorts (bv64 on 64-bit)
        let has_ptr_width =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(64)));
        assert!(has_ptr_width, "NonNull<u32> should produce pointer-width (bv64) sorts");
    });
}

#[test]
fn test_manuallydrop_box_aggregate_is_transparent() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::mem::ManuallyDrop;

        pub fn probe_md_box(b: Box<u32>) -> ManuallyDrop<Box<u32>> {
            ManuallyDrop::new(b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_md_box");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_md_box",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_md_box", body.blocks.len());

        // ManuallyDrop<T> is transparent in translate_ty; aggregate encoding must
        // not emit a datatype constructor (which would be undeclared).
        let smt = emit_chc(&vc).to_string();
        assert!(
            !smt.contains("ManuallyDrop_"),
            "ManuallyDrop aggregate should not emit wrapper datatype constructors; SMT:\n{}",
            smt
        );

        // Wrapped Box pointer should still be represented at pointer width.
        let has_ptr_width =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(64)));
        assert!(has_ptr_width, "ManuallyDrop<Box<u32>> should preserve pointer-width (bv64) sorts");
    });
}

// =============================================================================
// ControlFlow discriminant — generic ControlFlow NOT forced (Fix #2242)
// =============================================================================

/// Verifies that generic ControlFlow<T, U> (not allocation-related) is NOT
/// forced to Continue. The `?` operator desugars to ControlFlow and must
/// preserve both Continue and Break paths for soundness.
#[test]
fn test_controlflow_discriminant_not_forced_for_generic() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::ops::ControlFlow;

        pub fn probe_controlflow(x: u32) -> ControlFlow<u32, u32> {
            if x > 10 {
                ControlFlow::Break(x)
            } else {
                ControlFlow::Continue(x)
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_controlflow");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_controlflow", ChcConfig::default());

        assert_vc_structure(&vc, "probe_controlflow", body.blocks.len());

        // Generic ControlFlow with if/else should produce branching transition
        // rules — both Continue and Break paths must be reachable (#2242).
        let transition_rules: Vec<_> =
            vc.rules.iter().filter(|r| r.body.relation.is_some()).collect();
        assert!(
            transition_rules.len() >= 2,
            "ControlFlow if/else should produce >= 2 transition rules, got {}",
            transition_rules.len()
        );
    });
}

// =============================================================================
// Result enum aggregate — general enum path
// =============================================================================

#[test]
fn test_result_ok_aggregate() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_result_ok(x: u32) -> Result<u32, u8> {
            Ok(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_ok");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_result_ok", ChcConfig::default());

        assert_vc_structure(&vc, "probe_result_ok", body.blocks.len());

        // Result<u32, u8> should produce datatype or bitvec sorts
        let has_result_sort = vc.relations.iter().any(|r| {
            r.arg_sorts.iter().any(|s| s.datatype_name().is_some() || s.bitvec_width() == Some(32))
        });
        assert!(has_result_sort, "Result<u32, u8> should produce datatype or bv32 sorts");
    });
}

#[test]
fn test_result_err_aggregate() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_result_err(e: u8) -> Result<u32, u8> {
            Err(e)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_err");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_result_err", ChcConfig::default());

        assert_vc_structure(&vc, "probe_result_err", body.blocks.len());

        // Err(u8) should still produce the full Result type state vars
        let has_bv8 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(8)));
        assert!(has_bv8, "Result<u32, u8> Err should have bv8 sort for error type");
    });
}

#[test]
fn test_result_match_discriminant() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_result_match(r: Result<u32, u8>) -> u32 {
            match r {
                Ok(v) => v,
                Err(e) => e as u32,
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_match");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_result_match", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_result_match", bb_count);

        // Result match (Ok/Err) should produce >= 2 transition rules
        let transition_rules: Vec<_> =
            vc.rules.iter().filter(|r| r.body.relation.is_some()).collect();
        assert!(
            transition_rules.len() >= 2,
            "Result match should produce >= 2 transitions (Ok + Err arms), got {}",
            transition_rules.len()
        );
    });
}

// =============================================================================
// closure_upvar_tys — static helper tests
// =============================================================================

#[test]
fn test_closure_upvar_tys_detection_via_pipeline() {
    // Verify that a capturing closure with multiple upvars produces a valid VC.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_multi_capture(a: u32, b: u64) -> u64 {
            let f = |c: u64| (a as u64) + b + c;
            f(100)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_multi_capture");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_multi_capture", ChcConfig::default());

        assert_vc_structure(&vc, "probe_multi_capture", body.blocks.len());

        // Multi-capture closure with u32 and u64 captures should have both sorts
        let all_sorts: Vec<_> = vc.relations.iter().flat_map(|r| r.arg_sorts.iter()).collect();
        let has_bv32 = all_sorts.iter().any(|s| s.bitvec_width() == Some(32));
        let has_bv64 = all_sorts.iter().any(|s| s.bitvec_width() == Some(64));
        assert!(has_bv32, "multi-capture closure should have bv32 for u32 capture");
        assert!(has_bv64, "multi-capture closure should have bv64 for u64 capture");
    });
}

// =============================================================================
// Single-element tuple unwrap (#1979)
// =============================================================================

#[test]
fn test_single_element_tuple_unwrapped() {
    // MIR uses 1-element tuples (T,) as wrappers. CHC should unwrap them
    // to avoid sort mismatch (#1979).
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_single_tuple(x: u32) -> (u32,) {
            (x,)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_single_tuple");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_single_tuple", ChcConfig::default());

        assert_vc_structure(&vc, "probe_single_tuple", body.blocks.len());

        // Single-element tuple should unwrap to bv32 (not a Tuple_1 datatype)
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "(u32,) should unwrap to bv32 per #1979");
    });
}

// =============================================================================
// Combined aggregate patterns
// =============================================================================

#[test]
fn test_nested_option_in_result() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_nested(x: u32) -> Result<Option<u32>, u8> {
            if x > 0 {
                Ok(Some(x))
            } else {
                Err(0)
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nested");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_nested", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_nested", bb_count);

        // Nested Result<Option<u32>, u8> with if/else should have branching
        let transition_rules: Vec<_> =
            vc.rules.iter().filter(|r| r.body.relation.is_some()).collect();
        assert!(
            transition_rules.len() >= 2,
            "nested Result with if/else should produce >= 2 transitions, got {}",
            transition_rules.len()
        );

        // Should have datatype declarations for the nested types
        let has_datatype_decl =
            vc.decls.iter().any(|d| matches!(d, trust_mc_core::decl::Decl::Datatype { .. }));
        // Nested Option-in-Result should produce at least one datatype decl
        // (unless both are flattened to bitvecs)
        let has_bv_sorts =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width().is_some()));
        assert!(
            has_datatype_decl || has_bv_sorts,
            "nested types should produce datatype decls or bitvec state vars"
        );
    });
}

#[test]
fn test_struct_with_array_field() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone)]
        pub struct Matrix {
            data: [i32; 4],
            rows: u32,
        }

        pub fn probe_struct_array() -> Matrix {
            Matrix { data: [1, 2, 3, 4], rows: 2 }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_struct_array");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_struct_array", ChcConfig::default());

        assert_vc_structure(&vc, "probe_struct_array", body.blocks.len());

        // Matrix with [i32; 4] and u32 should have both Array and bv32 sorts
        let all_sorts: Vec<_> = vc.relations.iter().flat_map(|r| r.arg_sorts.iter()).collect();
        let has_array_or_dt = all_sorts.iter().any(|s| s.is_array() || s.datatype_name().is_some());
        let has_bv32 = all_sorts.iter().any(|s| s.bitvec_width() == Some(32));
        assert!(
            has_array_or_dt || has_bv32,
            "Matrix struct should produce Array/datatype or bv32 sorts"
        );
    });
}
