// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for SSA signedness and naming helpers.
//!
//! Part of #2016 (coverage for `statement/ssa.rs` helpers on real MIR locals).
//!
//! ## Coverage map
//!
//! | Production function           | Tests                                             |
//! |-------------------------------|----------------------------------------------------|
//! | `ty_signedness`               | signedness_helpers, ty_signedness_diverse_types    |
//! | `operand_signedness`          | signedness_helpers, ty_signedness_diverse_types    |
//! | `is_signed_integer_op`        | signedness_helpers, is_signed_integer_op_*          |
//! | `signedness_from_base_name`   | signedness_helpers, signedness_from_base_name_*     |
//! | `ssa_base_name`               | projection_base_helpers, base_name_field_deref_*    |
//! | `ssa_base_name_for_prefix`    | projection_base_helpers, prefix_*                   |
//! | `ssa_name`                    | ssa_name_via_place_*                                |
//! | `ssa_name_from_base`          | projection_base_helpers, cross_variable_*           |
//! | `next_ssa_version`            | (tested indirectly through ssa_name_from_base)      |

use super::*;

// --- Probe sources ---

/// Basic probe: i32, u32, bool, *const i32 parameters.
const SSA_PROBE_SOURCE: &str = r#"
pub fn ssa_probe(si: i32, ui: u32, flag: bool, ptr: *const i32) -> i32 {
    let mut x = si;
    if flag {
        x = x + si;
    }
    if !ptr.is_null() {
        unsafe { x = *ptr; }
    }
    x + ui as i32
}
"#;

/// Diverse-type probe: tests ty_signedness across all integer widths,
/// usize/isize, references, and non-integer types that should return None.
const DIVERSE_TYPE_SOURCE: &str = r#"
pub fn diverse_types(
    a_u8: u8,
    b_i8: i8,
    c_u16: u16,
    d_i16: i16,
    e_u64: u64,
    f_i64: i64,
    g_usize: usize,
    h_isize: isize,
    i_f32: f32,
    j_ref_i32: &i32,
    k_ref_u32: &u32,
) -> u8 {
    let _ = (b_i8, d_i16, f_i64, h_isize, i_f32, j_ref_i32, k_ref_u32);
    a_u8.wrapping_add(c_u16 as u8).wrapping_add(e_u64 as u8).wrapping_add(g_usize as u8)
}
"#;

/// Pointer-wrapper and tuple probe: exercises Adt and Tuple arms in ty_signedness.
/// Part of #2954: verify Box<i32>/Box<u32>/tuple signedness in BMC.
const POINTER_WRAPPER_TUPLE_SOURCE: &str = r#"
pub fn pointer_wrapper_tuple_probe(
    boxed_signed: Box<i32>,
    boxed_unsigned: Box<u32>,
    tuple_signed_first: (i32, bool),
    tuple_unsigned_first: (u64, i32),
) -> i32 {
    let _ = (&boxed_unsigned, &tuple_unsigned_first);
    *boxed_signed + tuple_signed_first.0
}
"#;

/// Struct probe: exercises Field projections in ssa_base_name.
const STRUCT_PROBE_SOURCE: &str = r#"
pub struct Pair {
    pub first: i32,
    pub second: u64,
}

pub fn struct_probe(p: Pair) -> i32 {
    p.first
}
"#;

/// Enum probe: exercises Downcast projections in ssa_base_name.
const ENUM_PROBE_SOURCE: &str = r#"
pub enum Choice {
    A(i32),
    B(u64),
}

pub fn enum_probe(c: Choice) -> i32 {
    match c {
        Choice::A(v) => v,
        Choice::B(v) => v as i32,
    }
}
"#;

// ─── Signedness detection ────────────────────────────────────────────

#[test]
fn test_ssa_signedness_helpers_from_mir_locals() {
    with_test_ay_ctx_for_source(SSA_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ssa_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let signed = local_operand(1); // i32
        let unsigned = local_operand(2); // u32
        let bool_op = local_operand(3); // bool
        let ptr_op = local_operand(4); // *const i32

        assert_eq!(codegen.operand_signedness(&signed), Some(true));
        assert_eq!(codegen.operand_signedness(&unsigned), Some(false));
        assert_eq!(codegen.operand_signedness(&bool_op), Some(false));
        assert_eq!(codegen.operand_signedness(&ptr_op), Some(true));

        assert_eq!(codegen.is_signed_integer_op(&signed, &ptr_op), Some(true));
        assert_eq!(codegen.is_signed_integer_op(&signed, &unsigned), None);

        assert_eq!(codegen.signedness_from_base_name("probe::local_1"), Some(true));
        assert_eq!(codegen.signedness_from_base_name("probe::local_2_field_0"), Some(false));
        assert_eq!(codegen.signedness_from_base_name("probe::local_not_a_number"), None);
    });
}

/// Tests ty_signedness across all major integer types, references, and floats.
/// Covers: u8, i8, u16, i16, u64, i64, usize, isize, f32, &i32, &u32.
#[test]
fn test_ty_signedness_diverse_integer_types() {
    with_test_ay_ctx_for_source(DIVERSE_TYPE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "diverse_types");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Parameters: local 0 = return, locals 1-11 = arguments
        // u8 → unsigned
        assert_eq!(
            codegen.operand_signedness(&local_operand(1)),
            Some(false),
            "u8 should be unsigned"
        );
        // i8 → signed
        assert_eq!(
            codegen.operand_signedness(&local_operand(2)),
            Some(true),
            "i8 should be signed"
        );
        // u16 → unsigned
        assert_eq!(
            codegen.operand_signedness(&local_operand(3)),
            Some(false),
            "u16 should be unsigned"
        );
        // i16 → signed
        assert_eq!(
            codegen.operand_signedness(&local_operand(4)),
            Some(true),
            "i16 should be signed"
        );
        // u64 → unsigned
        assert_eq!(
            codegen.operand_signedness(&local_operand(5)),
            Some(false),
            "u64 should be unsigned"
        );
        // i64 → signed
        assert_eq!(
            codegen.operand_signedness(&local_operand(6)),
            Some(true),
            "i64 should be signed"
        );
        // usize → unsigned
        assert_eq!(
            codegen.operand_signedness(&local_operand(7)),
            Some(false),
            "usize should be unsigned"
        );
        // isize → signed
        assert_eq!(
            codegen.operand_signedness(&local_operand(8)),
            Some(true),
            "isize should be signed"
        );
        // f32 → unsigned (modeled as bitvector with unsigned semantics, Part of #3094)
        assert_eq!(
            codegen.operand_signedness(&local_operand(9)),
            Some(false),
            "f32 should be unsigned (BV model)"
        );
        // &i32 → signed (recurses through reference)
        assert_eq!(
            codegen.operand_signedness(&local_operand(10)),
            Some(true),
            "&i32 should be signed (ref-through)"
        );
        // &u32 → unsigned (recurses through reference)
        assert_eq!(
            codegen.operand_signedness(&local_operand(11)),
            Some(false),
            "&u32 should be unsigned (ref-through)"
        );
    });
}

/// Tests ty_signedness on Box<i32>, Box<u32>, and tuple types (Part of #2954).
///
/// Verifies:
/// - Box<i32> → Some(true) (signed, recursing through pointer-wrapper Adt)
/// - Box<u32> → Some(false) (unsigned, recursing through pointer-wrapper Adt)
/// - (i32, bool) → Some(true) (first element is signed)
/// - (u64, i32) → Some(false) (first element is unsigned)
#[test]
fn test_ty_signedness_pointer_wrapper_and_tuple() {
    with_test_ay_ctx_for_source(POINTER_WRAPPER_TUPLE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "pointer_wrapper_tuple_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Parameters: local 0 = return, locals 1-4 = arguments
        // Box<i32> → signed (recurses through Adt wrapper to find i32)
        assert_eq!(
            codegen.operand_signedness(&local_operand(1)),
            Some(true),
            "Box<i32> should be signed (Adt pointer-wrapper recursion)"
        );
        // Box<u32> → unsigned (recurses through Adt wrapper to find u32)
        assert_eq!(
            codegen.operand_signedness(&local_operand(2)),
            Some(false),
            "Box<u32> should be unsigned (Adt pointer-wrapper recursion)"
        );
        // (i32, bool) → signed (first element is i32)
        assert_eq!(
            codegen.operand_signedness(&local_operand(3)),
            Some(true),
            "(i32, bool) should be signed (Tuple first-element recursion)"
        );
        // (u64, i32) → unsigned (first element is u64)
        assert_eq!(
            codegen.operand_signedness(&local_operand(4)),
            Some(false),
            "(u64, i32) should be unsigned (Tuple first-element recursion)"
        );
    });
}

/// Tests is_signed_integer_op when both operands agree on unsigned.
#[test]
fn test_is_signed_integer_op_both_unsigned_agree() {
    with_test_ay_ctx_for_source(DIVERSE_TYPE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "diverse_types");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let u8_op = local_operand(1); // u8
        let u16_op = local_operand(3); // u16
        assert_eq!(
            codegen.is_signed_integer_op(&u8_op, &u16_op),
            Some(false),
            "u8 + u16 should agree on unsigned"
        );
    });
}

/// Tests is_signed_integer_op when both operands agree on signed.
#[test]
fn test_is_signed_integer_op_both_signed_agree() {
    with_test_ay_ctx_for_source(DIVERSE_TYPE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "diverse_types");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let i8_op = local_operand(2); // i8
        let i64_op = local_operand(6); // i64
        assert_eq!(
            codegen.is_signed_integer_op(&i8_op, &i64_op),
            Some(true),
            "i8 + i64 should agree on signed"
        );
    });
}

/// Tests is_signed_integer_op when one operand is float (f32 → unsigned per #3094).
/// Since f32 is now modeled as unsigned BV, i8 + f32 disagrees (signed vs unsigned).
#[test]
fn test_is_signed_integer_op_one_unknown() {
    with_test_ay_ctx_for_source(DIVERSE_TYPE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "diverse_types");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let i8_op = local_operand(2); // i8 → signed
        let f32_op = local_operand(9); // f32 → unsigned (BV model, Part of #3094)
        // signed + unsigned → disagree → None
        assert_eq!(
            codegen.is_signed_integer_op(&i8_op, &f32_op),
            None,
            "i8 + f32: signed vs unsigned should disagree"
        );
        // Reversed order
        assert_eq!(
            codegen.is_signed_integer_op(&f32_op, &i8_op),
            None,
            "f32 + i8: unsigned vs signed should disagree"
        );

        let u64_op = local_operand(5); // u64 → unsigned
        // unsigned + unsigned → agree → Some(false)
        assert_eq!(
            codegen.is_signed_integer_op(&f32_op, &u64_op),
            Some(false),
            "f32 + u64: both unsigned should agree"
        );
    });
}

/// Tests is_signed_integer_op when both operands disagree (signed vs unsigned → None).
#[test]
fn test_is_signed_integer_op_disagree_returns_none() {
    with_test_ay_ctx_for_source(DIVERSE_TYPE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "diverse_types");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let i8_op = local_operand(2); // i8 → signed
        let u64_op = local_operand(5); // u64 → unsigned
        assert_eq!(
            codegen.is_signed_integer_op(&i8_op, &u64_op),
            None,
            "signed + unsigned should disagree → None"
        );
    });
}

// ─── signedness_from_base_name edge cases ────────────────────────────

/// Tests signedness_from_base_name with out-of-range local index.
#[test]
fn test_signedness_from_base_name_out_of_range_local() {
    with_test_ay_ctx_for_source(SSA_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ssa_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Local 9999 doesn't exist
        assert_eq!(
            codegen.signedness_from_base_name("fn::local_9999"),
            None,
            "out-of-range local should return None"
        );
    });
}

/// Tests signedness_from_base_name with no `::local_` pattern.
#[test]
fn test_signedness_from_base_name_no_local_pattern() {
    with_test_ay_ctx_for_source(SSA_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ssa_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        assert_eq!(
            codegen.signedness_from_base_name("no_local_prefix_here"),
            None,
            "missing ::local_ pattern should return None"
        );
        assert_eq!(codegen.signedness_from_base_name(""), None, "empty string should return None");
        assert_eq!(
            codegen.signedness_from_base_name("fn::var_0"),
            None,
            "wrong prefix (var instead of local) should return None"
        );
    });
}

/// Tests signedness_from_base_name with the return local (local_0).
#[test]
fn test_signedness_from_base_name_return_local() {
    with_test_ay_ctx_for_source(SSA_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ssa_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // local_0 is the return type (i32 for ssa_probe)
        assert_eq!(
            codegen.signedness_from_base_name("ssa_probe::local_0"),
            Some(true),
            "return local of fn() -> i32 should be signed"
        );
    });
}

// ─── SSA naming and projection base names ────────────────────────────

#[test]
fn test_ssa_name_and_projection_base_helpers() {
    with_test_ay_ctx_for_source(SSA_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ssa_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let base = codegen.ssa_base_name(&local_place(1));
        let v0 = codegen.ssa_name_from_base(&base, true);
        let v1 = codegen.ssa_name_from_base(&base, true);
        let current = codegen.ssa_name_from_base(&base, false);

        assert!(v0.ends_with("_0"), "first SSA allocation should use version 0: {v0}");
        assert!(v1.ends_with("_1"), "second SSA allocation should use version 1: {v1}");
        assert_eq!(current, v1, "increment=false should return current version");

        let projected = Place {
            local: Local::from(2usize),
            projection: vec![
                ProjectionElem::Index(Local::from(3usize)),
                ProjectionElem::ConstantIndex { offset: 1, min_length: 4, from_end: false },
                ProjectionElem::Subslice { from: 1, to: 2, from_end: true },
            ],
        };

        let projected_base = codegen.ssa_base_name(&projected);
        assert!(projected_base.contains("_idx_by_3"), "missing index suffix: {projected_base}");
        assert!(projected_base.contains("_cidx_1"), "missing const index suffix: {projected_base}");
        assert!(
            projected_base.contains("_subslice_end_1_2"),
            "missing subslice suffix: {projected_base}"
        );

        let prefix_base = codegen.ssa_base_name_for_prefix(&projected, 1);
        assert!(prefix_base.ends_with("_idx_by_3"), "prefix should include first projection");
    });
}

/// Tests ssa_base_name with Field projections from real struct access MIR.
#[test]
fn test_ssa_base_name_field_projection() {
    with_test_ay_ctx_for_source(SSA_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ssa_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Construct a Place with Field(0) projection
        let field_place = Place {
            local: Local::from(1usize),
            projection: vec![ProjectionElem::Field(0usize, body.locals()[1].ty)],
        };

        let base = codegen.ssa_base_name(&field_place);
        assert!(base.contains("::local_1"), "should contain local index: {base}");
        assert!(base.contains("_field_0"), "should contain field projection: {base}");
    });
}

/// Tests ssa_base_name with Deref projection.
#[test]
fn test_ssa_base_name_deref_projection() {
    with_test_ay_ctx_for_source(SSA_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ssa_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Place with Deref projection (e.g., *ptr)
        let deref_place = Place {
            local: Local::from(4usize), // ptr: *const i32
            projection: vec![ProjectionElem::Deref],
        };

        let base = codegen.ssa_base_name(&deref_place);
        assert!(base.contains("::local_4"), "should contain local index: {base}");
        assert!(base.ends_with("_deref"), "should end with deref suffix: {base}");
    });
}

// Downcast projection: VariantIdx is opaque from rustc_public, tested via
// real enum MIR in `test_ssa_base_name_real_enum_downcast` below.

/// Tests ssa_base_name with OpaqueCast projection.
#[test]
fn test_ssa_base_name_opaque_cast_projection() {
    with_test_ay_ctx_for_source(SSA_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ssa_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // OpaqueCast projection
        let cast_place = Place {
            local: Local::from(1usize),
            projection: vec![ProjectionElem::OpaqueCast(body.locals()[1].ty)],
        };

        let base = codegen.ssa_base_name(&cast_place);
        assert!(base.ends_with("_cast"), "should end with cast suffix: {base}");
    });
}

/// Tests ssa_base_name with ConstantIndex from_end=true variant.
#[test]
fn test_ssa_base_name_constant_index_from_end() {
    with_test_ay_ctx_for_source(SSA_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ssa_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let from_end_place = Place {
            local: Local::from(1usize),
            projection: vec![ProjectionElem::ConstantIndex {
                offset: 2,
                min_length: 5,
                from_end: true,
            }],
        };

        let base = codegen.ssa_base_name(&from_end_place);
        assert!(
            base.contains("_cidx_end_2"),
            "should contain cidx_end suffix for from_end=true: {base}"
        );
    });
}

/// Tests ssa_base_name with Subslice from_end=false variant.
#[test]
fn test_ssa_base_name_subslice_from_start() {
    with_test_ay_ctx_for_source(SSA_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ssa_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let subslice_place = Place {
            local: Local::from(1usize),
            projection: vec![ProjectionElem::Subslice { from: 0, to: 3, from_end: false }],
        };

        let base = codegen.ssa_base_name(&subslice_place);
        assert!(
            base.contains("_subslice_0_3"),
            "should contain subslice_0_3 (not subslice_end) for from_end=false: {base}"
        );
        assert!(
            !base.contains("_subslice_end"),
            "should NOT contain _end suffix for from_end=false: {base}"
        );
    });
}

/// Tests ssa_base_name with deeply nested projection chain.
#[test]
fn test_ssa_base_name_nested_projections() {
    with_test_ay_ctx_for_source(SSA_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ssa_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Simulate deeply nested: local_1.field_0.deref.field_2
        // (VariantIdx is opaque from rustc_public, so we use constructable projections)
        let nested = Place {
            local: Local::from(1usize),
            projection: vec![
                ProjectionElem::Field(0usize, body.locals()[1].ty),
                ProjectionElem::Deref,
                ProjectionElem::Field(2usize, body.locals()[1].ty),
            ],
        };

        let base = codegen.ssa_base_name(&nested);
        // Verify ordering of suffixes matches projection order
        let field0_pos = base.find("_field_0").expect("missing field_0");
        let deref_pos = base.find("_deref").expect("missing deref");
        let field2_pos = base.find("_field_2").expect("missing field_2");
        assert!(field0_pos < deref_pos, "field_0 should precede deref");
        assert!(deref_pos < field2_pos, "deref should precede field_2");
    });
}

// ─── ssa_base_name_for_prefix ────────────────────────────────────────

/// Tests that prefix=0 returns just the local name with no projections.
#[test]
fn test_ssa_prefix_zero_returns_bare_local() {
    with_test_ay_ctx_for_source(SSA_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ssa_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let nested = Place {
            local: Local::from(2usize),
            projection: vec![
                ProjectionElem::Field(0usize, body.locals()[1].ty),
                ProjectionElem::Deref,
            ],
        };

        let prefix_0 = codegen.ssa_base_name_for_prefix(&nested, 0);
        assert!(prefix_0.ends_with("::local_2"), "prefix=0 should be bare local: {prefix_0}");
        assert!(!prefix_0.contains("_field"), "prefix=0 should have no projections: {prefix_0}");
        assert!(!prefix_0.contains("_deref"), "prefix=0 should have no deref: {prefix_0}");
    });
}

/// Tests that prefix at full length matches ssa_base_name.
#[test]
fn test_ssa_prefix_full_length_matches_base_name() {
    with_test_ay_ctx_for_source(SSA_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ssa_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = Place {
            local: Local::from(1usize),
            projection: vec![
                ProjectionElem::Field(0usize, body.locals()[1].ty),
                ProjectionElem::Deref,
            ],
        };

        let full_base = codegen.ssa_base_name(&place);
        let prefix_full = codegen.ssa_base_name_for_prefix(&place, 2);
        assert_eq!(full_base, prefix_full, "prefix at full length should match ssa_base_name");
    });
}

/// Tests that prefix lengths beyond projection count are clamped, not panicking.
#[test]
fn test_ssa_prefix_out_of_bounds_clamps_to_full_length() {
    with_test_ay_ctx_for_source(SSA_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ssa_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = Place {
            local: Local::from(1usize),
            projection: vec![
                ProjectionElem::Field(0usize, body.locals()[1].ty),
                ProjectionElem::Deref,
            ],
        };

        let full_base = codegen.ssa_base_name(&place);
        let prefix_out_of_bounds =
            codegen.ssa_base_name_for_prefix(&place, place.projection.len() + 8);
        assert_eq!(
            full_base, prefix_out_of_bounds,
            "prefix beyond projection length should clamp to full base name"
        );
    });
}

/// Tests intermediate prefix lengths on a multi-projection place.
#[test]
fn test_ssa_prefix_intermediate_lengths() {
    with_test_ay_ctx_for_source(SSA_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ssa_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = Place {
            local: Local::from(1usize),
            projection: vec![
                ProjectionElem::Index(Local::from(2usize)),
                ProjectionElem::ConstantIndex { offset: 5, min_length: 10, from_end: false },
                ProjectionElem::Deref,
            ],
        };

        let prefix_1 = codegen.ssa_base_name_for_prefix(&place, 1);
        assert!(prefix_1.contains("_idx_by_2"), "prefix=1 should include Index: {prefix_1}");
        assert!(
            !prefix_1.contains("_cidx"),
            "prefix=1 should NOT include ConstantIndex: {prefix_1}"
        );

        let prefix_2 = codegen.ssa_base_name_for_prefix(&place, 2);
        assert!(prefix_2.contains("_idx_by_2"), "prefix=2 should include Index: {prefix_2}");
        assert!(prefix_2.contains("_cidx_5"), "prefix=2 should include ConstantIndex: {prefix_2}");
        assert!(!prefix_2.contains("_deref"), "prefix=2 should NOT include Deref: {prefix_2}");
    });
}

// ─── ssa_name via Place (integration) ────────────────────────────────

/// Tests ssa_name directly through Place (the main production entry point).
#[test]
fn test_ssa_name_via_place_increment() {
    with_test_ay_ctx_for_source(SSA_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ssa_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = local_place(1);
        let name_0 = codegen.ssa_name(&place, true);
        let name_1 = codegen.ssa_name(&place, true);

        assert!(name_0.ends_with("_0"), "first ssa_name should end with _0: {name_0}");
        assert!(name_1.ends_with("_1"), "second ssa_name should end with _1: {name_1}");
        assert_ne!(name_0, name_1, "consecutive ssa_name calls must produce different names");
    });
}

/// Tests ssa_name with increment=false returns current version.
#[test]
fn test_ssa_name_via_place_no_increment() {
    with_test_ay_ctx_for_source(SSA_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ssa_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place = local_place(2);
        // Before any allocation, increment=false returns _0 (saturating_sub(1) on 0)
        let pre_alloc = codegen.ssa_name(&place, false);
        assert!(pre_alloc.ends_with("_0"), "pre-alloc read should return _0: {pre_alloc}");

        // Allocate v0
        let v0 = codegen.ssa_name(&place, true);
        assert!(v0.ends_with("_0"), "first allocation should be _0: {v0}");

        // Read without increment should return current (v0)
        let read = codegen.ssa_name(&place, false);
        assert_eq!(read, v0, "increment=false after v0 should equal v0");

        // Allocate v1
        let v1 = codegen.ssa_name(&place, true);
        assert!(v1.ends_with("_1"), "second allocation should be _1: {v1}");

        // Read should now return v1
        let read2 = codegen.ssa_name(&place, false);
        assert_eq!(read2, v1, "increment=false after v1 should equal v1");
    });
}

// ─── Cross-variable independence ─────────────────────────────────────

/// Verifies that SSA version counters are independent per-place.
#[test]
fn test_ssa_cross_variable_version_independence() {
    with_test_ay_ctx_for_source(SSA_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ssa_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let place_a = local_place(1); // si: i32
        let place_b = local_place(2); // ui: u32

        // Allocate 3 versions for place_a
        let a0 = codegen.ssa_name(&place_a, true);
        let a1 = codegen.ssa_name(&place_a, true);
        let a2 = codegen.ssa_name(&place_a, true);

        // Allocate 1 version for place_b (should start at 0 regardless of place_a)
        let b0 = codegen.ssa_name(&place_b, true);

        assert!(a0.ends_with("_0"), "a0: {a0}");
        assert!(a1.ends_with("_1"), "a1: {a1}");
        assert!(a2.ends_with("_2"), "a2: {a2}");
        assert!(b0.ends_with("_0"), "b0 should start at 0 despite a having 3 versions: {b0}");

        // Verify they have different base names
        assert_ne!(
            a0.trim_end_matches("_0"),
            b0.trim_end_matches("_0"),
            "different places should have different base names"
        );
    });
}

/// Verifies uniqueness of SSA names across multiple places and versions.
#[test]
fn test_ssa_name_global_uniqueness_via_place() {
    with_test_ay_ctx_for_source(SSA_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ssa_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        let mut all_names = std::collections::HashSet::new();

        // Allocate names for locals 0-4 (return + 4 params), 5 versions each
        for local_idx in 0..5 {
            let place = local_place(local_idx);
            for _ in 0..5 {
                let name = codegen.ssa_name(&place, true);
                assert!(
                    all_names.insert(name.clone()),
                    "duplicate SSA name: {name} (local {local_idx})"
                );
            }
        }

        // Also allocate for projected places
        let projected =
            Place { local: Local::from(1usize), projection: vec![ProjectionElem::Deref] };
        for _ in 0..5 {
            let name = codegen.ssa_name(&projected, true);
            assert!(all_names.insert(name.clone()), "duplicate projected SSA name: {name}");
        }

        // 5 locals * 5 versions + 1 projected place * 5 versions = 30
        assert_eq!(all_names.len(), 30, "expected 30 unique SSA names");
    });
}

// ─── MIR-driven struct/enum projection tests ─────────────────────────

/// Tests that ssa_base_name produces Field projection suffixes from real struct MIR.
#[test]
fn test_ssa_base_name_real_struct_field_access() {
    with_test_ay_ctx_for_source(STRUCT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "struct_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Helper: check if a Place has Field projections and verify ssa_base_name
        let check_place =
            |codegen: &mut StatementCodegen<'_, '_, '_>, place: &Place, found: &mut bool| {
                if place.projection.iter().any(|p| matches!(p, ProjectionElem::Field(..))) {
                    let base = codegen.ssa_base_name(place);
                    assert!(
                        base.contains("_field_"),
                        "struct field access should contain _field_ suffix: {base}"
                    );
                    *found = true;
                }
            };

        let mut found_field_place = false;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(place, rvalue) = &stmt.kind {
                    check_place(&mut codegen, place, &mut found_field_place);
                    // Also check rvalue operand places (e.g., Copy(local_1.field_0))
                    match rvalue {
                        Rvalue::Use(Operand::Copy(p)) | Rvalue::Use(Operand::Move(p)) => {
                            check_place(&mut codegen, p, &mut found_field_place);
                        }
                        _ => {}
                    }
                }
            }
        }
        assert!(found_field_place, "should find at least one Field projection in struct_probe MIR");
    });
}

/// Tests that ssa_base_name produces Downcast projection suffixes from real enum MIR.
#[test]
fn test_ssa_base_name_real_enum_downcast() {
    with_test_ay_ctx_for_source(ENUM_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "enum_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Helper: check if a Place has Downcast projections
        let check_place =
            |codegen: &mut StatementCodegen<'_, '_, '_>, place: &Place, found: &mut bool| {
                if place.projection.iter().any(|p| matches!(p, ProjectionElem::Downcast(..))) {
                    let base = codegen.ssa_base_name(place);
                    assert!(
                        base.contains("_variant_"),
                        "enum downcast should contain _variant_ suffix: {base}"
                    );
                    *found = true;
                }
            };

        let mut found_downcast = false;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(place, rvalue) = &stmt.kind {
                    check_place(&mut codegen, place, &mut found_downcast);
                    match rvalue {
                        Rvalue::Use(Operand::Copy(p)) | Rvalue::Use(Operand::Move(p)) => {
                            check_place(&mut codegen, p, &mut found_downcast);
                        }
                        _ => {}
                    }
                }
            }
        }
        assert!(found_downcast, "should find at least one Downcast projection in enum_probe MIR");
    });
}

/// Tests that ssa_base_name handles Deref in real MIR (pointer dereference in ssa_probe).
#[test]
fn test_ssa_base_name_real_deref() {
    with_test_ay_ctx_for_source(SSA_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "ssa_probe");
        let body = instance.body().expect("function body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // The ssa_probe function has `unsafe { x = *ptr; }` which should produce a Deref
        let check_place =
            |codegen: &mut StatementCodegen<'_, '_, '_>, place: &Place, found: &mut bool| {
                if place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref)) {
                    let base = codegen.ssa_base_name(place);
                    assert!(
                        base.contains("_deref"),
                        "pointer deref should produce _deref suffix: {base}"
                    );
                    *found = true;
                }
            };

        let mut found_deref = false;
        for bb in &body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(place, rvalue) = &stmt.kind {
                    check_place(&mut codegen, place, &mut found_deref);
                    match rvalue {
                        Rvalue::Use(Operand::Copy(p)) | Rvalue::Use(Operand::Move(p)) => {
                            check_place(&mut codegen, p, &mut found_deref);
                        }
                        _ => {}
                    }
                }
            }
        }
        assert!(found_deref, "should find at least one Deref projection in ssa_probe MIR");
    });
}
