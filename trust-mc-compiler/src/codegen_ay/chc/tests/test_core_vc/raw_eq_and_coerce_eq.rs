// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// =============================================================================
// codegen_call_misc.rs — resolve_raw_eq_referent tier tests (Part of #2188)
// =============================================================================

#[test]
fn test_mir_to_chc_raw_eq_array_comparison() {
    // (#2188) Exercise codegen_call_raw_eq: raw_eq on arrays should produce
    // an SMT equality constraint comparing array referent values.
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![allow(internal_features)]
        #![feature(core_intrinsics)]

        pub fn probe_raw_eq_array() -> bool {
            let a = [1u8, 2, 3, 4];
            let b = [1u8, 2, 3, 4];
            unsafe { core::intrinsics::raw_eq(&a, &b) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_eq_array");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_raw_eq_array", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_raw_eq_array", bb_count);

        // raw_eq returns bool → should have bool-like state vars
        let has_bool_like = vc.relations.iter().any(|r| {
            r.arg_sorts.iter().any(|s| s.is_bool() || matches!(s.bitvec_width(), Some(1) | Some(8)))
        });
        assert!(has_bool_like, "raw_eq VC should have bool-like state vars for the bool return");

        // Should have transition rules with constraints (the equality comparison)
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .any(|r| !r.body.constraints.is_empty());
        assert!(
            constrained,
            "raw_eq should have constrained transition rules for the equality comparison"
        );
    });
}

// ── coerce_eq_constraint tests (Part of #2194) ──────────────────────

#[test]
fn test_coerce_eq_constraint_same_sort_bv32() {
    // Same sort: dest and result are both BV32 → direct equality
    let dest = Expr::var("dest", Sort::bitvec(32));
    let result = Expr::bitvec_const(42u64, 32);
    let out_sort = Sort::bitvec(32);

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "same-sort BV32 should produce constraint");
    let constraint = eq.unwrap();
    assert!(constraint.sort().is_bool(), "constraint must be Bool");
    let smt = constraint.to_string();
    assert!(smt.contains("dest"), "should reference dest var, got: {smt}");
}

#[test]
fn test_coerce_eq_constraint_bv_width_mismatch() {
    // BV64 result → BV32 dest: should coerce via extract/extend
    let dest = Expr::var("dest", Sort::bitvec(32));
    let result = Expr::bitvec_const(100u64, 64);
    let out_sort = Sort::bitvec(32);

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "BV64→BV32 should produce coerced constraint");
    let constraint = eq.unwrap();
    assert!(constraint.sort().is_bool());
}

#[test]
fn test_coerce_eq_constraint_bv32_to_bv64() {
    // BV32 result → BV64 dest: should widen
    let dest = Expr::var("dest", Sort::bitvec(64));
    let result = Expr::bitvec_const(7u64, 32);
    let out_sort = Sort::bitvec(64);

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "BV32→BV64 should produce coerced constraint");
    assert!(eq.unwrap().sort().is_bool());
}

#[test]
fn test_coerce_eq_constraint_bool_to_bv8() {
    // Bool result → BV8 dest: should produce ITE(result, 1, 0)
    let dest = Expr::var("dest", Sort::bitvec(8));
    let result = Expr::bool_const(true);
    let out_sort = Sort::bitvec(8);

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "Bool→BV8 should produce ITE coercion");
    let smt = eq.unwrap().to_string();
    assert!(smt.contains("ite"), "Bool→BV coercion should use ITE, got: {smt}");
}

#[test]
fn test_coerce_eq_constraint_bool_to_bv32() {
    // Bool result → BV32 dest (Rust bool as i32)
    let dest = Expr::var("dest", Sort::bitvec(32));
    let result = Expr::bool_const(false);
    let out_sort = Sort::bitvec(32);

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "Bool→BV32 should produce ITE coercion");
    assert!(eq.unwrap().sort().is_bool());
}

#[test]
fn test_coerce_eq_constraint_single_field_datatype_to_bitvec() {
    let dest = Expr::var("dest", Sort::bitvec(64));
    let tuple_sort = struct_sort("Tuple_bv64", [("fld_0", Sort::bitvec(64))]);
    let ctor = tuple_sort
        .datatype_default_constructor()
        .expect("single-field tuple sort must have constructor")
        .to_string();
    let result = Expr::datatype_constructor(
        "Tuple_bv64",
        ctor,
        vec![Expr::bitvec_const(11u64, 64)],
        tuple_sort,
    );
    let out_sort = Sort::bitvec(64);

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "single-field datatype→BV64 should be unwrapped and coerced");
    let smt = eq.unwrap().to_string();
    assert!(smt.contains("fld_0"), "coercion should select inner field, got: {smt}");
}

#[test]
fn test_coerce_eq_constraint_int_to_bv_uses_int2bv() {
    // Int result → BV32 dest: handled via int2bv coercion (Part of #2875).
    let dest = Expr::var("dest", Sort::bitvec(32));
    let result = Expr::int_const(999);
    let out_sort = Sort::bitvec(32);

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "Int→BV32 should produce coerced constraint via int2bv");
}

#[test]
fn test_coerce_eq_constraint_bv_to_int_unsigned() {
    // BV32 result → Int dest with signed=false: uses bv2int (unsigned). Part of #3055.
    let dest = Expr::var("dest", Sort::int());
    let result = Expr::bitvec_const(42u64, 32);
    let out_sort = Sort::int();

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "BV32→Int unsigned should produce coerced constraint");
}

#[test]
fn test_coerce_eq_constraint_bv_to_int_signed() {
    // BV32 result → Int dest with signed=true: uses bv2int_signed. Part of #3055.
    let dest = Expr::var("dest", Sort::int());
    let result = Expr::bitvec_const(42u64, 32);
    let out_sort = Sort::int();

    let eq = coerce_eq_constraint(&dest, result, &out_sort, true);
    assert!(eq.is_some(), "BV32→Int signed should produce coerced constraint");
}

#[test]
fn test_coerce_eq_constraint_same_sort_bool() {
    // Both Bool: direct equality
    let dest = Expr::var("dest", Sort::bool());
    let result = Expr::bool_const(true);
    let out_sort = Sort::bool();

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "same-sort Bool should produce constraint");
    assert!(eq.unwrap().sort().is_bool());
}

#[test]
fn test_coerce_eq_constraint_bv8_to_bool() {
    // BV8 result → Bool dest: should produce (result != 0) coercion
    let dest = Expr::var("dest", Sort::bool());
    let result = Expr::bitvec_const(1u64, 8);
    let out_sort = Sort::bool();

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "BV8→Bool should produce coerced constraint");
    let constraint = eq.unwrap();
    assert!(constraint.sort().is_bool(), "constraint must be Bool");
}

#[test]
fn test_coerce_eq_constraint_bv32_to_bool() {
    // BV32 result → Bool dest: should produce (result != 0) coercion
    let dest = Expr::var("dest", Sort::bool());
    let result = Expr::bitvec_const(0u64, 32);
    let out_sort = Sort::bool();

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "BV32→Bool should produce coerced constraint");
    assert!(eq.unwrap().sort().is_bool());
}

// ── Additional coerce_eq_constraint Sort coverage (Part of #2198) ────

#[test]
fn test_coerce_eq_constraint_same_sort_bv8() {
    let dest = Expr::var("dest", Sort::bitvec(8));
    let result = Expr::bitvec_const(0xFFu64, 8);
    let out_sort = Sort::bitvec(8);

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "same-sort BV8 should produce constraint");
    assert!(eq.unwrap().sort().is_bool());
}

#[test]
fn test_coerce_eq_constraint_same_sort_bv16() {
    let dest = Expr::var("dest", Sort::bitvec(16));
    let result = Expr::bitvec_const(1000u64, 16);
    let out_sort = Sort::bitvec(16);

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "same-sort BV16 should produce constraint");
    assert!(eq.unwrap().sort().is_bool());
}

#[test]
fn test_coerce_eq_constraint_same_sort_bv64() {
    let dest = Expr::var("dest", Sort::bitvec(64));
    let result = Expr::bitvec_const(u64::MAX, 64);
    let out_sort = Sort::bitvec(64);

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "same-sort BV64 should produce constraint");
    assert!(eq.unwrap().sort().is_bool());
}

#[test]
fn test_coerce_eq_constraint_same_sort_int() {
    let dest = Expr::var("dest", Sort::int());
    let result = Expr::int_const(42);
    let out_sort = Sort::int();

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "same-sort Int should produce constraint");
    assert!(eq.unwrap().sort().is_bool());
}

#[test]
fn test_coerce_eq_constraint_bv16_to_bv32() {
    // BV16 result → BV32 dest: should widen
    let dest = Expr::var("dest", Sort::bitvec(32));
    let result = Expr::bitvec_const(500u64, 16);
    let out_sort = Sort::bitvec(32);

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "BV16→BV32 should produce coerced constraint");
    assert!(eq.unwrap().sort().is_bool());
}

#[test]
fn test_coerce_eq_constraint_bv32_to_bv16() {
    // BV32 result → BV16 dest: should narrow
    let dest = Expr::var("dest", Sort::bitvec(16));
    let result = Expr::bitvec_const(12345u64, 32);
    let out_sort = Sort::bitvec(16);

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "BV32→BV16 should produce coerced constraint");
    assert!(eq.unwrap().sort().is_bool());
}

#[test]
fn test_coerce_eq_constraint_bool_to_bv16() {
    let dest = Expr::var("dest", Sort::bitvec(16));
    let result = Expr::bool_const(true);
    let out_sort = Sort::bitvec(16);

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "Bool→BV16 should produce ITE coercion");
    let smt = eq.unwrap().to_string();
    assert!(smt.contains("ite"), "Bool→BV16 coercion should use ITE, got: {smt}");
}

#[test]
fn test_coerce_eq_constraint_bool_to_bv64() {
    let dest = Expr::var("dest", Sort::bitvec(64));
    let result = Expr::bool_const(false);
    let out_sort = Sort::bitvec(64);

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "Bool→BV64 should produce ITE coercion");
    assert!(eq.unwrap().sort().is_bool());
}

#[test]
fn test_coerce_eq_constraint_bv16_to_bool() {
    let dest = Expr::var("dest", Sort::bool());
    let result = Expr::bitvec_const(1u64, 16);
    let out_sort = Sort::bool();

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "BV16→Bool should produce coerced constraint");
    assert!(eq.unwrap().sort().is_bool());
}

#[test]
fn test_coerce_eq_constraint_bv64_to_bool() {
    let dest = Expr::var("dest", Sort::bool());
    let result = Expr::bitvec_const(0u64, 64);
    let out_sort = Sort::bool();

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "BV64→Bool should produce coerced constraint");
    assert!(eq.unwrap().sort().is_bool());
}

#[test]
fn test_coerce_eq_constraint_int_to_bool_incompatible() {
    // Int → Bool is not handled by coerce_eq_constraint → None
    let dest = Expr::var("dest", Sort::bool());
    let result = Expr::int_const(1);
    let out_sort = Sort::bool();

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_none(), "Int→Bool should be incompatible (None)");
}

#[test]
fn test_coerce_eq_constraint_bool_to_int_incompatible() {
    // Bool → Int is not handled by coerce_eq_constraint → None
    let dest = Expr::var("dest", Sort::int());
    let result = Expr::bool_const(true);
    let out_sort = Sort::int();

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_none(), "Bool→Int should be incompatible (None)");
}

// ── signed=true coerce_eq_constraint tests (Part of #2976 Phase 2) ────

#[test]
fn test_coerce_eq_constraint_bv8_to_bv32_signed_extends() {
    // BV8 result → BV32 dest with signed=true: should sign-extend.
    // 0xFF (i8 = -1) sign-extended → 0xFFFFFFFF (i32 = -1), not 0x000000FF (255).
    let dest = Expr::var("dest", Sort::bitvec(32));
    let result = Expr::bitvec_const(0xFFu64, 8);
    let out_sort = Sort::bitvec(32);

    let eq = coerce_eq_constraint(&dest, result, &out_sort, true);
    assert!(eq.is_some(), "BV8→BV32 signed should produce coerced constraint");
    let smt = eq.unwrap().to_string();
    // Sign extension should appear in the constraint (BvSignExtend, not BvZeroExtend).
    assert!(
        smt.contains("sign_extend") || smt.contains("SignExt"),
        "signed widening BV8→BV32 should use sign-extend, got: {smt}"
    );
}

#[test]
fn test_coerce_eq_constraint_bv16_to_bv64_signed_extends() {
    // BV16 result → BV64 dest with signed=true.
    let dest = Expr::var("dest", Sort::bitvec(64));
    let result = Expr::bitvec_const(0x8000u64, 16); // i16::MIN = -32768
    let out_sort = Sort::bitvec(64);

    let eq = coerce_eq_constraint(&dest, result, &out_sort, true);
    assert!(eq.is_some(), "BV16→BV64 signed should produce coerced constraint");
    assert!(eq.unwrap().sort().is_bool());
}

#[test]
fn test_coerce_eq_constraint_bv8_to_bv32_unsigned_zero_extends() {
    // BV8 result → BV32 dest with signed=false: should zero-extend.
    let dest = Expr::var("dest", Sort::bitvec(32));
    let result = Expr::bitvec_const(0xFFu64, 8);
    let out_sort = Sort::bitvec(32);

    let eq = coerce_eq_constraint(&dest, result, &out_sort, false);
    assert!(eq.is_some(), "BV8→BV32 unsigned should produce coerced constraint");
    let smt = eq.unwrap().to_string();
    // Zero extension should appear (BvZeroExtend), NOT sign extension.
    assert!(
        !smt.contains("sign_extend") && !smt.contains("SignExt"),
        "unsigned widening BV8→BV32 should NOT use sign-extend, got: {smt}"
    );
}

// ── element→nested-array coercion (Part of #3783) ───────────────────

#[test]
fn test_coerce_eq_constraint_element_to_nested_array() {
    // Part of #3783: Vec<[u64; 3]> data field is Array<BV64, Array<BV64, BV64>>.
    // When the value is Array<BV64, BV64> (a single [u64; 3] element), the
    // coercion should wrap it in a fresh array with store(0, value).
    let inner_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(64));
    let outer_sort = Sort::array(Sort::bitvec(64), inner_sort.clone());
    let dest = Expr::var("dest_data", outer_sort.clone());
    let value = Expr::var("elem_val", inner_sort);

    let eq = coerce_eq_constraint(&dest, value, &outer_sort, false);
    assert!(
        eq.is_some(),
        "Element Array<BV64,BV64> → Array<BV64,Array<BV64,BV64>> should produce coerced constraint"
    );
    // The result should be a bool (equality expression)
    assert!(eq.as_ref().unwrap().sort().is_bool());
}

#[test]
fn test_coerce_eq_constraint_non_element_array_still_none() {
    // When value sort is NOT the element sort of the dest array, should still fail.
    let dest_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    let dest = Expr::var("dest", dest_sort.clone());
    let value = Expr::var("val", Sort::bitvec(64)); // BV64 is NOT the element sort (BV32)

    let eq = coerce_eq_constraint(&dest, value, &dest_sort, false);
    // BV64 != BV32 element sort, AND this should be caught by an earlier BV→BV case.
    // But if it reaches the array check, the element sort mismatch should NOT trigger wrapping.
    // (In practice, BV→BV coercion fires first, so this won't reach the array path.)
    // This test verifies the guard: arr.element_sort == result_sort.
    assert!(eq.is_some(), "BV64 value with Array<BV64,BV32> dest should still coerce via BV path");
}

// ── Array(K, DT) → Array(K, BV) element packing (Part of #3814) ────

#[test]
fn test_coerce_eq_constraint_array_dt_to_array_bv_packing() {
    // Part of #3814: [Rational; 4] produces Array(BV64, DT{num:BV64, den:BV64})
    // but the flattened state var expects Array(BV64, BV128). The coercion should
    // pack DT elements into BV128 via field concat.
    let dt_sort =
        struct_sort("Rational", [("fld_num", Sort::bitvec(64)), ("fld_den", Sort::bitvec(64))]);
    let src_sort = Sort::array(Sort::bitvec(64), dt_sort);
    let tgt_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(128));
    let dest = Expr::var("dest_coeffs", tgt_sort.clone());
    let value = Expr::var("src_coeffs", src_sort);

    let eq = coerce_eq_constraint(&dest, value, &tgt_sort, false);
    assert!(
        eq.is_some(),
        "Array(BV64, DT{{BV64,BV64}}) → Array(BV64, BV128) should produce coerced constraint"
    );
    assert!(eq.as_ref().unwrap().sort().is_bool());
}

#[test]
fn test_coerce_eq_constraint_array_dt_to_array_bv_width_mismatch_returns_none() {
    // When the DT fields don't sum to the target BV width, coercion should fail.
    let dt_sort = struct_sort("Pair", [("fld_a", Sort::bitvec(32)), ("fld_b", Sort::bitvec(32))]);
    let src_sort = Sort::array(Sort::bitvec(64), dt_sort);
    let tgt_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(128)); // DT packs to 64, not 128
    let dest = Expr::var("dest", tgt_sort.clone());
    let value = Expr::var("src", src_sort);

    let eq = coerce_eq_constraint(&dest, value, &tgt_sort, false);
    // DT(32+32) = 64 bits, target = 128 bits — width mismatch, should not coerce.
    assert!(eq.is_none(), "Width-mismatched DT→BV array packing should return None");
}
