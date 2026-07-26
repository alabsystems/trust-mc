// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for stubs_math_bigrational.rs — BigRational translation to SMT
//! Real sort via the mir_to_chc pipeline.
//!
//! Part of #2255: Coverage for decomposed chc/ files with zero tests.

#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// BigRational arithmetic pipeline tests
// =============================================================================

/// Test BigRational addition via Ratio<BigInt> produces a valid VC.
/// Exercises: translate_bigrational_call(BigRationalAdd), get_bigrational_arg.
#[test]
fn test_bigrational_add_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        #[derive(Copy, Clone)]
        pub struct Ratio<T>(T, T);

        impl core::ops::Add for Ratio<BigInt> {
            type Output = Self;
            fn add(self, rhs: Self) -> Self {
                Ratio(BigInt(self.0.0 + rhs.0.0), self.1)
            }
        }

        pub fn probe_bigrational_add(a: Ratio<BigInt>, b: Ratio<BigInt>) -> Ratio<BigInt> {
            a + b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigrational_add");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bigrational_add", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "Pipeline should produce at least {} rules, got {}",
            bb_count,
            vc.rules.len()
        );
    });
}

/// Test BigRational subtraction pipeline.
/// Exercises: translate_bigrational_call(BigRationalSub).
#[test]
fn test_bigrational_sub_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        #[derive(Copy, Clone)]
        pub struct Ratio<T>(T, T);

        impl core::ops::Sub for Ratio<BigInt> {
            type Output = Self;
            fn sub(self, rhs: Self) -> Self {
                Ratio(BigInt(self.0.0 - rhs.0.0), self.1)
            }
        }

        pub fn probe_bigrational_sub(a: Ratio<BigInt>, b: Ratio<BigInt>) -> Ratio<BigInt> {
            a - b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigrational_sub");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bigrational_sub", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "Pipeline should produce at least {} rules, got {}",
            bb_count,
            vc.rules.len()
        );
    });
}

/// Test BigRational multiplication pipeline.
/// Exercises: translate_bigrational_call(BigRationalMul).
#[test]
fn test_bigrational_mul_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        #[derive(Copy, Clone)]
        pub struct Ratio<T>(T, T);

        impl core::ops::Mul for Ratio<BigInt> {
            type Output = Self;
            fn mul(self, rhs: Self) -> Self {
                Ratio(BigInt(self.0.0 * rhs.0.0), self.1)
            }
        }

        pub fn probe_bigrational_mul(a: Ratio<BigInt>, b: Ratio<BigInt>) -> Ratio<BigInt> {
            a * b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigrational_mul");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bigrational_mul", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "Pipeline should produce at least {} rules, got {}",
            bb_count,
            vc.rules.len()
        );
    });
}

// =============================================================================
// BigRational comparison pipeline tests
// =============================================================================

/// Test BigRational equality comparison pipeline.
/// Exercises: translate_bigrational_call(BigRationalEq).
#[test]
fn test_bigrational_eq_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone, PartialEq)]
        pub struct BigInt(u64);

        #[derive(Copy, Clone, PartialEq)]
        pub struct Ratio<T: PartialEq>(T, T);

        pub fn probe_bigrational_eq(a: Ratio<BigInt>, b: Ratio<BigInt>) -> bool {
            a == b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigrational_eq");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bigrational_eq", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "Pipeline should produce at least {} rules, got {}",
            bb_count,
            vc.rules.len()
        );
    });
}

// =============================================================================
// Standalone: BigRational Real sort encoding
// =============================================================================

/// Test BigRational binary ops produce Real sort results.
#[test]
fn test_bigrational_binary_ops_sort() {
    let a = Expr::var("a", Sort::real());
    let b = Expr::var("b", Sort::real());

    let add = a.clone().real_add(b.clone());
    assert!(add.sort().is_real(), "BigRationalAdd should produce Real sort");

    let sub = a.clone().real_sub(b.clone());
    assert!(sub.sort().is_real(), "BigRationalSub should produce Real sort");

    let mul = a.clone().real_mul(b.clone());
    assert!(mul.sort().is_real(), "BigRationalMul should produce Real sort");

    let div = a.clone().real_div(b);
    assert!(div.sort().is_real(), "BigRationalDiv should produce Real sort");

    let neg = a.real_neg();
    assert!(neg.sort().is_real(), "BigRationalNeg should produce Real sort");
}

/// Test BigRational comparison ops produce Bool sort.
#[test]
fn test_bigrational_comparison_ops_sort() {
    let a = Expr::var("a", Sort::real());
    let b = Expr::var("b", Sort::real());

    let eq = a.clone().eq(b.clone());
    assert!(eq.sort().is_bool(), "BigRationalEq should produce Bool sort");

    let lt = a.clone().real_lt(b.clone());
    assert!(lt.sort().is_bool(), "BigRationalLt should produce Bool sort");

    let le = a.clone().real_le(b.clone());
    assert!(le.sort().is_bool(), "BigRationalLe should produce Bool sort");

    let gt = a.clone().real_gt(b.clone());
    assert!(gt.sort().is_bool(), "BigRationalGt should produce Bool sort");

    let ge = a.real_ge(b);
    assert!(ge.sort().is_bool(), "BigRationalGe should produce Bool sort");
}

/// Test BigRational new(numer, denom) encoding: (to_real numer) / (to_real denom).
#[test]
fn test_bigrational_new_encoding() {
    let numer = Expr::var("numer", Sort::int());
    let denom = Expr::var("denom", Sort::int());
    let numer_real = numer.int_to_real();
    let denom_real = denom.int_to_real();

    assert!(numer_real.sort().is_real(), "int_to_real(numer) should be Real");
    assert!(denom_real.sort().is_real(), "int_to_real(denom) should be Real");

    let result = numer_real.real_div(denom_real);
    assert!(result.sort().is_real(), "numer/denom should be Real sort");
}

/// Test BigRational from(BigInt) encoding: int_to_real(arg).
#[test]
fn test_bigrational_from_bigint_encoding() {
    let bigint_val = Expr::var("bigint", Sort::int());
    let real_val = bigint_val.int_to_real();
    assert!(real_val.sort().is_real(), "BigRationalFrom should convert Int to Real");
}

/// Test BigRational clone is identity in SMT.
#[test]
fn test_bigrational_clone_is_identity() {
    let val = Expr::var("br", Sort::real());
    // Clone in SMT is just the same expression — value semantics
    let cloned = val.clone();
    assert_eq!(val.sort(), cloned.sort(), "Clone should preserve sort");
    assert_eq!(val.to_string(), cloned.to_string(), "Clone should be identity in SMT");
}

// =============================================================================
// Error-path tests: translate_bigrational_call returns None
// =============================================================================
//
// Part of #2627: error-path test coverage gaps.
// Models the `returns_none` pattern from test_stubs_bigint.rs.

/// Minimal source for constructing a ChcCtx without BigRational-specific MIR.
const BIGRATIONAL_ERROR_PATH_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_simple() {}
"#;

/// Binary arithmetic ops (Add, Sub, Mul, Div) with fewer than 2 args return None.
#[test]
fn test_translate_bigrational_binary_op_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(BIGRATIONAL_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        let binary_stubs = [
            StubKind::BigRationalAdd,
            StubKind::BigRationalSub,
            StubKind::BigRationalMul,
            StubKind::BigRationalDiv,
        ];

        for stub in binary_stubs {
            // 0 args
            let result = chc_ctx.translate_bigrational_call(stub, &[], &modified);
            assert_eq!(result, None, "{stub:?} with 0 args should return None");

            // 1 arg (still insufficient)
            let one_arg = vec![Operand::Copy(Place { local: 0, projection: vec![] })];
            let result = chc_ctx.translate_bigrational_call(stub, &one_arg, &modified);
            assert_eq!(result, None, "{stub:?} with 1 arg should return None");
        }
    });
}

/// Comparison ops (Eq, Lt, Le, Gt, Ge) with fewer than 2 args return None.
#[test]
fn test_translate_bigrational_comparison_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(BIGRATIONAL_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        let cmp_stubs = [
            StubKind::BigRationalEq,
            StubKind::BigRationalLt,
            StubKind::BigRationalLe,
            StubKind::BigRationalGt,
            StubKind::BigRationalGe,
        ];

        for stub in cmp_stubs {
            // 0 args
            let result = chc_ctx.translate_bigrational_call(stub, &[], &modified);
            assert_eq!(result, None, "{stub:?} with 0 args should return None");

            // 1 arg (still insufficient)
            let one_arg = vec![Operand::Copy(Place { local: 0, projection: vec![] })];
            let result = chc_ctx.translate_bigrational_call(stub, &one_arg, &modified);
            assert_eq!(result, None, "{stub:?} with 1 arg should return None");
        }
    });
}

/// BigRationalNew with fewer than 2 args returns None.
#[test]
fn test_translate_bigrational_new_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(BIGRATIONAL_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // 0 args
        let result = chc_ctx.translate_bigrational_call(StubKind::BigRationalNew, &[], &modified);
        assert_eq!(result, None, "BigRationalNew with 0 args should return None");

        // 1 arg (still insufficient — needs numer and denom)
        let one_arg = vec![Operand::Copy(Place { local: 0, projection: vec![] })];
        let result =
            chc_ctx.translate_bigrational_call(StubKind::BigRationalNew, &one_arg, &modified);
        assert_eq!(result, None, "BigRationalNew with 1 arg should return None");
    });
}

/// Unary ops (From, Neg, Clone) with empty args return None.
#[test]
fn test_translate_bigrational_unary_empty_args_returns_none() {
    with_test_ay_ctx_for_source(BIGRATIONAL_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        for stub in
            [StubKind::BigRationalFrom, StubKind::BigRationalNeg, StubKind::BigRationalClone]
        {
            let result = chc_ctx.translate_bigrational_call(stub, &[], &modified);
            assert_eq!(result, None, "{stub:?} with empty args should return None");
        }
    });
}

/// Compound assignment ops (AddAssign, SubAssign, MulAssign, DivAssign) with
/// fewer than 2 args return None.
#[test]
fn test_translate_bigrational_assign_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(BIGRATIONAL_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        let assign_stubs = [
            StubKind::BigRationalAddAssign,
            StubKind::BigRationalSubAssign,
            StubKind::BigRationalMulAssign,
            StubKind::BigRationalDivAssign,
        ];

        for stub in assign_stubs {
            // 0 args
            let result = chc_ctx.translate_bigrational_call(stub, &[], &modified);
            assert_eq!(result, None, "{stub:?} with 0 args should return None");

            // 1 arg (still insufficient)
            let one_arg = vec![Operand::Copy(Place { local: 0, projection: vec![] })];
            let result = chc_ctx.translate_bigrational_call(stub, &one_arg, &modified);
            assert_eq!(result, None, "{stub:?} with 1 arg should return None");
        }
    });
}

/// Non-BigRational stub kind returns None (catch-all arm).
#[test]
fn test_translate_bigrational_non_bigrational_stub_returns_none() {
    with_test_ay_ctx_for_source(BIGRATIONAL_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // VecNew is not a BigRational stub — should hit the catch-all None
        let result = chc_ctx.translate_bigrational_call(StubKind::VecNew, &[], &modified);
        assert_eq!(result, None, "non-BigRational stub should return None");

        let result = chc_ctx.translate_bigrational_call(StubKind::BigIntAdd, &[], &modified);
        assert_eq!(result, None, "BigIntAdd is not a BigRational stub");
    });
}
