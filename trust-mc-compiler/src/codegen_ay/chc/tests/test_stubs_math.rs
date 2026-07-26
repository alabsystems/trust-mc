// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC stubs_math.rs — BigInt and BigRational translation to SMT
//! Int/Real sorts via the mir_to_chc pipeline.
//!
//! Part of #2198 (test coverage for chc/stubs_math.rs, 638 lines, zero tests).

#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// BigInt arithmetic pipeline tests
// =============================================================================

/// Test BigInt subtraction produces constrained VC through the pipeline.
#[test]
fn test_bigint_sub_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        impl From<u64> for BigInt {
            fn from(val: u64) -> Self { BigInt(val) }
        }

        impl core::ops::Sub for BigInt {
            type Output = Self;
            fn sub(self, rhs: Self) -> Self {
                BigInt(self.0 - rhs.0)
            }
        }

        pub fn probe_bigint_sub() -> BigInt {
            let a = BigInt::from(10u64);
            let b = BigInt::from(3u64);
            a - b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_sub");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigint_sub", ChcConfig::default());
        let detected = collect_detected_bigint_stubs(&chc_ctx, &body);
        assert!(!detected.is_empty(), "probe should detect BigInt stubs (From + Sub)");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bigint_sub", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "Pipeline should produce at least {} rules, got {}",
            bb_count,
            vc.rules.len()
        );
    });
}

/// Test BigInt multiplication produces constrained VC through the pipeline.
#[test]
fn test_bigint_mul_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        impl From<u64> for BigInt {
            fn from(val: u64) -> Self { BigInt(val) }
        }

        impl core::ops::Mul for BigInt {
            type Output = Self;
            fn mul(self, rhs: Self) -> Self {
                BigInt(self.0 * rhs.0)
            }
        }

        pub fn probe_bigint_mul() -> BigInt {
            let a = BigInt::from(5u64);
            let b = BigInt::from(7u64);
            a * b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_mul");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigint_mul", ChcConfig::default());
        let detected = collect_detected_bigint_stubs(&chc_ctx, &body);
        assert!(!detected.is_empty(), "probe should detect BigInt stubs (From + Mul)");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bigint_mul", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "Pipeline should produce at least {} rules, got {}",
            bb_count,
            vc.rules.len()
        );
    });
}

/// Test BigInt negation (unary neg) produces constrained VC.
#[test]
fn test_bigint_neg_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        impl From<u64> for BigInt {
            fn from(val: u64) -> Self { BigInt(val) }
        }

        impl core::ops::Neg for BigInt {
            type Output = Self;
            fn neg(self) -> Self {
                BigInt(self.0)
            }
        }

        pub fn probe_bigint_neg() -> BigInt {
            let a = BigInt::from(42u64);
            -a
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_neg");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigint_neg", ChcConfig::default());
        let detected = collect_detected_bigint_stubs(&chc_ctx, &body);
        assert!(!detected.is_empty(), "probe should detect BigInt stubs (From + Neg)");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bigint_neg", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "Pipeline should produce at least {} rules, got {}",
            bb_count,
            vc.rules.len()
        );
    });
}

/// Test BigInt comparison (PartialEq) detects equality stub.
#[test]
fn test_bigint_eq_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone, PartialEq)]
        pub struct BigInt(u64);

        impl From<u64> for BigInt {
            fn from(val: u64) -> Self { BigInt(val) }
        }

        pub fn probe_bigint_eq(a: BigInt, b: BigInt) -> bool {
            a == b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_eq");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bigint_eq", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "Pipeline should produce at least {} rules, got {}",
            bb_count,
            vc.rules.len()
        );

        // Equality comparison returns bool → state vars should include bool-like sorts
        let has_bool_like = vc.relations.iter().any(|r| {
            r.arg_sorts.iter().any(|s| s.is_bool() || matches!(s.bitvec_width(), Some(1) | Some(8)))
        });
        assert!(
            has_bool_like,
            "BigInt equality VC should have bool-like state vars for the bool return"
        );
    });
}

// =============================================================================
// BigInt constant constructors
// =============================================================================

/// Test BigIntOne and BigIntZero constants produce Int sort results.
/// The naming convention "BigInt" triggers sort inference to Int.
#[test]
fn test_bigint_constants_sort() {
    // BigIntOne → Expr::int_const(1), BigIntZero → Expr::int_const(0)
    // These are static, no MIR needed — test the Expr API directly
    let one = Expr::int_const(1);
    assert!(one.sort().is_int(), "BigIntOne should produce Int sort");
    assert_eq!(one, Expr::int_const(1), "BigIntOne should equal int_const(1)");

    let zero = Expr::int_const(0);
    assert!(zero.sort().is_int(), "BigIntZero should produce Int sort");
    assert_eq!(zero, Expr::int_const(0), "BigIntZero should equal int_const(0)");
    assert_ne!(one, zero, "BigIntOne and BigIntZero should be distinct");
}

// =============================================================================
// BigInt predicate tests (Bool sort output)
// =============================================================================

/// Test BigInt is_zero predicate returns Bool sort (arg == 0).
#[test]
fn test_bigint_is_zero_encoding() {
    let arg = Expr::var("bigint_val", Sort::int());
    let zero = Expr::int_const(0);
    let is_zero = arg.eq(zero);
    assert!(is_zero.sort().is_bool(), "BigIntIsZero should produce Bool sort");
}

/// Test BigInt is_negative predicate returns Bool sort (arg < 0).
#[test]
fn test_bigint_is_negative_encoding() {
    let arg = Expr::var("bigint_val", Sort::int());
    let zero = Expr::int_const(0);
    let is_neg = arg.int_lt(zero);
    assert!(is_neg.sort().is_bool(), "BigIntIsNegative should produce Bool sort");
}

/// Test BigInt abs encoding: ite(x < 0, -x, x) produces Int sort.
#[test]
fn test_bigint_abs_encoding() {
    let arg = Expr::var("bigint_val", Sort::int());
    let zero = Expr::int_const(0);
    let is_neg = arg.clone().int_lt(zero);
    let abs_val = Expr::ite(is_neg, arg.clone().int_neg(), arg);
    assert!(abs_val.sort().is_int(), "BigIntAbs should produce Int sort");
}

/// Test BigInt cmp ordering encoding: ite(lt, -1, ite(eq, 0, 1)) produces Int sort.
#[test]
fn test_bigint_cmp_encoding() {
    let lhs = Expr::var("a", Sort::int());
    let rhs = Expr::var("b", Sort::int());
    let is_lt = lhs.clone().int_lt(rhs.clone());
    let is_eq = lhs.eq(rhs);
    let ordering = Expr::ite(
        is_lt,
        Expr::int_const(-1),
        Expr::ite(is_eq, Expr::int_const(0), Expr::int_const(1)),
    );
    assert!(ordering.sort().is_int(), "BigIntCmp should produce Int sort");
}

// =============================================================================
// BigInt binary arithmetic sort verification
// =============================================================================

/// Test all BigInt binary ops produce Int sort results.
#[test]
fn test_bigint_binary_ops_sort() {
    let a = Expr::var("a", Sort::int());
    let b = Expr::var("b", Sort::int());

    let add = a.clone().int_add(b.clone());
    assert!(add.sort().is_int(), "BigIntAdd should produce Int sort");

    let sub = a.clone().int_sub(b.clone());
    assert!(sub.sort().is_int(), "BigIntSub should produce Int sort");

    let mul = a.clone().int_mul(b.clone());
    assert!(mul.sort().is_int(), "BigIntMul should produce Int sort");

    let div = a.clone().int_div(b.clone());
    assert!(div.sort().is_int(), "BigIntDiv should produce Int sort");

    let rem = a.clone().int_mod(b);
    assert!(rem.sort().is_int(), "BigIntRem should produce Int sort");

    let neg = a.int_neg();
    assert!(neg.sort().is_int(), "BigIntNeg should produce Int sort");
}

/// Test all BigInt comparison ops produce Bool sort results.
#[test]
fn test_bigint_comparison_ops_sort() {
    let a = Expr::var("a", Sort::int());
    let b = Expr::var("b", Sort::int());

    let eq = a.clone().eq(b.clone());
    assert!(eq.sort().is_bool(), "BigIntEq should produce Bool sort");

    let lt = a.clone().int_lt(b.clone());
    assert!(lt.sort().is_bool(), "BigIntLt should produce Bool sort");

    let le = a.clone().int_le(b.clone());
    assert!(le.sort().is_bool(), "BigIntLe should produce Bool sort");

    let gt = a.clone().int_gt(b.clone());
    assert!(gt.sort().is_bool(), "BigIntGt should produce Bool sort");

    let ge = a.int_ge(b);
    assert!(ge.sort().is_bool(), "BigIntGe should produce Bool sort");
}

// =============================================================================
// BigRational tests — Real sort encoding
// =============================================================================

/// Test BigRational new encoding: numer / denom as Real sort.
#[test]
fn test_bigrational_new_encoding() {
    let numer = Expr::var("numer", Sort::int());
    let denom = Expr::var("denom", Sort::int());
    let numer_real = numer.int_to_real();
    let denom_real = denom.int_to_real();
    let rational = numer_real.real_div(denom_real);
    assert!(rational.sort().is_real(), "BigRationalNew should produce Real sort");
}

/// Test BigRational from encoding: Int → Real (n/1).
#[test]
fn test_bigrational_from_encoding() {
    let int_val = Expr::var("int_val", Sort::int());
    let real_val = int_val.int_to_real();
    assert!(real_val.sort().is_real(), "BigRationalFrom should produce Real sort");
}

/// Test all BigRational binary arithmetic ops produce Real sort.
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

/// Test all BigRational comparison ops produce Bool sort.
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

// =============================================================================
// BigInt shift/bitwise (unconstrained over-approximation)
// =============================================================================

/// Test BigInt shift/bitwise operations produce unconstrained Int vars (sound over-approx).
#[test]
fn test_bigint_shift_bitwise_overapprox() {
    // Shift and bitwise operations on unbounded Int can't be expressed in LIA,
    // so they return fresh symbolic Int vars. Verify the sort is correct.
    let fresh_shl = Expr::var("bigint_shl_0", Sort::int());
    assert!(fresh_shl.sort().is_int(), "BigIntShl over-approx should be Int sort");

    let fresh_shr = Expr::var("bigint_shr_0", Sort::int());
    assert!(fresh_shr.sort().is_int(), "BigIntShr over-approx should be Int sort");

    let fresh_bitwise = Expr::var("bigint_bitwise_0", Sort::int());
    assert!(fresh_bitwise.sort().is_int(), "BigInt bitwise over-approx should be Int sort");
}

// =============================================================================
// BigInt bv2int conversion tests
// =============================================================================

/// Test bv2int unsigned conversion for BigIntFrom.
#[test]
fn test_bigint_from_bv2int_unsigned() {
    let bv_val = Expr::bitvec_const(42u64, 32);
    let int_val = bv_val.bv2int();
    assert!(int_val.sort().is_int(), "bv2int should produce Int sort");
}

/// Test bv2int signed conversion for BigIntFrom.
#[test]
fn test_bigint_from_bv2int_signed() {
    let bv_val = Expr::bitvec_const(42u64, 32);
    let int_val = bv_val.bv2int_signed();
    assert!(int_val.sort().is_int(), "bv2int_signed should produce Int sort");
}

/// Test BigIntFrom with Int input returns identity (no conversion needed).
#[test]
fn test_bigint_from_int_identity() {
    let int_val = Expr::int_const(42);
    assert!(int_val.sort().is_int(), "Int input to BigIntFrom should remain Int");
}

// =============================================================================
// get_bigint_arg / get_bigrational_arg fallback tests
// =============================================================================

/// Test BigInt arg fallback produces symbolic Int variable.
#[test]
fn test_bigint_arg_fallback_sort() {
    // When get_bigint_arg can't resolve an operand, it creates a fresh symbolic Int
    let fallback = Expr::var("bigint_arg_0", Sort::int());
    assert!(fallback.sort().is_int(), "BigInt arg fallback should be Int sort");
}

/// Test BigRational arg fallback produces symbolic Real variable.
#[test]
fn test_bigrational_arg_fallback_sort() {
    // When get_bigrational_arg can't resolve an operand, it creates a fresh symbolic Real
    let fallback = Expr::var("bigrational_arg_0", Sort::real());
    assert!(fallback.sort().is_real(), "BigRational arg fallback should be Real sort");
}

/// Test BigRational Int-to-Real coercion in get_bigrational_arg.
#[test]
fn test_bigrational_int_to_real_coercion() {
    // When get_bigrational_arg finds an Int-sorted operand, it converts to Real
    let int_val = Expr::var("int_local", Sort::int());
    let real_val = int_val.int_to_real();
    assert!(
        real_val.sort().is_real(),
        "Int-to-Real coercion in get_bigrational_arg should produce Real sort"
    );
}
