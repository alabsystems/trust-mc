// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test code: unwrap is acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// BigInt detection — normal path (Part of #2187)
// Exercises detect_bigint_stub for BigInt constructor paths.
// Normal path: BigInt stubs are detected without triggering skip.
// =============================================================================

#[test]
fn test_bigint_detection_normal_path_no_skip() {
    use super::super::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        impl From<u64> for BigInt {
            fn from(val: u64) -> Self { BigInt(val) }
        }

        pub trait One { fn one() -> Self; }
        impl One for BigInt {
            fn one() -> Self { BigInt(1) }
        }

        pub fn probe_bigint_detect() -> BigInt {
            let a = BigInt::from(42u64);
            let _b = <BigInt as One>::one();
            a
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_detect");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigint_detect", ChcConfig::default());

        let skip_before = GLOBAL_COUNTERS.bigint_unsound_skip.load(Ordering::Relaxed);
        let detected = collect_detected_bigint_stubs(&chc_ctx, &body);
        let skip_after = GLOBAL_COUNTERS.bigint_unsound_skip.load(Ordering::Relaxed);

        // Detection alone should NOT increment the unsound skip counter
        assert_eq!(
            skip_before, skip_after,
            "BigInt detection should not increment UNSOUND_SKIP_COUNT"
        );
        // Should detect at least one BigInt stub
        assert!(!detected.is_empty(), "Should detect at least one BigInt stub in MIR");
    });
}

// =========================================================================
// BigInt Stub Detection Tests (#1902)
// =========================================================================
//
// Tests for `ChcCtx::detect_bigint_stub` regression coverage.
// Per designs/2026-02-02-bigint-stub-detection-tests.md
//
// Since with_test_ay_ctx_for_source doesn't pass --extern, we define local
// `BigInt`/`BigUint` structs. Detection uses trimmed_name(), so local types
// with these names trigger detection.

#[test]
fn test_detect_bigint_stub_constructors() {
    // Test that BigInt constructors (from, one, zero) are detected.
    // Detection requires BigInt in generic args. For inherent methods, use trait impls.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        // Use From trait so generic args contain BigInt
        impl From<u64> for BigInt {
            fn from(val: u64) -> Self { BigInt(val) }
        }

        // Use traits that have Self in generic args
        pub trait One { fn one() -> Self; }
        pub trait Zero { fn zero() -> Self; }

        impl One for BigInt {
            fn one() -> Self { BigInt(1) }
        }

        impl Zero for BigInt {
            fn zero() -> Self { BigInt(0) }
        }

        pub fn probe_bigint_constructors() -> BigInt {
            let a = BigInt::from(42u64);
            let _b = <BigInt as One>::one();
            let _c = <BigInt as Zero>::zero();
            a
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_constructors");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_bigint_constructors", ChcConfig::default());

        let detected = collect_detected_bigint_stubs(&chc_ctx, &body);

        // We expect BigIntFrom, BigIntOne, BigIntZero to be detected
        assert!(
            detected.contains(&StubKind::BigIntFrom),
            "BigInt::from should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigIntOne),
            "BigInt::one should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigIntZero),
            "BigInt::zero should be detected; got: {:?}",
            detected
        );
    });
}

#[test]
fn test_detect_bigint_stub_arithmetic_ops() {
    // Test that BigInt arithmetic operators (add, sub, mul, div, neg, abs) are detected.
    // Per design doc: cover operator/method detection via argument types.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(i64);

        impl std::ops::Add for BigInt {
            type Output = Self;
            fn add(self, rhs: Self) -> Self { BigInt(self.0 + rhs.0) }
        }

        impl std::ops::Sub for BigInt {
            type Output = Self;
            fn sub(self, rhs: Self) -> Self { BigInt(self.0 - rhs.0) }
        }

        impl std::ops::Mul for BigInt {
            type Output = Self;
            fn mul(self, rhs: Self) -> Self { BigInt(self.0 * rhs.0) }
        }

        impl std::ops::Div for BigInt {
            type Output = Self;
            fn div(self, rhs: Self) -> Self { BigInt(self.0 / rhs.0) }
        }

        impl std::ops::Neg for BigInt {
            type Output = Self;
            fn neg(self) -> Self { BigInt(-self.0) }
        }

        impl BigInt {
            pub fn abs(self) -> Self { BigInt(self.0.abs()) }
        }

        pub fn probe_bigint_arithmetic(a: BigInt, b: BigInt) -> BigInt {
            let sum = a + b;
            let diff = sum - b;
            let prod = diff * b;
            let quot = prod / b;
            let negated = -quot;
            negated.abs()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_arithmetic");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigint_arithmetic", ChcConfig::default());

        let detected = collect_detected_bigint_stubs(&chc_ctx, &body);

        // Check arithmetic operations are detected
        assert!(
            detected.contains(&StubKind::BigIntAdd),
            "BigInt::add should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigIntSub),
            "BigInt::sub should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigIntMul),
            "BigInt::mul should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigIntDiv),
            "BigInt::div should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigIntNeg),
            "BigInt::neg should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigIntAbs),
            "BigInt::abs should be detected; got: {:?}",
            detected
        );
    });
}

#[test]
fn test_detect_bigint_stub_biguint_gate() {
    // Test that BigUint types also trigger detection.
    // Per design doc: cover BigUint equivalently (same detection gate).
    // Detection uses argument types for Add, and generic args for From trait.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigUint(u64);

        impl From<u64> for BigUint {
            fn from(val: u64) -> Self { BigUint(val) }
        }

        impl std::ops::Add for BigUint {
            type Output = Self;
            fn add(self, rhs: Self) -> Self { BigUint(self.0 + rhs.0) }
        }

        pub fn probe_biguint(val: u64) -> BigUint {
            let a = BigUint::from(val);
            let b = BigUint::from(1);
            a + b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_biguint");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_biguint", ChcConfig::default());

        let detected = collect_detected_bigint_stubs(&chc_ctx, &body);

        // BigUint should trigger the same detection as BigInt
        assert!(
            detected.contains(&StubKind::BigIntFrom),
            "BigUint::from should be detected (uses BigInt stubs); got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigIntAdd),
            "BigUint::add should be detected (uses BigInt stubs); got: {:?}",
            detected
        );
    });
}

#[test]
fn test_detect_bigint_stub_ignores_non_bigint_types() {
    // Test that types with similar method names but NOT named BigInt/BigUint are ignored.
    // Per design doc: include negative test proving non-BigInt types are not detected.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        // NotBigInt has same method names but should NOT be detected
        pub struct NotBigInt(i64);

        impl NotBigInt {
            pub fn from(val: i64) -> Self { NotBigInt(val) }
            pub fn one() -> Self { NotBigInt(1) }
            pub fn zero() -> Self { NotBigInt(0) }
        }

        impl std::ops::Add for NotBigInt {
            type Output = Self;
            fn add(self, rhs: Self) -> Self { NotBigInt(self.0 + rhs.0) }
        }

        pub fn probe_not_bigint() -> NotBigInt {
            let a = NotBigInt::from(42);
            let b = NotBigInt::one();
            let _c = NotBigInt::zero();
            a + b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_not_bigint");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_not_bigint", ChcConfig::default());

        let detected = collect_detected_bigint_stubs(&chc_ctx, &body);

        // NotBigInt methods should NOT be detected
        assert!(
            detected.is_empty(),
            "NotBigInt should not trigger BigInt detection; got: {:?}",
            detected
        );
    });
}

// =========================================================================
// BigInt Comparison Detection Tests (Part of #1674)
// =========================================================================

#[test]
fn test_detect_bigint_stub_comparison_ops() {
    // Test that BigInt comparison operators (eq, lt, le, gt, ge) are detected.
    // We assert the five stable comparison stubs directly.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(i64);

        impl PartialEq for BigInt {
            fn eq(&self, other: &Self) -> bool { self.0 == other.0 }
        }

        impl PartialOrd for BigInt {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                self.0.partial_cmp(&other.0)
            }
            fn lt(&self, other: &Self) -> bool { self.0 < other.0 }
            fn le(&self, other: &Self) -> bool { self.0 <= other.0 }
            fn gt(&self, other: &Self) -> bool { self.0 > other.0 }
            fn ge(&self, other: &Self) -> bool { self.0 >= other.0 }
        }

        impl Eq for BigInt {}
        impl Ord for BigInt {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering { self.0.cmp(&other.0) }
        }

        pub fn probe_bigint_comparisons(a: BigInt, b: BigInt) -> bool {
            let _ = a.eq(&b);
            let _ = a.lt(&b);
            let _ = a.le(&b);
            let _ = a.gt(&b);
            let _ = a.ge(&b);
            let _ = a.partial_cmp(&b);
            let _ = a.cmp(&b);
            a == b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_comparisons");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigint_comparisons", ChcConfig::default());

        let detected = collect_detected_bigint_stubs(&chc_ctx, &body);

        assert!(
            detected.contains(&StubKind::BigIntEq),
            "BigInt::eq should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigIntLt),
            "BigInt::lt should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigIntLe),
            "BigInt::le should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigIntGt),
            "BigInt::gt should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigIntGe),
            "BigInt::ge should be detected; got: {:?}",
            detected
        );
    });
}

// =========================================================================
// BigRational Stub Detection Tests (Part of #1674)
// =========================================================================

#[test]
fn test_detect_bigrational_stub_constructors() {
    // Test that BigRational constructors (new, from) are detected.
    // Detection uses type_name_contains_bigrational which matches "BigRational", "Ratio".
    //
    // Note: Inherent methods on local structs (like `BigRational::new`) get inlined by
    // rustc's MIR optimizer even with #[inline(never)], eliminating the Call terminator
    // that detect_bigrational_stub scans. Trait method calls survive MIR inlining because
    // trait dispatch prevents devirtualization in the caller's MIR. This test uses a
    // `New` trait to exercise the "new" short-name detection path.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(i64);

        #[derive(Copy, Clone)]
        pub struct BigRational { numer: BigInt, denom: BigInt }

        pub trait New<A, B> { fn new(a: A, b: B) -> Self; }

        impl New<BigInt, BigInt> for BigRational {
            fn new(n: BigInt, d: BigInt) -> Self { BigRational { numer: n, denom: d } }
        }

        impl From<BigInt> for BigRational {
            fn from(val: BigInt) -> Self { BigRational { numer: val, denom: BigInt(1) } }
        }

        pub fn probe_bigrational_constructors() -> BigRational {
            let n = BigInt(3);
            let d = BigInt(4);
            let a = <BigRational as New<BigInt, BigInt>>::new(n, d);
            let _b = BigRational::from(n);
            a
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigrational_constructors");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_bigrational_constructors", ChcConfig::default());

        let detected = collect_detected_bigrational_stubs(&chc_ctx, &body);

        assert!(
            detected.contains(&StubKind::BigRationalNew),
            "BigRational::new should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigRationalFrom),
            "BigRational::from should be detected; got: {:?}",
            detected
        );
    });
}

#[test]
fn test_detect_bigrational_stub_arithmetic_ops() {
    // Test that BigRational arithmetic operators are detected.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigRational(i64);

        impl std::ops::Add for BigRational {
            type Output = Self;
            fn add(self, rhs: Self) -> Self { BigRational(self.0 + rhs.0) }
        }

        impl std::ops::Sub for BigRational {
            type Output = Self;
            fn sub(self, rhs: Self) -> Self { BigRational(self.0 - rhs.0) }
        }

        impl std::ops::Mul for BigRational {
            type Output = Self;
            fn mul(self, rhs: Self) -> Self { BigRational(self.0 * rhs.0) }
        }

        impl std::ops::Div for BigRational {
            type Output = Self;
            fn div(self, rhs: Self) -> Self { BigRational(self.0 / rhs.0) }
        }

        impl std::ops::Neg for BigRational {
            type Output = Self;
            fn neg(self) -> Self { BigRational(-self.0) }
        }

        pub fn probe_bigrational_arithmetic(a: BigRational, b: BigRational) -> BigRational {
            let sum = a + b;
            let diff = sum - b;
            let prod = diff * b;
            let quot = prod / b;
            -quot
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigrational_arithmetic");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_bigrational_arithmetic", ChcConfig::default());

        let detected = collect_detected_bigrational_stubs(&chc_ctx, &body);

        assert!(
            detected.contains(&StubKind::BigRationalAdd),
            "BigRational::add should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigRationalSub),
            "BigRational::sub should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigRationalMul),
            "BigRational::mul should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigRationalDiv),
            "BigRational::div should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigRationalNeg),
            "BigRational::neg should be detected; got: {:?}",
            detected
        );
    });
}

#[test]
fn test_detect_bigrational_stub_comparison_ops() {
    // Test that BigRational comparison operators are detected.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigRational(i64);

        impl PartialEq for BigRational {
            fn eq(&self, other: &Self) -> bool { self.0 == other.0 }
        }

        impl PartialOrd for BigRational {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                self.0.partial_cmp(&other.0)
            }
            fn lt(&self, other: &Self) -> bool { self.0 < other.0 }
            fn le(&self, other: &Self) -> bool { self.0 <= other.0 }
            fn gt(&self, other: &Self) -> bool { self.0 > other.0 }
            fn ge(&self, other: &Self) -> bool { self.0 >= other.0 }
        }

        pub fn probe_bigrational_comparisons(a: BigRational, b: BigRational) -> bool {
            let _ = a.eq(&b);
            let _ = a.lt(&b);
            let _ = a.le(&b);
            let _ = a.gt(&b);
            let _ = a.ge(&b);
            a == b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigrational_comparisons");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_bigrational_comparisons", ChcConfig::default());

        let detected = collect_detected_bigrational_stubs(&chc_ctx, &body);

        assert!(
            detected.contains(&StubKind::BigRationalEq),
            "BigRational::eq should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigRationalLt),
            "BigRational::lt should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigRationalLe),
            "BigRational::le should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigRationalGt),
            "BigRational::gt should be detected; got: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::BigRationalGe),
            "BigRational::ge should be detected; got: {:?}",
            detected
        );
    });
}

#[test]
fn test_detect_bigrational_stub_ignores_non_bigrational_types() {
    // Test that types not named BigRational/Ratio/Rational are not detected.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct MyFraction(i64, i64);

        impl MyFraction {
            pub fn new(n: i64, d: i64) -> Self { MyFraction(n, d) }
        }

        impl std::ops::Add for MyFraction {
            type Output = Self;
            fn add(self, rhs: Self) -> Self { MyFraction(self.0 + rhs.0, self.1) }
        }

        pub fn probe_not_bigrational() -> MyFraction {
            let a = MyFraction::new(1, 2);
            let b = MyFraction::new(3, 4);
            a + b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_not_bigrational");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_not_bigrational", ChcConfig::default());

        let detected = collect_detected_bigrational_stubs(&chc_ctx, &body);

        assert!(
            detected.is_empty(),
            "MyFraction should not trigger BigRational detection; got: {:?}",
            detected
        );
    });
}

#[test]
fn test_detect_bigrational_stub_ratio_name_triggers_detection() {
    // Verify that "Ratio" type name triggers BigRational detection.
    // num_rational uses Ratio<T> as the underlying type for BigRational.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct Ratio(i64, i64);

        impl std::ops::Add for Ratio {
            type Output = Self;
            fn add(self, rhs: Self) -> Self { Ratio(self.0 + rhs.0, self.1) }
        }

        pub fn probe_ratio(a: Ratio, b: Ratio) -> Ratio {
            a + b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ratio");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ratio", ChcConfig::default());

        let detected = collect_detected_bigrational_stubs(&chc_ctx, &body);

        assert!(
            detected.contains(&StubKind::BigRationalAdd),
            "Ratio::add should trigger BigRational detection; got: {:?}",
            detected
        );
    });
}

// =========================================================================
// type_is_hashmap / type_name_contains_biguint predicate tests (Part of #1674)
// =========================================================================

#[test]
fn test_type_name_contains_biguint_positive() {
    // Verify BigUint type is recognized by the predicate.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct BigUint(u64);

        fn takes_biguint(a: BigUint, b: &BigUint) {
            let _ = (a, b);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "takes_biguint");
        let args = fn_sig.inputs();

        assert!(
            ChcCtx::type_name_contains_biguint(&args[0]),
            "BigUint should be detected by type_name_contains_biguint"
        );
        assert!(
            ChcCtx::type_name_contains_biguint(&args[1]),
            "&BigUint should be detected through reference"
        );
    });
}

#[test]
fn test_type_name_contains_biguint_negative() {
    // Verify non-BigUint types are rejected.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct MyUint(u64);
        pub struct BigInt(i64);

        fn takes_non_biguint(a: MyUint, b: BigInt, c: u64) {
            let _ = (a, b, c);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "takes_non_biguint");
        let args = fn_sig.inputs();

        assert!(
            !ChcCtx::type_name_contains_biguint(&args[0]),
            "MyUint should not match type_name_contains_biguint"
        );
        assert!(
            !ChcCtx::type_name_contains_biguint(&args[1]),
            "BigInt should not match type_name_contains_biguint"
        );
        assert!(
            !ChcCtx::type_name_contains_biguint(&args[2]),
            "u64 should not match type_name_contains_biguint"
        );
    });
}

// =============================================================================
// BigInt pipeline normal-path — codegen_call_numeric.rs (Part of #2187)
// Exercises codegen_call_bigint → translate_bigint_call → codegen_bigint_regular
// through mir_to_chc(). Mock BigInt wraps u64, but declare_block_relations()
// recognizes "BigInt" in the type name and maps locals to Int sort (codegen_decl.rs:71).
// translate_bigint_call also returns Int → sort match → normal constrained path.
// =============================================================================

/// Test BigInt normal path through the full mir_to_chc pipeline.
/// Mock BigInt(u64) gets Int sort from declare_block_relations (name-based recognition).
/// translate_bigint_call returns Int for BigIntFrom. Sort matches → no skip counter
/// increment. Validates the happy path produces constrained VCs.
#[test]
fn test_bigint_pipeline_normal_path_no_skip() {
    use super::super::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        impl From<u64> for BigInt {
            fn from(val: u64) -> Self { BigInt(val) }
        }

        pub fn probe_bigint_normal_pipeline() -> BigInt {
            BigInt::from(42u64)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_normal_pipeline");
        let body = instance.body().expect("function body");

        // Verify BigInt stubs are actually detected in this probe
        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_bigint_normal_pipeline", ChcConfig::default());
        let detected = collect_detected_bigint_stubs(&chc_ctx, &body);
        assert!(!detected.is_empty(), "probe should detect at least one BigInt stub");

        let skip_before = GLOBAL_COUNTERS.bigint_unsound_skip.load(Ordering::Relaxed);

        // Run the full pipeline. declare_block_relations() maps BigInt locals to
        // Int sort (codegen_decl.rs:71), and translate_bigint_call returns Int for
        // BigIntFrom. Sort match → codegen_bigint_regular takes the normal path.
        let vc = mir_to_chc(ctx.tcx, &body, "probe_bigint_normal_pipeline", ChcConfig::default());

        let skip_after = GLOBAL_COUNTERS.bigint_unsound_skip.load(Ordering::Relaxed);

        // Normal path: BigInt locals mapped to Int by sort inference, translate
        // returns Int, sorts match → no skip counter increment.
        assert_eq!(
            skip_before, skip_after,
            "BigInt normal path should NOT increment BIGINT_UNSOUND_SKIP_COUNT; \
             stubs={:?}, before={}, after={}",
            detected, skip_before, skip_after
        );

        // Pipeline should produce non-trivial VCs (rules for all BBs)
        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "Pipeline should produce at least {} rules (one per BB), got {}",
            bb_count,
            vc.rules.len()
        );
    });
}

/// Test BigInt add normal path through mir_to_chc.
/// Both BigIntFrom and BigIntAdd produce Int sort results.
/// declare_block_relations maps BigInt locals to Int sort (name-based).
/// Sort match → codegen_bigint_regular normal path → no skip.
#[test]
fn test_bigint_pipeline_add_normal_path() {
    use super::super::GLOBAL_COUNTERS;
    use std::sync::atomic::Ordering;

    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        impl From<u64> for BigInt {
            fn from(val: u64) -> Self { BigInt(val) }
        }

        impl core::ops::Add for BigInt {
            type Output = Self;
            fn add(self, rhs: Self) -> Self {
                BigInt(self.0 + rhs.0)
            }
        }

        pub fn probe_bigint_add_normal() -> BigInt {
            let a = BigInt::from(1u64);
            let b = BigInt::from(2u64);
            a + b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_add_normal");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigint_add_normal", ChcConfig::default());
        let detected = collect_detected_bigint_stubs(&chc_ctx, &body);
        assert!(
            !detected.is_empty(),
            "probe should detect BigInt stubs (From + Add); got: {:?}",
            detected
        );

        let skip_before = GLOBAL_COUNTERS.bigint_unsound_skip.load(Ordering::Relaxed);

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bigint_add_normal", ChcConfig::default());

        let skip_after = GLOBAL_COUNTERS.bigint_unsound_skip.load(Ordering::Relaxed);

        // Normal path: BigInt locals mapped to Int by sort inference,
        // translate returns Int, sorts match → no skip.
        assert_eq!(
            skip_before, skip_after,
            "BigInt add normal path should NOT increment BIGINT_UNSOUND_SKIP_COUNT; \
             stubs={:?}, before={}, after={}",
            detected, skip_before, skip_after
        );

        // Pipeline should produce non-trivial VCs
        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "Pipeline should produce at least {} rules, got {}",
            bb_count,
            vc.rules.len()
        );
    });
}
