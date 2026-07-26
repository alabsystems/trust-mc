// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC codegen_call_numeric.rs — BigInt and BigRational call codegen
//! through the mir_to_chc pipeline.
//!
//! Part of #2246 (wave 3 test coverage for decomposed chc/ files).
//! Exercises codegen_call_bigint, codegen_call_bigrational, and their
//! compound assignment / regular / sort-mismatch paths.

#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// BigInt compound assignment pipeline tests
// =============================================================================

/// Test BigInt compound AddAssign routes through codegen_bigint_compound_assign.
///
/// Exercises the is_compound_assign branch in codegen_call_bigint which calls
/// codegen_bigint_compound_assign instead of codegen_bigint_regular.
#[test]
fn test_bigint_add_assign_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        impl From<u64> for BigInt {
            fn from(val: u64) -> Self { BigInt(val) }
        }

        impl core::ops::AddAssign for BigInt {
            fn add_assign(&mut self, rhs: Self) {
                self.0 += rhs.0;
            }
        }

        pub fn probe_bigint_add_assign() -> BigInt {
            let mut a = BigInt::from(10u64);
            let b = BigInt::from(5u64);
            a += b;
            a
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_add_assign");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigint_add_assign", ChcConfig::default());
        let detected = collect_detected_bigint_stubs(&chc_ctx, &body);
        assert!(!detected.is_empty(), "probe should detect BigInt stubs (From + AddAssign)");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bigint_add_assign", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_bigint_add_assign", bb_count);
    });
}

/// Test BigInt compound SubAssign pipeline coverage.
#[test]
fn test_bigint_sub_assign_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        impl From<u64> for BigInt {
            fn from(val: u64) -> Self { BigInt(val) }
        }

        impl core::ops::SubAssign for BigInt {
            fn sub_assign(&mut self, rhs: Self) {
                self.0 -= rhs.0;
            }
        }

        pub fn probe_bigint_sub_assign() -> BigInt {
            let mut a = BigInt::from(20u64);
            let b = BigInt::from(3u64);
            a -= b;
            a
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_sub_assign");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigint_sub_assign", ChcConfig::default());
        let detected = collect_detected_bigint_stubs(&chc_ctx, &body);
        assert!(!detected.is_empty(), "probe should detect BigInt stubs (From + SubAssign)");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bigint_sub_assign", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_bigint_sub_assign", bb_count);
    });
}

// =============================================================================
// BigInt sort mismatch / fallback path tests
// =============================================================================

/// Test BigInt comparison returning bool triggers sort conversion
/// in codegen_bigint_regular (the is_bool → is_bool path at line 171).
#[test]
fn test_bigint_comparison_sort_conversion() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone, PartialOrd, PartialEq)]
        pub struct BigInt(u64);

        impl From<u64> for BigInt {
            fn from(val: u64) -> Self { BigInt(val) }
        }

        pub fn probe_bigint_lt(a: BigInt, b: BigInt) -> bool {
            a < b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_lt");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigint_lt", ChcConfig::default());
        let detected = collect_detected_bigint_stubs(&chc_ctx, &body);
        assert!(
            detected.contains(&StubKind::BigIntLt),
            "probe_bigint_lt should detect BigIntLt stub, detected: {:?}",
            detected
        );

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bigint_lt", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_bigint_lt", bb_count);
    });
}

/// Test BigInt Add call is detected and lowered through the normal bigint path.
#[test]
fn test_bigint_add_pipeline_detects_stub() {
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

        pub fn probe_bigint_add() -> BigInt {
            let a = BigInt::from(1u64);
            let b = BigInt::from(2u64);
            a + b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_add");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigint_add", ChcConfig::default());
        let detected = collect_detected_bigint_stubs(&chc_ctx, &body);
        assert!(
            detected.contains(&StubKind::BigIntAdd),
            "probe_bigint_add should detect BigIntAdd stub, detected: {:?}",
            detected
        );

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bigint_add", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_bigint_add", bb_count);
    });
}

// =============================================================================
// BigRational pipeline tests
// =============================================================================

/// Test BigRational addition routes through codegen_call_bigrational.
#[test]
fn test_bigrational_add_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigRational(u64, u64);

        impl core::ops::Add for BigRational {
            type Output = Self;
            fn add(self, rhs: Self) -> Self {
                BigRational(self.0 + rhs.0, self.1 + rhs.1)
            }
        }

        pub fn probe_bigrational_add() -> BigRational {
            let a = BigRational(1, 2);
            let b = BigRational(3, 4);
            a + b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigrational_add");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigrational_add", ChcConfig::default());
        let detected = collect_detected_bigrational_stubs(&chc_ctx, &body);
        assert!(
            detected.contains(&StubKind::BigRationalAdd),
            "probe_bigrational_add should detect BigRationalAdd stub, detected: {:?}",
            detected
        );

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bigrational_add", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_bigrational_add", bb_count);
    });
}

/// Test BigRational compound DivAssign exercises the compound_assign path.
#[test]
fn test_bigrational_div_assign_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigRational(u64, u64);

        impl core::ops::DivAssign for BigRational {
            fn div_assign(&mut self, rhs: Self) {
                self.0 /= rhs.0;
                self.1 /= rhs.1;
            }
        }

        pub fn probe_bigrational_div_assign() -> BigRational {
            let mut a = BigRational(10, 4);
            let b = BigRational(2, 2);
            a /= b;
            a
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigrational_div_assign");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_bigrational_div_assign", ChcConfig::default());
        let detected = collect_detected_bigrational_stubs(&chc_ctx, &body);
        assert!(
            detected.contains(&StubKind::BigRationalDivAssign),
            "probe_bigrational_div_assign should detect BigRationalDivAssign stub, detected: {:?}",
            detected
        );

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bigrational_div_assign", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_bigrational_div_assign", bb_count);
    });
}

/// Test BigRational comparison (PartialEq) exercises the bool→bitvec sort
/// conversion path in codegen_bigrational_regular.
#[test]
fn test_bigrational_eq_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone, PartialEq)]
        pub struct BigRational(u64, u64);

        pub fn probe_bigrational_eq(a: BigRational, b: BigRational) -> bool {
            a == b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigrational_eq");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigrational_eq", ChcConfig::default());
        let detected = collect_detected_bigrational_stubs(&chc_ctx, &body);
        assert!(
            detected.contains(&StubKind::BigRationalEq),
            "probe_bigrational_eq should detect BigRationalEq stub, detected: {:?}",
            detected
        );

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bigrational_eq", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_bigrational_eq", bb_count);
    });
}
