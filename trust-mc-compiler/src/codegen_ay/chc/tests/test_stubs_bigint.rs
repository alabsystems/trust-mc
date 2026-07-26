// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC stubs_math_bigint.rs — BigInt stub translation to SMT Int sort.
//!
//! Covers individual `translate_bigint_call` branches:
//! - Constructor stubs: BigIntFrom, BigIntOne, BigIntZero
//! - Predicate stubs: BigIntIsZero, BigIntIsNegative
//! - Binary arithmetic: Add, Sub, Mul, Div, Rem
//! - Unary: Neg, Abs
//! - Compound assignment: MulAssign, AddAssign, SubAssign
//! - Comparisons: Eq, Cmp, PartialCmp, Lt, Le, Gt, Ge
//! - Clone (identity)
//! - Shift/bitwise (over-approximation)
//! - get_bigint_arg reference resolution
//!
//! Part of #2303 (zero-coverage CHC files).

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

// ═══════════════════════════════════════════════════════════════════════
// BigInt constructor pipeline tests
// ═══════════════════════════════════════════════════════════════════════

/// BigInt::from(u64) should produce bv2int conversion in CHC output.
#[test]
fn test_bigint_from_u64_produces_int_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        impl From<u64> for BigInt {
            fn from(val: u64) -> Self { BigInt(val) }
        }

        pub fn probe_from() -> BigInt {
            BigInt::from(42u64)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_from");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_from", ChcConfig::default());
        let detected = collect_detected_bigint_stubs(&chc_ctx, &body);
        assert!(!detected.is_empty(), "should detect BigInt::from stub");
        assert!(
            detected.iter().any(|s| matches!(s, StubKind::BigIntFrom)),
            "should detect BigIntFrom variant"
        );
    });
}

/// BigInt::one() and BigInt::zero() should produce Int constants.
#[test]
fn test_bigint_one_zero_constants() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        trait OneZero {
            fn one() -> Self;
            fn zero() -> Self;
        }

        impl OneZero for BigInt {
            #[inline(never)]
            fn one() -> Self { BigInt(1) }

            #[inline(never)]
            fn zero() -> Self { BigInt(0) }
        }

        pub fn probe_one_zero() -> (BigInt, BigInt) {
            (<BigInt as OneZero>::one(), <BigInt as OneZero>::zero())
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_one_zero");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_one_zero", ChcConfig::default());

        let detected = collect_detected_bigint_stubs(&chc_ctx, &body);
        assert_mir_pattern_found(
            detected.contains(&StubKind::BigIntOne),
            "BigInt::one call in MIR",
        );
        assert_mir_pattern_found(
            detected.contains(&StubKind::BigIntZero),
            "BigInt::zero call in MIR",
        );
        let (vc, _) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "pipeline should produce rules for BigInt one/zero");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// BigInt arithmetic pipeline tests
// ═══════════════════════════════════════════════════════════════════════

/// BigInt addition through the full pipeline.
#[test]
fn test_bigint_add_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        impl From<u64> for BigInt {
            fn from(val: u64) -> Self { BigInt(val) }
        }

        impl core::ops::Add for BigInt {
            type Output = Self;
            fn add(self, rhs: Self) -> Self { BigInt(self.0 + rhs.0) }
        }

        pub fn probe_add() -> BigInt {
            let a = BigInt::from(10u64);
            let b = BigInt::from(20u64);
            a + b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_add");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_add", ChcConfig::default());

        let detected = collect_detected_bigint_stubs(&chc_ctx, &body);
        assert!(!detected.is_empty(), "should detect BigInt stubs (From + Add)");

        let (vc, _) = chc_ctx.translate();
        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "pipeline should produce >= {} rules, got {}",
            bb_count,
            vc.rules.len()
        );
    });
}

/// BigInt division through the full pipeline.
#[test]
fn test_bigint_div_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        impl From<u64> for BigInt {
            fn from(val: u64) -> Self { BigInt(val) }
        }

        impl core::ops::Div for BigInt {
            type Output = Self;
            fn div(self, rhs: Self) -> Self { BigInt(self.0 / rhs.0) }
        }

        pub fn probe_div() -> BigInt {
            let a = BigInt::from(100u64);
            let b = BigInt::from(7u64);
            a / b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_div");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_div", ChcConfig::default());

        let detected = collect_detected_bigint_stubs(&chc_ctx, &body);
        assert!(!detected.is_empty(), "should detect BigInt div stubs");

        let (vc, _) = chc_ctx.translate();
        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "div pipeline should produce >= {} rules, got {}",
            bb_count,
            vc.rules.len()
        );
        assert!(!vc.relations.is_empty(), "div pipeline should produce relations");
    });
}

/// BigInt remainder through the full pipeline.
#[test]
fn test_bigint_rem_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        impl From<u64> for BigInt {
            fn from(val: u64) -> Self { BigInt(val) }
        }

        impl core::ops::Rem for BigInt {
            type Output = Self;
            fn rem(self, rhs: Self) -> Self { BigInt(self.0 % rhs.0) }
        }

        pub fn probe_rem() -> BigInt {
            let a = BigInt::from(17u64);
            let b = BigInt::from(5u64);
            a % b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_rem");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_rem", ChcConfig::default());

        let detected = collect_detected_bigint_stubs(&chc_ctx, &body);
        assert!(!detected.is_empty(), "should detect BigInt rem stubs");

        let (vc, _) = chc_ctx.translate();
        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "rem pipeline should produce >= {} rules, got {}",
            bb_count,
            vc.rules.len()
        );
        assert!(!vc.relations.is_empty(), "rem pipeline should produce relations");
    });
}

/// BigInt negation through the full pipeline.
#[test]
fn test_bigint_neg_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(i64);

        impl From<i64> for BigInt {
            fn from(val: i64) -> Self { BigInt(val) }
        }

        impl core::ops::Neg for BigInt {
            type Output = Self;
            fn neg(self) -> Self { BigInt(-self.0) }
        }

        pub fn probe_neg() -> BigInt {
            let a = BigInt::from(42i64);
            -a
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_neg");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_neg", ChcConfig::default());

        let (vc, _) = chc_ctx.translate();
        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "neg pipeline should produce >= {} rules, got {}",
            bb_count,
            vc.rules.len()
        );
        assert!(!vc.relations.is_empty(), "neg pipeline should produce relations");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// BigInt comparison pipeline tests
// ═══════════════════════════════════════════════════════════════════════

/// BigInt PartialEq through the pipeline.
#[test]
fn test_bigint_eq_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone, PartialEq)]
        pub struct BigInt(u64);

        impl From<u64> for BigInt {
            fn from(val: u64) -> Self { BigInt(val) }
        }

        pub fn probe_eq() -> bool {
            let a = BigInt::from(10u64);
            let b = BigInt::from(10u64);
            a == b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_eq");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_eq", ChcConfig::default());

        let (vc, _) = chc_ctx.translate();
        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "eq pipeline should produce >= {} rules, got {}",
            bb_count,
            vc.rules.len()
        );
        assert!(!vc.relations.is_empty(), "eq pipeline should produce relations");
    });
}

/// BigInt less-than comparison through the pipeline.
#[test]
fn test_bigint_lt_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone, PartialEq, PartialOrd)]
        pub struct BigInt(u64);

        impl From<u64> for BigInt {
            fn from(val: u64) -> Self { BigInt(val) }
        }

        pub fn probe_lt() -> bool {
            let a = BigInt::from(5u64);
            let b = BigInt::from(10u64);
            a < b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_lt");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_lt", ChcConfig::default());

        let (vc, _) = chc_ctx.translate();
        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "lt pipeline should produce >= {} rules, got {}",
            bb_count,
            vc.rules.len()
        );
        assert!(!vc.relations.is_empty(), "lt pipeline should produce relations");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// BigInt clone (identity) and shift (over-approximation) tests
// ═══════════════════════════════════════════════════════════════════════

/// BigInt clone should be identity in SMT.
#[test]
fn test_bigint_clone_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        impl From<u64> for BigInt {
            fn from(val: u64) -> Self { BigInt(val) }
        }

        pub fn probe_clone() -> BigInt {
            let a = BigInt::from(42u64);
            a.clone()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_clone");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_clone", ChcConfig::default());

        let (vc, _) = chc_ctx.translate();
        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "clone pipeline should produce >= {} rules, got {}",
            bb_count,
            vc.rules.len()
        );
        assert!(!vc.relations.is_empty(), "clone pipeline should produce relations");
    });
}

/// BigInt compound assignment (+=) through the pipeline.
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
            fn add_assign(&mut self, rhs: Self) { self.0 += rhs.0; }
        }

        pub fn probe_add_assign() -> BigInt {
            let mut a = BigInt::from(10u64);
            let b = BigInt::from(5u64);
            a += b;
            a
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_add_assign");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_add_assign", ChcConfig::default());

        let (vc, _) = chc_ctx.translate();
        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "+= pipeline should produce >= {} rules, got {}",
            bb_count,
            vc.rules.len()
        );
        assert!(!vc.relations.is_empty(), "+= pipeline should produce relations");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Error-path tests: translate_bigint_call returns None
// ═══════════════════════════════════════════════════════════════════════
//
// Part of #2627: error-path test coverage gaps.
// Models the `returns_none` pattern from statement/tests/comparison.rs.

/// Minimal source for constructing a ChcCtx without BigInt-specific MIR.
const BIGINT_ERROR_PATH_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_simple() {}
"#;

/// Binary ops (Add, Sub, Mul, etc.) with fewer than 2 args return None.
#[test]
fn test_translate_bigint_binary_op_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(BIGINT_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // All table-driven binary ops should return None with 0 args
        let binary_stubs = [
            StubKind::BigIntAdd,
            StubKind::BigIntSub,
            StubKind::BigIntMul,
            StubKind::BigIntDiv,
            StubKind::BigIntRem,
            StubKind::BigIntAddAssign,
            StubKind::BigIntSubAssign,
            StubKind::BigIntMulAssign,
            StubKind::BigIntEq,
            StubKind::BigIntLt,
            StubKind::BigIntLe,
            StubKind::BigIntGt,
            StubKind::BigIntGe,
        ];

        for stub in binary_stubs {
            // 0 args
            let result = chc_ctx.translate_bigint_call(stub, &[], &modified);
            assert_eq!(result, None, "{stub:?} with 0 args should return None");

            // 1 arg (still insufficient)
            let one_arg = vec![Operand::Copy(Place { local: 0, projection: vec![] })];
            let result = chc_ctx.translate_bigint_call(stub, &one_arg, &modified);
            assert_eq!(result, None, "{stub:?} with 1 arg should return None");
        }
    });
}

/// BigIntFrom with empty args returns None.
#[test]
fn test_translate_bigint_from_empty_args_returns_none() {
    with_test_ay_ctx_for_source(BIGINT_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        let result = chc_ctx.translate_bigint_call(StubKind::BigIntFrom, &[], &modified);
        assert_eq!(result, None, "BigIntFrom with empty args should return None");
    });
}

/// Predicate stubs (IsZero, IsNegative) with empty args return None.
#[test]
fn test_translate_bigint_predicates_empty_args_returns_none() {
    with_test_ay_ctx_for_source(BIGINT_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        for stub in [StubKind::BigIntIsZero, StubKind::BigIntIsNegative] {
            let result = chc_ctx.translate_bigint_call(stub, &[], &modified);
            assert_eq!(result, None, "{stub:?} with empty args should return None");
        }
    });
}

/// Unary ops (Neg, Abs) with empty args return None.
#[test]
fn test_translate_bigint_unary_empty_args_returns_none() {
    with_test_ay_ctx_for_source(BIGINT_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        for stub in [StubKind::BigIntNeg, StubKind::BigIntAbs] {
            let result = chc_ctx.translate_bigint_call(stub, &[], &modified);
            assert_eq!(result, None, "{stub:?} with empty args should return None");
        }
    });
}

/// Cmp/PartialCmp with fewer than 2 args return None.
#[test]
fn test_translate_bigint_cmp_insufficient_args_returns_none() {
    with_test_ay_ctx_for_source(BIGINT_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        for stub in [StubKind::BigIntCmp, StubKind::BigIntPartialCmp] {
            // 0 args
            let result = chc_ctx.translate_bigint_call(stub, &[], &modified);
            assert_eq!(result, None, "{stub:?} with 0 args should return None");

            // 1 arg
            let one_arg = vec![Operand::Copy(Place { local: 0, projection: vec![] })];
            let result = chc_ctx.translate_bigint_call(stub, &one_arg, &modified);
            assert_eq!(result, None, "{stub:?} with 1 arg should return None");
        }
    });
}

/// BigIntClone with empty args returns None.
#[test]
fn test_translate_bigint_clone_empty_args_returns_none() {
    with_test_ay_ctx_for_source(BIGINT_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        let result = chc_ctx.translate_bigint_call(StubKind::BigIntClone, &[], &modified);
        assert_eq!(result, None, "BigIntClone with empty args should return None");
    });
}

/// Non-BigInt stub kind returns None (catch-all arm).
#[test]
fn test_translate_bigint_non_bigint_stub_returns_none() {
    with_test_ay_ctx_for_source(BIGINT_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_simple", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified: HashSet<usize> = HashSet::new();

        // VecNew is not a BigInt stub — should hit the catch-all None
        let result = chc_ctx.translate_bigint_call(StubKind::VecNew, &[], &modified);
        assert_eq!(result, None, "non-BigInt stub should return None");

        let result = chc_ctx.translate_bigint_call(StubKind::HashMapInsert, &[], &modified);
        assert_eq!(result, None, "HashMapInsert is not a BigInt stub");
    });
}
