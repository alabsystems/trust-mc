// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Tests for stubs_impl.rs — type detection functions:
// detect_bigint_stub, detect_bigrational_stub, detect_collection_type,
// type_name_contains_bigint, type_name_contains_biguint,
// type_name_contains_bigrational, type_is_hashmap, deref_pointee_ty,
// resolve_callee_path.
//
// Part of #2188: CHC module test coverage.
//
// NOTE: Tests use local mock types (e.g., `struct BigInt(u64)`) because
// with_test_ay_ctx_for_source compiles minimal Rust without external crates.
// Type detection in stubs_impl.rs checks trimmed_name() matching, so local
// types named "BigInt" etc. trigger the same detection paths.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

// =============================================================================
// BigInt stub detection via local mock types
// =============================================================================

#[test]
fn test_detect_bigint_add_stub() {
    // Local BigInt with Add trait — should detect StubKind::BigIntAdd.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        impl core::ops::Add for BigInt {
            type Output = Self;
            fn add(self, rhs: Self) -> Self { BigInt(self.0 + rhs.0) }
        }

        pub fn probe_bigint_add(a: BigInt, b: BigInt) -> BigInt {
            a + b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_add");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigint_add", ChcConfig::default());
        let stubs = collect_detected_bigint_stubs(&chc_ctx, &body);

        assert!(
            stubs.iter().any(|s| matches!(s, StubKind::BigIntAdd)),
            "Should detect BigInt add stub, got: {:?}",
            stubs
        );
    });
}

#[test]
fn test_detect_bigint_mul_stub() {
    // Local BigInt with Mul trait — should detect StubKind::BigIntMul.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        impl core::ops::Mul for BigInt {
            type Output = Self;
            fn mul(self, rhs: Self) -> Self { BigInt(self.0 * rhs.0) }
        }

        pub fn probe_bigint_mul(a: BigInt, b: BigInt) -> BigInt {
            a * b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_mul");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigint_mul", ChcConfig::default());
        let stubs = collect_detected_bigint_stubs(&chc_ctx, &body);

        assert!(
            stubs.iter().any(|s| matches!(s, StubKind::BigIntMul)),
            "Should detect BigInt mul stub, got: {:?}",
            stubs
        );
    });
}

#[test]
fn test_detect_bigint_eq_stub() {
    // Local BigInt with PartialEq — should detect StubKind::BigIntEq.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        impl PartialEq for BigInt {
            fn eq(&self, other: &Self) -> bool { self.0 == other.0 }
        }

        pub fn probe_bigint_eq(a: &BigInt, b: &BigInt) -> bool {
            a == b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_eq");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigint_eq", ChcConfig::default());
        let stubs = collect_detected_bigint_stubs(&chc_ctx, &body);

        assert!(
            stubs.iter().any(|s| matches!(s, StubKind::BigIntEq)),
            "Should detect BigInt eq stub, got: {:?}",
            stubs
        );
    });
}

#[test]
fn test_detect_bigint_from_constructor() {
    // Local BigInt with From — should detect StubKind::BigIntFrom.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        impl From<u64> for BigInt {
            fn from(val: u64) -> Self { BigInt(val) }
        }

        pub fn probe_bigint_from() -> BigInt {
            BigInt::from(42u64)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_from");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigint_from", ChcConfig::default());
        let stubs = collect_detected_bigint_stubs(&chc_ctx, &body);

        assert!(
            stubs.iter().any(|s| matches!(s, StubKind::BigIntFrom)),
            "Should detect BigInt from constructor, got: {:?}",
            stubs
        );
    });
}

#[test]
fn test_detect_bigint_clone_stub() {
    // Local BigInt with Clone — should detect StubKind::BigIntClone.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct BigInt(u64);

        impl Clone for BigInt {
            fn clone(&self) -> Self { BigInt(self.0) }
        }

        pub fn probe_bigint_clone(a: &BigInt) -> BigInt {
            a.clone()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_clone");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigint_clone", ChcConfig::default());
        let stubs = collect_detected_bigint_stubs(&chc_ctx, &body);

        assert!(
            stubs.iter().any(|s| matches!(s, StubKind::BigIntClone)),
            "Should detect BigInt clone stub, got: {:?}",
            stubs
        );
    });
}

#[test]
fn test_no_bigint_stub_for_plain_function() {
    // Source with no BigInt types — should detect no stubs.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_no_bigint(a: u32, b: u32) -> u32 {
            a.wrapping_add(b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_no_bigint");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_no_bigint", ChcConfig::default());
        let stubs = collect_detected_bigint_stubs(&chc_ctx, &body);

        assert!(
            stubs.is_empty(),
            "Plain u32 function should detect no BigInt stubs, got: {:?}",
            stubs
        );
    });
}

// =============================================================================
// BigRational stub detection via local mock types
// =============================================================================

#[test]
fn test_detect_bigrational_add_stub() {
    // Local BigRational with Add — should detect StubKind::BigRationalAdd.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigRational(u64, u64);

        impl core::ops::Add for BigRational {
            type Output = Self;
            fn add(self, rhs: Self) -> Self { BigRational(self.0 + rhs.0, self.1) }
        }

        pub fn probe_bigrational_add(a: BigRational, b: BigRational) -> BigRational {
            a + b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigrational_add");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigrational_add", ChcConfig::default());
        let stubs = collect_detected_bigrational_stubs(&chc_ctx, &body);

        assert!(
            stubs.iter().any(|s| matches!(s, StubKind::BigRationalAdd)),
            "Should detect BigRational add stub, got: {:?}",
            stubs
        );
    });
}

#[test]
fn test_detect_bigrational_mul_stub() {
    // Local BigRational with Mul trait — should detect StubKind::BigRationalMul.
    // Detection needs BigRational-typed arguments, not just the type name on return.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigRational(u64, u64);

        impl core::ops::Mul for BigRational {
            type Output = Self;
            fn mul(self, rhs: Self) -> Self { BigRational(self.0 * rhs.0, self.1 * rhs.1) }
        }

        pub fn probe_bigrational_mul(a: BigRational, b: BigRational) -> BigRational {
            a * b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigrational_mul");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigrational_mul", ChcConfig::default());
        let stubs = collect_detected_bigrational_stubs(&chc_ctx, &body);

        assert!(
            stubs.iter().any(|s| matches!(s, StubKind::BigRationalMul)),
            "Should detect BigRational mul stub, got: {:?}",
            stubs
        );
    });
}

#[test]
fn test_no_bigrational_stub_for_plain_function() {
    // Source with no BigRational types — should detect no stubs.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_no_bigrational(a: f64, b: f64) -> f64 {
            a + b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_no_bigrational");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_no_bigrational", ChcConfig::default());
        let stubs = collect_detected_bigrational_stubs(&chc_ctx, &body);

        assert!(
            stubs.is_empty(),
            "Plain f64 function should detect no BigRational stubs, got: {:?}",
            stubs
        );
    });
}

// =============================================================================
// HashMap stub detection via local mock types
// =============================================================================

#[test]
fn test_detect_hashmap_insert_stub() {
    // Local HashMap with insert — should detect a HashMap stub.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct HashMap<K, V>(Option<(K, V)>);

        impl<K, V> HashMap<K, V> {
            pub fn insert(&mut self, k: K, v: V) -> Option<V> {
                let old = None;
                self.0 = Some((k, v));
                old
            }
        }

        pub fn probe_hashmap_insert(map: &mut HashMap<u32, u32>, k: u32, v: u32) {
            map.insert(k, v);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_insert");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashmap_insert", ChcConfig::default());
        let stubs = collect_detected_hashmap_stubs(&chc_ctx, &body);

        assert!(!stubs.is_empty(), "HashMap insert should be detected as a stub");
    });
}

#[test]
fn test_no_hashmap_stub_for_non_collection() {
    // A type NOT named HashMap/HashSet — should detect no stubs.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct MyMap(u32);

        impl MyMap {
            pub fn insert(&mut self, v: u32) { self.0 = v; }
        }

        pub fn probe_non_collection(m: &mut MyMap, v: u32) {
            m.insert(v);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_non_collection");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_non_collection", ChcConfig::default());
        let stubs = collect_detected_hashmap_stubs(&chc_ctx, &body);

        assert!(
            stubs.is_empty(),
            "Non-collection type should NOT be detected as HashMap stub, got: {:?}",
            stubs
        );
    });
}

// =============================================================================
// BigInt sub / neg detection
// =============================================================================

#[test]
fn test_detect_bigint_sub_stub() {
    // Local BigInt with Sub — should detect StubKind::BigIntSub.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigInt(u64);

        impl core::ops::Sub for BigInt {
            type Output = Self;
            fn sub(self, rhs: Self) -> Self { BigInt(self.0 - rhs.0) }
        }

        pub fn probe_bigint_sub(a: BigInt, b: BigInt) -> BigInt {
            a - b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bigint_sub");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_bigint_sub", ChcConfig::default());
        let stubs = collect_detected_bigint_stubs(&chc_ctx, &body);

        assert!(
            stubs.iter().any(|s| matches!(s, StubKind::BigIntSub)),
            "Should detect BigInt sub stub, got: {:?}",
            stubs
        );
    });
}

// =============================================================================
// BigUint detection (separate from BigInt)
// =============================================================================

#[test]
fn test_detect_biguint_add_stub() {
    // Local BigUint with Add — type_name_contains_bigint also matches BigUint.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct BigUint(u64);

        impl core::ops::Add for BigUint {
            type Output = Self;
            fn add(self, rhs: Self) -> Self { BigUint(self.0 + rhs.0) }
        }

        pub fn probe_biguint_add(a: BigUint, b: BigUint) -> BigUint {
            a + b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_biguint_add");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_biguint_add", ChcConfig::default());
        let stubs = collect_detected_bigint_stubs(&chc_ctx, &body);

        assert!(
            stubs.iter().any(|s| matches!(s, StubKind::BigIntAdd)),
            "Should detect BigUint add as BigInt stub, got: {:?}",
            stubs
        );
    });
}

// =============================================================================
// Numeric stub method table coverage
// =============================================================================

fn assert_table_sorted_unique(table: &[MethodStubSpec], table_name: &str) {
    for window in table.windows(2) {
        let prev = window[0].method;
        let next = window[1].method;
        assert!(
            prev < next,
            "{table_name} must be sorted with unique keys for binary search: {prev} !< {next}"
        );
    }
}

/// Part of #3850: user-defined `Rational` struct methods must NOT detect as BigRational stubs.
///
/// The `type_name_contains_bigrational` predicate matches `["BigRational", "Ratio"]`.
/// A bare `Rational` (user-defined) has trimmed_name "Rational" which matches neither,
/// so `detect_bigrational_stub` must return None for all its methods.
#[test]
fn test_bare_rational_not_detected_as_bigrational() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Copy, Clone)]
        pub struct Rational { pub num: i64, pub den: i64 }

        impl Rational {
            pub fn zero() -> Self { Rational { num: 0, den: 1 } }
            pub fn is_zero(&self) -> bool { self.num == 0 }
            pub fn add(self, rhs: Self) -> Self {
                Rational { num: self.num * rhs.den + rhs.num * self.den, den: self.den * rhs.den }
            }
        }

        impl core::ops::Add for Rational {
            type Output = Self;
            fn add(self, rhs: Self) -> Self { Rational::add(self, rhs) }
        }

        pub fn probe_rational_ops(a: Rational, b: Rational) -> Rational {
            let _z = Rational::zero();
            let _check = a.is_zero();
            a + b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_rational_ops");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_rational_ops", ChcConfig::default());
        let stubs = collect_detected_bigrational_stubs(&chc_ctx, &body);

        assert!(
            stubs.is_empty(),
            "Bare user-defined Rational must NOT detect as BigRational stubs, got: {:?}",
            stubs
        );
    });
}

#[test]
fn test_bigint_method_table_known_mappings() {
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "add"), Some(StubKind::BigIntAdd));
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "from"), Some(StubKind::BigIntFrom));
    assert_eq!(
        lookup_method_stub(BIGINT_METHOD_STUBS, "partial_cmp"),
        Some(StubKind::BigIntPartialCmp)
    );
    assert_table_sorted_unique(BIGINT_METHOD_STUBS, "BIGINT_METHOD_STUBS");
}

#[test]
fn test_bigrational_method_table_known_mappings() {
    assert_eq!(lookup_method_stub(BIGRATIONAL_METHOD_STUBS, "add"), Some(StubKind::BigRationalAdd));
    assert_eq!(lookup_method_stub(BIGRATIONAL_METHOD_STUBS, "new"), Some(StubKind::BigRationalNew));
    assert_eq!(
        lookup_method_stub(BIGRATIONAL_METHOD_STUBS, "mul_assign"),
        Some(StubKind::BigRationalMulAssign)
    );
    assert_table_sorted_unique(BIGRATIONAL_METHOD_STUBS, "BIGRATIONAL_METHOD_STUBS");
}

#[test]
fn test_numeric_method_table_unknown_method_returns_none() {
    assert_eq!(lookup_method_stub(BIGINT_METHOD_STUBS, "__unknown__"), None);
    assert_eq!(lookup_method_stub(BIGRATIONAL_METHOD_STUBS, "__unknown__"), None);
}
