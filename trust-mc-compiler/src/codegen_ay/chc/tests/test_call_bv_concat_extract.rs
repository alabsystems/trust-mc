// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC inline handling of Bits::extract and Bits::concat patterns
//! from the `bv_concat_extract_roundtrip` smoke harness.
//!
//! Part of #3903 (BV concat/extract inferable predicate investigation).
//! Extracted from test_call_vec_ops.rs to stay under file size limits.

#![allow(clippy::unwrap_used)]

use super::common::*;

fn reset_slice_to_vec_roundtrip_counters() {
    let _ = crate::codegen_ay::take_inferable_predicate_count();
    let _ = crate::codegen_ay::take_unhandled_call_by_fn();
}

/// Part of #3903: Diagnose which calls become inferable predicates when
/// `Bits::extract` is called through a harness (not directly inlined).
#[test]
fn test_bits_extract_inferable_predicate_diagnostic() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone, Debug, PartialEq, Eq)]
        pub struct Bits(Vec<bool>);

        impl Bits {
            fn width(&self) -> usize { self.0.len() }

            fn extract(&self, high: usize, low: usize) -> Self {
                assert!(high < self.width());
                assert!(low <= high);
                Self(self.0[low..=high].to_vec())
            }
        }

        pub fn probe_bits_extract() {
            let bits = Bits(vec![true, false, true, false]);
            let extracted = bits.extract(2, 1);
            assert_eq!(extracted, Bits(vec![false, true]));
        }
    "#;

    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_slice_to_vec_roundtrip_counters();

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_name = "probe_bits_extract";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());

        let inferable_decls: Vec<_> = vc
            .decls
            .iter()
            .filter_map(|decl| match decl {
                trust_mc_core::decl::Decl::Fun { name, .. } if name.starts_with("P_inf_") => {
                    Some(name.as_str())
                }
                _ => None,
            })
            .collect();

        let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
        let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();

        // Part of #3903: After walker fallback + slice::to_vec recovery,
        // extract should not produce inferable predicates.
        assert!(
            inferable_decls.is_empty(),
            "{fn_name} should not emit P_inf_* after #3903 walker fallback: {inferable_decls:?}"
        );
        assert_eq!(
            inferable_count, 0,
            "{fn_name} inferable_predicate should be 0, unhandled={unhandled_calls:?}"
        );
    });

    reset_slice_to_vec_roundtrip_counters();
}

/// Part of #3903: Diagnose which calls produce inferable predicates for
/// concat+extract paths. Previous tests proved `Bits::extract` and
/// `Bits::from_u64` inline cleanly; this test covers concat+extract together.
///
/// Uses pre-built vec literals instead of `from_u64` loops to keep
/// `mir_to_chc` fast (from_u64 loop coverage is in the dedicated tests below).
#[test]
fn test_bits_concat_extract_full_inferable_diagnostic() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone, Debug, PartialEq, Eq)]
        pub struct Bits(Vec<bool>);

        impl Bits {
            fn width(&self) -> usize { self.0.len() }

            fn concat(&self, other: &Self) -> Self {
                let mut bits = other.0.clone();
                bits.extend_from_slice(&self.0);
                Self(bits)
            }

            fn extract(&self, high: usize, low: usize) -> Self {
                assert!(high < self.width());
                assert!(low <= high);
                Self(self.0[low..=high].to_vec())
            }
        }

        pub fn probe_concat_extract() {
            let ba = Bits(vec![true, false, true, false]);
            let bb = Bits(vec![true, true, false, false]);
            let concatenated = ba.concat(&bb);
            let extracted_low = concatenated.extract(3, 0);
            assert_eq!(extracted_low, bb);
            let extracted_high = concatenated.extract(7, 4);
            assert_eq!(extracted_high, ba);
        }
    "#;

    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_slice_to_vec_roundtrip_counters();

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_name = "probe_concat_extract";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());

        let inferable_decls: Vec<_> = vc
            .decls
            .iter()
            .filter_map(|decl| match decl {
                trust_mc_core::decl::Decl::Fun { name, .. } if name.starts_with("P_inf_") => {
                    Some(name.as_str())
                }
                _ => None,
            })
            .collect();

        let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
        let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();

        // Production encoding now inlines all paths including from_u64 loops,
        // so no inferable predicates remain. DT→BV flatten generalization
        // (378bea4a4c) means from_u64's Bits(Vec<bool>) is also fully inlined.
        assert_eq!(
            inferable_count, 0,
            "concat_extract should have 0 inferable predicates after encoding improvements, \
             got {inferable_count}; inferable_decls={inferable_decls:?}, unhandled={unhandled_calls:?}"
        );
        assert_eq!(
            inferable_decls.len(),
            0,
            "all paths now fully inlined — no P_inf_ declarations expected: {inferable_decls:?}"
        );
    });

    reset_slice_to_vec_roundtrip_counters();
}

/// Part of #3903 D1: Source-parity regression for the direct `from_u64` call
/// using the REAL harness shape (`for i in 0..width`) instead of the synthetic
/// `while i < width` loop. Rust lowers `for i in 0..width` to a
/// `Range { start: 0, end: width }` MIR aggregate — recognized by
/// `detect_for_range_push` in the vec_builder dispatcher.
#[test]
fn test_bits_from_u64_for_loop_direct_parity() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Bits(Vec<bool>);

        impl Bits {
            fn from_u64(value: u64, width: usize) -> Self {
                let mut bits = Vec::with_capacity(width);
                for i in 0..width {
                    bits.push(if i < 64 {
                        (value >> i) & 1 == 1
                    } else {
                        false
                    });
                }
                Self(bits)
            }
        }

        pub fn probe_bits_from_u64(value: u64, width: usize) -> Bits {
            Bits::from_u64(value, width)
        }
    "#;

    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_slice_to_vec_roundtrip_counters();

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bits_from_u64");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_bits_from_u64", ChcConfig::default());

        assert_vc_structure(&vc, "probe_bits_from_u64", body.blocks.len());

        let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
        let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();

        eprintln!(
            "[#3903 D1] direct for-loop from_u64: \
             inferable_predicate={inferable_count}, \
             unhandled={unhandled_calls:?}"
        );

        // Direct call with `for i in 0..width` should be handled by vec_builder
        // (Range aggregate detected). The while-loop diagnostic gives
        // inferable_predicate=2; the for-loop should give 0 if vec_builder fires.
        assert_eq!(
            inferable_count, 0,
            "direct probe_bits_from_u64 with for-loop should have 0 inferable predicates \
             (vec_builder handles Range-based push loops), got {inferable_count}; \
             unhandled={unhandled_calls:?}"
        );
    });

    reset_slice_to_vec_roundtrip_counters();
}

/// Part of #3903 D1: Source-parity regression for nested `from_u64` calls
/// using the REAL `for i in 0..width` harness shape. Tests whether vec_builder
/// dispatch fires for from_u64 when called as a nested callee.
///
/// NOTE: Uses a minimal probe (no clone/extend/assert_eq!) to avoid triggering
/// the W2 #3872 virtual dispatch index-OOB crash on the shared worktree.
#[test]
fn test_bits_from_u64_for_loop_nested_parity() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Bits(Vec<bool>);

        impl Bits {
            fn from_u64(value: u64, width: usize) -> Self {
                let mut bits = Vec::with_capacity(width);
                for i in 0..width {
                    bits.push(if i < 64 {
                        (value >> i) & 1 == 1
                    } else {
                        false
                    });
                }
                Self(bits)
            }
        }

        pub fn probe_two_from_u64(a: u64, b: u64, w: usize) -> (Bits, Bits) {
            let ba = Bits::from_u64(a, w);
            let bb = Bits::from_u64(b, w);
            (ba, bb)
        }
    "#;

    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_slice_to_vec_roundtrip_counters();

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_name = "probe_two_from_u64";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());

        let inferable_decls: Vec<_> = vc
            .decls
            .iter()
            .filter_map(|decl| match decl {
                trust_mc_core::decl::Decl::Fun { name, .. } if name.starts_with("P_inf_") => {
                    Some(name.clone())
                }
                _ => None,
            })
            .collect();

        let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
        let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();

        eprintln!(
            "[#3903 D1] for-loop two-call nested probe: \
             inferable_predicate={inferable_count}, \
             P_inf_decls={inferable_decls:?}, \
             unhandled={unhandled_calls:?}"
        );

        // Part of #3903: vec_builder now fires correctly for flattened
        // struct-wrapped Vec destinations at non-zero state variable offsets.
        // Both for-loop from_u64 calls should produce 0 inferable predicates.
        assert_eq!(
            inferable_count, 0,
            "for-loop nested from_u64 should have 0 inferable predicates \
             (vec_builder handles both calls after #3903 offset fix), \
             got {inferable_count}; P_inf_decls={inferable_decls:?}, unhandled={unhandled_calls:?}"
        );
        assert!(
            inferable_decls.is_empty(),
            "for-loop parity: no P_inf_ decls expected after #3903 fix: {inferable_decls:?}"
        );
    });

    reset_slice_to_vec_roundtrip_counters();
}
