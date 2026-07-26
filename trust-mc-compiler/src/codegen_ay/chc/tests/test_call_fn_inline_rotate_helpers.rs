// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for rotate-style local helper inlining.
//!
//! Part of #3747: the earlier probe only exercised a top-level helper returning
//! `bool`. The real rotate regressions define local helper items inside the
//! outer proof function, return `()`, and end in helper-local `assert!` checks.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

const LOCAL_ROTATE_HELPER_PROBE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            unsafe { std::mem::zeroed() }
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(cond: bool) {
            let _ = cond;
        }
    }

    pub fn probe_rotate_left_local_helper_u8() {
        fn check_rol_u8(x: u8, rot_x: u8, n: u32) {
            let i: u32 = kani::any();
            kani::assume(i < u8::BITS);
            let bitmask = 1 << i;
            let bit = (x & bitmask) != 0;
            let rot_i = (i + n) % u8::BITS;
            let rot_bitmask = 1 << rot_i;
            let rot_bit = (rot_x & rot_bitmask) != 0;
            assert!(bit == rot_bit);
        }

        let x: u8 = kani::any();
        let rot_x: u8 = kani::any();
        let n: u32 = kani::any();
        kani::assume(n <= u8::MAX as u32);
        check_rol_u8(x, rot_x, n);
    }

    pub fn probe_rotate_right_local_helper_u128() {
        fn check_ror_u128(x: u128, rot_x: u128, n: u32) {
            let bits_i32 = u128::BITS as i32;
            let i: i32 = kani::any();
            kani::assume(i < bits_i32);
            kani::assume(i >= 0);
            let bitmask = 1 << i;
            let bit = (x & bitmask) != 0;
            let mut rot_i = (i - (n as i32)) % bits_i32;
            if rot_i < 0 {
                rot_i = rot_i + bits_i32;
            }
            let rot_bitmask = 1 << rot_i;
            let rot_bit = (rot_x & rot_bitmask) != 0;
            assert!(bit == rot_bit);
        }

        let x: u128 = kani::any();
        let rot_x: u128 = kani::any();
        let n: u32 = kani::any();
        kani::assume(n <= u8::MAX as u32);
        check_ror_u128(x, rot_x, n);
    }
"#;

const PROBE_FN_NAMES: [&str; 2] =
    ["probe_rotate_left_local_helper_u8", "probe_rotate_right_local_helper_u128"];

const DIRECT_BIT_INTRINSIC_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(internal_features)]
    #![feature(core_intrinsics)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            unsafe { std::mem::zeroed() }
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(cond: bool) {
            let _ = cond;
        }
    }

    pub fn probe_reverse_bits_u8(x: u8) -> u8 {
        x.reverse_bits()
    }

    pub fn probe_ctlz_u16(x: u16) -> u32 {
        std::intrinsics::ctlz(x)
    }

    pub fn probe_cttz_u32(x: u32) -> u32 {
        std::intrinsics::cttz(x)
    }

    pub fn probe_ctpop_u64(x: u64) -> u32 {
        std::intrinsics::ctpop(x)
    }
"#;

const HELPER_WRAPPED_BIT_INTRINSIC_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(internal_features)]
    #![feature(core_intrinsics)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            unsafe { std::mem::zeroed() }
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(cond: bool) {
            let _ = cond;
        }
    }

    pub fn probe_bitreverse_helper_u8() {
        fn get_bit_at_u8(x: u8, n: usize) -> bool {
            x & (1 << n) != 0
        }

        fn check_reverse_u8(a: u8, b: u8) {
            let len = std::mem::size_of::<u8>() * 8;
            let n: usize = kani::any();
            kani::assume(n < len);
            assert!(get_bit_at_u8(a, n) == get_bit_at_u8(b, (len - 1) - n));
        }

        let x: u8 = kani::any();
        check_reverse_u8(x, x.reverse_bits());
    }

    pub fn probe_ctlz_helper_u8() {
        fn my_ctlz_u8(x: u8) -> u32 {
            let mut count = 0;
            let num_bits = u8::BITS;
            for i in 0..num_bits {
                let bitmask = 1 << (num_bits - i - 1);
                let bit = x & bitmask;
                if bit == 0 {
                    count += 1;
                } else {
                    break;
                }
            }
            count
        }

        let var: u8 = kani::any();
        assert!(my_ctlz_u8(var) == std::intrinsics::ctlz(var));
    }
"#;

const BITREVERSE_SOLVER_PROBE_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(overflowing_literals)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    const BITS_PER_BYTE: usize = 8;

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            unsafe { std::mem::zeroed() }
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(cond: bool) {
            let _ = cond;
        }
    }

    pub fn probe_bitreverse_u8() {
        fn get_bit_at_u8(x: u8, n: usize) -> bool {
            x & (1 << n) != 0
        }

        fn check_reverse_u8(a: u8, b: u8) {
            let len: usize = std::mem::size_of::<u8>() * BITS_PER_BYTE;
            let n: usize = kani::any();
            kani::assume(n < len);
            assert!(get_bit_at_u8(a, n) == get_bit_at_u8(b, (len - 1) - n));
        }

        let x: u8 = kani::any();
        check_reverse_u8(x, x.reverse_bits());
    }

    pub fn probe_bitreverse_u16() {
        fn get_bit_at_u16(x: u16, n: usize) -> bool {
            x & (1 << n) != 0
        }

        fn check_reverse_u16(a: u16, b: u16) {
            let len: usize = std::mem::size_of::<u16>() * BITS_PER_BYTE;
            let n: usize = kani::any();
            kani::assume(n < len);
            assert!(get_bit_at_u16(a, n) == get_bit_at_u16(b, (len - 1) - n));
        }

        let x: u16 = kani::any();
        check_reverse_u16(x, x.reverse_bits());
    }

    pub fn probe_bitreverse_u32() {
        fn get_bit_at_u32(x: u32, n: usize) -> bool {
            x & (1 << n) != 0
        }

        fn check_reverse_u32(a: u32, b: u32) {
            let len: usize = std::mem::size_of::<u32>() * BITS_PER_BYTE;
            let n: usize = kani::any();
            kani::assume(n < len);
            assert!(get_bit_at_u32(a, n) == get_bit_at_u32(b, (len - 1) - n));
        }

        let x: u32 = kani::any();
        check_reverse_u32(x, x.reverse_bits());
    }

    pub fn probe_bitreverse_u64() {
        fn get_bit_at_u64(x: u64, n: usize) -> bool {
            x & (1 << n) != 0
        }

        fn check_reverse_u64(a: u64, b: u64) {
            let len: usize = std::mem::size_of::<u64>() * BITS_PER_BYTE;
            let n: usize = kani::any();
            kani::assume(n < len);
            assert!(get_bit_at_u64(a, n) == get_bit_at_u64(b, (len - 1) - n));
        }

        let x: u64 = kani::any();
        check_reverse_u64(x, x.reverse_bits());
    }

    pub fn probe_bitreverse_u128() {
        fn get_bit_at_u128(x: u128, n: usize) -> bool {
            x & (1 << n) != 0
        }

        fn check_reverse_u128(a: u128, b: u128) {
            let len: usize = std::mem::size_of::<u128>() * BITS_PER_BYTE;
            let n: usize = kani::any();
            kani::assume(n < len);
            assert!(get_bit_at_u128(a, n) == get_bit_at_u128(b, (len - 1) - n));
        }

        let x: u128 = kani::any();
        check_reverse_u128(x, x.reverse_bits());
    }

    pub fn probe_bitreverse_usize() {
        fn get_bit_at_usize(x: usize, n: usize) -> bool {
            x & (1 << n) != 0
        }

        fn check_reverse_usize(a: usize, b: usize) {
            let len: usize = std::mem::size_of::<usize>() * BITS_PER_BYTE;
            let n: usize = kani::any();
            kani::assume(n < len);
            assert!(get_bit_at_usize(a, n) == get_bit_at_usize(b, (len - 1) - n));
        }

        let x: usize = kani::any();
        check_reverse_usize(x, x.reverse_bits());
    }
"#;

const BITREVERSE_AGGREGATE_PROBE_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(overflowing_literals)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    const BITS_PER_BYTE: usize = 8;

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            unsafe { std::mem::zeroed() }
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(cond: bool) {
            let _ = cond;
        }
    }

    macro_rules! test_bitreverse_intrinsic {
        ($ty:ty, $check_name:ident, $get_bit_name:ident) => {
            fn $get_bit_name(x: $ty, n: usize) -> bool {
                x & (1 << n) != 0
            }

            fn $check_name(a: $ty, b: $ty) {
                let len: usize = std::mem::size_of::<$ty>() * BITS_PER_BYTE;
                let n: usize = kani::any();
                kani::assume(n < len);
                assert!($get_bit_name(a, n) == $get_bit_name(b, (len - 1) - n));
            }

            let x: $ty = kani::any();
            $check_name(x, x.reverse_bits());
        };
    }

    pub fn probe_bitreverse_aggregate() {
        test_bitreverse_intrinsic!(u8, check_reverse_u8, get_bit_at_u8);
        test_bitreverse_intrinsic!(u16, check_reverse_u16, get_bit_at_u16);
        test_bitreverse_intrinsic!(u32, check_reverse_u32, get_bit_at_u32);
        test_bitreverse_intrinsic!(u64, check_reverse_u64, get_bit_at_u64);
        test_bitreverse_intrinsic!(u128, check_reverse_u128, get_bit_at_u128);
        test_bitreverse_intrinsic!(usize, check_reverse_usize, get_bit_at_usize);
    }
"#;

const BITREVERSE_HARNESS_SHAPE_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(overflowing_literals)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    const BITS_PER_BYTE: usize = 8;

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            unsafe { std::mem::zeroed() }
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(cond: bool) {
            let _ = cond;
        }
    }

    macro_rules! test_bitreverse_intrinsic {
        ($ty:ty, $check_name:ident, $get_bit_name:ident) => {
            fn $get_bit_name(x: $ty, n: usize) -> bool {
                x & (1 << n) != 0
            }

            fn $check_name(a: $ty, b: $ty) {
                let len: usize = std::mem::size_of::<$ty>() * BITS_PER_BYTE;
                let n: usize = kani::any();
                kani::assume(n < len);
                assert!($get_bit_name(a, n) == $get_bit_name(b, (len - 1) - n));
            }

            let x: $ty = kani::any();
            $check_name(x, x.reverse_bits());
        };
    }

    #[kanitool::proof]
    fn main() {
        test_bitreverse_intrinsic!(u8, check_reverse_u8, get_bit_at_u8);
        test_bitreverse_intrinsic!(u16, check_reverse_u16, get_bit_at_u16);
        test_bitreverse_intrinsic!(u32, check_reverse_u32, get_bit_at_u32);
        test_bitreverse_intrinsic!(u64, check_reverse_u64, get_bit_at_u64);
        test_bitreverse_intrinsic!(u128, check_reverse_u128, get_bit_at_u128);
        test_bitreverse_intrinsic!(usize, check_reverse_usize, get_bit_at_usize);
    }
"#;

const BITREVERSE_WRAPPER_CHAIN_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(overflowing_literals)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    const BITS_PER_BYTE: usize = 8;

    mod kani {
        pub trait Arbitrary: Sized {
            fn any() -> Self;
        }

        impl Arbitrary for u32 {
            #[inline(always)]
            fn any() -> Self {
                unsafe { any_raw_internal::<Self>() }
            }
        }

        impl Arbitrary for usize {
            #[inline(always)]
            fn any() -> Self {
                unsafe { any_raw_internal::<Self>() }
            }
        }

        #[inline(never)]
        pub unsafe fn any_raw_internal<T: Copy>() -> T {
            any_raw::<T>()
        }

        #[kanitool::fn_marker = "AnyRawHook"]
        #[inline(never)]
        fn any_raw<T: Copy>() -> T {
            panic!("model-only marker function")
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(_cond: bool) {}

        #[kanitool::fn_marker = "AssertHook"]
        pub fn assert(_cond: bool, _msg: &'static str) {}
    }

    pub fn probe_bitreverse_any_raw_internal_wrapper() {
        fn get_bit_at_u32(x: u32, n: usize) -> bool {
            x & (1 << n) != 0
        }

        fn check_reverse_u32(a: u32, b: u32) {
            let len: usize = std::mem::size_of::<u32>() * BITS_PER_BYTE;
            let n: usize = unsafe { kani::any_raw_internal::<usize>() };
            kani::assume(n < len);
            kani::assert(
                get_bit_at_u32(a, n) == get_bit_at_u32(b, (len - 1) - n),
                "bitreverse relation",
            );
        }

        let x: u32 = unsafe { kani::any_raw_internal::<u32>() };
        check_reverse_u32(x, x.reverse_bits());
    }

    pub fn probe_bitreverse_arbitrary_any_wrapper() {
        fn get_bit_at_u32(x: u32, n: usize) -> bool {
            x & (1 << n) != 0
        }

        fn check_reverse_u32(a: u32, b: u32) {
            let len: usize = std::mem::size_of::<u32>() * BITS_PER_BYTE;
            let n: usize = <usize as kani::Arbitrary>::any();
            kani::assume(n < len);
            kani::assert(
                get_bit_at_u32(a, n) == get_bit_at_u32(b, (len - 1) - n),
                "bitreverse relation",
            );
        }

        let x: u32 = <u32 as kani::Arbitrary>::any();
        check_reverse_u32(x, x.reverse_bits());
    }
"#;

const DIRECT_BIT_INTRINSIC_PROBES: [&str; 4] =
    ["probe_reverse_bits_u8", "probe_ctlz_u16", "probe_cttz_u32", "probe_ctpop_u64"];

const HELPER_WRAPPED_BIT_INTRINSIC_PROBES: [&str; 2] =
    ["probe_bitreverse_helper_u8", "probe_ctlz_helper_u8"];

const BITREVERSE_SOLVER_PROBES: [&str; 6] = [
    "probe_bitreverse_u8",
    "probe_bitreverse_u16",
    "probe_bitreverse_u32",
    "probe_bitreverse_u64",
    "probe_bitreverse_u128",
    "probe_bitreverse_usize",
];

const BITREVERSE_WRAPPER_CHAIN_PROBES: [&str; 2] =
    ["probe_bitreverse_any_raw_internal_wrapper", "probe_bitreverse_arbitrary_any_wrapper"];

fn reset_rotate_helper_counters() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
    let _ = crate::codegen_ay::take_unhandled_call_by_fn();
    let _ = crate::codegen_ay::take_unsupported_construct_fallback_count();
}

fn assert_solver_probe_produces_proof(source: &str, fn_name: &str) {
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();

        assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");
        assert!(
            !vc_error_rules_contain_var(&vc, "__assert_fail_inline"),
            "{fn_name} should not leak nested helper fallback markers into error()"
        );
        assert_z3_result(&smt, "unsat");
    });
}

fn assert_inline_probe_stays_precise_and_produces_proof(source: &str, fn_name: &str) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_rotate_helper_counters();

    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();

        assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");
        assert!(
            !vc_error_rules_contain_var(&vc, "__assert_fail_inline"),
            "{fn_name} should not leak nested helper fallback markers into error()"
        );

        let fallback_counts = get_chc_fallback_counts();
        let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
        let translation_drops = take_translation_drop_by_fn();
        let unsupported = crate::codegen_ay::take_unsupported_construct_fallback_count();

        assert_eq!(
            fallback_counts.get(fn_name).copied().unwrap_or(0),
            0,
            "{fn_name} should avoid CHC fallback, map={fallback_counts:?}"
        );
        assert_eq!(
            unhandled_calls.get(fn_name).copied().unwrap_or(0),
            0,
            "{fn_name} should not increment unhandled_call, map={unhandled_calls:?}"
        );
        assert_eq!(
            translation_drops.get(fn_name).copied().unwrap_or(0),
            0,
            "{fn_name} should not drop inline translation sites, map={translation_drops:?}"
        );
        assert_eq!(unsupported, 0, "{fn_name} should not hit unsupported-construct fallback");

        assert_z3_result(&smt, "unsat");
    });

    reset_rotate_helper_counters();
}

#[test]
fn test_local_rotate_helpers_inline_without_fallbacks() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_rotate_helper_counters();

    with_test_ay_ctx_for_source(LOCAL_ROTATE_HELPER_PROBE, |ctx| {
        for fn_name in PROBE_FN_NAMES {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

            assert!(!vc.relations.is_empty(), "{fn_name} should produce relations");
            assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");
        }

        let fallback_counts = get_chc_fallback_counts();
        let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();

        for fn_name in PROBE_FN_NAMES {
            let fallback_count = fallback_counts.get(fn_name).copied().unwrap_or(0);
            assert_eq!(
                fallback_count, 0,
                "{fn_name} should stay on the inline path without CHC fallback, map={fallback_counts:?}"
            );

            let unhandled_count = unhandled_calls.get(fn_name).copied().unwrap_or(0);
            assert_eq!(
                unhandled_count, 0,
                "{fn_name} should not increment unhandled_call, map={unhandled_calls:?}"
            );
        }
    });

    reset_rotate_helper_counters();
}

#[test]
fn test_local_rotate_helpers_emit_no_p_inf_rules() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_rotate_helper_counters();

    with_test_ay_ctx_for_source(LOCAL_ROTATE_HELPER_PROBE, |ctx| {
        for fn_name in PROBE_FN_NAMES {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

            assert!(!vc.relations.is_empty(), "{fn_name} should produce relations");
            assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");

            let inferable_decls: Vec<_> = vc
                .vars()
                .iter()
                .filter(|decl| decl.name.contains("P_inf_"))
                .map(|decl| decl.name.clone())
                .collect();
            assert!(
                inferable_decls.is_empty(),
                "{fn_name} should not emit P_inf_* declarations for local rotate helpers: {inferable_decls:?}"
            );

            let has_p_inf = vc.rules.iter().any(|rule| format!("{:?}", rule).contains("P_inf_"));
            assert!(
                !has_p_inf,
                "{fn_name} should not reference P_inf_* summaries in emitted rules"
            );
        }
    });

    reset_rotate_helper_counters();
}

#[test]
fn test_direct_bit_intrinsics_emit_no_unhandled_calls() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_rotate_helper_counters();

    with_test_ay_ctx_for_source(DIRECT_BIT_INTRINSIC_SOURCE, |ctx| {
        for fn_name in DIRECT_BIT_INTRINSIC_PROBES {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

            assert!(!vc.relations.is_empty(), "{fn_name} should produce relations");
            assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");

            let has_p_inf = vc.rules.iter().any(|rule| format!("{rule:?}").contains("P_inf_"));
            assert!(
                !has_p_inf,
                "{fn_name} should not reference P_inf_* summaries in emitted rules"
            );
        }

        let fallback_counts = get_chc_fallback_counts();
        let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
        let unsupported = crate::codegen_ay::take_unsupported_construct_fallback_count();

        assert_eq!(
            unsupported, 0,
            "direct bit intrinsic probes should not hit unsupported-construct fallback"
        );

        for fn_name in DIRECT_BIT_INTRINSIC_PROBES {
            let fallback_count = fallback_counts.get(fn_name).copied().unwrap_or(0);
            assert_eq!(
                fallback_count, 0,
                "{fn_name} should avoid CHC fallback, map={fallback_counts:?}"
            );

            let unhandled_count = unhandled_calls.get(fn_name).copied().unwrap_or(0);
            assert_eq!(
                unhandled_count, 0,
                "{fn_name} should not increment unhandled_call, map={unhandled_calls:?}"
            );
        }
    });

    reset_rotate_helper_counters();
}

#[test]
fn test_helper_wrapped_bit_intrinsics_emit_no_unhandled_calls() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_rotate_helper_counters();

    with_test_ay_ctx_for_source(HELPER_WRAPPED_BIT_INTRINSIC_SOURCE, |ctx| {
        for fn_name in HELPER_WRAPPED_BIT_INTRINSIC_PROBES {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

            assert!(!vc.relations.is_empty(), "{fn_name} should produce relations");
            assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");
        }

        let fallback_counts = get_chc_fallback_counts();
        let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
        let translation_drops = take_translation_drop_by_fn();
        let unsupported = crate::codegen_ay::take_unsupported_construct_fallback_count();

        assert_eq!(
            unsupported, 0,
            "helper-wrapped bit intrinsic probes should not hit unsupported-construct fallback"
        );

        for fn_name in HELPER_WRAPPED_BIT_INTRINSIC_PROBES {
            let fallback_count = fallback_counts.get(fn_name).copied().unwrap_or(0);
            assert_eq!(
                fallback_count, 0,
                "{fn_name} should avoid CHC fallback, map={fallback_counts:?}"
            );

            let unhandled_count = unhandled_calls.get(fn_name).copied().unwrap_or(0);
            assert_eq!(
                unhandled_count, 0,
                "{fn_name} should not increment unhandled_call, map={unhandled_calls:?}"
            );

            let translation_drop_count = translation_drops.get(fn_name).copied().unwrap_or(0);
            assert_eq!(
                translation_drop_count, 0,
                "{fn_name} should not drop inline translation sites, map={translation_drops:?}"
            );
        }
    });

    reset_rotate_helper_counters();
}

#[test]
fn test_bitreverse_solver_helpers_produce_proof() {
    for fn_name in BITREVERSE_SOLVER_PROBES {
        assert_solver_probe_produces_proof(BITREVERSE_SOLVER_PROBE_SOURCE, fn_name);
    }
}

#[test]
fn test_bitreverse_aggregate_solver_produces_proof() {
    assert_solver_probe_produces_proof(
        BITREVERSE_AGGREGATE_PROBE_SOURCE,
        "probe_bitreverse_aggregate",
    );
}

#[test]
fn test_bitreverse_harness_shape_solver_produces_proof() {
    assert_solver_probe_produces_proof(BITREVERSE_HARNESS_SHAPE_SOURCE, "main");
}

#[test]
fn test_bitreverse_wrapper_chain_stays_inline_and_produces_proof() {
    for fn_name in BITREVERSE_WRAPPER_CHAIN_PROBES {
        assert_inline_probe_stays_precise_and_produces_proof(
            BITREVERSE_WRAPPER_CHAIN_SOURCE,
            fn_name,
        );
    }
}
