// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven regression tests for CHC float assertion pattern lowering.
//! Part of #3763.

use super::common::*;
use crate::codegen_ay::emit_chc;

fn assert_no_fp_theory_tokens(smt: &str, context: &str) {
    for token in ["fp.abs", "fp.sub", "roundNearestTiesToEven", "roundTowardZero"] {
        assert!(
            !smt.contains(token),
            "{context} should stay on the pure-BV CHC path, found '{token}' in:\n{smt}"
        );
    }
}

fn has_f32_finite_error_rule(smt: &str) -> bool {
    smt.lines().any(|line| {
        line.starts_with("(rule") && line.contains(" error))") && line.contains("extract 30 23")
    })
}

#[test]
fn test_mir_to_chc_trunc_diff_assertion_avoids_fp_rounding_modes() {
    const SOURCE: &str = r#"
        #![allow(internal_features)]
        #![feature(core_intrinsics)]
        #![allow(dead_code)]

        use std::intrinsics::truncf32;

        pub fn probe_trunc_diff(x: f32) {
            if !x.is_nan() && !x.is_infinite() {
                let trunc_res = truncf32(x);
                let diff = (x - trunc_res).abs();
                assert!(diff < 1.0);
                assert!(diff >= 0.0);
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_trunc_diff");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_trunc_diff", ChcConfig::default());
        let smt = emit_chc(&vc).to_string();

        assert_no_fp_theory_tokens(&smt, "trunc diff assertions");
    });
}

#[test]
fn test_mir_to_chc_round_fract_assertion_avoids_fp_rounding_modes() {
    const SOURCE: &str = r#"
        #![allow(internal_features)]
        #![feature(core_intrinsics)]
        #![allow(dead_code)]

        use std::intrinsics::roundf32;

        pub fn probe_round_direction(x: f32) {
            if !x.is_nan() && !x.is_infinite() {
                let result = roundf32(x);
                let frac = x.fract().abs();
                if x.is_sign_positive() {
                    if frac >= 0.5 {
                        assert!(result > x);
                    } else {
                        assert!(result <= x);
                    }
                } else if frac >= 0.5 {
                    assert!(result < x);
                } else {
                    assert!(result >= x);
                }
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_round_direction");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_round_direction", ChcConfig::default());
        let smt = emit_chc(&vc).to_string();

        assert_no_fp_theory_tokens(&smt, "fract threshold assertions");
    });
}

#[test]
fn test_mir_to_chc_kani_ceil_diff_assertion_avoids_fp_rounding_modes() {
    const SOURCE: &str = r#"
        #![allow(internal_features)]
        #![feature(core_intrinsics)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]
        #![allow(dead_code)]

        mod kani {
            #[kanitool::fn_marker = "AnyModel"]
            pub fn any<T>() -> T {
                panic!("model-only marker function")
            }

            #[kanitool::fn_marker = "AssumeHook"]
            pub fn assume(_cond: bool) {}
        }

        use std::intrinsics::ceilf32;

        pub fn probe_kani_ceil_diff() {
            let x: f32 = kani::any();
            kani::assume(!x.is_nan());
            kani::assume(!x.is_infinite());
            let ceil_res = ceilf32(x);
            let diff = (x - ceil_res).abs();
            assert!(diff <= 1.0);
            assert!(diff >= 0.0);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_kani_ceil_diff");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_kani_ceil_diff", ChcConfig::default());
        let smt = emit_chc(&vc).to_string();

        assert_no_fp_theory_tokens(&smt, "Kani ceil diff assertions");
    });
}

#[test]
fn test_mir_to_chc_kani_ceil_diff_assertion_handles_deep_passthrough_copies() {
    const SOURCE: &str = r#"
        #![allow(internal_features)]
        #![feature(core_intrinsics)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]
        #![allow(dead_code)]

        mod kani {
            #[kanitool::fn_marker = "AnyModel"]
            pub fn any<T>() -> T {
                panic!("model-only marker function")
            }

            #[kanitool::fn_marker = "AssumeHook"]
            pub fn assume(_cond: bool) {}
        }

        use std::intrinsics::ceilf32;

        pub fn probe_kani_ceil_diff_deep_alias() {
            let x0: f32 = kani::any();
            kani::assume(!x0.is_nan());
            kani::assume(!x0.is_infinite());
            let x1 = x0;
            let x2 = x1;
            let x3 = x2;
            let x4 = x3;
            let x5 = x4;
            let ceil_res = ceilf32(x5);
            let y0 = x5;
            let y1 = y0;
            let y2 = y1;
            let y3 = y2;
            let y4 = y3;
            let raw_diff = (y4 - ceil_res).abs();
            let d0 = raw_diff;
            let d1 = d0;
            let d2 = d1;
            let d3 = d2;
            let d4 = d3;
            assert!(d4 <= 1.0);
            assert!(d4 >= 0.0);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_kani_ceil_diff_deep_alias");
        let body = instance.body().expect("function body");
        let vc =
            mir_to_chc(ctx.tcx, &body, "probe_kani_ceil_diff_deep_alias", ChcConfig::default());
        let smt = emit_chc(&vc).to_string();

        assert_no_fp_theory_tokens(&smt, "Kani ceil diff assertions with deep aliases");
    });
}

#[test]
fn test_mir_to_chc_floorf64_direction_assertion_uses_nan_guard() {
    const SOURCE: &str = r#"
        #![allow(internal_features)]
        #![feature(core_intrinsics)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]
        #![allow(dead_code)]

        mod kani {
            #[kanitool::fn_marker = "AnyModel"]
            pub fn any<T>() -> T {
                panic!("model-only marker function")
            }

            #[kanitool::fn_marker = "AssumeHook"]
            pub fn assume(_cond: bool) {}
        }

        use std::intrinsics::floorf64;

        pub fn probe_floorf64_direction() {
            let x: f64 = kani::any();
            kani::assume(!x.is_nan());
            let result = floorf64(x);
            assert!(result <= x);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_floorf64_direction");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_floorf64_direction", ChcConfig::default());
        let smt = emit_chc(&vc).to_string();

        assert_no_fp_theory_tokens(&smt, "floorf64 direction assertion");
        assert!(
            smt.contains("extract 62 52"),
            "floorf64 direction assertion should lower to an f64 NaN guard:\n{smt}"
        );
    });
}

#[test]
fn test_mir_to_chc_kani_round_direction_assertion_avoids_fp_rounding_modes() {
    const SOURCE: &str = r#"
        #![allow(internal_features)]
        #![feature(core_intrinsics)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]
        #![allow(dead_code)]

        mod kani {
            #[kanitool::fn_marker = "AnyModel"]
            pub fn any<T>() -> T {
                panic!("model-only marker function")
            }

            #[kanitool::fn_marker = "AssumeHook"]
            pub fn assume(_cond: bool) {}
        }

        use std::intrinsics::roundf32;

        pub fn probe_kani_round_direction() {
            let x: f32 = kani::any();
            kani::assume(!x.is_nan());
            kani::assume(!x.is_infinite());
            let result = roundf32(x);
            let frac = x.fract().abs();
            if x.is_sign_positive() {
                if frac >= 0.5 {
                    assert!(result > x);
                } else {
                    assert!(result <= x);
                }
            } else if frac >= 0.5 {
                assert!(result < x);
            } else {
                assert!(result >= x);
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_kani_round_direction");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_kani_round_direction", ChcConfig::default());
        let smt = emit_chc(&vc).to_string();

        assert_no_fp_theory_tokens(&smt, "Kani round direction assertions");
    });
}

#[test]
fn test_mir_to_chc_finite_assume_discharges_fast_math_input_checks() {
    const SOURCE: &str = r#"
        #![allow(internal_features)]
        #![feature(core_intrinsics)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]
        #![allow(dead_code)]

        mod kani {
            #[kanitool::fn_marker = "AnyModel"]
            pub fn any<T>() -> T {
                unsafe { std::mem::zeroed() }
            }

            #[kanitool::fn_marker = "AssumeHook"]
            pub fn assume(_cond: bool) {}
        }

        pub fn probe_fast_math_finite_assume() {
            let x: f32 = kani::any();
            let y: f32 = kani::any();
            kani::assume(x.is_finite());
            kani::assume(y.is_finite());
            let z = unsafe { std::intrinsics::fadd_fast(x, y) };
            let w = x + y;
            assert!(z == w);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_fast_math_finite_assume");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_fast_math_finite_assume", ChcConfig::default());
        let smt = emit_chc(&vc).to_string();

        assert!(
            smt.contains("extract 30 23"),
            "finite assumptions should lower to direct exponent checks: {smt}"
        );
        assert!(
            !smt.contains("not (ite"),
            "fast-math result equality should simplify before generic float equality: {smt}"
        );
        assert_z3_result_with_timeout(&smt, "unsat", 10);
    });
}

#[test]
fn test_mir_to_chc_branch_local_finite_assume_keeps_fast_math_input_checks() {
    const SOURCE: &str = r#"
        #![allow(internal_features)]
        #![feature(core_intrinsics)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]
        #![allow(dead_code)]

        mod kani {
            #[kanitool::fn_marker = "AnyModel"]
            pub fn any<T>() -> T {
                unsafe { std::mem::zeroed() }
            }

            #[kanitool::fn_marker = "AssumeHook"]
            pub fn assume(_cond: bool) {}
        }

        pub fn probe_fast_math_branch_local_assume(flag: bool) -> f32 {
            let x: f32 = kani::any();
            let y: f32 = kani::any();
            if flag {
                kani::assume(x.is_finite());
                kani::assume(y.is_finite());
            }
            unsafe { std::intrinsics::fadd_fast(x, y) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_fast_math_branch_local_assume");
        let body = instance.body().expect("function body");
        let vc =
            mir_to_chc(ctx.tcx, &body, "probe_fast_math_branch_local_assume", ChcConfig::default());
        let smt = emit_chc(&vc).to_string();

        assert!(
            has_f32_finite_error_rule(&smt),
            "branch-local finite assumptions must not discharge fast-math checks: {smt}"
        );
    });
}

// Part of #4110: float-to-int round-trip assertion pattern bypass tests.

#[test]
fn test_mir_to_chc_f32_to_u32_roundtrip_avoids_int_to_float_chain() {
    const SOURCE: &str = r#"
        #![allow(internal_features)]
        #![feature(core_intrinsics)]
        #![allow(dead_code)]

        use std::intrinsics::{float_to_int_unchecked, truncf32};

        pub fn probe_f32_u32_roundtrip(f: f32) {
            if f.is_finite() && f > 0.0 && f < u32::MAX as f32 {
                let u: u32 = unsafe { float_to_int_unchecked(f) };
                assert_eq!(u as f32, truncf32(f));
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_f32_u32_roundtrip");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_f32_u32_roundtrip", ChcConfig::default());
        let smt = emit_chc(&vc).to_string();

        assert_no_fp_theory_tokens(&smt, "f32→u32 roundtrip assertion");
    });
}

#[test]
fn test_mir_to_chc_f64_to_u32_roundtrip_avoids_int_to_float_chain() {
    const SOURCE: &str = r#"
        #![allow(internal_features)]
        #![feature(core_intrinsics)]
        #![allow(dead_code)]

        use std::intrinsics::{float_to_int_unchecked, truncf64};

        pub fn probe_f64_u32_roundtrip(f: f64) {
            if f.is_finite() && f > 0.0 && f < u32::MAX as f64 {
                let u: u32 = unsafe { float_to_int_unchecked(f) };
                assert_eq!(u as f64, truncf64(f));
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_f64_u32_roundtrip");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_f64_u32_roundtrip", ChcConfig::default());
        let smt = emit_chc(&vc).to_string();

        assert_no_fp_theory_tokens(&smt, "f64→u32 roundtrip assertion");
    });
}

#[test]
fn test_mir_to_chc_f32_to_u64_roundtrip_avoids_int_to_float_chain() {
    const SOURCE: &str = r#"
        #![allow(internal_features)]
        #![feature(core_intrinsics)]
        #![allow(dead_code)]

        use std::intrinsics::{float_to_int_unchecked, truncf32};

        pub fn probe_f32_u64_roundtrip(f: f32) {
            if f.is_finite() && f > 0.0 && f < u64::MAX as f32 {
                let u: u64 = unsafe { float_to_int_unchecked(f) };
                assert_eq!(u as f32, truncf32(f));
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_f32_u64_roundtrip");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_f32_u64_roundtrip", ChcConfig::default());
        let smt = emit_chc(&vc).to_string();

        assert_no_fp_theory_tokens(&smt, "f32→u64 roundtrip assertion");
    });
}

#[test]
fn test_mir_to_chc_f64_to_u128_roundtrip_avoids_int_to_float_chain() {
    const SOURCE: &str = r#"
        #![allow(internal_features)]
        #![feature(core_intrinsics)]
        #![allow(dead_code)]

        use std::intrinsics::{float_to_int_unchecked, truncf64};

        pub fn probe_f64_u128_roundtrip(f: f64) {
            if f.is_finite() && f > 0.0 && f < u128::MAX as f64 {
                let u: u128 = unsafe { float_to_int_unchecked(f) };
                assert_eq!(u as f64, truncf64(f));
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_f64_u128_roundtrip");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_f64_u128_roundtrip", ChcConfig::default());
        let smt = emit_chc(&vc).to_string();

        assert_no_fp_theory_tokens(&smt, "f64→u128 roundtrip assertion");
    });
}

/// Regression test for #3774: (Round, Half, Lt) is unhandled by the comparison
/// builder, so the Sub bypass must NOT fire. Before the fix, the bypass would
/// replace the subtraction with a hardcoded zero, producing a false PROOF.
#[test]
fn test_mir_to_chc_round_half_lt_bypass_does_not_fire() {
    const SOURCE: &str = r#"
        #![allow(internal_features)]
        #![feature(core_intrinsics)]
        #![allow(dead_code)]

        use std::intrinsics::roundf32;

        pub fn probe_round_half_lt(x: f32) {
            if !x.is_nan() && !x.is_infinite() {
                let result = roundf32(x);
                let diff = (x - result).abs();
                assert!(diff < 0.5);
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_round_half_lt");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_round_half_lt", ChcConfig::default());
        let smt = emit_chc(&vc).to_string();

        // The (Round, Half, Lt) pattern is NOT handled by the comparison builder.
        // The Sub bypass must NOT fire, so the SMT should contain a subtraction
        // operation (bvsub or fp.sub) rather than a hardcoded zero.
        let has_sub = smt.contains("bvsub") || smt.contains("fp.sub");
        assert!(
            has_sub,
            "Round/Half/Lt bypass should NOT fire — expected bvsub or fp.sub in SMT output, \
             but neither found. This means the Sub was bypassed with zero (false PROOF).\n{smt}"
        );
    });
}
