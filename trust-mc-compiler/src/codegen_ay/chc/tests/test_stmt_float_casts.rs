// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Regression tests for CHC float cast lowering.
//! Part of #3465.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;

const FLOAT_CAST_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_u32_to_f32(x: u32) -> f32 {
        x as f32
    }

    pub fn probe_i64_to_f64(x: i64) -> f64 {
        x as f64
    }

    pub fn probe_f32_to_u32(x: f32) -> u32 {
        x as u32
    }

    pub fn probe_f64_to_i64(x: f64) -> i64 {
        x as i64
    }
"#;

const FORBIDDEN_ROUNDING_TOKENS: &[&str] = &[
    "fp.to_sbv",
    "fp.to_ubv",
    "roundTowardZero",
    "roundNearestTiesToEven",
    "roundNearestTiesToAway",
    "roundTowardPositive",
    "roundTowardNegative",
];

fn assert_no_rounding_terms(probe: &str, smt: &str) {
    let found = FORBIDDEN_ROUNDING_TOKENS
        .iter()
        .copied()
        .filter(|token| smt.contains(token))
        .collect::<Vec<_>>();
    assert!(
        found.is_empty(),
        "{probe} must stay on the parser-safe BV path, found {found:?} in: {}",
        &smt[..smt.len().min(2000)]
    );
}

#[test]
fn test_mir_to_chc_int_to_float_casts_use_pure_bv_encoding() {
    with_test_ay_ctx_for_source(FLOAT_CAST_SOURCE, |ctx| {
        for probe in ["probe_u32_to_f32", "probe_i64_to_f64"] {
            let instance = find_instance_by_suffix(ctx.tcx, probe);
            let body = instance.body().expect("function body");
            let vc = mir_to_chc(ctx.tcx, &body, probe, ChcConfig::default());
            let smt = emit_chc(&vc).to_string();

            assert_no_rounding_terms(probe, &smt);
            assert!(
                smt.contains("concat"),
                "{probe} should pack IEEE-754 fields with concat, got: {}",
                &smt[..smt.len().min(2000)]
            );
            assert!(
                smt.contains("bvshl") || smt.contains("bvlshr"),
                "{probe} should normalize integer bits with BV shifts, got: {}",
                &smt[..smt.len().min(2000)]
            );
        }
    });
}

#[test]
fn test_mir_to_chc_float_to_int_casts_use_bv_extractor() {
    with_test_ay_ctx_for_source(FLOAT_CAST_SOURCE, |ctx| {
        for (probe, exponent_extract, mantissa_extract) in [
            ("probe_f32_to_u32", "extract 30 23", "extract 22 0"),
            ("probe_f64_to_i64", "extract 62 52", "extract 51 0"),
        ] {
            let instance = find_instance_by_suffix(ctx.tcx, probe);
            let body = instance.body().expect("function body");
            let vc = mir_to_chc(ctx.tcx, &body, probe, ChcConfig::default());
            let smt = emit_chc(&vc).to_string();

            assert_no_rounding_terms(probe, &smt);
            assert!(
                smt.contains(exponent_extract) && smt.contains(mantissa_extract),
                "{probe} should extract IEEE-754 exponent and mantissa bits, got: {}",
                &smt[..smt.len().min(2000)]
            );
        }
    });
}
