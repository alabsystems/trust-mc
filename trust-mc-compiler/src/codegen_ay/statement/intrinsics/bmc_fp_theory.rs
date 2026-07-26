// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Part of #3094: BMC FP theory helpers.
//!
//! These use AY FP theory operations (fp.roundToIntegral, fp.sqrt, fp.fma,
//! fp.min, fp.max) which work in SMT-LIB/BMC but are rejected by Z3's CHC
//! fixedpoint parser (cannot parse rounding-mode constants). The CHC path
//! uses pure BV encoding in `chc/call/codegen_call_cmp_string/float_rounding.rs`.

use crate::codegen_ay::float_arithmetic::float_width_to_eb_sb;
use ay_bindings::{Expr, RoundingMode};

fn bv_to_ieee_fp(bv: Expr, eb: u32, sb: u32) -> Expr {
    let total = eb + sb;
    let sign = bv.clone().extract(total - 1, total - 1);
    let exponent = bv.clone().extract(total - 2, sb - 1);
    let significand = bv.extract(sb - 2, 0);
    Expr::fp_from_bvs(sign, exponent, significand)
}

pub(super) fn bmc_fp_round_to_integral(src: Expr, width: u32, rm: RoundingMode) -> Option<Expr> {
    let (eb, sb) = float_width_to_eb_sb(width)?;
    let fp = bv_to_ieee_fp(src, eb, sb);
    Some(fp.fp_round_to_integral(rm).fp_to_ieee_bv())
}

pub(super) fn bmc_fp_sqrt(src: Expr, width: u32) -> Option<Expr> {
    let (eb, sb) = float_width_to_eb_sb(width)?;
    let fp = bv_to_ieee_fp(src, eb, sb);
    Some(fp.fp_sqrt(RoundingMode::RNE).fp_to_ieee_bv())
}

pub(super) fn bmc_fp_fma(a: Expr, b: Expr, c: Expr, width: u32) -> Option<Expr> {
    let (eb, sb) = float_width_to_eb_sb(width)?;
    let fp_a = bv_to_ieee_fp(a, eb, sb);
    let fp_b = bv_to_ieee_fp(b, eb, sb);
    let fp_c = bv_to_ieee_fp(c, eb, sb);
    Some(fp_a.fp_fma(RoundingMode::RNE, fp_b, fp_c).fp_to_ieee_bv())
}

pub(super) fn bmc_fp_minmax(a: Expr, b: Expr, width: u32, is_min: bool) -> Option<Expr> {
    let (eb, sb) = float_width_to_eb_sb(width)?;
    let fp_a = bv_to_ieee_fp(a, eb, sb);
    let fp_b = bv_to_ieee_fp(b, eb, sb);
    if is_min {
        Some(fp_a.fp_min(fp_b).fp_to_ieee_bv())
    } else {
        Some(fp_a.fp_max(fp_b).fp_to_ieee_bv())
    }
}
