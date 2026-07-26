// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Pure BV math and wrapping arithmetic fast paths for the inline translator.
//!
//! Split from `inline_known_calls.rs` to stay under the 500-line file limit.

use ay_bindings::Expr;
use num_bigint::BigInt;
use rustc_public::mir::{LocalDecl, Operand};
use rustc_public::ty::{RigidTy, TyKind};

/// Pure BV encoding for exact math operations (abs, copysign).
///
/// Unlike constant-folding in `math.rs`, these work on symbolic args because
/// they use BV bit-manipulation (mask sign bit) rather than host-float eval.
/// Part of #3839: math intrinsic inline encoding.
pub(super) fn inline_exact_math_call(callee_path: &str, args: &[Expr]) -> Option<Expr> {
    // f32 abs: clear sign bit
    if (callee_path.contains("f32") && callee_path.ends_with("::abs"))
        || callee_path.ends_with("fabsf32")
    {
        let arg = args.first()?;
        return Some(arg.clone().bvand(Expr::bitvec_const(0x7FFF_FFFFu64, 32)));
    }
    // f64 abs: clear sign bit
    if (callee_path.contains("f64") && callee_path.ends_with("::abs"))
        || callee_path.ends_with("fabsf64")
    {
        let arg = args.first()?;
        return Some(arg.clone().bvand(Expr::bitvec_const(0x7FFF_FFFF_FFFF_FFFFu64, 64)));
    }
    // f32 copysign: copy sign bit from second arg
    if callee_path.ends_with("copysignf32") {
        let (mag, sign) = (args.first()?, args.get(1)?);
        return Some(
            mag.clone()
                .bvand(Expr::bitvec_const(0x7FFF_FFFFu64, 32))
                .bvor(sign.clone().bvand(Expr::bitvec_const(0x8000_0000u64, 32))),
        );
    }
    // f64 copysign: copy sign bit from second arg
    if callee_path.ends_with("copysignf64") {
        let (mag, sign) = (args.first()?, args.get(1)?);
        return Some(
            mag.clone()
                .bvand(Expr::bitvec_const(0x7FFF_FFFF_FFFF_FFFFu64, 64))
                .bvor(sign.clone().bvand(Expr::bitvec_const(0x8000_0000_0000_0000u64, 64))),
        );
    }
    None
}

/// Part of #3889: Inline wrapping integer arithmetic so nested method bodies
/// (e.g. `i64::unsigned_abs` → `wrapping_abs` → `wrapping_neg` → `wrapping_sub`)
/// resolve directly to BV operations instead of exhausting MAX_INLINE_DEPTH.
pub(super) fn inline_wrapping_arith_expr(callee_path: &str, args: &[Expr]) -> Option<Expr> {
    let method = callee_path.rsplit("::").next()?;
    match method {
        // Part of #3973: guard on is_bitvec() — Int-lifted operands have
        // bitvec_width() == None, and None == None passes the old guard.
        "wrapping_add"
            if args.len() == 2
                && args[0].sort().is_bitvec()
                && args[0].sort().bitvec_width() == args[1].sort().bitvec_width() =>
        {
            Some(args[0].clone().bvadd(args[1].clone()))
        }
        "wrapping_sub"
            if args.len() == 2
                && args[0].sort().is_bitvec()
                && args[0].sort().bitvec_width() == args[1].sort().bitvec_width() =>
        {
            Some(args[0].clone().bvsub(args[1].clone()))
        }
        "wrapping_mul"
            if args.len() == 2
                && args[0].sort().is_bitvec()
                && args[0].sort().bitvec_width() == args[1].sort().bitvec_width() =>
        {
            Some(args[0].clone().bvmul(args[1].clone()))
        }
        "wrapping_neg" if args.len() == 1 => Some(args[0].clone().bvneg()),
        "wrapping_abs" | "unsigned_abs" if args.len() == 1 => {
            let val = &args[0];
            let width = val.sort().bitvec_width()?;
            let zero = Expr::bitvec_const(0u64, width);
            let neg = val.clone().bvneg();
            Some(Expr::ite(val.clone().bvsge(zero), val.clone(), neg))
        }
        _ => None,
    }
}

/// Inline saturating integer arithmetic inside nested bodies so the inline
/// walker does not fall back to an unconstrained result for `saturating_*`.
///
/// Part of #3993: coroutine re-entry bodies use `resume.saturating_add(1)`.
pub(super) fn inline_saturating_arith_expr(
    callee_path: &str,
    args: &[Expr],
    first_arg: Option<&Operand>,
    caller_locals: &[LocalDecl],
) -> Option<Expr> {
    let method = callee_path.rsplit("::").next()?;
    let is_add = match method {
        "saturating_add" => true,
        "saturating_sub" => false,
        _ => return None,
    };

    if args.len() != 2 || !args[0].sort().is_bitvec() || !args[1].sort().is_bitvec() {
        return None;
    }
    let width = args[0].sort().bitvec_width()?;
    if args[1].sort().bitvec_width() != Some(width) {
        return None;
    }

    let is_signed = infer_inline_arith_signedness(first_arg, caller_locals, callee_path)?;
    let lhs = args[0].clone();
    let rhs = args[1].clone();
    let overflow = if is_add {
        if is_signed {
            lhs.clone().bvadd_no_overflow_signed(rhs.clone()).not()
        } else {
            lhs.clone().bvadd_no_overflow_unsigned(rhs.clone()).not()
        }
    } else if is_signed {
        lhs.clone().bvsub_no_overflow_signed(rhs.clone()).not()
    } else {
        lhs.clone().bvsub_no_underflow_unsigned(rhs.clone()).not()
    };
    let result = if is_add { lhs.clone().bvadd(rhs) } else { lhs.clone().bvsub(rhs) };
    let saturated = saturating_bound_expr(&lhs, width, is_add, is_signed)?;
    Some(Expr::ite(overflow, saturated, result))
}

pub(super) fn infer_inline_arith_signedness(
    first_arg: Option<&Operand>,
    caller_locals: &[LocalDecl],
    callee_path: &str,
) -> Option<bool> {
    if let Some(first_arg) = first_arg
        && let Ok(ty) = first_arg.ty(caller_locals)
    {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Int(_)) => return Some(true),
            TyKind::RigidTy(RigidTy::Uint(_)) => return Some(false),
            _ => {}
        }
    }

    let mut segments = callee_path.rsplit("::");
    let _method = segments.next()?;
    let receiver = segments.next()?;
    match receiver {
        "<impl i8>" | "<impl i16>" | "<impl i32>" | "<impl i64>" | "<impl i128>"
        | "<impl isize>" | "i8" | "i16" | "i32" | "i64" | "i128" | "isize" => Some(true),
        "<impl u8>" | "<impl u16>" | "<impl u32>" | "<impl u64>" | "<impl u128>"
        | "<impl usize>" | "u8" | "u16" | "u32" | "u64" | "u128" | "usize" => Some(false),
        _ => None,
    }
}

fn saturating_bound_expr(lhs: &Expr, width: u32, is_add: bool, is_signed: bool) -> Option<Expr> {
    if is_signed {
        let half = BigInt::from(1u128) << (width - 1);
        let max_val = Expr::bitvec_const(&half - 1, width);
        let min_val = Expr::bitvec_const(-half, width);
        let lhs_positive = lhs.clone().extract(width - 1, width - 1).eq(Expr::bitvec_const(0, 1));
        return Some(Expr::ite(lhs_positive, max_val, min_val));
    }

    if is_add {
        Some(Expr::bitvec_const(-1i128, width))
    } else {
        Some(Expr::bitvec_const(0u64, width))
    }
}
