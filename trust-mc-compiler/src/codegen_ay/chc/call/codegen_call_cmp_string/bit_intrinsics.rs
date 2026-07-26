// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Bit-manipulation intrinsic call handlers for CHC codegen.
//!
//! Handles compiler intrinsics that appear as `TerminatorKind::Call` in MIR:
//! - `bswap` / `swap_bytes` (byte reversal)
//! - `bitreverse` / `reverse_bits` (bit reversal)
//! - `black_box` / `likely` / `unlikely` (identity/no-op)
//! - `ctlz` / `ctlz_nonzero` / `leading_zeros` (count leading zeros)
//! - `cttz` / `cttz_nonzero` / `trailing_zeros` (count trailing zeros)
//! - `ctpop` / `count_ones` (population count)
//! - `rotate_left` / `rotate_right` (bit rotation)
//! - `unchecked_funnel_shl` / `unchecked_funnel_shr` (funnel shift)
//!
//! Both raw compiler intrinsics and their standard library wrapper methods
//! (e.g., `core::num::<impl u8>::leading_zeros`) are matched. The wrappers
//! have MIR bodies that call the raw intrinsics, but since the raw intrinsics
//! lack MIR bodies, fn_inline cannot resolve them. Handling both levels
//! ensures coverage regardless of MIR inlining success.
//!
//! These intrinsics have BV-level SMT translations but lack MIR bodies,
//! so fn_inline cannot handle them. Without call-level dispatch, they fall
//! through to the catch-all and get unconstrained treatment, causing
//! OverApproximation CTREX.
//!
//! Part of #3323: OverApproximation CTREX reduction Phase 2, Tier B.
//! BV implementations mirror `statement/intrinsics/bits.rs`.

use ay_bindings::Expr;
use rustc_public::mir::BasicBlockIdx;
use tracing::debug;

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::super::codegen_rules::CodegenRules;

mod bswap;
use bswap::compute_bswap;
mod cttz;
use cttz::compute_cttz;

/// Detect bit-manipulation intrinsic from callee path.
///
/// Returns the intrinsic kind if the path matches a known bit intrinsic,
/// None otherwise.
pub(in crate::codegen_ay::chc) fn detect_bit_intrinsic(path: &str) -> Option<BitIntrinsicKind> {
    let method = path
        .rsplit("::")
        .find(|segment| !segment.is_empty() && !segment.starts_with('<'))?
        .split('<')
        .next()?;
    match method {
        // Raw intrinsics + std lib wrapper methods
        "bswap" | "swap_bytes" => Some(BitIntrinsicKind::Bswap),
        "bitreverse" | "reverse_bits" => Some(BitIntrinsicKind::BitReverse),
        "black_box" => Some(BitIntrinsicKind::Identity),
        "likely" | "unlikely" => Some(BitIntrinsicKind::Identity),
        "ctlz" | "leading_zeros" => Some(BitIntrinsicKind::Ctlz),
        "ctlz_nonzero" => Some(BitIntrinsicKind::CtlzNonzero),
        "cttz" | "trailing_zeros" => Some(BitIntrinsicKind::Cttz),
        "cttz_nonzero" => Some(BitIntrinsicKind::CttzNonzero),
        "ctpop" | "count_ones" => Some(BitIntrinsicKind::Ctpop),
        "rotate_left" => Some(BitIntrinsicKind::RotateLeft),
        "rotate_right" => Some(BitIntrinsicKind::RotateRight),
        "unchecked_funnel_shl" => Some(BitIntrinsicKind::FunnelShiftLeft),
        "unchecked_funnel_shr" => Some(BitIntrinsicKind::FunnelShiftRight),
        _ => None,
    }
}

/// Inline a pure bit-intrinsic call as a BV expression when no side rules are needed.
///
/// This is used by the inline-known-calls fast path, which can only substitute
/// an expression into the caller. We therefore keep `_nonzero` variants
/// fail-closed here because their precise encoding also requires an UB error rule.
pub(in crate::codegen_ay) fn inline_bit_intrinsic_expr(
    callee_path: &str,
    translated_args: &[Expr],
) -> Option<Expr> {
    let kind = detect_bit_intrinsic(callee_path)?;
    let arg_expr = translated_args.first()?;
    match kind {
        BitIntrinsicKind::Identity => Some(arg_expr.clone()),
        BitIntrinsicKind::Bswap => compute_bswap(arg_expr),
        BitIntrinsicKind::BitReverse => compute_bitreverse(arg_expr),
        BitIntrinsicKind::Ctlz => compute_ctlz(arg_expr),
        BitIntrinsicKind::CtlzNonzero => None,
        BitIntrinsicKind::Cttz => compute_cttz(arg_expr),
        BitIntrinsicKind::CttzNonzero => None,
        BitIntrinsicKind::Ctpop => compute_ctpop(arg_expr),
        BitIntrinsicKind::RotateLeft => compute_rotate(arg_expr, translated_args.get(1)?, true),
        BitIntrinsicKind::RotateRight => compute_rotate(arg_expr, translated_args.get(1)?, false),
        BitIntrinsicKind::FunnelShiftLeft => {
            compute_funnel_shift(arg_expr, translated_args.get(1)?, translated_args.get(2)?, true)
        }
        BitIntrinsicKind::FunnelShiftRight => {
            compute_funnel_shift(arg_expr, translated_args.get(1)?, translated_args.get(2)?, false)
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(in crate::codegen_ay::chc) enum BitIntrinsicKind {
    Bswap,
    BitReverse,
    Identity,
    Ctlz,
    /// ctlz_nonzero: UB when input is zero. Emits error rule for zero input.
    CtlzNonzero,
    Cttz,
    /// cttz_nonzero: UB when input is zero. Emits error rule for zero input.
    CttzNonzero,
    Ctpop,
    /// rotate_left(x, n): bit rotation left. Two-argument intrinsic.
    RotateLeft,
    /// rotate_right(x, n): bit rotation right. Two-argument intrinsic.
    RotateRight,
    /// unchecked_funnel_shl(a, b, n): double-wide left shift. Three-argument intrinsic.
    /// fshl(a, b, n) = (a << n) | (b >> (width - n))
    FunnelShiftLeft,
    /// unchecked_funnel_shr(a, b, n): double-wide right shift. Three-argument intrinsic.
    /// fshr(a, b, n) = (a << (width - n)) | (b >> n)
    FunnelShiftRight,
}

/// Handle a bit-manipulation intrinsic call in CHC codegen.
///
/// Translates the intrinsic's first argument, computes the BV result,
/// constrains the destination, and emits a goto rule.
pub(in crate::codegen_ay::chc) fn codegen_bit_intrinsic(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    kind: BitIntrinsicKind,
) {
    let args = dcx.args;
    let destination = dcx.destination;
    let from_app = dcx.from_app;
    let stmt_constraints = dcx.stmt_constraints;
    let modified_locals = dcx.modified_locals;
    let dest_local: usize = destination.local;

    if args.is_empty() {
        debug!("bit intrinsic {:?} with no args — fallback", kind);
        emit_sound_fallback_goto(
            ctx,
            from_app,
            target,
            modified_locals,
            &[dest_local],
            stmt_constraints,
        );
        return;
    }

    // Translate the first argument
    let arg_expr = ctx.translate_operand_with_modified(&args[0], modified_locals);
    let Some(arg_expr) = arg_expr else {
        debug!("bit intrinsic {:?}: arg translation failed — fallback", kind);
        emit_sound_fallback_goto(
            ctx,
            from_app,
            target,
            modified_locals,
            &[dest_local],
            stmt_constraints,
        );
        return;
    };

    // Part of #3363: Emit nonzero UB error rule for ctlz_nonzero/cttz_nonzero.
    // These intrinsics have undefined behavior when the input is zero.
    // Mirrors BMC path: statement/intrinsics/bits.rs record_violation_guarded.
    if matches!(kind, BitIntrinsicKind::CtlzNonzero | BitIntrinsicKind::CttzNonzero) {
        if let Some(width) = arg_expr.sort().bitvec_width() {
            let zero = Expr::bitvec_const(0u64, width);
            // Check condition: input != 0 (true when safe).
            // emit_error_rule_for_condition negates: !(input != 0) → error.
            let nonzero_check = arg_expr.clone().eq(zero).not();
            ctx.emit_error_rule_for_condition(from_app, nonzero_check, stmt_constraints, target);
            debug!("bit intrinsic {:?}: emitted nonzero UB check (#3363)", kind);
        }
    }

    // Compute the result expression.
    // *_nonzero variants use the same BV formula — the "nonzero" precondition
    // means UB on zero input, not a different computation.
    // Rotate intrinsics need a second argument (rotation amount).
    let result = match kind {
        BitIntrinsicKind::Identity => Some(arg_expr),
        BitIntrinsicKind::Bswap => compute_bswap(&arg_expr),
        BitIntrinsicKind::BitReverse => compute_bitreverse(&arg_expr),
        BitIntrinsicKind::Ctlz | BitIntrinsicKind::CtlzNonzero => compute_ctlz(&arg_expr),
        BitIntrinsicKind::Cttz | BitIntrinsicKind::CttzNonzero => compute_cttz(&arg_expr),
        BitIntrinsicKind::Ctpop => compute_ctpop(&arg_expr),
        BitIntrinsicKind::RotateLeft | BitIntrinsicKind::RotateRight => {
            if args.len() < 2 {
                debug!("rotate intrinsic {:?}: needs 2 args, got {} — fallback", kind, args.len());
                None
            } else {
                let n_expr = ctx.translate_operand_with_modified(&args[1], modified_locals);
                match n_expr {
                    Some(n) => {
                        compute_rotate(&arg_expr, &n, matches!(kind, BitIntrinsicKind::RotateLeft))
                    }
                    None => {
                        debug!("rotate intrinsic {:?}: second arg translation failed", kind);
                        None
                    }
                }
            }
        }
        BitIntrinsicKind::FunnelShiftLeft | BitIntrinsicKind::FunnelShiftRight => {
            if args.len() < 3 {
                debug!("funnel shift {:?}: needs 3 args, got {} — fallback", kind, args.len());
                None
            } else {
                let b_expr = ctx.translate_operand_with_modified(&args[1], modified_locals);
                let n_expr = ctx.translate_operand_with_modified(&args[2], modified_locals);
                match (b_expr, n_expr) {
                    (Some(b), Some(n)) => compute_funnel_shift(
                        &arg_expr,
                        &b,
                        &n,
                        matches!(kind, BitIntrinsicKind::FunnelShiftLeft),
                    ),
                    _ => {
                        debug!("funnel shift {:?}: arg translation failed", kind);
                        None
                    }
                }
            }
        }
    };

    let Some(result) = result else {
        debug!("bit intrinsic {:?}: BV computation failed — fallback", kind);
        emit_sound_fallback_goto(
            ctx,
            from_app,
            target,
            modified_locals,
            &[dest_local],
            stmt_constraints,
        );
        return;
    };

    // FLATTEN_DEST (char_validity unit-wrapper gap): when the destination is a
    // flattened aggregate local — e.g. `black_box`'s (Identity) `TwoFields<(),
    // char>` pass-through — `resolve_destination` returns only the FIRST
    // flattened slot's var (here a Bool placeholder for the unit field), so
    // coercing the WHOLE datatype `result` into it fails and DROPS the equality
    // (a spurious `chc_coerce_eq_drop` that taints the whole harness's
    // counterexample OverApproximation). Decompose the datatype result into its
    // per-slot constraints instead — bit-exact and drop-free — mirroring the
    // `exact_div` handler. Scalar destinations are not flattened, so this returns
    // None for the common bit-intrinsic case and falls through unchanged.
    if let Some(fc) = ctx.build_flattened_destination_constraints(dest_local, result.clone()) {
        let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
        ctx.emit_goto_rule_extra(from_app, target, &new_output_args, stmt_constraints, fc);
        return;
    }

    // Constrain destination = result and emit goto rule
    if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
        let out_sort = dest_var.sort();
        let eq = ctx.make_coerced_eq_constraint(
            &dest_var,
            result,
            out_sort,
            dest_local,
            "codegen_call_bit_intrinsic",
        );
        let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
        ctx.emit_goto_rule_extra(from_app, target, &new_output_args, stmt_constraints, eq);
    } else {
        // Can't resolve destination — emit unconstrained transition
        emit_sound_fallback_goto(
            ctx,
            from_app,
            target,
            modified_locals,
            &[dest_local],
            stmt_constraints,
        );
    }
}

/// Compute `bitreverse` (bit reversal) for a bitvector expression.
///
/// Reverses all bits: bitreverse(0b1100) = 0b0011.
fn compute_bitreverse(x: &Expr) -> Option<Expr> {
    let width = x.sort().bitvec_width()?;

    let mut result: Option<Expr> = None;
    for i in 0..width {
        let bit = x.clone().extract(i, i);
        result = Some(match result {
            None => bit,
            Some(acc) => acc.concat(bit),
        });
    }

    result
}

/// Compute `ctlz` (count leading zeros) for a bitvector expression.
///
/// Uses an ITE cascade: if MSB is 1 → 0, elif bit[width-2] → 1, ...
/// If x == 0, result is width.
///
/// Rust intrinsic `ctlz::<T>(x: T) -> u32` always returns u32 regardless of
/// input width, so the result is BV32.
fn compute_ctlz(x: &Expr) -> Option<Expr> {
    let width = x.sort().bitvec_width()?;
    let out_width: u32 = 32;

    // Build ITE cascade from LSB (inner) to MSB (outer)
    let mut result = Expr::bitvec_const(width as u64, out_width);
    for i in 0..width {
        let bit = x.clone().extract(i, i);
        let bit_is_one = bit.eq(Expr::bitvec_const(1u64, 1));
        let count = (width - 1 - i) as u64;
        result = Expr::ite(bit_is_one, Expr::bitvec_const(count, out_width), result);
    }

    Some(result)
}

/// Compute `ctpop` (population count / count ones) for a bitvector expression.
///
/// Uses balanced binary tree reduction to keep formula depth O(log N) instead
/// of O(N). This is critical for solver performance on wider types (u32/u64)
/// where the linear chain causes timeouts.
///
/// Rust intrinsic `ctpop::<T>(x: T) -> u32` always returns u32 regardless of
/// input width, so the result is BV32.
fn compute_ctpop(x: &Expr) -> Option<Expr> {
    let width = x.sort().bitvec_width()?;
    let out_width: u32 = 32;
    let acc_width = ctpop_accumulator_width(width, out_width);

    // Sum in the smallest BV width that can represent `width`. Since the
    // population count is always in 0..=width, this avoids modular overflow
    // without forcing every intermediate addition into BV32.
    let mut bits: Vec<Expr> = (0..width)
        .map(|i| {
            let bit = x.clone().extract(i, i);
            if acc_width == 1 { bit } else { bit.zero_extend(acc_width - 1) }
        })
        .collect();

    // Tree reduction: pairwise sum until one value remains
    while bits.len() > 1 {
        let mut next = Vec::new();
        let mut i = 0;
        while i + 1 < bits.len() {
            next.push(bits[i].clone().bvadd(bits[i + 1].clone()));
            i += 2;
        }
        if i < bits.len() {
            next.push(bits[i].clone());
        }
        bits = next;
    }

    let result = bits.into_iter().next().unwrap_or_else(|| Expr::bitvec_const(0u64, acc_width));
    Some(if acc_width == out_width { result } else { result.zero_extend(out_width - acc_width) })
}

fn ctpop_accumulator_width(input_width: u32, out_width: u32) -> u32 {
    if input_width <= 32 { bit_width_for_unsigned_max(input_width) } else { out_width }
}

fn bit_width_for_unsigned_max(max: u32) -> u32 {
    (u32::BITS - max.leading_zeros()).max(1).next_power_of_two().min(32)
}

/// Compute `rotate_left` or `rotate_right` for bitvector expressions.
///
/// rotate_left(x, n) = (x << n') | (x >> (width - n')) where n' = n % width
/// rotate_right(x, n) = (x >> n') | (x << (width - n')) where n' = n % width
///
/// Mirrors `statement/intrinsics/bits.rs::codegen_rotate`.
fn compute_rotate(x: &Expr, n: &Expr, left: bool) -> Option<Expr> {
    let width = x.sort().bitvec_width()?;

    // Coerce n to same width as x (Rust rotate intrinsics take u32 for n,
    // but the BV operations need matching widths).
    let n_width = n.sort().bitvec_width()?;
    let n = if n_width < width {
        n.clone().zero_extend(width - n_width)
    } else if n_width > width {
        n.clone().extract(width - 1, 0)
    } else {
        n.clone()
    };

    let width_const = Expr::bitvec_const(width as u64, width);
    // Rust integer widths are powers of two, so n % width is n & (width - 1).
    // Avoiding bvurem keeps rotate VCs in the cheaper bitwise fragment.
    let rotate_mask = Expr::bitvec_const(width as u64 - 1, width);
    let n_mod = n.bvand(rotate_mask);
    let width_minus_n = width_const.bvsub(n_mod.clone());

    let result = if left {
        // rotate_left: (x << n') | (x >> (width - n'))
        x.clone().bvshl(n_mod).bvor(x.clone().bvlshr(width_minus_n))
    } else {
        // rotate_right: (x >> n') | (x << (width - n'))
        x.clone().bvlshr(n_mod).bvor(x.clone().bvshl(width_minus_n))
    };

    Some(result)
}

/// Compute `unchecked_funnel_shl` or `unchecked_funnel_shr` for bitvector expressions.
///
/// Funnel shift concatenates two values and shifts across them:
/// - funnel_shl(a, b, n) = (a << n) | (b >> (width - n))
/// - funnel_shr(a, b, n) = (a << (width - n)) | (b >> n)
///
/// The "unchecked" variant assumes n is in range [0, width) — no bounds checking.
/// The shift amount `n` comes as u32 from Rust, so width coercion is needed.
///
/// Mirrors `statement/intrinsics/bits.rs::codegen_funnel_shift`.
fn compute_funnel_shift(a: &Expr, b: &Expr, n: &Expr, left: bool) -> Option<Expr> {
    let width = a.sort().bitvec_width()?;

    // Coerce n to same width as a/b (Rust funnel shift intrinsics take u32 for n,
    // but the BV operations need matching widths).
    let n_width = n.sort().bitvec_width()?;
    let n = if n_width < width {
        n.clone().zero_extend(width - n_width)
    } else if n_width > width {
        n.clone().extract(width - 1, 0)
    } else {
        n.clone()
    };

    let width_const = Expr::bitvec_const(width as u64, width);
    let width_minus_n = width_const.bvsub(n.clone());

    let result = if left {
        // funnel_shl(a, b, n) = (a << n) | (b >> (width - n))
        a.clone().bvshl(n).bvor(b.clone().bvlshr(width_minus_n))
    } else {
        // funnel_shr(a, b, n) = (a << (width - n)) | (b >> n)
        a.clone().bvshl(width_minus_n).bvor(b.clone().bvlshr(n))
    };

    Some(result)
}

#[cfg(test)]
#[path = "bit_intrinsics_tests.rs"]
mod bit_intrinsics_tests;
