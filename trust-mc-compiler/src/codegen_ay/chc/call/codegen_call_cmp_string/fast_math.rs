// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Fast-math intrinsic call handlers for CHC codegen.
//!
//! Handles `fadd_fast`, `fsub_fast`, `fmul_fast`, `fdiv_fast` compiler
//! intrinsics that appear as `TerminatorKind::Call` in MIR. These intrinsics
//! have undefined behavior when operands are NaN or Inf (non-finite).
//!
//! Emits IEEE 754 finiteness error rules: extracts the exponent field and
//! checks if all-ones (NaN/Inf indicator). When non-finite, emits `error()`.
//! The arithmetic result is constrained via FP theory (bv_to_fp → fp.op →
//! fp_to_ieee_bv), matching the normal float BinOp encoding (Part of #3693).
//!
//! Mirrors BMC path: `statement/intrinsics/math.rs::record_fast_float_finite`.
//! Part of #3363: false PROOF on intentionally buggy fast-math harnesses.

use crate::codegen_ay::chc::float_fast_math_patterns::float_finite_condition_matches_operand;
use crate::kani_middle::kani_functions::KaniHook;
use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, TerminatorKind};
use tracing::debug;

use super::super::ChcCtx;
use super::super::RelationApp;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::super::codegen_rules::CodegenRules;

/// Detect fast-math intrinsic from callee path.
///
/// Returns `true` if the path matches a known fast-math intrinsic.
pub(in crate::codegen_ay::chc) fn detect_fast_math_intrinsic(path: &str) -> bool {
    path.contains("fadd_fast")
        || path.contains("fsub_fast")
        || path.contains("fmul_fast")
        || path.contains("fdiv_fast")
}

/// Handle a fast-math intrinsic call in CHC codegen.
///
/// Translates both operand arguments, emits IEEE 754 finiteness error rules
/// for each (NaN/Inf = UB), and constrains the destination via FP theory
/// arithmetic (bv_to_fp → fp.add/sub/mul/div → fp_to_ieee_bv).
/// This matches the BMC path and normal float BinOp encoding (Part of #3693).
///
/// Part of #3140: fast-math BV arithmetic axioms.
pub(in crate::codegen_ay::chc) fn codegen_fast_math_intrinsic(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    callee_path: &str,
) {
    let args = dcx.args;
    let destination = dcx.destination;
    let from_app = dcx.from_app;
    let stmt_constraints = dcx.stmt_constraints;
    let modified_locals = dcx.modified_locals;
    let dest_local: usize = destination.local;

    if args.len() < 2 {
        debug!("fast-math intrinsic with < 2 args — fallback");
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

    // Translate both operands and emit finiteness checks.
    let lhs = ctx.translate_operand_with_modified(&args[0], modified_locals);
    let rhs = ctx.translate_operand_with_modified(&args[1], modified_locals);

    let lhs_assumed_finite = has_dominating_finite_assume(ctx, dcx.bb_idx, &args[0]);
    let rhs_assumed_finite = has_dominating_finite_assume(ctx, dcx.bb_idx, &args[1]);

    if let Some(ref expr) = lhs
        && !lhs_assumed_finite
    {
        emit_finite_check(ctx, expr, from_app, stmt_constraints, target);
    }
    if let Some(ref expr) = rhs
        && !rhs_assumed_finite
    {
        emit_finite_check(ctx, expr, from_app, stmt_constraints, target);
    }

    debug!(
        lhs_assumed_finite,
        rhs_assumed_finite, "fast-math intrinsic: emitted required finiteness checks (#3363)"
    );

    // Constrain destination to the BV arithmetic result (Part of #3140).
    // Fast-math semantics: same as regular arithmetic when inputs are finite.
    // The BV encoding (bvadd/bvsub/bvmul/bvudiv) matches how regular
    // BinOp::Add/Sub/Mul/Div encodes float arithmetic in the CHC path.
    //
    // No NaN-generation obligation is emitted HERE (unlike the regular BinOp
    // site, Kani --nan-check parity): for fadd/fsub/fmul_fast the operand
    // finiteness rules above subsume it — either an operand can be non-finite
    // (finiteness error fires) or all operands are finite (finite ⊕ finite can
    // overflow to ±inf but can NEVER produce NaN). fdiv_fast(0, 0) result-NaN
    // with finite operands remains uncovered, matching the pre-existing
    // behavior (the destination used to be havocked with nothing checking it)
    // and Kani's args-only intrinsic checks.
    if let (Some(l), Some(r)) = (lhs, rhs)
        && let Some((_, dest_var)) = ctx.resolve_destination(dest_local)
    {
        // Part of #3693: Route fast-math through the shared float-binop helper
        // so the intrinsic emits the SAME term as the regular BinOp site.
        let bv_result = compute_fp_arith(ctx, callee_path, l, r);
        if let Some(result_expr) = bv_result {
            let eq = ctx.make_coerced_eq_constraint(
                &dest_var,
                result_expr,
                dest_var.sort(),
                dest_local,
                "codegen_fast_math_intrinsic",
            );
            let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(from_app, target, &new_output_args, stmt_constraints, eq);
            return;
        }
    }

    // Fallback: unconstrained destination (sound over-approximation).
    // Do NOT call record_sound_fallback() — finiteness checks are the
    // primary contribution; the unconstrained result is standard behavior
    // for fast-math intrinsics (matches original handler).
    let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
    ctx.emit_goto_rule(from_app, target, &new_output_args, stmt_constraints);
}

/// Compute the arithmetic result term for a fast-math intrinsic.
///
/// Routes through `ChcCtx::float_binop_chc_term` — the same helper the
/// regular BinOp site uses — so identical `(op, lhs, rhs)` produce identical
/// terms (constant fold, or congruent unconstrained-table select; see
/// float_binop_table.rs). Congruence is what lets AY discharge
/// `fadd_fast(x, y) == x + y` style equalities semantically.
/// Part of #3693: eliminate BV/FP mismatch between fast-math and normal ops.
fn compute_fp_arith(ctx: &ChcCtx<'_, '_>, callee_path: &str, lhs: Expr, rhs: Expr) -> Option<Expr> {
    use rustc_public::mir::BinOp;

    let op = if callee_path.contains("fadd_fast") {
        BinOp::Add
    } else if callee_path.contains("fsub_fast") {
        BinOp::Sub
    } else if callee_path.contains("fmul_fast") {
        BinOp::Mul
    } else if callee_path.contains("fdiv_fast") {
        BinOp::Div
    } else {
        return None;
    };
    let width = lhs.sort().bitvec_width()?;
    ctx.float_binop_chc_term(op, lhs, rhs, width)
}

/// True when a `kani::assume(is_finite(arg))`-shaped call strictly dominates
/// `call_bb` for this operand. Shared with the regular-BinOp NaN-generation
/// obligation (Kani --nan-check parity) as its non-NaN-source discharge test.
pub(in crate::codegen_ay::chc) fn has_dominating_finite_assume<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    call_bb: BasicBlockIdx,
    arg: &'body Operand,
) -> bool {
    let dominators = compute_dominators(ctx);
    ctx.body.blocks.iter().enumerate().any(|(assume_bb, block)| {
        assume_bb != call_bb
            && block_dominates(&dominators, assume_bb, call_bb)
            && matches!(
                &block.terminator.kind,
                TerminatorKind::Call {
                    func,
                    args,
                    target: Some(_),
                    ..
                } if matches!(ctx.detect_kani_hook(func), Some(KaniHook::Assume))
                    && args.first().is_some_and(|cond| {
                        float_finite_condition_matches_operand(ctx, cond, arg)
                    })
            )
    })
}

fn compute_dominators<'tcx, 'body>(ctx: &ChcCtx<'tcx, 'body>) -> Vec<Vec<bool>> {
    let block_count = ctx.body.blocks.len();
    let successors = ctx
        .body
        .blocks
        .iter()
        .map(|block| ChcCtx::block_successors(&block.terminator.kind))
        .collect::<Vec<_>>();
    let reachable = reachable_blocks(&successors);
    let mut predecessors = vec![Vec::new(); block_count];
    for (source, targets) in successors.iter().enumerate() {
        for &target in targets {
            if target < block_count {
                predecessors[target].push(source);
            }
        }
    }

    let mut dominators = vec![vec![false; block_count]; block_count];
    for block in 0..block_count {
        if reachable[block] {
            dominators[block].fill(true);
        }
    }
    if block_count > 0 {
        dominators[0].fill(false);
        dominators[0][0] = true;
    }

    let mut changed = true;
    while changed {
        changed = false;
        for block in 1..block_count {
            if !reachable[block] {
                continue;
            }
            let mut next = vec![true; block_count];
            let mut saw_reachable_pred = false;
            for &pred in &predecessors[block] {
                if !reachable[pred] {
                    continue;
                }
                saw_reachable_pred = true;
                for (candidate, dominated) in next.iter_mut().enumerate() {
                    *dominated &= dominators[pred][candidate];
                }
            }
            if !saw_reachable_pred {
                next.fill(false);
            }
            next[block] = true;
            if next != dominators[block] {
                dominators[block] = next;
                changed = true;
            }
        }
    }

    dominators
}

fn reachable_blocks(successors: &[Vec<usize>]) -> Vec<bool> {
    let mut reachable = vec![false; successors.len()];
    if successors.is_empty() {
        return reachable;
    }
    let mut stack = vec![0usize];
    reachable[0] = true;
    while let Some(block) = stack.pop() {
        for &successor in &successors[block] {
            if successor < successors.len() && !reachable[successor] {
                reachable[successor] = true;
                stack.push(successor);
            }
        }
    }
    reachable
}

fn block_dominates(dominators: &[Vec<bool>], dominator: usize, block: usize) -> bool {
    dominators
        .get(block)
        .and_then(|block_dominators| block_dominators.get(dominator))
        .copied()
        .unwrap_or(false)
}

/// Emit IEEE 754 finiteness check: `error()` when exponent bits are all-ones.
///
/// For f32: exponent is bits [30:23], all-ones = 0xFF.
/// For f64: exponent is bits [62:52], all-ones = 0x7FF.
/// When exponent is all-ones, the value is NaN or Inf — UB for fast-math.
///
/// Mirrors `statement/intrinsics/math.rs::record_fast_float_finite`.
fn emit_finite_check(
    ctx: &mut ChcCtx<'_, '_>,
    value: &Expr,
    from_app: &RelationApp,
    stmt_constraints: &[Expr],
    bb_idx: BasicBlockIdx,
) {
    let Some(width) = value.sort().bitvec_width() else {
        return;
    };

    let (exp_hi, exp_lo, exp_all_ones) = match width {
        32 => (30u32, 23u32, 0xFFu64),
        64 => (62u32, 52u32, 0x7FFu64),
        _ => return,
    };

    let exp = value.clone().extract(exp_hi, exp_lo);
    let exp_width = exp_hi - exp_lo + 1;
    // is_finite: exponent != all-ones (true when operand is finite/safe).
    // emit_error_rule_for_condition negates: !(is_finite) → error.
    let is_finite = exp.eq(Expr::bitvec_const(exp_all_ones, exp_width)).not();
    ctx.emit_error_rule_for_condition(from_app, is_finite, stmt_constraints, bb_idx);
}
