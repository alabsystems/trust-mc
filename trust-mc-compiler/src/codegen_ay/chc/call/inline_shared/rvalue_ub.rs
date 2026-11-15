// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Integer `BinaryOp` UB checks for the inline body walker.
//!
//! The statement path checks every UB-carrying integer BinOp in
//! `emit_assignment_safety_checks` (`stmt/codegen_stmt/codegen_stmt_fallback.rs`).
//! The inline walker translated the same BinOps to plain bitvector arithmetic
//! (`inline_rvalue_to_expr` -> `binop_to_expr` -> `translate_binop`) and
//! recorded nothing, so `_0 = AddUnchecked(_1, _2)` inside a WALKED body (a dyn
//! method, a fn_inline body walk, a fn-pointer or `Box<dyn Fn>` body, a nested
//! helper, core's own `unchecked_*` wrapper) verified SUCCESSFUL when it
//! overflows. Core's `assert_unsafe_precondition!` cannot catch it: its branch
//! is dead in both tools (`check_language_ub()` folds to `false`, as Kani
//! compiles `RuntimeChecks`), so the obligation Kani reports is the BinOp's own
//! (kani-compiler `codegen_rvalue.rs::codegen_binop_with_overflow_check`,
//! `check_unchecked_shift_distance`, `check_div_overflow`).
//!
//! [`inline_binop_ub_checks`] computes the statement path's conditions with the
//! statement path's helpers and gates, and labels them with Kani's property
//! class and messages. The walker records them on its deferred-check channel
//! (`InlineExecutionState::record_deferred_check`), which adds the walk's path
//! condition and is emitted by the host call site as real error rules. Only
//! error clauses are added: no value, transition or assume changes. (The host
//! skips a check that is valid whatever its state, and an exact duplicate such
//! as the divisor check beside a walked user `a / b`'s own MIR `Assert`:
//! `emit_deferred_inline_checks_at`.)
//!
//! A consumer that walks a body must either emit the returned
//! `deferred_checks` (the call hosts and drop consumers) or fail closed when
//! it drops one (`translate_closure_inline_body`,
//! the fold replay's fallback). Several walker routes still lose checks before
//! they are recorded -- see `rustc_compat.rs` (`UbChecks`) for the measured list.

use ay_bindings::Expr;
use rustc_public::mir::{BinOp, LocalDecl, Operand, Rvalue};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashMap;
use trust_mc_core::violation::PropertyKind;

use super::super::ChcCtx;
use super::super::codegen_expr_signedness::infer_inline_binop_signedness;
use super::super::inline_body::{DeferredInlineCheck, InlineReturn};
use super::PlaceResolver;
use super::place::inline_operand_to_expr;
use super::rvalue_ptr::coerce_dt_wrapper_to_bv;
use crate::codegen_ay::chc::heap_state::HeapWriteMark;
use crate::codegen_ay::chc::stmt::codegen_stmt::codegen_stmt_safety_checks::{
    division_by_zero_condition, signed_div_overflow_condition, unchecked_shift_distance_condition,
};
use crate::codegen_ay::chc::ty_signedness;
use crate::codegen_ay::types::ty_to_bv_width;

/// Fallback reason recorded when a UB-carrying BinOp's operand does not
/// translate. Deliberately NOT on the `fallback_soundness` blessed list: an
/// obligation was dropped, so it must fail closed. The driver then never
/// reports a clean SUCCESSFUL: a proof is demoted (measured on this engine as a
/// non-certified `FAILED` with `[AY:CTREX_CAT:OverApproximation:
/// chc_translation_drop=N]` and zero failed checks), which costs precision on a
/// correct program and never soundness.
pub(in crate::codegen_ay::chc) const INLINE_RVALUE_UB_CHECK_DROPPED: &str =
    "inline_rvalue_ub_check_dropped";

/// Outcome of [`inline_binop_ub_checks`].
pub(in crate::codegen_ay::chc) enum InlineUbChecks {
    /// Not an integer BinOp that carries a UB obligation, or the obligation is
    /// disabled by configuration exactly as on the statement path.
    NotApplicable,
    /// The MUST-HOLD checks, WITHOUT a path condition (the caller records them
    /// through `record_deferred_check`, which adds it).
    Checks(Vec<DeferredInlineCheck>),
    /// The BinOp carries an obligation, but an operand did not translate to a
    /// bitvector. The caller must record [`INLINE_RVALUE_UB_CHECK_DROPPED`].
    Untranslatable,
}

/// The UB checks one inline `Rvalue` carries, mirroring the statement path.
///
/// | op | condition (statement-path helper) | when |
/// |---|---|---|
/// | `AddUnchecked` / `SubUnchecked` / `MulUnchecked` | `ChcCtx::unchecked_overflow_condition` | always |
/// | `ShlUnchecked` / `ShrUnchecked` | `unchecked_shift_distance_condition` | always |
/// | `Div` / `Rem`, divisor zero | `division_by_zero_condition` | always |
/// | `Div` / `Rem`, signed `MIN / -1` | `signed_div_overflow_condition` | signed |
///
/// No check is gated by `--no-overflow-checks`: each is UB Kani's compiler
/// asserts whatever that flag says (it takes only CBMC's instrumentation off),
/// or the redundant twin of a MIR `Assert` this lane keeps, as the statement
/// path's `emit_assignment_safety_checks` records them.
///
/// Float operands are `NotApplicable`: float division by zero is defined.
/// `Offset` and every other BinOp are `NotApplicable` (Kani checks no
/// `BinOp::Offset`). Operands are read BEFORE the caller writes the
/// destination, so `_1 = AddUnchecked(_1, _2)` checks the old `_1`.
pub(in crate::codegen_ay::chc) fn inline_binop_ub_checks(
    ctx: &mut ChcCtx<'_, '_>,
    rvalue: &Rvalue,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
    dest_local: Option<usize>,
) -> InlineUbChecks {
    let Rvalue::BinaryOp(op, lhs, rhs) = rvalue else {
        return InlineUbChecks::NotApplicable;
    };
    let op = *op;
    let unchecked = matches!(
        op,
        BinOp::AddUnchecked
            | BinOp::SubUnchecked
            | BinOp::MulUnchecked
            | BinOp::ShlUnchecked
            | BinOp::ShrUnchecked
    );
    if !unchecked && !matches!(op, BinOp::Div | BinOp::Rem) {
        return InlineUbChecks::NotApplicable;
    }
    let Ok(lhs_ty) = lhs.ty(locals) else {
        // Cannot tell a float from an integer, so cannot rule the check out.
        return InlineUbChecks::Untranslatable;
    };
    if matches!(lhs_ty.kind(), TyKind::RigidTy(RigidTy::Float(_))) {
        return InlineUbChecks::NotApplicable;
    }
    let (Some(l), Some(r)) = (
        inline_ub_operand_bv(ctx, lhs, local_exprs, resolver, locals),
        inline_ub_operand_bv(ctx, rhs, local_exprs, resolver, locals),
    ) else {
        return InlineUbChecks::Untranslatable;
    };
    // The walker's signedness source (`infer_inline_binop_signedness`, as its
    // VALUE translation of this BinOp uses). When it cannot tell, fall back as
    // the statement path's checks do (`emit_assignment_safety_checks`:
    // `signedness_fallback_for_arithmetic`, i.e. SIGNED), not as the value path
    // does (Div/Rem default unsigned): assuming signed keeps the `MIN / -1`
    // check, and the fallback is counted, so the harness is demoted either way.
    // Computed only when a condition needs it, so a shift or an unsigned-only
    // path adds no fallback count.
    let signed = || {
        infer_inline_binop_signedness(op, lhs, rhs, locals, dest_local).unwrap_or_else(|| {
            crate::codegen_ay::shared::signedness_fallback_for_arithmetic("inline_binop_ub_checks")
        })
    };
    // Distance signedness from the distance operand's own type, default
    // unsigned, as `emit_assignment_safety_checks` does.
    let distance_signed = || rhs.ty(locals).ok().and_then(ty_signedness).unwrap_or(false);
    let write_mark = ctx.heap_state.write_mark();
    match binop_ub_conditions(op, &l, &r, signed, distance_signed, write_mark) {
        Some(checks) => InlineUbChecks::Checks(checks),
        // A helper declined an operand it should have accepted (both are
        // bitvectors here): the obligation is lost, so fail closed.
        None => InlineUbChecks::Untranslatable,
    }
}

/// The UB checks of an integer `op` on bitvector operands `l` and `r`, with
/// Kani's property class and messages (see [`inline_binop_ub_checks`]'s
/// table); `None` if a condition helper declines an operand. `signed` and
/// `distance_signed` are asked only when a condition needs them. `write_mark`
/// is the heap write mark at the BinOp (`DeferredInlineCheck::write_mark`).
fn binop_ub_conditions(
    op: BinOp,
    l: &Expr,
    r: &Expr,
    signed: impl Fn() -> bool,
    distance_signed: impl FnOnce() -> bool,
    write_mark: HeapWriteMark,
) -> Option<Vec<DeferredInlineCheck>> {
    let mut checks = Vec::new();
    let mut push = |condition: Option<Expr>, message: &str| -> Option<()> {
        checks.push(DeferredInlineCheck {
            check: condition?,
            kind: PropertyKind::ArithmeticOverflow,
            message: Some(message.to_string()),
            write_mark,
            merge_key: None,
        });
        Some(())
    };
    match op {
        BinOp::AddUnchecked | BinOp::SubUnchecked | BinOp::MulUnchecked => {
            let op_name = match op {
                BinOp::AddUnchecked => "unchecked_add",
                BinOp::SubUnchecked => "unchecked_sub",
                _ => "unchecked_mul",
            };
            push(
                ChcCtx::unchecked_overflow_condition(op, l, r, signed()),
                &format!("attempt to compute `{op_name}` which would overflow"),
            )?;
        }
        BinOp::ShlUnchecked | BinOp::ShrUnchecked => {
            // A negative signed distance fails this one check; Kani words that
            // case "attempt to shift by negative distance", the verdict is the
            // same.
            push(
                unchecked_shift_distance_condition(l, r, distance_signed()),
                "attempt to shift by excessive shift distance",
            )?;
        }
        BinOp::Div | BinOp::Rem => {
            let is_rem = matches!(op, BinOp::Rem);
            let zero_message = if is_rem {
                "attempt to calculate the remainder with a divisor of zero"
            } else {
                "attempt to divide by zero"
            };
            push(division_by_zero_condition(r), zero_message)?;
            if signed() {
                let overflow_message = if is_rem {
                    "attempt to calculate the remainder with overflow"
                } else {
                    "attempt to divide with overflow"
                };
                push(signed_div_overflow_condition_mir_form(l, r), overflow_message)?;
            }
        }
        _ => {}
    }
    Some(checks)
}

/// A nested call of core's `unchecked_*` wrapper on a primitive, answered
/// without walking its body: the value of its one BinOp and that BinOp's UB
/// checks. Exactly what walking the body yields (its
/// `assert_unsafe_precondition!` branch is dead), but it spends no inline
/// depth. Walked, the wrapper sits at the bottom of std chains such as
/// `Rev::next -> Range::next_back -> spec_next_back ->
/// Step::backward_unchecked -> u8::unchecked_sub`, where `MAX_INLINE_DEPTH`
/// refused its body; the havoc that replaced it dropped the check, and now
/// books its lost effect (Rule D: the wrapper is not inert). `None` (so the caller
/// walks or havocs as before) unless both arguments are bitvectors and the
/// receiver is a primitive integer.
pub(in crate::codegen_ay::chc) fn inline_unchecked_arith_wrapper_call(
    ctx: &ChcCtx<'_, '_>,
    callee_path: &str,
    args: &[Operand],
    translated_args: &[Expr],
    locals: &[LocalDecl],
) -> Option<InlineReturn> {
    if !(callee_path.starts_with("core::num::<impl ")
        || callee_path.starts_with("std::num::<impl "))
    {
        return None;
    }
    let op = match callee_path.rsplit("::").next()? {
        "unchecked_add" => BinOp::AddUnchecked,
        "unchecked_sub" => BinOp::SubUnchecked,
        "unchecked_mul" => BinOp::MulUnchecked,
        "unchecked_shl" => BinOp::ShlUnchecked,
        "unchecked_shr" => BinOp::ShrUnchecked,
        _ => return None,
    };
    let ([lhs_op, rhs_op], [l, r]) = (args, translated_args) else {
        return None;
    };
    let l = coerce_dt_wrapper_to_bv(l.clone());
    let r = coerce_dt_wrapper_to_bv(r.clone());
    if !l.sort().is_bitvec() || !r.sort().is_bitvec() {
        return None;
    }
    let signed = match ctx.resolve_body_ty(lhs_op.ty(locals).ok()?).kind() {
        TyKind::RigidTy(RigidTy::Int(_)) => true,
        TyKind::RigidTy(RigidTy::Uint(_)) => false,
        _ => return None,
    };
    let width = l.sort().bitvec_width()?;
    let value = ctx.translate_binop(op, l.clone(), r.clone(), signed, width, false)?;
    let distance_signed = || {
        rhs_op
            .ty(locals)
            .ok()
            .and_then(|ty| ty_signedness(ctx.resolve_body_ty(ty)))
            .unwrap_or(false)
    };
    let checks =
        binop_ub_conditions(op, &l, &r, || signed, distance_signed, ctx.heap_state.write_mark())?;
    let mut result = InlineReturn::value_only(value);
    result.deferred_checks = checks;
    Some(result)
}

/// Does `body` carry an integer BinOp UB obligation that no MIR `Assert` of the
/// same body guards? The five unchecked ops never have one; an integer
/// `Div`/`Rem` from user `a / b` does (rustc asserts the divisor first), one
/// from `intrinsics::unchecked_div` / `Div<NonZero>` does not, so Div/Rem
/// count only beyond the body's divisor-zero asserts.
///
/// For translators that do NOT record [`inline_binop_ub_checks`] (the
/// quantifier closure-body walk): they must fail closed on such a body.
pub(in crate::codegen_ay::chc) fn body_carries_unguarded_binop_ub(
    body: &rustc_public::mir::Body,
) -> bool {
    use rustc_public::mir::{AssertMessage, StatementKind, TerminatorKind};
    let locals = body.locals();
    let mut div_rem = 0usize;
    let mut zero_asserts = 0usize;
    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(_, Rvalue::BinaryOp(op, lhs, _)) = &stmt.kind else {
                continue;
            };
            match op {
                BinOp::AddUnchecked
                | BinOp::SubUnchecked
                | BinOp::MulUnchecked
                | BinOp::ShlUnchecked
                | BinOp::ShrUnchecked => return true,
                BinOp::Div | BinOp::Rem => {
                    let is_float = lhs
                        .ty(locals)
                        .is_ok_and(|ty| matches!(ty.kind(), TyKind::RigidTy(RigidTy::Float(_))));
                    if !is_float {
                        div_rem += 1;
                    }
                }
                _ => {}
            }
        }
        if let TerminatorKind::Assert {
            msg: AssertMessage::DivisionByZero(_) | AssertMessage::RemainderByZero(_),
            ..
        } = &block.terminator.kind
        {
            zero_asserts += 1;
        }
    }
    div_rem > zero_asserts
}

/// `¬(rhs == -1 ∧ lhs == MIN)`: the statement path's
/// `signed_div_overflow_condition` (`lhs != MIN ∨ rhs != -1`), spelled the way
/// the walker translates rustc's own guard for a user `a / b` on a signed type
/// (`_5 = Eq(rhs, -1); _6 = Eq(lhs, MIN); _7 = BitAnd(_5, _6); assert(!_7)`,
/// rustc_mir_build `build_binary_op`), so the two checks are the same `Expr`
/// and the host emits it once. The two spellings are equivalent by De Morgan.
fn signed_div_overflow_condition_mir_form(lhs: &Expr, rhs: &Expr) -> Option<Expr> {
    let width = lhs.sort().bitvec_width()?;
    if rhs.sort().bitvec_width() != Some(width) {
        return signed_div_overflow_condition(lhs, rhs);
    }
    let int_min = Expr::bitvec_const(1u128 << (width - 1), width);
    let neg_one = Expr::bitvec_const(!0u128, width);
    Some(rhs.clone().eq(neg_one).and(lhs.clone().eq(int_min)).not())
}

/// Translate one BinOp operand to a bitvector, as `inline_rvalue_to_expr`
/// does (`coerce_dt_wrapper_to_bv`), lowering an Int-lifted local through the
/// same `int2bv(ty_to_bv_width(ty))` round trip its bitwise-`Not` arm uses.
fn inline_ub_operand_bv(
    ctx: &mut ChcCtx<'_, '_>,
    operand: &Operand,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
) -> Option<Expr> {
    let expr = coerce_dt_wrapper_to_bv(inline_operand_to_expr(
        ctx,
        operand,
        local_exprs,
        resolver,
        locals,
    )?);
    if expr.sort().is_bitvec() {
        Some(expr)
    } else if expr.sort().is_int() {
        Some(expr.int2bv(ty_to_bv_width(operand.ty(locals).ok()?)?))
    } else {
        None
    }
}
