// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The inline walker records the integer BinOp UB checks the statement path
//! records (`inline_shared/rvalue_ub.rs`).
//!
//! Before the fix the walker translated `AddUnchecked` & co. as plain bitvector
//! arithmetic and recorded nothing, so an overflowing `unchecked_add` inside a
//! dyn method body verified SUCCESSFUL (tools/soundness-duals/
//! unchecked_arith_walker_dual.rs). Every test first asserts that the probe body
//! really contains the BinOp it is about, so a MIR-lowering change cannot turn a
//! test into a vacuous pass.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

use crate::codegen_ay::chc::call::inline_body::{InlineReturn, translate_inline_body};
use crate::codegen_ay::chc::call::inline_shared::{
    INLINE_RVALUE_UB_CHECK_DROPPED, InlineUbChecks, PlaceResolver, inline_binop_ub_checks,
};
use crate::codegen_ay::chc::codegen_ctx::{FallbackSoundness, fallback_soundness};
use ay_bindings::{Expr, Sort};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{BinOp, Body, Rvalue, StatementKind, TerminatorKind};
use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use trust_mc_core::violation::PropertyKind;

const BINOP_UB_PROBE: &str = r#"
    #![allow(dead_code)]
    #![allow(internal_features)]
    #![feature(core_intrinsics)]

    use core::intrinsics;

    pub fn probe_ub_add_u8(a: u8, b: u8) -> u8 { unsafe { intrinsics::unchecked_add(a, b) } }
    pub fn probe_ub_sub_u8(a: u8, b: u8) -> u8 { unsafe { intrinsics::unchecked_sub(a, b) } }
    pub fn probe_ub_mul_u8(a: u8, b: u8) -> u8 { unsafe { intrinsics::unchecked_mul(a, b) } }
    pub fn probe_ub_add_i8(a: i8, b: i8) -> i8 { unsafe { intrinsics::unchecked_add(a, b) } }
    pub fn probe_ub_sub_i8(a: i8, b: i8) -> i8 { unsafe { intrinsics::unchecked_sub(a, b) } }
    pub fn probe_ub_mul_i8(a: i8, b: i8) -> i8 { unsafe { intrinsics::unchecked_mul(a, b) } }
    pub fn probe_ub_shl_u8(a: u8, b: u32) -> u8 { unsafe { intrinsics::unchecked_shl(a, b) } }
    pub fn probe_ub_shr_u8(a: u8, b: u32) -> u8 { unsafe { intrinsics::unchecked_shr(a, b) } }

    pub fn probe_ub_wrapper_add_u8(a: u8, b: u8) -> u8 { unsafe { a.unchecked_add(b) } }
    pub fn probe_ub_guarded_add_u8(a: u8, b: u8) -> u8 {
        if a < 100 && b < 100 { unsafe { intrinsics::unchecked_add(a, b) } } else { 0 }
    }

    pub fn probe_ub_wrapping_add_u8(a: u8, b: u8) -> u8 { intrinsics::wrapping_add(a, b) }
    pub fn probe_ub_div_f32(a: f32, b: f32) -> f32 { a / b }

    pub fn probe_ub_shl_i32_distance(a: u8, b: i32) -> u8 { unsafe { intrinsics::unchecked_shl(a, b) } }
    pub fn probe_ub_add_into_field(a: u8, b: u8) -> (u8, u8) {
        let mut t = (0u8, 0u8);
        t.0 = unsafe { intrinsics::unchecked_add(a, b) };
        t
    }
    pub fn probe_ub_single_guard_add(a: u8, b: u8) -> u8 {
        if a < 100 { unsafe { intrinsics::unchecked_add(a, b) } } else { 0 }
    }
    pub fn probe_user_div_i32(a: i32, b: i32) -> i32 { a / b }

    pub fn probe_std_checked_sub(a: u32, b: u32) -> Option<u32> { a.checked_sub(b) }
    pub fn probe_std_checked_div(a: u32, b: u32) -> Option<u32> { a.checked_div(b) }
    pub fn probe_std_wrapping_shl(a: u32, s: u32) -> u32 { a.wrapping_shl(s) }
    pub fn probe_std_wrapping_shr_u8(a: u8, s: u32) -> u8 { a.wrapping_shr(s) }

    pub fn probe_ub_div_u32(a: u32, b: u32) -> u32 { unsafe { intrinsics::unchecked_div(a, b) } }
    pub fn probe_ub_rem_u32(a: u32, b: u32) -> u32 { unsafe { intrinsics::unchecked_rem(a, b) } }
    pub fn probe_ub_div_i32(a: i32, b: i32) -> i32 { unsafe { intrinsics::unchecked_div(a, b) } }
    pub fn probe_ub_rem_i32(a: i32, b: i32) -> i32 { unsafe { intrinsics::unchecked_rem(a, b) } }
"#;

fn bv_param(name: &str, width: u32) -> Expr {
    Expr::var(name.to_string(), Sort::bitvec(width))
}

/// Compile `BINOP_UB_PROBE` and run `test` on it, failing if `test` never ran
/// (a compile that stops early would otherwise pass every assertion vacuously).
fn with_probe(test: impl for<'tcx> FnOnce(TyCtxt<'tcx>) + Send) {
    let ran = AtomicBool::new(false);
    with_test_ay_ctx_for_source(BINOP_UB_PROBE, |ctx| {
        test(ctx.tcx);
        ran.store(true, Ordering::SeqCst);
    });
    assert!(ran.load(Ordering::SeqCst), "the probe crate compiled and the test body ran");
}

/// One fresh parameter per argument local, with the sort the encoder gives
/// the argument's type (`ChcCtx::translate_ty`).
fn arg_params(body: &Body) -> Vec<Expr> {
    (1..=body.arg_locals().len())
        .map(|local| {
            let ty = body.locals()[local].ty;
            let sort = ChcCtx::translate_ty(ty).expect("argument type translates");
            Expr::var(format!("arg{local}"), sort)
        })
        .collect()
}

/// The first `BinaryOp(op, ..)` rvalue assigned anywhere in `body`.
fn find_binop(body: &Body, op: BinOp) -> Option<Rvalue> {
    body.blocks.iter().flat_map(|bb| bb.statements.iter()).find_map(|stmt| match &stmt.kind {
        StatementKind::Assign(_, rvalue @ Rvalue::BinaryOp(found, ..)) if *found == op => {
            Some(rvalue.clone())
        }
        _ => None,
    })
}

fn assert_body_has_binop(body: &Body, op: BinOp, fn_name: &str) {
    assert!(
        find_binop(body, op).is_some(),
        "{fn_name}: probe body must contain a `BinaryOp({op:?}, ..)` statement, got {:#?}",
        body.blocks
    );
}

/// Walk `body` as an inline body with the given parameter expressions.
fn walk(
    tcx: TyCtxt<'_>,
    instance: Instance,
    body: &Body,
    fn_name: &str,
    config: ChcConfig,
    params: &[Expr],
) -> InlineReturn {
    let mut chc_ctx = ChcCtx::new(tcx, body, fn_name, config);
    chc_ctx.declare_block_relations();
    chc_ctx.mark_inline_field_reads(body, params, 0);
    translate_inline_body(&mut chc_ctx, body, params, 0, &HashMap::new(), Some(instance), 0)
        .unwrap_or_else(|| panic!("{fn_name}: inline body should translate"))
}

/// The walk's `ArithmeticOverflow` deferred checks, as `(message, check)`.
fn overflow_checks(inline_result: &InlineReturn) -> Vec<(String, Expr)> {
    inline_result
        .deferred_checks
        .iter()
        .filter(|c| c.kind == PropertyKind::ArithmeticOverflow)
        .map(|c| (c.message.clone().expect("a Kani message"), c.check.clone()))
        .collect()
}

/// Walk the two-argument `fn_name` (which must contain `op`) with fresh
/// parameters and return its `ArithmeticOverflow` checks with the parameters.
fn walk_binop_probe(
    tcx: TyCtxt<'_>,
    fn_name: &str,
    op: BinOp,
    config: ChcConfig,
) -> (Vec<(String, Expr)>, Expr, Expr) {
    let instance = find_instance_by_suffix(tcx, fn_name);
    let body = instance.body().expect("function body");
    assert_body_has_binop(&body, op, fn_name);
    let params = arg_params(&body);
    let [a, b] = <[Expr; 2]>::try_from(params.clone()).expect("two arguments");
    let inline_result = walk(tcx, instance, &body, fn_name, config, &params);
    (overflow_checks(&inline_result), a, b)
}

#[test]
fn test_inline_unchecked_add_sub_mul_record_one_kani_check_each() {
    with_probe(|tcx| {
        let cases = [
            ("probe_ub_add_u8", BinOp::AddUnchecked, false, "unchecked_add"),
            ("probe_ub_sub_u8", BinOp::SubUnchecked, false, "unchecked_sub"),
            ("probe_ub_mul_u8", BinOp::MulUnchecked, false, "unchecked_mul"),
            ("probe_ub_add_i8", BinOp::AddUnchecked, true, "unchecked_add"),
            ("probe_ub_sub_i8", BinOp::SubUnchecked, true, "unchecked_sub"),
            ("probe_ub_mul_i8", BinOp::MulUnchecked, true, "unchecked_mul"),
        ];
        for (fn_name, op, signed, op_name) in cases {
            let (checks, a, b) = walk_binop_probe(tcx, fn_name, op, ChcConfig::default());
            assert_eq!(checks.len(), 1, "{fn_name}: exactly one overflow check, got {checks:?}");
            assert_eq!(
                checks[0].0,
                format!("attempt to compute `{op_name}` which would overflow"),
                "{fn_name}: Kani's message"
            );
            // The statement path's exact condition, with the signedness of the
            // operand type (u8 unsigned, i8 signed).
            let expected = ChcCtx::unchecked_overflow_condition(op, &a, &b, signed)
                .expect("statement-path condition");
            assert_eq!(checks[0].1, expected, "{fn_name}: statement-path condition");
        }
    });
}

#[test]
fn test_inline_unchecked_shifts_record_shift_distance_check() {
    with_probe(|tcx| {
        for (fn_name, op) in
            [("probe_ub_shl_u8", BinOp::ShlUnchecked), ("probe_ub_shr_u8", BinOp::ShrUnchecked)]
        {
            let (checks, a, b) = walk_binop_probe(tcx, fn_name, op, ChcConfig::default());
            assert_eq!(checks.len(), 1, "{fn_name}: exactly one shift check, got {checks:?}");
            assert_eq!(checks[0].0, "attempt to shift by excessive shift distance");
            let expected = crate::codegen_ay::chc::stmt::codegen_stmt::codegen_stmt_safety_checks::unchecked_shift_distance_condition(&a, &b, false)
                .expect("statement-path condition");
            assert_eq!(checks[0].1, expected, "{fn_name}: statement-path condition (u32 distance)");
        }
    });
}

#[test]
fn test_inline_unchecked_add_wrapper_records_one_check() {
    with_probe(|tcx| {
        let fn_name = "probe_ub_wrapper_add_u8";
        let instance = find_instance_by_suffix(tcx, fn_name);
        let body = instance.body().expect("function body");
        // Either the call to core's wrapper survives (opt-level 0: the walker
        // walks the wrapper body, where `check_language_ub()` folds to false and
        // the BinOp is the obligation), or MIR inlining left the BinOp here.
        let calls_wrapper = body.blocks.iter().any(|bb| match &bb.terminator.kind {
            TerminatorKind::Call { func, .. } => func
                .ty(body.locals())
                .ok()
                .and_then(|ty| match ty.kind() {
                    TyKind::RigidTy(RigidTy::FnDef(def, _)) => Some(def.name()),
                    _ => None,
                })
                .is_some_and(|name| name.ends_with("unchecked_add")),
            _ => false,
        });
        assert!(
            calls_wrapper || find_binop(&body, BinOp::AddUnchecked).is_some(),
            "probe must call `u8::unchecked_add` or contain its BinOp, got {:#?}",
            body.blocks
        );
        let a = bv_param("a", 8);
        let b = bv_param("b", 8);
        let inline_result =
            walk(tcx, instance, &body, fn_name, ChcConfig::default(), &[a.clone(), b.clone()]);
        let checks = overflow_checks(&inline_result);
        let unchecked_add: Vec<_> = checks
            .iter()
            .filter(|(message, _)| {
                message == "attempt to compute `unchecked_add` which would overflow"
            })
            .collect();
        assert_eq!(
            unchecked_add.len(),
            1,
            "one unchecked_add check through the wrapper, got {checks:?}"
        );
        let raw = ChcCtx::unchecked_overflow_condition(BinOp::AddUnchecked, &a, &b, false)
            .expect("statement-path condition");
        assert!(
            constraint_tree_contains(&unchecked_add[0].1, &|expr| *expr == raw),
            "the wrapper's check is the u8 overflow condition on the caller's operands, got {:?}",
            unchecked_add[0].1
        );
    });
}

#[test]
fn test_inline_unchecked_add_check_carries_its_branch_guard() {
    with_probe(|tcx| {
        let fn_name = "probe_ub_guarded_add_u8";
        let instance = find_instance_by_suffix(tcx, fn_name);
        let body = instance.body().expect("function body");
        assert_body_has_binop(&body, BinOp::AddUnchecked, fn_name);
        assert!(
            body.blocks
                .iter()
                .any(|bb| matches!(bb.terminator.kind, TerminatorKind::SwitchInt { .. })),
            "probe must branch before the add"
        );
        let a = bv_param("a", 8);
        let b = bv_param("b", 8);
        let inline_result =
            walk(tcx, instance, &body, fn_name, ChcConfig::default(), &[a.clone(), b.clone()]);
        let checks = overflow_checks(&inline_result);
        assert_eq!(checks.len(), 1, "one overflow check, got {checks:?}");
        let raw = ChcCtx::unchecked_overflow_condition(BinOp::AddUnchecked, &a, &b, false)
            .expect("statement-path condition");
        assert_ne!(checks[0].1, raw, "the check must be weakened by the branch guard");
        assert!(
            constraint_tree_contains(&checks[0].1, &|expr| *expr == raw),
            "the weakened check still contains the raw condition, got {:?}",
            checks[0].1
        );
    });
}

#[test]
fn test_inline_binops_without_ub_record_no_overflow_check() {
    with_probe(|tcx| {
        // Wrapping add is defined on overflow.
        let (checks, _, _) =
            walk_binop_probe(tcx, "probe_ub_wrapping_add_u8", BinOp::Add, ChcConfig::default());
        assert!(checks.is_empty(), "wrapping_add has no UB, got {checks:?}");
    });
}

#[test]
fn test_inline_float_div_is_not_applicable() {
    with_probe(|tcx| {
        // Float division by zero is defined (inf / NaN), so even with both
        // operands translated there is no divisor check. Called directly: the
        // question is the helper's exclusion, not whether a walk of the float
        // body translates its value.
        let fn_name = "probe_ub_div_f32";
        let instance = find_instance_by_suffix(tcx, fn_name);
        let body = instance.body().expect("function body");
        let rvalue = find_binop(&body, BinOp::Div).expect("probe carries a float Div");
        let populated: HashMap<usize, Expr> =
            arg_params(&body).into_iter().enumerate().map(|(i, p)| (i + 1, p)).collect();
        let mut chc_ctx = ChcCtx::new(tcx, &body, fn_name, ChcConfig::default());
        let field_map = HashMap::new();
        let outcome = inline_binop_ub_checks(
            &mut chc_ctx,
            &rvalue,
            &populated,
            &PlaceResolver::FieldMap(&field_map),
            body.locals(),
            Some(0),
        );
        assert!(matches!(outcome, InlineUbChecks::NotApplicable), "f32 Div is not applicable");
    });
}

/// `--no-overflow-checks` removes none of these: each is UB Kani's compiler
/// asserts whatever that flag says (an `unchecked_*` intrinsic, a lowered
/// `unchecked_div`'s divisor and `MIN / -1`), or the redundant twin of a MIR
/// `Assert` (a source `/`). Gated, the flag dropped the only check of the UB:
/// an overflowing `unchecked_add` and a lowered `unchecked_div(MIN, -1)`
/// verified.
#[test]
fn test_inline_overflow_checks_off_keeps_every_ub_check() {
    with_probe(|tcx| {
        let off = || ChcConfig { overflow_checks: false, ..ChcConfig::default() };
        for (fn_name, op, count) in [
            ("probe_ub_add_u8", BinOp::AddUnchecked, 1),
            ("probe_ub_shl_u8", BinOp::ShlUnchecked, 1),
            ("probe_ub_div_u32", BinOp::Div, 1),
            ("probe_ub_div_i32", BinOp::Div, 2),
        ] {
            let (on, _, _) = walk_binop_probe(tcx, fn_name, op, ChcConfig::default());
            let (checks, _, _) = walk_binop_probe(tcx, fn_name, op, off());
            assert_eq!(checks.len(), count, "{fn_name}: overflow_checks=false, got {checks:?}");
            let messages =
                |c: &[(String, Expr)]| c.iter().map(|(m, _)| m.clone()).collect::<Vec<_>>();
            assert_eq!(messages(&checks), messages(&on), "{fn_name}: the flag changes no UB check");
        }
        let (checks, _, _) = walk_binop_probe(tcx, "probe_ub_div_i32", BinOp::Div, off());
        let messages: Vec<_> = checks.iter().map(|(m, _)| m.as_str()).collect();
        assert_eq!(
            messages,
            ["attempt to divide by zero", "attempt to divide with overflow"],
            "signed MIN / -1 is kept with overflow_checks=false"
        );
    });
}

#[test]
fn test_inline_div_rem_record_zero_and_signed_overflow_checks() {
    with_probe(|tcx| {
        use crate::codegen_ay::chc::stmt::codegen_stmt::codegen_stmt_safety_checks::{
            division_by_zero_condition, signed_div_overflow_condition,
        };
        let unsigned = [
            ("probe_ub_div_u32", BinOp::Div, "attempt to divide by zero"),
            (
                "probe_ub_rem_u32",
                BinOp::Rem,
                "attempt to calculate the remainder with a divisor of zero",
            ),
        ];
        for (fn_name, op, message) in unsigned {
            let (checks, _, b) = walk_binop_probe(tcx, fn_name, op, ChcConfig::default());
            assert_eq!(
                checks.len(),
                1,
                "{fn_name}: unsigned has only the zero check, got {checks:?}"
            );
            assert_eq!(checks[0].0, message, "{fn_name}: Kani's message");
            assert_eq!(checks[0].1, division_by_zero_condition(&b).unwrap(), "{fn_name}");
        }
        let signed = [
            (
                "probe_ub_div_i32",
                BinOp::Div,
                "attempt to divide by zero",
                "attempt to divide with overflow",
            ),
            (
                "probe_ub_rem_i32",
                BinOp::Rem,
                "attempt to calculate the remainder with a divisor of zero",
                "attempt to calculate the remainder with overflow",
            ),
        ];
        for (fn_name, op, zero_message, overflow_message) in signed {
            let (checks, a, b) = walk_binop_probe(tcx, fn_name, op, ChcConfig::default());
            assert_eq!(checks.len(), 2, "{fn_name}: zero and MIN / -1 checks, got {checks:?}");
            assert_eq!(checks[0].0, zero_message, "{fn_name}");
            assert_eq!(checks[0].1, division_by_zero_condition(&b).unwrap(), "{fn_name}");
            assert_eq!(checks[1].0, overflow_message, "{fn_name}");
            // `¬(b == -1 ∧ a == MIN)`: the statement path's
            // `signed_div_overflow_condition` (`a != MIN ∨ b != -1`) by De
            // Morgan, spelled as the walker translates rustc's own guard for a
            // user `/` so the host can emit the pair once.
            let (min, neg_one) =
                (Expr::bitvec_const(1u128 << 31, 32), Expr::bitvec_const(!0u128, 32));
            let mir_form = b.clone().eq(neg_one.clone()).and(a.clone().eq(min.clone())).not();
            assert_eq!(checks[1].1, mir_form, "{fn_name}");
            let statement_form = signed_div_overflow_condition(&a, &b).unwrap();
            assert_eq!(statement_form, a.clone().eq(min).not().or(b.clone().eq(neg_one).not()));
        }
    });
}

#[test]
fn test_inline_binop_ub_checks_untranslatable_operand_fails_closed() {
    with_probe(|tcx| {
        let fn_name = "probe_ub_add_u8";
        let instance = find_instance_by_suffix(tcx, fn_name);
        let body = instance.body().expect("function body");
        let rvalue = find_binop(&body, BinOp::AddUnchecked).expect("probe carries AddUnchecked");
        let mut chc_ctx = ChcCtx::new(tcx, &body, fn_name, ChcConfig::default());
        let field_map = HashMap::new();
        let resolver = PlaceResolver::FieldMap(&field_map);
        // No local is populated, so neither operand translates.
        let outcome = inline_binop_ub_checks(
            &mut chc_ctx,
            &rvalue,
            &HashMap::new(),
            &resolver,
            body.locals(),
            None,
        );
        assert!(
            matches!(outcome, InlineUbChecks::Untranslatable),
            "empty locals are untranslatable"
        );
        // With the operands populated the same rvalue yields its check.
        let populated: HashMap<usize, Expr> =
            [(1, bv_param("a", 8)), (2, bv_param("b", 8))].into_iter().collect();
        let outcome = inline_binop_ub_checks(
            &mut chc_ctx,
            &rvalue,
            &populated,
            &resolver,
            body.locals(),
            None,
        );
        assert!(
            matches!(&outcome, InlineUbChecks::Checks(checks) if checks.len() == 1),
            "populated operands yield one check"
        );
        // The dropped-obligation reason is NOT blessed: it fails closed.
        assert_eq!(INLINE_RVALUE_UB_CHECK_DROPPED, "inline_rvalue_ub_check_dropped");
        assert_eq!(
            fallback_soundness(INLINE_RVALUE_UB_CHECK_DROPPED),
            FallbackSoundness::FailClose
        );
    });
}

/// The call site reads the operands BEFORE the assignment writes the
/// destination: `_1 = AddUnchecked(_1, _2)` checks the incoming `_1`.
///
/// rustc's MIR building puts the sum in a temporary, so the self-assigning
/// statement is made by rewriting `probe_ub_add_u8`'s body:
/// `_1 = AddUnchecked(copy _1, copy _2); _0 = copy _1`.
#[test]
fn test_inline_self_assigning_binop_checks_the_old_operand() {
    use crate::rustc_compat::rvalue_use;
    use rustc_public::mir::{Operand, Place};
    with_probe(|tcx| {
        let fn_name = "probe_ub_add_u8";
        let instance = find_instance_by_suffix(tcx, fn_name);
        let mut body = instance.body().expect("function body");
        let (block_idx, stmt_idx, span) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(b, bb)| {
                bb.statements
                    .iter()
                    .position(|stmt| {
                        matches!(
                            &stmt.kind,
                            StatementKind::Assign(_, Rvalue::BinaryOp(BinOp::AddUnchecked, ..))
                        )
                    })
                    .map(|i| (b, i, mir_span!(bb.statements[i])))
            })
            .expect("probe carries AddUnchecked");
        let place = |local: usize| Place { local, projection: Vec::new() };
        let self_assign = crate::rustc_compat::mir_statement(
            StatementKind::Assign(
                place(1),
                Rvalue::BinaryOp(
                    BinOp::AddUnchecked,
                    Operand::Copy(place(1)),
                    Operand::Copy(place(2)),
                ),
            ),
            span,
        );
        let ret = crate::rustc_compat::mir_statement(
            StatementKind::Assign(place(0), rvalue_use!(Rvalue::Use(Operand::Copy(place(1))))),
            span,
        );
        let statements = &mut body.blocks[block_idx].statements;
        statements.splice(stmt_idx..=stmt_idx, [self_assign, ret]);
        let a = bv_param("a", 8);
        let b = bv_param("b", 8);
        let inline_result =
            walk(tcx, instance, &body, fn_name, ChcConfig::default(), &[a.clone(), b.clone()]);
        let checks = overflow_checks(&inline_result);
        assert_eq!(checks.len(), 1, "one overflow check, got {checks:?}");
        let expected = ChcCtx::unchecked_overflow_condition(BinOp::AddUnchecked, &a, &b, false)
            .expect("statement-path condition");
        assert_eq!(checks[0].1, expected, "the check reads the incoming `_1`, not the sum");
        assert_eq!(inline_result.value, a.bvadd(b), "and the assignment still happens");
    });
}

/// A SIGNED shift distance also rules out negative distances.
#[test]
fn test_inline_unchecked_shl_signed_distance_checks_non_negative() {
    with_probe(|tcx| {
        let (checks, a, b) = walk_binop_probe(
            tcx,
            "probe_ub_shl_i32_distance",
            BinOp::ShlUnchecked,
            ChcConfig::default(),
        );
        assert_eq!(checks.len(), 1, "one shift check, got {checks:?}");
        let expected = crate::codegen_ay::chc::stmt::codegen_stmt::codegen_stmt_safety_checks::unchecked_shift_distance_condition(&a, &b, true)
            .expect("statement-path condition");
        assert_eq!(checks[0].1, expected, "i32 distance: `< 8` and `>= 0`");
        let unsigned = crate::codegen_ay::chc::stmt::codegen_stmt::codegen_stmt_safety_checks::unchecked_shift_distance_condition(&a, &b, false)
            .expect("statement-path condition");
        assert_ne!(checks[0].1, unsigned, "the signed form is not the unsigned one");
    });
}

/// A projected destination (`t.0 = AddUnchecked(..)`) is checked too: the
/// call site runs before the projected-assignment skips.
#[test]
fn test_inline_binop_into_projected_destination_is_checked() {
    use rustc_public::mir::Operand;
    with_probe(|tcx| {
        let fn_name = "probe_ub_add_into_field";
        let instance = find_instance_by_suffix(tcx, fn_name);
        let mut body = instance.body().expect("function body");
        assert_body_has_binop(&body, BinOp::AddUnchecked, fn_name);
        // rustc computes the sum into a temporary and moves it into `t.0`.
        // Fold the pair into ONE projected assignment, `t.0 = AddUnchecked(..)`,
        // which is the shape whose destination has no local (`dest_local:
        // None`) and which the walker's projected-assignment branch skips.
        let mut folded = false;
        for block in &mut body.blocks {
            let Some(sum_idx) = block.statements.iter().position(|stmt| {
                matches!(
                    &stmt.kind,
                    StatementKind::Assign(p, Rvalue::BinaryOp(BinOp::AddUnchecked, ..))
                        if p.projection.is_empty()
                )
            }) else {
                continue;
            };
            let StatementKind::Assign(temp, _) = block.statements[sum_idx].kind.clone() else {
                unreachable!()
            };
            let Some(move_idx) = block.statements.iter().position(|stmt| {
                matches!(
                    &stmt.kind,
                    StatementKind::Assign(dest, Rvalue::Use(Operand::Move(src) | Operand::Copy(src), ..))
                        if !dest.projection.is_empty() && *src == temp
                )
            }) else {
                continue;
            };
            let StatementKind::Assign(dest, _) = block.statements[move_idx].kind.clone() else {
                unreachable!()
            };
            if let StatementKind::Assign(place, _) = &mut block.statements[sum_idx].kind {
                *place = dest;
            }
            block.statements.remove(move_idx);
            folded = true;
            break;
        }
        assert!(
            folded,
            "probe must compute the sum and move it into a field, got {:#?}",
            body.blocks
        );
        let params = arg_params(&body);
        let [a, b] = <[Expr; 2]>::try_from(params.clone()).expect("two arguments");
        let mut chc_ctx = ChcCtx::new(tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();
        chc_ctx.mark_inline_field_reads(&body, &params, 0);
        let inline_result = translate_inline_body(
            &mut chc_ctx,
            &body,
            &params,
            0,
            &HashMap::new(),
            Some(instance),
            0,
        )
        .unwrap_or_else(|| panic!("{fn_name}: inline body should translate"));
        let checks = overflow_checks(&inline_result);
        assert_eq!(checks.len(), 1, "one overflow check, got {checks:?}");
        let expected = ChcCtx::unchecked_overflow_condition(BinOp::AddUnchecked, &a, &b, false)
            .expect("statement-path condition");
        assert_eq!(checks[0].1, expected);
    });
}

/// The branch guard is exactly `a < 100 → overflow-free`.
#[test]
fn test_inline_single_guard_is_the_branch_condition() {
    with_probe(|tcx| {
        let (checks, a, b) = walk_binop_probe(
            tcx,
            "probe_ub_single_guard_add",
            BinOp::AddUnchecked,
            ChcConfig::default(),
        );
        assert_eq!(checks.len(), 1, "one overflow check, got {checks:?}");
        let raw = ChcCtx::unchecked_overflow_condition(BinOp::AddUnchecked, &a, &b, false)
            .expect("statement-path condition");
        let guard = a.clone().bvult(Expr::bitvec_const(100u64, 8));
        // SwitchInt(false-arm = 0, otherwise = then): the then-arm's check is
        // weakened by the NEGATED false-arm guard `¬(a < 100)`, i.e.
        // `¬(a < 100) ∨ raw`.
        let expected = guard.not().or(raw);
        assert_eq!(checks[0].1, expected, "exactly `a < 100 → no overflow`");
    });
}

/// The call site's `Untranslatable` arm records the NOT-blessed reason on a
/// real walk: an operand that is not a bitvector drops the check, and the
/// fail-closed counter must move (mutating the arm to `{}` fails this test).
#[test]
fn test_inline_untranslatable_operand_fails_closed_through_the_walk() {
    with_probe(|tcx| {
        let fn_name = "probe_ub_add_u8";
        let instance = find_instance_by_suffix(tcx, fn_name);
        let body = instance.body().expect("function body");
        assert_body_has_binop(&body, BinOp::AddUnchecked, fn_name);
        let walk_counting = |params: &[Expr]| -> (usize, usize) {
            let mut chc_ctx = ChcCtx::new(tcx, &body, fn_name, ChcConfig::default());
            chc_ctx.declare_block_relations();
            chc_ctx.mark_inline_field_reads(&body, params, 0);
            let before_fail = chc_ctx.diagnostics.place_translation_drop.get();
            let before_havoc = chc_ctx.diagnostics.sound_havoc_drop.get();
            let _ = translate_inline_body(
                &mut chc_ctx,
                &body,
                params,
                0,
                &HashMap::new(),
                Some(instance),
                0,
            );
            (
                chc_ctx.diagnostics.place_translation_drop.get() - before_fail,
                chc_ctx.diagnostics.sound_havoc_drop.get() - before_havoc,
            )
        };
        // Control: bitvector operands record the check and no fallback.
        let (fail_closed, _) = walk_counting(&[bv_param("a", 8), bv_param("b", 8)]);
        assert_eq!(fail_closed, 0, "translatable operands drop nothing");
        // A Bool where the u8 `b` belongs cannot be read as a bitvector.
        let (fail_closed, blessed) =
            walk_counting(&[bv_param("a", 8), Expr::var("b".to_string(), Sort::bool())]);
        assert!(fail_closed >= 1, "the dropped check fails closed (place_translation_drop)");
        assert_eq!(blessed, 0, "and is not counted as a blessed havoc");
    });
}

/// The host skips a walked check that is valid on its own. These are the
/// std wrappers the precision review measured (9-13 s each as properties):
/// each walk records at least one check and every one is trivially valid,
/// while a real unchecked op's check is not.
#[test]
fn test_std_wrapper_checks_are_trivially_valid() {
    use crate::codegen_ay::chc::call::inline_shared::check_is_trivially_valid;
    with_probe(|tcx| {
        for fn_name in [
            "probe_std_checked_sub",
            "probe_std_checked_div",
            "probe_std_wrapping_shl",
            "probe_std_wrapping_shr_u8",
        ] {
            let instance = find_instance_by_suffix(tcx, fn_name);
            let body = instance.body().expect("function body");
            let params = arg_params(&body);
            let inline_result = walk(tcx, instance, &body, fn_name, ChcConfig::default(), &params);
            let checks = overflow_checks(&inline_result);
            assert!(!checks.is_empty(), "{fn_name}: the walk records the wrapper's UB check");
            for (message, check) in &checks {
                assert!(
                    check_is_trivially_valid(check),
                    "{fn_name}: `{message}` should be valid on its own, got {check:?}"
                );
            }
        }
        let (checks, _, _) =
            walk_binop_probe(tcx, "probe_ub_add_u8", BinOp::AddUnchecked, ChcConfig::default());
        assert!(!check_is_trivially_valid(&checks[0].1), "a real unchecked_add stays a property");
    });
}

/// A walked user `a / b` on i32 records its MIR Asserts AND the walker's own
/// Div checks; each pair is the SAME expression, so the host emits it once.
#[test]
fn test_user_div_asserts_and_walker_checks_coincide() {
    with_probe(|tcx| {
        let fn_name = "probe_user_div_i32";
        let instance = find_instance_by_suffix(tcx, fn_name);
        let body = instance.body().expect("function body");
        assert_body_has_binop(&body, BinOp::Div, fn_name);
        let params = arg_params(&body);
        let inline_result = walk(tcx, instance, &body, fn_name, ChcConfig::default(), &params);
        let all: Vec<_> = inline_result
            .deferred_checks
            .iter()
            .map(|c| (c.message.clone().unwrap_or_default(), c.check.clone()))
            .collect();
        for message in ["attempt to divide by zero", "attempt to divide with overflow"] {
            let same: Vec<_> = all.iter().filter(|(m, _)| m == message).collect();
            assert_eq!(
                same.len(),
                2,
                "`{message}`: the MIR Assert and the walker check, got {all:?}"
            );
            assert_eq!(same[0].1, same[1].1, "`{message}`: identical expressions, emitted once");
        }
    });
}

/// Core's `unchecked_*` wrapper is answered at the call (value + UB check)
/// without walking its body, so the check survives where the walker has no
/// inline depth left for the wrapper's body: from a walk at
/// `MAX_INLINE_DEPTH`, the wrapper's own next-level walk is refused, and the
/// havoc that replaced it dropped the check.
#[test]
fn test_unchecked_wrapper_check_survives_depth_exhaustion() {
    with_probe(|tcx| {
        let fn_name = "probe_ub_wrapper_add_u8";
        let instance = find_instance_by_suffix(tcx, fn_name);
        let body = instance.body().expect("function body");
        let a = bv_param("a", 8);
        let b = bv_param("b", 8);
        let raw = ChcCtx::unchecked_overflow_condition(BinOp::AddUnchecked, &a, &b, false)
            .expect("statement-path condition");
        for depth in
            [0usize, crate::codegen_ay::chc::call::codegen_call_virtual_inline::MAX_INLINE_DEPTH]
        {
            let mut chc_ctx = ChcCtx::new(tcx, &body, fn_name, ChcConfig::default());
            chc_ctx.declare_block_relations();
            let params = [a.clone(), b.clone()];
            chc_ctx.mark_inline_field_reads(&body, &params, 0);
            let inline_result = translate_inline_body(
                &mut chc_ctx,
                &body,
                &params,
                0,
                &HashMap::new(),
                Some(instance),
                depth,
            )
            .unwrap_or_else(|| panic!("{fn_name} at depth {depth}: inline body should translate"));
            let checks = overflow_checks(&inline_result);
            assert_eq!(checks.len(), 1, "depth {depth}: one unchecked_add check, got {checks:?}");
            assert!(
                constraint_tree_contains(&checks[0].1, &|expr| *expr == raw),
                "depth {depth}: the u8 overflow condition, got {:?}",
                checks[0].1
            );
            assert!(
                constraint_tree_contains(&inline_result.value, &|expr| *expr
                    == a.clone().bvadd(b.clone())),
                "depth {depth}: and the sum as the value, got {:?}",
                inline_result.value
            );
        }
    });
}

/// The legacy inline-assert guard (`emit_inline_assert_guard_error`, the
/// "assertion failed inside inlined callee" property) emits no error rule for
/// a guard valid on its own, as the deferred checks do, and still returns it
/// as the success edge's constraint. A guard that can fail keeps its rule.
#[test]
fn test_inline_assert_guard_valid_on_its_own_emits_no_error_rule() {
    use crate::codegen_ay::chc::chc_call_context::DispatchCallContext;
    with_probe(|tcx| {
        let fn_name = "probe_ub_wrapper_add_u8";
        let instance = find_instance_by_suffix(tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();
        let (bb_idx, block) = body
            .blocks
            .iter()
            .enumerate()
            .find(|(_, bb)| matches!(bb.terminator.kind, TerminatorKind::Call { .. }))
            .expect("the probe calls unchecked_add");
        let TerminatorKind::Call { func, args, destination, target, .. } = &block.terminator.kind
        else {
            unreachable!()
        };
        let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals = HashSet::new();
        let dcx = DispatchCallContext {
            bb_idx,
            func,
            args,
            destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
            callee_path: None,
        };
        let s = bv_param("s", 32);
        let valid =
            s.clone().bvand(Expr::bitvec_const(7u64, 32)).bvult(Expr::bitvec_const(8u64, 32));
        let open = s.bvult(Expr::bitvec_const(8u64, 32));

        let before = chc_ctx.vc.rules.len();
        let kept = chc_ctx.emit_inline_assert_guard_error(&dcx, Some(valid.clone()));
        assert_eq!(kept, vec![valid], "the valid guard is still the success edge's constraint");
        assert_eq!(chc_ctx.vc.rules.len(), before, "a valid guard emits no error rule");

        let kept = chc_ctx.emit_inline_assert_guard_error(&dcx, Some(open.clone()));
        assert_eq!(kept, vec![open]);
        assert!(chc_ctx.vc.rules.len() > before, "a guard that can fail keeps its error rule");
        assert!(chc_ctx.emit_inline_assert_guard_error(&dcx, None).is_empty());
    });
}
