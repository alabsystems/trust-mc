// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! CHC-only lowering for rounding-assertion float comparison patterns.
//!
//! The residual #3763 UNKNOWNs do not need general IEEE-754 subtraction in CHC.
//! They only compare:
//! - `abs(x.fract())` against `0.5`
//! - `abs(x - <rounding>(x))` against `0.0`, `0.5`, or `1.0`
//!
//! This module recognizes those MIR temp patterns and emits the equivalent
//! pure-BV boolean directly, avoiding the FP-theory subtraction path.
use super::ChcCtx;
use super::codegen_ctx::diagnostics::CellCounter;
use super::float_floor_direction_patterns::try_build_floorf64_direction_comparison;
use crate::codegen_ay::chc::call::codegen_call_cmp_string::float_predicates::{
    FloatPredicateKind, build_float_predicate_expr,
};
use crate::codegen_ay::chc::call::codegen_call_cmp_string::float_rounding::{
    FractHalfCmp, build_float_abs_fract_cmp_half,
};
use crate::codegen_ay::chc::call::codegen_call_cmp_string::math::normalize_to_intrinsic_suffix;
use crate::codegen_ay::chc::call::codegen_call_cmp_string::math_const::{
    try_extract_const_f32, try_extract_const_f64,
};
use ay_bindings::Expr;
use rustc_public::mir::{BinOp, Body, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{ConstantKind, RigidTy, TyConstKind, TyKind};
use std::collections::HashSet;
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FloatConstKind {
    Zero,
    Half,
    One,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum RoundingKind {
    Trunc,
    Floor,
    Ceil,
    Round,
    RoundTiesEven,
}
#[derive(Clone, Copy, Debug)]
struct AbsPattern<'body> {
    input: &'body Operand,
    kind: RoundingKind,
    sub_local: Option<usize>,
}
struct ComparisonPattern<'body> {
    abs_pattern: AbsPattern<'body>,
    cmp: BinOp,
    constant: FloatConstKind,
}
pub(super) enum LocalDef<'body> {
    Assign(&'body Rvalue),
    Call { func: &'body Operand, args: &'body [Operand] },
}
pub(in crate::codegen_ay) fn try_build_float_assertion_comparison<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    op: BinOp,
    lhs_op: &Operand,
    rhs_op: &Operand,
    modified_locals: &HashSet<usize>,
) -> Option<Expr> {
    if let Some(result) =
        try_build_floorf64_direction_comparison(ctx, op, lhs_op, rhs_op, modified_locals)
    {
        // AUDIT (task #65, rounding_assertion_bypass): `floor(x) <= x` (and the
        // mirrored `x >= floor(x)`) → `!is_nan(x)` is PROVABLY EXACT incl. NaN:
        // IEEE floor is exact and floor(x) ≤ x holds for every non-NaN x
        // (±inf, ±0, subnormals included: floor(±inf) = ±inf ≤ ±inf); for
        // x = NaN both `floor(NaN) ≤ NaN` (unordered) and `!is_nan(NaN)` are
        // FALSE. Not a bypass — do not count.
        return Some(result);
    }

    let detected = detect_float_assertion_comparison(ctx, op, lhs_op, rhs_op)?;
    let input = ctx.translate_operand_with_modified(detected.abs_pattern.input, modified_locals)?;
    // AUDIT (task #65, rounding_assertion_bypass) — per-arm exactness of the
    // `|x - <rounding>(x)| cmp K` rewrites. Key fact used throughout: for
    // finite x the SUBTRACTION `x - trunc(x)` is always exact (|x| < 1 ⇒
    // trunc(x) = ±0 ⇒ exact; |x| ≥ 1 ⇒ trunc(x) ∈ [x/2, x] same sign ⇒
    // Sterbenz), but `x - floor(x)` / `x - ceil(x)` are NOT: for tiny |x| on
    // the "wrong" side (e.g. x = -1e-20, floor(x) = -1) the true difference
    // 1 - 1e-20 ROUNDS UP to exactly 1.0. For x = ±inf/NaN every
    // `|x - f(x)| cmp K` is FALSE (NaN operand, unordered), matching
    // Finite(x) = FALSE, so specials never distinguish the arms.
    //
    //   (Trunc, Half, cmp) → build_float_abs_fract_cmp_half: EXACT. fract is
    //     exact (above) and the builder is a bit-precise |fract| vs 0.5
    //     classifier incl. the NaN/Ne polarity. Not a bypass.
    //   (Trunc, One, Lt|Le) → Finite: EXACT. exact fract ∈ (-1, 1) so
    //     |fract| < 1 ⇔ finite (and ≤ 1 a fortiori).
    //   (Floor|Ceil, One, Le) → Finite: EXACT. the computed difference is
    //     fl(d) with true d ∈ [0,1); round-to-nearest is monotone and 1.0 is
    //     representable, so fl(d) ≤ 1.0 always — Le holds for every finite x.
    //   (Floor|Ceil, One, Lt) → Finite: GENUINELY WEAKENING (counted below).
    //     fl(x - floor(x)) can round to exactly 1.0 (x = -1e-20 above), so the
    //     real assertion `|x - floor(x)| < 1.0` FAILS at runtime while the
    //     rewrite proves it — an assertion bypass that can mask a real bug.
    //   (Round|RoundTiesEven, Half, Le) → Finite: EXACT. true d ∈ [-0.5, 0.5],
    //     fl is monotone and ±0.5 representable ⇒ |fl(d)| ≤ 0.5 for every
    //     finite x (the d = ±0.5 boundary is why only Le is admitted).
    //   (*, Zero, Ge) → Finite: EXACT. |fl(d)| ≥ 0.0 for every non-NaN
    //     result (finite - finite is never NaN; |·| clears -0.0).
    let arm = (detected.abs_pattern.kind, detected.constant, detected.cmp);
    let result = match arm {
        (RoundingKind::Trunc, FloatConstKind::Half, cmp) => {
            build_float_abs_fract_cmp_half(&input, to_fract_half_cmp(cmp)?)
        }
        (
            RoundingKind::Trunc | RoundingKind::Floor | RoundingKind::Ceil,
            FloatConstKind::One,
            BinOp::Lt | BinOp::Le,
        )
        | (RoundingKind::Round | RoundingKind::RoundTiesEven, FloatConstKind::Half, BinOp::Le)
        | (
            RoundingKind::Trunc
            | RoundingKind::Floor
            | RoundingKind::Ceil
            | RoundingKind::Round
            | RoundingKind::RoundTiesEven,
            FloatConstKind::Zero,
            BinOp::Ge,
        ) => build_float_predicate_expr(&input, FloatPredicateKind::Finite),
        _ => None,
    };
    // Only the (Floor|Ceil, One, Lt) arm is a genuine weakening (see audit
    // above): count it so the plumbed `rounding_assertion_bypass` DEMOTED
    // category fail-closes any PROOF that leaned on the bypassed boundary.
    if result.is_some()
        && matches!(arm, (RoundingKind::Floor | RoundingKind::Ceil, FloatConstKind::One, BinOp::Lt))
    {
        ctx.diagnostics.rounding_assertion_bypass.inc();
    }
    result
}
pub(in crate::codegen_ay) fn should_bypass_float_assertion_sub<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    local: usize,
) -> bool {
    ctx.body.blocks.iter().flat_map(|bb| bb.statements.iter()).any(|stmt| {
        let StatementKind::Assign(_, rvalue) = &stmt.kind else {
            return false;
        };
        let (Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs)) = rvalue
        else {
            return false;
        };
        detect_float_assertion_comparison(ctx, *op, lhs, rhs).is_some_and(|pattern| {
            pattern.abs_pattern.sub_local == Some(local)
                && would_comparison_builder_succeed(&pattern)
        })
    })
}
fn would_comparison_builder_succeed(p: &ComparisonPattern<'_>) -> bool {
    matches!(
        (p.abs_pattern.kind, p.constant, p.cmp),
        (RoundingKind::Trunc, FloatConstKind::Half, _)
            | (
                RoundingKind::Trunc | RoundingKind::Floor | RoundingKind::Ceil,
                FloatConstKind::One,
                BinOp::Lt | BinOp::Le
            )
            | (RoundingKind::Round | RoundingKind::RoundTiesEven, FloatConstKind::Half, BinOp::Le)
            | (_, FloatConstKind::Zero, BinOp::Ge)
    )
}
fn detect_float_assertion_comparison<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    op: BinOp,
    lhs_op: &'body Operand,
    rhs_op: &'body Operand,
) -> Option<ComparisonPattern<'body>> {
    if let Some(constant) = classify_float_constant(ctx.body, rhs_op) {
        Some(ComparisonPattern { abs_pattern: detect_abs_pattern(ctx, lhs_op)?, cmp: op, constant })
    } else if let Some(constant) = classify_float_constant(ctx.body, lhs_op) {
        Some(ComparisonPattern {
            abs_pattern: detect_abs_pattern(ctx, rhs_op)?,
            cmp: flip_comparison(op)?,
            constant,
        })
    } else {
        None
    }
}
fn classify_float_constant(body: &Body, operand: &Operand) -> Option<FloatConstKind> {
    if let Some(bits) = try_extract_const_f32(operand, body) {
        match bits {
            0x0000_0000 => Some(FloatConstKind::Zero),
            0x3F00_0000 => Some(FloatConstKind::Half),
            0x3F80_0000 => Some(FloatConstKind::One),
            _ => None,
        }
    } else if let Some(bits) = try_extract_const_f64(operand, body) {
        match bits {
            0x0000_0000_0000_0000 => Some(FloatConstKind::Zero),
            0x3FE0_0000_0000_0000 => Some(FloatConstKind::Half),
            0x3FF0_0000_0000_0000 => Some(FloatConstKind::One),
            _ => None,
        }
    } else {
        None
    }
}
fn detect_abs_pattern<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    operand: &'body Operand,
) -> Option<AbsPattern<'body>> {
    let operand = follow_passthrough_uses(ctx.body, operand)?;
    if let Some(masked_abs) = detect_masked_abs_pattern(ctx, operand) {
        return Some(masked_abs);
    }
    detect_call_abs_pattern(ctx, operand)
}

fn detect_call_abs_pattern<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    operand: &'body Operand,
) -> Option<AbsPattern<'body>> {
    let local = trace_passthrough_local(ctx.body, operand)?;
    let LocalDef::Call { func, args } = find_local_def(ctx.body, local)? else {
        return None;
    };

    let callee = normalize_math_path(ctx.resolve_callee_path(func)?);
    if !is_abs_call(&callee) {
        return None;
    }

    if let Some(fract_pattern) = detect_abs_fract_pattern(ctx, args.first()?) {
        return Some(fract_pattern);
    }

    detect_abs_sub_pattern(ctx, args.first()?)
}

fn detect_masked_abs_pattern<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    operand: &'body Operand,
) -> Option<AbsPattern<'body>> {
    let local = operand_local(operand)?;
    let LocalDef::Assign(rvalue) = find_local_def(ctx.body, local)? else {
        return None;
    };
    let (Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs)) = rvalue else {
        return None;
    };
    if !matches!(op, BinOp::BitAnd) {
        return None;
    }

    let inner = if is_float_abs_mask(ctx.body, lhs) {
        follow_passthrough_uses(ctx.body, rhs)?
    } else if is_float_abs_mask(ctx.body, rhs) {
        follow_passthrough_uses(ctx.body, lhs)?
    } else {
        return None;
    };

    if let Some(fract_pattern) = detect_abs_fract_pattern(ctx, inner) {
        return Some(fract_pattern);
    }

    detect_abs_sub_pattern(ctx, inner)
}

fn detect_abs_fract_pattern<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    operand: &'body Operand,
) -> Option<AbsPattern<'body>> {
    let operand = follow_passthrough_uses(ctx.body, operand)?;
    let local = operand_local(operand)?;
    let LocalDef::Call { func, args } = find_local_def(ctx.body, local)? else {
        return None;
    };

    let callee = normalize_math_path(ctx.resolve_callee_path(func)?);
    if !is_fract_call(&callee) {
        return None;
    }

    Some(AbsPattern {
        input: follow_passthrough_uses(ctx.body, args.first()?)?,
        kind: RoundingKind::Trunc,
        sub_local: None,
    })
}

fn detect_abs_sub_pattern<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    operand: &'body Operand,
) -> Option<AbsPattern<'body>> {
    let operand = follow_passthrough_uses(ctx.body, operand)?;
    let local = operand_local(operand)?;
    let LocalDef::Assign(rvalue) = find_local_def(ctx.body, local)? else {
        return None;
    };
    let (Rvalue::BinaryOp(op, lhs, rhs) | Rvalue::CheckedBinaryOp(op, lhs, rhs)) = rvalue else {
        return None;
    };
    if !matches!(op, BinOp::Sub | BinOp::SubUnchecked) {
        return None;
    }

    let lhs = follow_passthrough_uses(ctx.body, lhs)?;
    let rhs = follow_passthrough_uses(ctx.body, rhs)?;
    let rhs_local = operand_local(rhs)?;
    let LocalDef::Call { func, args } = find_local_def(ctx.body, rhs_local)? else {
        return None;
    };

    let callee = normalize_math_path(ctx.resolve_callee_path(func)?);
    let kind = detect_rounding_kind(&callee)?;
    let call_input = follow_passthrough_uses(ctx.body, args.first()?)?;
    if same_local_operand(ctx.body, lhs, call_input) {
        Some(AbsPattern { input: call_input, kind, sub_local: Some(local) })
    } else {
        None
    }
}

pub(super) fn is_float_abs_mask(body: &Body, operand: &Operand) -> bool {
    match try_extract_const_u128(body, operand) {
        Some(bits) => bits == 0x7FFF_FFFF || bits == 0x7FFF_FFFF_FFFF_FFFF,
        None => false,
    }
}

pub(super) fn operand_local(operand: &Operand) -> Option<usize> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(place.local)
        }
        _ => None,
    }
}

pub(super) fn same_local_operand(body: &Body, lhs: &Operand, rhs: &Operand) -> bool {
    trace_passthrough_local(body, lhs) == trace_passthrough_local(body, rhs)
}

pub(super) fn trace_passthrough_local(body: &Body, operand: &Operand) -> Option<usize> {
    let mut local = operand_local(operand)?;
    let mut seen = HashSet::new();
    while seen.insert(local) {
        let Some(LocalDef::Assign(Rvalue::Use(next))) = find_local_def(body, local) else {
            return Some(local);
        };
        let Some(next_local) = operand_local(next) else {
            return Some(local);
        };
        local = next_local;
    }
    Some(local)
}

pub(super) fn follow_passthrough_uses<'body>(
    body: &'body Body,
    operand: &'body Operand,
) -> Option<&'body Operand> {
    let mut current = operand;
    let mut seen = HashSet::new();
    while let Some(local) = operand_local(current) {
        if !seen.insert(local) {
            break;
        }
        let Some(LocalDef::Assign(Rvalue::Use(next))) = find_local_def(body, local) else {
            break;
        };
        current = next;
    }
    Some(current)
}

fn try_extract_const_u128(body: &Body, operand: &Operand) -> Option<u128> {
    match operand {
        Operand::Constant(c) => extract_u128_from_const_op(c),
        Operand::Copy(place) | Operand::Move(place) => {
            if !place.projection.is_empty() {
                return None;
            }
            find_const_u128_assignment(body, place.local)
        }
    }
}

fn find_const_u128_assignment(body: &Body, local_idx: usize) -> Option<u128> {
    for bb in &body.blocks {
        for stmt in &bb.statements {
            if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                && lhs.local == local_idx
                && lhs.projection.is_empty()
            {
                match rhs {
                    Rvalue::Use(Operand::Constant(c)) => return extract_u128_from_const_op(c),
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                        if src.projection.is_empty() =>
                    {
                        return find_const_u128_direct(body, src.local);
                    }
                    _ => {}
                }
            }
        }
    }
    None
}

fn find_const_u128_direct(body: &Body, local_idx: usize) -> Option<u128> {
    for bb in &body.blocks {
        for stmt in &bb.statements {
            if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                && lhs.local == local_idx
                && lhs.projection.is_empty()
                && let Rvalue::Use(Operand::Constant(c)) = rhs
            {
                return extract_u128_from_const_op(c);
            }
        }
    }
    None
}

fn extract_u128_from_const_op(const_op: &rustc_public::mir::ConstOperand) -> Option<u128> {
    let mir_const = &const_op.const_;

    let extract_from_alloc =
        |alloc: &rustc_public::ty::Allocation, ty: rustc_public::ty::Ty| -> Option<u128> {
            match ty.kind() {
                TyKind::RigidTy(RigidTy::Uint(_)) => alloc.read_uint().ok(),
                TyKind::RigidTy(RigidTy::Int(_)) => {
                    let value = alloc.read_int().ok()?;
                    u128::try_from(value).ok()
                }
                _ => None,
            }
        };

    let ty = mir_const.ty();
    match mir_const.kind() {
        ConstantKind::Allocated(alloc) => extract_from_alloc(alloc, ty),
        ConstantKind::Ty(ty_const) => match ty_const.kind() {
            TyConstKind::Value(value_ty, alloc) => extract_from_alloc(alloc, *value_ty),
            _ => None,
        },
        _ => None,
    }
}

pub(super) fn find_local_def<'body>(body: &'body Body, local: usize) -> Option<LocalDef<'body>> {
    let mut found = None;
    for bb in &body.blocks {
        for stmt in &bb.statements {
            if let StatementKind::Assign(place, rvalue) = &stmt.kind
                && place.local == local
                && place.projection.is_empty()
            {
                if found.is_some() {
                    return None;
                }
                found = Some(LocalDef::Assign(rvalue));
            }
        }
        if let TerminatorKind::Call { func, args, destination, .. } = &bb.terminator.kind
            && destination.local == local
            && destination.projection.is_empty()
        {
            if found.is_some() {
                return None;
            }
            found = Some(LocalDef::Call { func, args });
        }
    }
    found
}

pub(super) fn normalize_math_path(path: String) -> String {
    normalize_to_intrinsic_suffix(&path).unwrap_or(path)
}

fn is_abs_call(path: &str) -> bool {
    path.ends_with("fabsf32")
        || path.ends_with("fabsf64")
        || (path.ends_with("abs") && (path.contains("f32") || path.contains("f64")))
}

fn is_fract_call(path: &str) -> bool {
    path.ends_with("fract") && (path.contains("f32") || path.contains("f64"))
}

pub(super) fn detect_rounding_kind(path: &str) -> Option<RoundingKind> {
    if !path.contains("f32") && !path.contains("f64") {
        None
    } else if path.ends_with("truncf32") || path.ends_with("truncf64") || path.ends_with("trunc") {
        Some(RoundingKind::Trunc)
    } else if path.ends_with("floorf32") || path.ends_with("floorf64") || path.ends_with("floor") {
        Some(RoundingKind::Floor)
    } else if path.ends_with("ceilf32") || path.ends_with("ceilf64") || path.ends_with("ceil") {
        Some(RoundingKind::Ceil)
    } else if path.ends_with("roundf32") || path.ends_with("roundf64") || path.ends_with("round") {
        Some(RoundingKind::Round)
    } else if path.ends_with("round_ties_even_f32")
        || path.ends_with("round_ties_even_f64")
        || path.ends_with("round_ties_even")
    {
        Some(RoundingKind::RoundTiesEven)
    } else {
        None
    }
}

fn flip_comparison(op: BinOp) -> Option<BinOp> {
    Some(match op {
        BinOp::Lt => BinOp::Gt,
        BinOp::Le => BinOp::Ge,
        BinOp::Gt => BinOp::Lt,
        BinOp::Ge => BinOp::Le,
        BinOp::Eq => BinOp::Eq,
        BinOp::Ne => BinOp::Ne,
        _ => return None,
    })
}

fn to_fract_half_cmp(op: BinOp) -> Option<FractHalfCmp> {
    Some(match op {
        BinOp::Lt => FractHalfCmp::Lt,
        BinOp::Le => FractHalfCmp::Le,
        BinOp::Gt => FractHalfCmp::Gt,
        BinOp::Ge => FractHalfCmp::Ge,
        BinOp::Eq => FractHalfCmp::Eq,
        BinOp::Ne => FractHalfCmp::Ne,
        _ => return None,
    })
}
