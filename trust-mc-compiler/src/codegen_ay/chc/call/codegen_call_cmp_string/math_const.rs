// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Constant extraction helpers for math intrinsic constant folding.
//!
//! Extracts compile-time float/integer constants from MIR operands for
//! math intrinsic constant folding in the CHC path. Handles both direct
//! `Operand::Constant` and `Operand::Copy/Move` of locals assigned constants.
//! Follows up to 8 levels of Copy/Move indirection (Part of #3616).
//!
//! A local's constant is taken from its assignment ONLY when that assignment is
//! the sole write the body can make to it (`sole_plain_assignment`). The scan
//! used to return the first `local = const` it found anywhere in the body,
//! flow-insensitively, so `let mut a = 1.0; if c { a = -0.0 } a.min(0.0)` was
//! folded as `min(1.0, 0.0)` and CHC proved a sign Rust leaves to either zero
//! on the `c` path. With one plain assignment and no borrow, call destination,
//! partial write or discriminant write to the local, borrow checking guarantees
//! that value reaches every use, on every path; anything else is not folded
//! and the relation decides.
//!
//! Split from `math.rs` per file size limit (Part of #3524).

use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::{Body, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{FloatTy, RigidTy, TyKind};
use std::collections::HashSet;

use super::super::ChcCtx;

/// Extract a constant f32 value (as raw bits) from a MIR operand.
///
/// Handles two cases:
/// 1. `Operand::Constant` — extracts directly from the constant allocation
/// 2. `Operand::Copy/Move` — scans the MIR body for the assignment to the local,
///    and extracts the constant if the RHS is `Rvalue::Use(Operand::Constant(_))`
///    or follows one level of Copy/Move indirection (Part of #3616)
pub(in crate::codegen_ay::chc) fn try_extract_const_f32(
    operand: &Operand,
    body: &Body,
) -> Option<u32> {
    match operand {
        Operand::Constant(c) => extract_f32_from_const_op(c),
        Operand::Copy(place) | Operand::Move(place) => {
            if !place.projection.is_empty() {
                return None;
            }
            find_const_f32_assignment(body, place.local)
        }
        #[cfg(trust_toolchain)]
        Operand::RuntimeChecks(_) => None,
    }
}

/// Extract a constant f32 value from an operand using the current CHC env first.
///
/// `local_expr_env` carries precise intra-block expressions for temps produced by
/// earlier statements in the same block. When a math intrinsic consumes such a temp,
/// reading the already-built expr recovers constants that are no longer obvious from
/// the raw MIR assignment chain alone.
pub(in crate::codegen_ay::chc) fn try_extract_const_f32_with_ctx(
    ctx: &mut ChcCtx<'_, '_>,
    operand: &Operand,
    modified_locals: &HashSet<usize>,
) -> Option<u32> {
    try_extract_f32_from_expr(&ctx.translate_operand_with_modified(operand, modified_locals)?)
        .or_else(|| try_extract_const_f32(operand, ctx.body))
}

/// Extract a constant f64 value (as raw bits) from a MIR operand.
pub(in crate::codegen_ay::chc) fn try_extract_const_f64(
    operand: &Operand,
    body: &Body,
) -> Option<u64> {
    match operand {
        Operand::Constant(c) => extract_f64_from_const_op(c),
        Operand::Copy(place) | Operand::Move(place) => {
            if !place.projection.is_empty() {
                return None;
            }
            find_const_f64_assignment(body, place.local)
        }
        #[cfg(trust_toolchain)]
        Operand::RuntimeChecks(_) => None,
    }
}

/// Extract a constant f64 value from an operand using the current CHC env first.
pub(in crate::codegen_ay::chc) fn try_extract_const_f64_with_ctx(
    ctx: &mut ChcCtx<'_, '_>,
    operand: &Operand,
    modified_locals: &HashSet<usize>,
) -> Option<u64> {
    try_extract_f64_from_expr(&ctx.translate_operand_with_modified(operand, modified_locals)?)
        .or_else(|| try_extract_const_f64(operand, ctx.body))
}

/// Extract a constant i32 value from a MIR operand (for powi).
pub(in crate::codegen_ay::chc) fn try_extract_const_i32(
    operand: &Operand,
    body: &Body,
) -> Option<i32> {
    match operand {
        Operand::Constant(c) => extract_i32_from_const_op(c),
        Operand::Copy(place) | Operand::Move(place) => {
            if !place.projection.is_empty() {
                return None;
            }
            find_const_i32_assignment(body, place.local)
        }
        #[cfg(trust_toolchain)]
        Operand::RuntimeChecks(_) => None,
    }
}

/// Extract a constant i32 value from an operand using the current CHC env first.
pub(in crate::codegen_ay::chc) fn try_extract_const_i32_with_ctx(
    ctx: &mut ChcCtx<'_, '_>,
    operand: &Operand,
    modified_locals: &HashSet<usize>,
) -> Option<i32> {
    try_extract_i32_from_expr(&ctx.translate_operand_with_modified(operand, modified_locals)?)
        .or_else(|| try_extract_const_i32(operand, ctx.body))
}

/// Try to constant-fold an f32 math intrinsic.
/// Returns the result as raw f32 bits if all arguments are constant.
pub(in crate::codegen_ay::chc) fn try_fold_f32_intrinsic(
    ctx: &mut ChcCtx<'_, '_>,
    intrinsic_name: &str,
    args: &[Operand],
    modified_locals: &HashSet<usize>,
) -> Option<u32> {
    let arg0 = args.first()?;
    let bits0 = try_extract_const_f32_with_ctx(ctx, arg0, modified_locals)?;
    let val0 = f32::from_bits(bits0);

    let compute_unary = |val: f32| -> Option<f32> {
        if intrinsic_name.ends_with("sqrtf32") {
            Some(val.sqrt())
        } else if intrinsic_name.ends_with("sinf32") {
            Some(val.sin())
        } else if intrinsic_name.ends_with("cosf32") {
            Some(val.cos())
        } else if intrinsic_name.ends_with("expf32") {
            Some(val.exp())
        } else if intrinsic_name.ends_with("exp2f32") {
            Some(val.exp2())
        } else if intrinsic_name.ends_with("logf32") {
            Some(val.ln())
        } else if intrinsic_name.ends_with("log2f32") {
            Some(val.log2())
        } else if intrinsic_name.ends_with("log10f32") {
            Some(val.log10())
        } else if intrinsic_name.ends_with("fabsf32") {
            Some(val.abs())
        } else if intrinsic_name.ends_with("floorf32") {
            Some(val.floor())
        } else if intrinsic_name.ends_with("ceilf32") {
            Some(val.ceil())
        } else if intrinsic_name.ends_with("truncf32") {
            Some(val.trunc())
        } else if intrinsic_name.ends_with("roundf32") {
            Some(val.round())
        } else if intrinsic_name.ends_with("round_ties_even_f32") {
            Some(val.round_ties_even())
        } else {
            None
        }
    };

    if intrinsic_name.ends_with("powf32") {
        let bits1 = try_extract_const_f32_with_ctx(ctx, args.get(1)?, modified_locals)?;
        return Some(val0.powf(f32::from_bits(bits1)).to_bits());
    } else if intrinsic_name.ends_with("powif32") {
        let bits1 = try_extract_const_i32_with_ctx(ctx, args.get(1)?, modified_locals)?;
        return Some(val0.powi(bits1).to_bits());
    } else if intrinsic_name.ends_with("copysignf32") {
        let bits1 = try_extract_const_f32_with_ctx(ctx, args.get(1)?, modified_locals)?;
        return Some(val0.copysign(f32::from_bits(bits1)).to_bits());
    } else if intrinsic_name.ends_with("minnumf32") || intrinsic_name.ends_with("maxnumf32") {
        let val1 =
            f32::from_bits(try_extract_const_f32_with_ctx(ctx, args.get(1)?, modified_locals)?);
        // Decided by IEEE comparison where both toolchains agree; opposite zeros, two NaNs and
        // a signalling NaN are left to the relation (`float_minmax`). Never the host's `min`.
        let is_min = intrinsic_name.ends_with("minnumf32");
        return crate::codegen_ay::float_minmax::minmax_num_fold_f32(is_min, val0, val1)
            .map(f32::to_bits);
    } else if intrinsic_name.ends_with("fmaf32") {
        let bits1 = try_extract_const_f32_with_ctx(ctx, args.get(1)?, modified_locals)?;
        let bits2 = try_extract_const_f32_with_ctx(ctx, args.get(2)?, modified_locals)?;
        return Some(val0.mul_add(f32::from_bits(bits1), f32::from_bits(bits2)).to_bits());
    }

    let result = compute_unary(val0)?;
    if result.is_nan() && !val0.is_nan() {
        return None;
    }
    Some(result.to_bits())
}

/// Try to constant-fold an f64 math intrinsic.
/// Returns the result as raw f64 bits if all arguments are constant.
pub(in crate::codegen_ay::chc) fn try_fold_f64_intrinsic(
    ctx: &mut ChcCtx<'_, '_>,
    intrinsic_name: &str,
    args: &[Operand],
    modified_locals: &HashSet<usize>,
) -> Option<u64> {
    let arg0 = args.first()?;
    let bits0 = try_extract_const_f64_with_ctx(ctx, arg0, modified_locals)?;
    let val0 = f64::from_bits(bits0);

    let compute_unary = |val: f64| -> Option<f64> {
        if intrinsic_name.ends_with("sqrtf64") {
            Some(val.sqrt())
        } else if intrinsic_name.ends_with("sinf64") {
            Some(val.sin())
        } else if intrinsic_name.ends_with("cosf64") {
            Some(val.cos())
        } else if intrinsic_name.ends_with("expf64") {
            Some(val.exp())
        } else if intrinsic_name.ends_with("exp2f64") {
            Some(val.exp2())
        } else if intrinsic_name.ends_with("logf64") {
            Some(val.ln())
        } else if intrinsic_name.ends_with("log2f64") {
            Some(val.log2())
        } else if intrinsic_name.ends_with("log10f64") {
            Some(val.log10())
        } else if intrinsic_name.ends_with("fabsf64") {
            Some(val.abs())
        } else if intrinsic_name.ends_with("floorf64") {
            Some(val.floor())
        } else if intrinsic_name.ends_with("ceilf64") {
            Some(val.ceil())
        } else if intrinsic_name.ends_with("truncf64") {
            Some(val.trunc())
        } else if intrinsic_name.ends_with("roundf64") {
            Some(val.round())
        } else if intrinsic_name.ends_with("round_ties_even_f64") {
            Some(val.round_ties_even())
        } else {
            None
        }
    };

    if intrinsic_name.ends_with("powf64") {
        let bits1 = try_extract_const_f64_with_ctx(ctx, args.get(1)?, modified_locals)?;
        return Some(val0.powf(f64::from_bits(bits1)).to_bits());
    } else if intrinsic_name.ends_with("powif64") {
        let bits1 = try_extract_const_i32_with_ctx(ctx, args.get(1)?, modified_locals)?;
        return Some(val0.powi(bits1).to_bits());
    } else if intrinsic_name.ends_with("copysignf64") {
        let bits1 = try_extract_const_f64_with_ctx(ctx, args.get(1)?, modified_locals)?;
        return Some(val0.copysign(f64::from_bits(bits1)).to_bits());
    } else if intrinsic_name.ends_with("minnumf64") || intrinsic_name.ends_with("maxnumf64") {
        let val1 =
            f64::from_bits(try_extract_const_f64_with_ctx(ctx, args.get(1)?, modified_locals)?);
        // See the f32 arm: IEEE comparison where determined, the relation otherwise.
        let is_min = intrinsic_name.ends_with("minnumf64");
        return crate::codegen_ay::float_minmax::minmax_num_fold_f64(is_min, val0, val1)
            .map(f64::to_bits);
    } else if intrinsic_name.ends_with("fmaf64") {
        let bits1 = try_extract_const_f64_with_ctx(ctx, args.get(1)?, modified_locals)?;
        let bits2 = try_extract_const_f64_with_ctx(ctx, args.get(2)?, modified_locals)?;
        return Some(val0.mul_add(f64::from_bits(bits1), f64::from_bits(bits2)).to_bits());
    }

    let result = compute_unary(val0)?;
    if result.is_nan() && !val0.is_nan() {
        return None;
    }
    Some(result.to_bits())
}

/// Maximum depth for Copy/Move chain tracing in MIR constant scan.
/// Prevents infinite loops on pathological MIR (e.g., self-referencing locals).
const MAX_COPY_CHAIN_DEPTH: usize = 8;

/// The one `Rvalue` assigned to `local`, when that assignment is the ONLY write the body
/// can make to it: exactly one whole-place `Assign`, and no partial write
/// (`local.field = …`), no `SetDiscriminant`, no borrow or raw address of any
/// place rooted at the local (a write through the reference would not name it), no call or
/// `Yield` destination, no inline assembly (whose outputs are opaque here), and the local is
/// not an argument (its first value is the caller's). Under those conditions borrow checking
/// guarantees the assigned value reaches every use on every path, so reading it is
/// flow-insensitive only in appearance.
///
/// Returns `None` for every other shape. The previous scan returned the FIRST `local = const`
/// found in any block, so a local assigned on two paths folded to whichever assignment came
/// first in block order: a false proof when the other path's constant changes the result.
fn sole_plain_assignment(body: &Body, local: usize) -> Option<&Rvalue> {
    if (1..=body.arg_locals().len()).contains(&local) {
        return None;
    }
    let mut sole: Option<&Rvalue> = None;
    for bb in &body.blocks {
        for stmt in &bb.statements {
            match &stmt.kind {
                StatementKind::Assign(lhs, rhs) => {
                    if lhs.local == local {
                        if !lhs.projection.is_empty() || sole.is_some() {
                            return None;
                        }
                        sole = Some(rhs);
                    }
                    if let Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) = rhs
                        && place.local == local
                    {
                        return None;
                    }
                }
                StatementKind::SetDiscriminant { place, .. } if place.local == local => {
                    return None;
                }
                _ => {}
            }
        }
        match &bb.terminator.kind {
            TerminatorKind::Call { destination, .. } if destination.local == local => {
                return None;
            }
            TerminatorKind::InlineAsm { .. } => return None,
            _ => {}
        }
    }
    sole
}

/// Follow `local`'s sole assignment to a constant, through up to `depth` plain copies of
/// other sole-assigned locals, reading the constant with `extract`.
fn find_sole_const_assignment<T>(
    body: &Body,
    local: usize,
    depth: usize,
    extract: fn(&rustc_public::mir::ConstOperand) -> Option<T>,
) -> Option<T> {
    if depth == 0 {
        return None;
    }
    match sole_plain_assignment(body, local)? {
        Rvalue::Use(Operand::Constant(c), ..) => extract(c),
        Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) if src.projection.is_empty() => {
            find_sole_const_assignment(body, src.local, depth - 1, extract)
        }
        _ => None,
    }
}

/// The constant f32 `local` holds at every use, if its sole assignment is one.
/// Follows Copy/Move chains up to MAX_COPY_CHAIN_DEPTH levels deep.
fn find_const_f32_assignment(body: &Body, local_idx: usize) -> Option<u32> {
    find_sole_const_assignment(body, local_idx, MAX_COPY_CHAIN_DEPTH, extract_f32_from_const_op)
}

/// The constant f64 `local` holds at every use, if its sole assignment is one.
fn find_const_f64_assignment(body: &Body, local_idx: usize) -> Option<u64> {
    find_sole_const_assignment(body, local_idx, MAX_COPY_CHAIN_DEPTH, extract_f64_from_const_op)
}

/// The constant i32 `local` holds at every use, if its sole assignment is one.
fn find_const_i32_assignment(body: &Body, local_idx: usize) -> Option<i32> {
    find_sole_const_assignment(body, local_idx, MAX_COPY_CHAIN_DEPTH, extract_i32_from_const_op)
}

fn try_extract_f32_from_expr(expr: &Expr) -> Option<u32> {
    match expr.value() {
        ExprValue::BitVecConst { value, width } if *width == 32 => u32::try_from(value).ok(),
        _ => None,
    }
}

fn try_extract_f64_from_expr(expr: &Expr) -> Option<u64> {
    match expr.value() {
        ExprValue::BitVecConst { value, width } if *width == 64 => u64::try_from(value).ok(),
        _ => None,
    }
}

fn try_extract_i32_from_expr(expr: &Expr) -> Option<i32> {
    match expr.value() {
        ExprValue::BitVecConst { value, width } if *width == 32 => {
            u32::try_from(value).ok().map(|bits| bits as i32)
        }
        _ => None,
    }
}

/// Extract f32 bits from a ConstOperand.
fn extract_f32_from_const_op(const_op: &rustc_public::mir::ConstOperand) -> Option<u32> {
    let mir_const = &const_op.const_;
    let ty = mir_const.ty();
    if !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Float(FloatTy::F32))) {
        return None;
    }
    let bits = crate::codegen_ay::shared::const_pointer::const_uint(mir_const)?;
    u32::try_from(bits).ok()
}

/// Extract f64 bits from a ConstOperand.
fn extract_f64_from_const_op(const_op: &rustc_public::mir::ConstOperand) -> Option<u64> {
    let mir_const = &const_op.const_;
    let ty = mir_const.ty();
    if !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Float(FloatTy::F64))) {
        return None;
    }
    let bits = crate::codegen_ay::shared::const_pointer::const_uint(mir_const)?;
    u64::try_from(bits).ok()
}

/// Extract i32 from a ConstOperand.
fn extract_i32_from_const_op(const_op: &rustc_public::mir::ConstOperand) -> Option<i32> {
    let mir_const = &const_op.const_;
    crate::codegen_ay::shared::const_pointer::const_int(mir_const).map(|v| v as i32)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen_ay::context::with_test_ay_ctx_for_source;
    use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
    use rustc_public::CrateDef;
    use rustc_public::ty::{RigidTy, TyKind};

    const SOURCE: &str = r#"#![allow(dead_code, unused_assignments)]
pub fn straight() -> f32 {
    let a = 1.0f32;
    a.min(0.0)
}
pub fn copied() -> f32 {
    let a = -0.0f32;
    let b = a;
    b.min(0.0)
}
pub fn phi(c: bool) -> f32 {
    let mut a = 1.0f32;
    if c {
        a = -0.0;
    }
    a.min(0.0)
}
pub fn reassigned() -> f32 {
    let mut a = 1.0f32;
    a = -0.0;
    a.min(0.0)
}
#[inline(never)]
fn set(p: &mut f32) {
    *p = -0.0;
}
pub fn borrowed() -> f32 {
    let mut a = 1.0f32;
    set(&mut a);
    a.min(0.0)
}
pub fn raw(c: bool) -> f32 {
    let mut a = 1.0f32;
    let p = &raw mut a;
    if c {
        unsafe { *p = -0.0 };
    }
    a.min(0.0)
}
pub fn argument(a: f32) -> f32 {
    a.min(0.0)
}
pub fn wide(c: bool) -> f64 {
    let mut a = 1.0f64;
    if c {
        a = -0.0;
    }
    a.max(0.0)
}
"#;

    /// The first argument operand of the `min` / `max` call in `body`.
    fn min_max_first_arg(body: &Body) -> Operand {
        for bb in &body.blocks {
            if let TerminatorKind::Call { func, args, .. } = &bb.terminator.kind
                && let Ok(ty) = func.ty(body.locals())
                && let TyKind::RigidTy(RigidTy::FnDef(def, _)) = ty.kind()
                && let Some(name) = def.name().rsplit("::").next()
                && matches!(name, "min" | "max")
            {
                return args[0].clone();
            }
        }
        panic!("no min/max call in body");
    }

    fn first_arg_f32(fn_suffix: &str) -> Option<u32> {
        let mut result = None;
        with_test_ay_ctx_for_source(SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
            let body = instance.body().expect("body");
            result = Some(try_extract_const_f32(&min_max_first_arg(&body), &body));
        });
        result.expect("callback ran")
    }

    fn first_arg_f64(fn_suffix: &str) -> Option<u64> {
        let mut result = None;
        with_test_ay_ctx_for_source(SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
            let body = instance.body().expect("body");
            result = Some(try_extract_const_f64(&min_max_first_arg(&body), &body));
        });
        result.expect("callback ran")
    }

    /// A local with one plain assignment, directly or through a copy, folds.
    #[test]
    fn sole_assignment_folds_through_copies() {
        assert_eq!(first_arg_f32("straight"), Some(1.0f32.to_bits()));
        assert_eq!(first_arg_f32("copied"), Some(0x8000_0000));
    }

    /// A local written on two paths, reassigned, borrowed, aliased by a raw pointer or
    /// received as an argument is never folded: the value at the call depends on the path.
    #[test]
    fn multiply_written_or_aliased_locals_do_not_fold() {
        assert_eq!(first_arg_f32("phi"), None);
        assert_eq!(first_arg_f32("reassigned"), None);
        assert_eq!(first_arg_f32("borrowed"), None);
        assert_eq!(first_arg_f32("raw"), None);
        assert_eq!(first_arg_f32("argument"), None);
        assert_eq!(first_arg_f64("wide"), None);
    }
}
