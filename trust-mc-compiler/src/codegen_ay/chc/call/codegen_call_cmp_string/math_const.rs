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
//! Split from `math.rs` per file size limit (Part of #3524).

use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::{Body, Operand, Rvalue, StatementKind};
use rustc_public::ty::{ConstantKind, FloatTy, RigidTy, TyConstKind, TyKind};
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
    } else if intrinsic_name.ends_with("minnumf32") {
        let bits1 = try_extract_const_f32_with_ctx(ctx, args.get(1)?, modified_locals)?;
        return Some(val0.min(f32::from_bits(bits1)).to_bits());
    } else if intrinsic_name.ends_with("maxnumf32") {
        let bits1 = try_extract_const_f32_with_ctx(ctx, args.get(1)?, modified_locals)?;
        return Some(val0.max(f32::from_bits(bits1)).to_bits());
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
    } else if intrinsic_name.ends_with("minnumf64") {
        let bits1 = try_extract_const_f64_with_ctx(ctx, args.get(1)?, modified_locals)?;
        return Some(val0.min(f64::from_bits(bits1)).to_bits());
    } else if intrinsic_name.ends_with("maxnumf64") {
        let bits1 = try_extract_const_f64_with_ctx(ctx, args.get(1)?, modified_locals)?;
        return Some(val0.max(f64::from_bits(bits1)).to_bits());
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

/// Scan MIR body for a constant f32 assignment to the given local.
/// Follows Copy/Move chains up to MAX_COPY_CHAIN_DEPTH levels deep.
/// Part of #3839: fix multi-hop constant extraction for math intrinsics.
fn find_const_f32_assignment(body: &Body, local_idx: usize) -> Option<u32> {
    find_const_f32_recursive(body, local_idx, MAX_COPY_CHAIN_DEPTH)
}

fn find_const_f32_recursive(body: &Body, local_idx: usize, depth: usize) -> Option<u32> {
    if depth == 0 {
        return None;
    }
    for bb in &body.blocks {
        for stmt in &bb.statements {
            if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                && lhs.local == local_idx
                && lhs.projection.is_empty()
            {
                match rhs {
                    Rvalue::Use(Operand::Constant(c)) => {
                        return extract_f32_from_const_op(c);
                    }
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                        if src.projection.is_empty() =>
                    {
                        return find_const_f32_recursive(body, src.local, depth - 1);
                    }
                    _ => {}
                }
            }
        }
    }
    None
}

/// Scan MIR body for a constant f64 assignment to the given local.
/// Follows Copy/Move chains up to MAX_COPY_CHAIN_DEPTH levels deep.
/// Part of #3839: fix multi-hop constant extraction for math intrinsics.
fn find_const_f64_assignment(body: &Body, local_idx: usize) -> Option<u64> {
    find_const_f64_recursive(body, local_idx, MAX_COPY_CHAIN_DEPTH)
}

fn find_const_f64_recursive(body: &Body, local_idx: usize, depth: usize) -> Option<u64> {
    if depth == 0 {
        return None;
    }
    for bb in &body.blocks {
        for stmt in &bb.statements {
            if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                && lhs.local == local_idx
                && lhs.projection.is_empty()
            {
                match rhs {
                    Rvalue::Use(Operand::Constant(c)) => {
                        return extract_f64_from_const_op(c);
                    }
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                        if src.projection.is_empty() =>
                    {
                        return find_const_f64_recursive(body, src.local, depth - 1);
                    }
                    _ => {}
                }
            }
        }
    }
    None
}

/// Scan MIR body for a constant i32 assignment to the given local.
/// Follows Copy/Move chains up to MAX_COPY_CHAIN_DEPTH levels deep.
/// Part of #3839: fix multi-hop constant extraction for math intrinsics.
fn find_const_i32_assignment(body: &Body, local_idx: usize) -> Option<i32> {
    find_const_i32_recursive(body, local_idx, MAX_COPY_CHAIN_DEPTH)
}

fn find_const_i32_recursive(body: &Body, local_idx: usize, depth: usize) -> Option<i32> {
    if depth == 0 {
        return None;
    }
    for bb in &body.blocks {
        for stmt in &bb.statements {
            if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                && lhs.local == local_idx
                && lhs.projection.is_empty()
            {
                match rhs {
                    Rvalue::Use(Operand::Constant(c)) => {
                        return extract_i32_from_const_op(c);
                    }
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                        if src.projection.is_empty() =>
                    {
                        return find_const_i32_recursive(body, src.local, depth - 1);
                    }
                    _ => {}
                }
            }
        }
    }
    None
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
    let read_f32 = |alloc: &rustc_public::ty::Allocation| -> Option<u32> {
        if alloc.bytes.len() < 4 {
            return None;
        }
        let mut arr = [0u8; 4];
        for (i, b) in alloc.bytes.iter().take(4).enumerate() {
            arr[i] = (*b)?;
        }
        Some(u32::from_le_bytes(arr))
    };
    match mir_const.kind() {
        ConstantKind::Allocated(alloc) => read_f32(alloc),
        ConstantKind::Ty(ty_const) => match ty_const.kind() {
            TyConstKind::Value(_ty, alloc) => read_f32(alloc),
            _ => None,
        },
        _ => None,
    }
}

/// Extract f64 bits from a ConstOperand.
fn extract_f64_from_const_op(const_op: &rustc_public::mir::ConstOperand) -> Option<u64> {
    let mir_const = &const_op.const_;
    let ty = mir_const.ty();
    if !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Float(FloatTy::F64))) {
        return None;
    }
    let read_f64 = |alloc: &rustc_public::ty::Allocation| -> Option<u64> {
        if alloc.bytes.len() < 8 {
            return None;
        }
        let mut arr = [0u8; 8];
        for (i, b) in alloc.bytes.iter().take(8).enumerate() {
            arr[i] = (*b)?;
        }
        Some(u64::from_le_bytes(arr))
    };
    match mir_const.kind() {
        ConstantKind::Allocated(alloc) => read_f64(alloc),
        ConstantKind::Ty(ty_const) => match ty_const.kind() {
            TyConstKind::Value(_ty, alloc) => read_f64(alloc),
            _ => None,
        },
        _ => None,
    }
}

/// Extract i32 from a ConstOperand.
fn extract_i32_from_const_op(const_op: &rustc_public::mir::ConstOperand) -> Option<i32> {
    let mir_const = &const_op.const_;
    let read_i32 = |alloc: &rustc_public::ty::Allocation| -> Option<i32> {
        alloc.read_int().ok().map(|v| v as i32)
    };
    match mir_const.kind() {
        ConstantKind::Allocated(alloc) => read_i32(alloc),
        ConstantKind::Ty(ty_const) => match ty_const.kind() {
            TyConstKind::Value(_ty, alloc) => read_i32(alloc),
            _ => None,
        },
        _ => None,
    }
}
