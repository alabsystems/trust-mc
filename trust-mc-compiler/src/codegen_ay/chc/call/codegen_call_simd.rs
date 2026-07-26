// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SIMD intrinsic dispatch for CHC code generation.
//!
//! Handles element-wise binary operations (add, sub, mul, and, or, xor, shl, shr,
//! div, rem), comparison (eq, ne, lt, le, gt, ge), extract/insert, and sound
//! over-approximation fallback for unimplemented operations.
//!
//! Part of #3441: CHC SIMD intrinsic handlers.
//! Handler implementations in `codegen_call_simd_ops.rs`.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_call_simd_ops::{
    codegen_simd_cast, codegen_simd_comparison, codegen_simd_elementwise_binop,
    codegen_simd_extract, codegen_simd_insert, codegen_simd_reduce, codegen_simd_reduce_bool,
    codegen_simd_shift, codegen_simd_shuffle,
};
use super::codegen_rules::CodegenRules;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Classification of SIMD intrinsic operations.
#[derive(Clone, Copy, Debug)]
pub(in crate::codegen_ay::chc) enum SimdIntrinsicKind {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    ReduceAdd,
    ReduceMul,
    ReduceAnd,
    ReduceOr,
    ReduceXor,
    ReduceMin,
    ReduceMax,
    ReduceAll,
    ReduceAny,
    Neg,
    Extract,
    Insert,
    Shuffle,
    Cast,
    Select,
}

/// Detect SIMD intrinsic from callee path.
fn detect_simd_intrinsic(path: &str) -> Option<SimdIntrinsicKind> {
    if !path.contains("simd") {
        return None;
    }
    let m = path.rsplit("::").next()?;
    match m {
        "simd_add" => Some(SimdIntrinsicKind::Add),
        "simd_sub" => Some(SimdIntrinsicKind::Sub),
        "simd_mul" => Some(SimdIntrinsicKind::Mul),
        "simd_div" => Some(SimdIntrinsicKind::Div),
        "simd_rem" => Some(SimdIntrinsicKind::Rem),
        "simd_and" => Some(SimdIntrinsicKind::And),
        "simd_or" => Some(SimdIntrinsicKind::Or),
        "simd_xor" => Some(SimdIntrinsicKind::Xor),
        "simd_shl" => Some(SimdIntrinsicKind::Shl),
        "simd_shr" => Some(SimdIntrinsicKind::Shr),
        "simd_eq" => Some(SimdIntrinsicKind::Eq),
        "simd_ne" => Some(SimdIntrinsicKind::Ne),
        "simd_lt" => Some(SimdIntrinsicKind::Lt),
        "simd_le" => Some(SimdIntrinsicKind::Le),
        "simd_gt" => Some(SimdIntrinsicKind::Gt),
        "simd_ge" => Some(SimdIntrinsicKind::Ge),
        "simd_reduce_add_ordered" | "simd_reduce_add_unordered" => {
            Some(SimdIntrinsicKind::ReduceAdd)
        }
        "simd_reduce_mul_ordered" | "simd_reduce_mul_unordered" => {
            Some(SimdIntrinsicKind::ReduceMul)
        }
        "simd_reduce_and" => Some(SimdIntrinsicKind::ReduceAnd),
        "simd_reduce_or" => Some(SimdIntrinsicKind::ReduceOr),
        "simd_reduce_xor" => Some(SimdIntrinsicKind::ReduceXor),
        "simd_reduce_min" => Some(SimdIntrinsicKind::ReduceMin),
        "simd_reduce_max" => Some(SimdIntrinsicKind::ReduceMax),
        "simd_reduce_all" => Some(SimdIntrinsicKind::ReduceAll),
        "simd_reduce_any" => Some(SimdIntrinsicKind::ReduceAny),
        "simd_extract" => Some(SimdIntrinsicKind::Extract),
        "simd_insert" => Some(SimdIntrinsicKind::Insert),
        "simd_neg" => Some(SimdIntrinsicKind::Neg),
        "simd_select" | "simd_select_bitmask" => Some(SimdIntrinsicKind::Select),
        "simd_cast" | "simd_as" => Some(SimdIntrinsicKind::Cast),
        _ if m.starts_with("simd_shuffle") => Some(SimdIntrinsicKind::Shuffle),
        _ => None,
    }
}

/// SIMD layout info extracted from the MIR type.
pub(in crate::codegen_ay::chc) struct SimdLayoutInfo {
    pub(in crate::codegen_ay::chc) lane_count: usize,
    pub(in crate::codegen_ay::chc) elem_width: u32,
    pub(in crate::codegen_ay::chc) is_signed: bool,
    pub(in crate::codegen_ay::chc) is_float: bool, // Part of #3857
}

/// Extract SIMD layout information from a `#[repr(simd)]` type.
pub(in crate::codegen_ay::chc) fn extract_simd_layout(
    ty: rustc_public::ty::Ty,
) -> Option<SimdLayoutInfo> {
    let TyKind::RigidTy(RigidTy::Adt(adt_def, args)) = ty.kind() else {
        return None;
    };
    let variants = adt_def.variants();
    if variants.len() != 1 || variants[0].fields().is_empty() {
        return None;
    }
    let fields = variants[0].fields();

    if fields.len() == 1 {
        let field_ty = fields[0].ty_with_args(&args);
        if let TyKind::RigidTy(RigidTy::Array(elem_ty, len_const)) = field_ty.kind() {
            let lane_count = len_const.eval_target_usize().ok()? as usize;
            let (elem_width, is_signed, is_float) = elem_ty_info(elem_ty)?;
            return Some(SimdLayoutInfo { lane_count, elem_width, is_signed, is_float });
        }
    }

    let first_field_ty = fields[0].ty_with_args(&args);
    let (elem_width, is_signed, is_float) = elem_ty_info(first_field_ty)?;
    Some(SimdLayoutInfo { lane_count: fields.len(), elem_width, is_signed, is_float })
}

/// Extract (width, is_signed, is_float) from a scalar element type. Part of #3857.
fn elem_ty_info(ty: rustc_public::ty::Ty) -> Option<(u32, bool, bool)> {
    use rustc_public::ty::{FloatTy, IntTy, UintTy};
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Int(k)) => {
            let w = match k {
                IntTy::I8 => 8,
                IntTy::I16 => 16,
                IntTy::I32 => 32,
                IntTy::I64 => 64,
                IntTy::I128 => 128,
                IntTy::Isize => POINTER_WIDTH,
            };
            Some((w, true, false))
        }
        TyKind::RigidTy(RigidTy::Uint(k)) => {
            let w = match k {
                UintTy::U8 => 8,
                UintTy::U16 => 16,
                UintTy::U32 => 32,
                UintTy::U64 => 64,
                UintTy::U128 => 128,
                UintTy::Usize => POINTER_WIDTH,
            };
            Some((w, false, false))
        }
        TyKind::RigidTy(RigidTy::Float(k)) => {
            let w = match k {
                FloatTy::F16 => 16,
                FloatTy::F32 => 32,
                FloatTy::F64 => 64,
                FloatTy::F128 => 128,
            };
            Some((w, false, true))
        }
        _ => None,
    }
}

/// Resolve a SIMD operand to the underlying array expression in CHC state.
///
/// SIMD types like `i32x2([i32; 2])` may appear as either:
/// - `Array(BV64, BV_elem)` — flattened state variable (common case)
/// - `Datatype(i32x2, fld_0: Array(...))` — when translate_operand succeeds
///
/// In the Datatype case, extract the inner `fld_0` array field.
pub(in crate::codegen_ay::chc) fn resolve_simd_array(
    ctx: &mut ChcCtx<'_, '_>,
    operand: &Operand,
    modified_locals: &HashSet<usize>,
) -> Option<Expr> {
    if let Some(expr) = ctx.translate_operand_with_modified(operand, modified_locals) {
        return Some(unwrap_simd_to_array(expr));
    }
    // Fallback: access base state variable directly (flattened array-based SIMD).
    let arg_local = match operand {
        Operand::Copy(p) | Operand::Move(p) => p.local,
        _ => return None,
    };
    let vec_idx = ctx.try_state_idx_for_local(arg_local)?;
    let vars = if modified_locals.contains(&arg_local) {
        &ctx.state_var_mgr.output_state_vars
    } else {
        &ctx.state_var_mgr.state_vars
    };
    vars.get(vec_idx).map(|(name, sort)| unwrap_simd_to_array(Expr::var(&**name, sort.clone())))
}

/// If the expression has Datatype sort wrapping an Array field, extract the inner array.
/// Otherwise return the expression unchanged (it's already Array sort from flattening).
fn unwrap_simd_to_array(expr: Expr) -> Expr {
    if expr.sort().is_array() {
        return expr;
    }
    // Datatype with single constructor and single Array field → extract fld_0
    if let Some(dt) = expr.sort().datatype_sort() {
        if dt.constructors.len() == 1 && dt.constructors[0].fields.len() == 1 {
            let field = &dt.constructors[0].fields[0];
            if field.sort.is_array() {
                let dt_name = dt.name.clone();
                let field_name = field.name.clone();
                let field_sort = field.sort.clone();
                return expr.field_select(dt_name, field_name, field_sort);
            }
        }
    }
    expr
}

/// Extension trait for SIMD intrinsic dispatch in CHC call terminators.
pub(in crate::codegen_ay::chc) trait CallDispatchSimd {
    fn try_dispatch_call_simd(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchSimd for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_simd(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let callee_path = dcx.callee_path.clone().or_else(|| self.resolve_callee_path(dcx.func));
        let Some(ref path) = callee_path else { return false };
        let Some(kind) = detect_simd_intrinsic(path) else { return false };

        let Some(target) = dcx.target else { return true };
        debug!("CHC simd dispatch: {:?} (bb{}->bb{})", kind, dcx.bb_idx, target);

        match kind {
            SimdIntrinsicKind::Add
            | SimdIntrinsicKind::Sub
            | SimdIntrinsicKind::Mul
            | SimdIntrinsicKind::And
            | SimdIntrinsicKind::Or
            | SimdIntrinsicKind::Xor
            | SimdIntrinsicKind::Div
            | SimdIntrinsicKind::Rem => {
                codegen_simd_elementwise_binop(self, dcx, *target, kind);
            }
            SimdIntrinsicKind::Shl | SimdIntrinsicKind::Shr => {
                codegen_simd_shift(self, dcx, *target, kind);
            }
            SimdIntrinsicKind::Eq
            | SimdIntrinsicKind::Ne
            | SimdIntrinsicKind::Lt
            | SimdIntrinsicKind::Le
            | SimdIntrinsicKind::Gt
            | SimdIntrinsicKind::Ge => {
                codegen_simd_comparison(self, dcx, *target, kind);
            }
            SimdIntrinsicKind::Extract => codegen_simd_extract(self, dcx, *target),
            SimdIntrinsicKind::Insert => codegen_simd_insert(self, dcx, *target),
            SimdIntrinsicKind::ReduceAdd
            | SimdIntrinsicKind::ReduceMul
            | SimdIntrinsicKind::ReduceAnd
            | SimdIntrinsicKind::ReduceOr
            | SimdIntrinsicKind::ReduceXor
            | SimdIntrinsicKind::ReduceMin
            | SimdIntrinsicKind::ReduceMax => {
                codegen_simd_reduce(self, dcx, *target, kind);
            }
            SimdIntrinsicKind::ReduceAll => codegen_simd_reduce_bool(self, dcx, *target, true),
            SimdIntrinsicKind::ReduceAny => codegen_simd_reduce_bool(self, dcx, *target, false),
            SimdIntrinsicKind::Neg => codegen_simd_neg(self, dcx, *target),
            SimdIntrinsicKind::Select => codegen_simd_select(self, dcx, *target),
            SimdIntrinsicKind::Shuffle => codegen_simd_shuffle(self, dcx, *target),
            SimdIntrinsicKind::Cast => codegen_simd_cast(self, dcx, *target),
        }
        true
    }
}

/// Element-wise unary negation handler (simd_neg).
/// Integer lanes: BV two's complement negation (bvneg).
/// Float lanes: toggle sign bit via XOR with 0x80..0.
fn codegen_simd_neg(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;
    let src_arr = resolve_simd_array(ctx, &dcx.args[0], dcx.modified_locals);
    let layout = dcx.args.first().and_then(|op| {
        let ty = op.ty(ctx.body.locals()).ok()?;
        extract_simd_layout(ty)
    });

    if let (Some(src), Some(layout)) = (src_arr, layout) {
        let mut result =
            neutral_simd_result_array_like(&src, layout.elem_width).unwrap_or_else(|| src.clone());
        let sign_mask = if layout.is_float {
            Some(Expr::bitvec_const(1u64 << (layout.elem_width - 1), layout.elem_width))
        } else {
            None
        };
        for i in 0..layout.lane_count {
            let idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
            let elem = src.clone().select(idx.clone());
            let neg = if let Some(ref mask) = sign_mask {
                elem.bvxor(mask.clone())
            } else {
                elem.bvneg()
            };
            result = result.store(idx, neg);
        }
        emit_simd_dest_constraint(ctx, dcx, target, dest_local, result);
    } else {
        debug!("CHC simd_neg: operand resolution failed, sound fallback");
        emit_simd_sound_fallback(ctx, dcx, target);
    }
}

/// Element-wise mask select: `simd_select(mask, a, b) -> if mask[i] != 0 then a[i] else b[i]`.
fn codegen_simd_select(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;
    if dcx.args.len() < 3 {
        debug!("CHC simd_select: need 3 args, sound fallback");
        emit_simd_sound_fallback(ctx, dcx, target);
        return;
    }
    let mask_arr = resolve_simd_array(ctx, &dcx.args[0], dcx.modified_locals);
    let a_arr = resolve_simd_array(ctx, &dcx.args[1], dcx.modified_locals);
    let b_arr = resolve_simd_array(ctx, &dcx.args[2], dcx.modified_locals);
    let layout = dcx.args.get(1).and_then(|op| {
        let ty = op.ty(ctx.body.locals()).ok()?;
        extract_simd_layout(ty)
    });

    if let (Some(mask), Some(a), Some(b), Some(layout)) = (mask_arr, a_arr, b_arr, layout) {
        let mut result =
            neutral_simd_result_array_like(&a, layout.elem_width).unwrap_or_else(|| a.clone());
        let zero = Expr::bitvec_const(0u64, layout.elem_width);
        for i in 0..layout.lane_count {
            let idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
            let m = mask.clone().select(idx.clone());
            let a_elem = a.clone().select(idx.clone());
            let b_elem = b.clone().select(idx.clone());
            let selected = Expr::ite(m.eq(zero.clone()).not(), a_elem, b_elem);
            result = result.store(idx, selected);
        }
        emit_simd_dest_constraint(ctx, dcx, target, dest_local, result);
    } else {
        debug!("CHC simd_select: operand resolution failed, sound fallback");
        emit_simd_sound_fallback(ctx, dcx, target);
    }
}

/// Emit a CHC rule constraining destination = result.
pub(in crate::codegen_ay::chc) fn emit_simd_dest_constraint(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    dest_local: usize,
    result: Expr,
) {
    if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
        let s = dest_var.sort().clone();
        let eq = ctx.make_coerced_eq_constraint(&dest_var, result, &s, dest_local, "simd_op");
        let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        if let Some(eq) = eq {
            ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, [eq]);
        } else {
            ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        }
    } else {
        emit_sound_fallback_goto(
            ctx,
            dcx.from_app,
            target,
            dcx.modified_locals,
            &[dest_local],
            dcx.stmt_constraints,
        );
    }
}

/// Emit sound over-approximation fallback.
pub(in crate::codegen_ay::chc) fn emit_simd_sound_fallback(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    emit_sound_fallback_goto(
        ctx,
        dcx.from_app,
        target,
        dcx.modified_locals,
        &[dcx.destination.local],
        dcx.stmt_constraints,
    );
}

/// Build a neutral Array base for SIMD operations that overwrite every lane.
///
/// Reusing the lhs/source array as the store-chain base preserves irrelevant
/// out-of-lane dependencies in the infinite Array encoding of finite SIMD
/// values. A zero `const_array` keeps only the meaningful lane stores.
pub(in crate::codegen_ay::chc) fn neutral_simd_result_array_like(
    source: &Expr,
    elem_width: u32,
) -> Option<Expr> {
    let arr = source.sort().array_sort()?;
    Some(Expr::const_array(arr.index_sort.clone(), Expr::bitvec_const(0u64, elem_width)))
}

/// Coerce an index expression to pointer width (BV64) for array select/store.
pub(in crate::codegen_ay::chc) fn coerce_to_pointer_width(expr: &Expr) -> Expr {
    if let Some(w) = expr.sort().bitvec_width() {
        if w == POINTER_WIDTH {
            return expr.clone();
        }
        if w < POINTER_WIDTH {
            return expr.clone().zero_extend(POINTER_WIDTH - w);
        }
        return expr.clone().extract(POINTER_WIDTH - 1, 0);
    }
    expr.clone()
}
