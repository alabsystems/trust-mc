// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Pointer-specific miscellaneous intrinsic handlers for CHC codegen.

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::super::codegen_rules::CodegenRules;
use crate::codegen_ay::chc::pointer_step::step_split_pointer;
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};
use crate::kani_middle::abi::LayoutOf;

pub(in crate::codegen_ay::chc) fn codegen_arith_offset(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let args = dcx.args;
    let destination = dcx.destination;
    let from_app = dcx.from_app;
    let stmt_constraints = dcx.stmt_constraints;
    let modified_locals = dcx.modified_locals;
    let dest_local: usize = destination.local;

    if args.len() < 2 {
        debug!("arith_offset with < 2 args — unconstrained fallback");
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

    let base = ctx.translate_operand_with_modified(&args[0], modified_locals);
    let offset = ctx.translate_operand_with_modified(&args[1], modified_locals);

    if let (Some(base_expr), Some(offset_expr)) = (base, offset)
        && base_expr.sort().is_bitvec()
        && offset_expr.sort().is_bitvec()
    {
        let elem_size = extract_pointee_size(ctx, &args[0]);
        let Some(size) = elem_size else {
            debug!("arith_offset with unknown pointee size — unconstrained fallback");
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

        let size_expr = Expr::bitvec_const(size as u128, POINTER_WIDTH);
        let offset_coerced =
            coerce_bitvec_width_safe(offset_expr, POINTER_WIDTH, SignExtension::SignExtend);
        let byte_offset = offset_coerced.bvmul(size_expr);
        // Fail-closed provenance: `arith_offset` itself is legal (wrapping), but
        // when the base pointer's provenance is unresolved a later OOB deref of
        // the result cannot be bounds-checked. Provenance resolves either
        // syntactically (obj_id lane const-folds) or via the metadata
        // side-channel (`known_obj_id_for_operand`: identity-modeled as_ptr
        // results whose obj_id lane is an opaque SSA variable constrained equal
        // to the receiver's allocation). Only genuinely-unresolved cases record
        // the skipped check so the harness is demoted rather than falsely
        // proven Safe on an OOB read.
        if !ctx.int_lift
            && ctx
                .split_pointer(&base_expr)
                .and_then(|(obj_id, _)| ChcCtx::const_obj_id_u32(&obj_id))
                .or_else(|| ctx.known_obj_id_for_operand(&args[0]))
                .is_none()
        {
            // Task #78: record the skip AND plumb the base pointer's freed
            // identity so a count-independent counterexample can recertify.
            ctx.record_offset_provenance_unresolved(&base_expr);
        }
        // Part of #3921: use split-pointer step to preserve obj_id.
        let result = step_split_pointer(base_expr, byte_offset).result;

        debug!("CHC: arith_offset encoded as pointer arithmetic (Part of #3444)");

        if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
            let out_sort = dest_var.sort();
            let eq = ctx.make_coerced_eq_constraint(
                &dest_var,
                result,
                out_sort,
                dest_local,
                "codegen_arith_offset",
            );
            let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(from_app, target, &new_output_args, stmt_constraints, eq);
            // Mirror KaniModel::Offset (Part of #3798/#4156): propagate the source
            // pointer's ref_targets/subslice_offset (shifted by the const count) to
            // the result local so a downstream OOB deref of `arith_offset(ptr, k)`
            // resolves back to the original allocation and gets a real bounds check
            // — otherwise the result carries only a symbolic SSA address and the
            // deref is silently proven Safe (missed bug: arith-offset-u8-fail).
            ctx.propagate_signed_ptr_offset_result_metadata(dest_local, args, modified_locals);
        } else {
            emit_sound_fallback_goto(
                ctx,
                from_app,
                target,
                modified_locals,
                &[dest_local],
                stmt_constraints,
            );
        }
        return;
    }

    debug!("CHC: arith_offset fallback — args not translatable");
    emit_sound_fallback_goto(
        ctx,
        from_app,
        target,
        modified_locals,
        &[dest_local],
        stmt_constraints,
    );
}

pub(in crate::codegen_ay::chc) fn codegen_ptr_guaranteed_cmp(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let args = dcx.args;
    let destination = dcx.destination;
    let from_app = dcx.from_app;
    let stmt_constraints = dcx.stmt_constraints;
    let modified_locals = dcx.modified_locals;
    let dest_local: usize = destination.local;

    if args.len() < 2 {
        debug!("ptr_guaranteed_cmp with < 2 args — unconstrained fallback");
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

    let a = ctx.translate_operand_with_modified(&args[0], modified_locals);
    let b = ctx.translate_operand_with_modified(&args[1], modified_locals);

    if let (Some(a_expr), Some(b_expr)) = (a, b) {
        let one = Expr::bitvec_const(1u128, 8);
        let zero = Expr::bitvec_const(0u128, 8);
        let eq = a_expr.eq(b_expr);
        let result = Expr::ite(eq, one, zero);

        debug!("CHC: ptr_guaranteed_cmp encoded as ite(a==b, 1u8, 0u8) (Part of #3470)");

        if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
            let out_sort = dest_var.sort();
            let constraint = ctx.make_coerced_eq_constraint(
                &dest_var,
                result,
                out_sort,
                dest_local,
                "codegen_ptr_guaranteed_cmp",
            );
            let new_output_args = ctx.build_output_args(modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(
                from_app,
                target,
                &new_output_args,
                stmt_constraints,
                constraint,
            );
        } else {
            emit_sound_fallback_goto(
                ctx,
                from_app,
                target,
                modified_locals,
                &[dest_local],
                stmt_constraints,
            );
        }
        return;
    }

    debug!("CHC: ptr_guaranteed_cmp fallback — args not translatable");
    emit_sound_fallback_goto(
        ctx,
        from_app,
        target,
        modified_locals,
        &[dest_local],
        stmt_constraints,
    );
}

/// Handle `offset_from_unsigned::runtime_ptr_ge(self, origin) -> bool`.
///
/// Part of #3783: Internal runtime check within `offset_from_unsigned` that
/// verifies `self >= origin`. Encodes as BV unsigned >= comparison on pointer
/// values.
pub(in crate::codegen_ay::chc) fn codegen_runtime_ptr_ge(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;

    let result = (|| -> Option<Expr> {
        let lhs = ctx.translate_operand_with_modified(dcx.args.first()?, dcx.modified_locals)?;
        let rhs = ctx.translate_operand_with_modified(dcx.args.get(1)?, dcx.modified_locals)?;
        if lhs.sort() != rhs.sort() {
            return None;
        }
        Some(Expr::ite(lhs.bvuge(rhs), Expr::bitvec_const(1u128, 8), Expr::bitvec_const(0u128, 8)))
    })();

    if let Some(result_expr) = result {
        if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
            let out_sort = dest_var.sort();
            if let Some(eq) = ctx.make_coerced_eq_constraint(
                &dest_var,
                result_expr,
                out_sort,
                dest_local,
                "codegen_runtime_ptr_ge",
            ) {
                let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
                ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, [eq]);
                debug!("CHC: runtime_ptr_ge encoded as bvuge (#3783)");
                return;
            }
        }
    }

    debug!("CHC: runtime_ptr_ge fallback — unconstrained");
    emit_sound_fallback_goto(
        ctx,
        dcx.from_app,
        target,
        dcx.modified_locals,
        &[dest_local],
        dcx.stmt_constraints,
    );
}

/// Handle intrinsics that produce a constant boolean value.
pub(in crate::codegen_ay::chc) fn codegen_bool_const_intrinsic(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    value: bool,
    label: &'static str,
) {
    let dest_local = dcx.destination.local;
    let Some((_, dest_var)) = ctx.resolve_destination(dest_local) else {
        emit_sound_fallback_goto(
            ctx,
            dcx.from_app,
            target,
            dcx.modified_locals,
            &[dest_local],
            dcx.stmt_constraints,
        );
        return;
    };
    let Some(eq) = ctx.make_coerced_eq_constraint(
        &dest_var,
        Expr::bool_const(value),
        dest_var.sort(),
        dest_local,
        label,
    ) else {
        emit_sound_fallback_goto(
            ctx,
            dcx.from_app,
            target,
            dcx.modified_locals,
            &[dest_local],
            dcx.stmt_constraints,
        );
        return;
    };
    let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
    ctx.emit_goto_rule_extra(dcx.from_app, target, &out, dcx.stmt_constraints, [eq]);
}

fn extract_pointee_size(ctx: &ChcCtx<'_, '_>, operand: &Operand) -> Option<usize> {
    let ty = match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            ctx.body.locals().get(place.local).map(|local| local.ty)?
        }
        Operand::Constant(constant) => constant.ty(),
    };

    match ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(pointee_ty, _)) => LayoutOf::new(pointee_ty).size_of(),
        _ => None,
    }
}
