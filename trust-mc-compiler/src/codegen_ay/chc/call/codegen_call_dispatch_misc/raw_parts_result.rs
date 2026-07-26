// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Raw-pointer `to_raw_parts()` result construction, `NonNull::from_raw_parts`
//! reassembly, and flattened-destination emission.
//! Extracted from codegen_call_dispatch_misc (Part of #4010, #4153).

use std::borrow::Cow;

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::super::codegen_rules::CodegenRules;
use super::super::dyn_coercion::extract_pointer_expr;
use super::super::{ChcCtx, RelationApp};
use super::raw_parts_ref_target::propagate_nonnull_from_raw_parts_identity;
use crate::codegen_ay::names::{self, struct_sort};
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(super) fn raw_ptr_to_raw_parts_metadata_expr(
        &mut self,
        arg: &Operand,
        dest_local: usize,
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<Expr> {
        let dest_ty = self.body.locals()[dest_local].ty;
        let TyKind::RigidTy(RigidTy::Tuple(fields)) = dest_ty.kind() else {
            return None;
        };
        let metadata_ty = *fields.get(1)?;
        match metadata_ty.kind() {
            TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty() => Some(Expr::bool_const(true)),
            _ => self.translate_ptr_metadata(arg, modified_locals),
        }
    }

    pub(super) fn build_tuple_result_expr(&mut self, field_exprs: Vec<Expr>) -> Option<Expr> {
        if field_exprs.is_empty() {
            return Some(Expr::bool_const(true));
        }
        if field_exprs.len() == 1 {
            return field_exprs.into_iter().next();
        }

        let fields: Vec<(Cow<'static, str>, ay_bindings::Sort)> = field_exprs
            .iter()
            .enumerate()
            .map(|(idx, expr)| (names::tuple_field_name(idx), expr.sort().clone()))
            .collect();
        let tuple_sort_name = Self::tuple_sort_name(&fields);
        let tuple_sort = struct_sort(&tuple_sort_name, fields);
        self.declare_datatype_sort_if_needed(&tuple_sort);
        let cons_name = names::resolve_ctor_name(&tuple_sort, &tuple_sort_name);
        Some(Expr::datatype_constructor(tuple_sort_name, cons_name, field_exprs, tuple_sort))
    }

    pub(super) fn try_emit_raw_ptr_to_raw_parts_flattened_destination(
        &mut self,
        dest_local: usize,
        data_expr: Expr,
        metadata_expr: Expr,
        from_app: &RelationApp,
        target: rustc_public::mir::BasicBlockIdx,
        stmt_constraints: &[Expr],
        modified_locals: &std::collections::HashSet<usize>,
    ) -> bool {
        if !self.flatten.flattened_tuple_locals.contains(&dest_local)
            || self.flattened_field_count(dest_local) < 2
        {
            return false;
        }

        let Some(vec_idx) = self.try_state_idx_for_local(dest_local) else {
            return false;
        };
        let mut constraints = Vec::new();

        for (field_idx, value) in [(0, data_expr), (1, metadata_expr)] {
            let Some((out_name, out_sort)) =
                self.state_var_mgr.output_state_vars.get(vec_idx + field_idx).cloned()
            else {
                return false;
            };
            let Some(coerced) = Self::coerce_flatten_slot_value(&out_sort, value) else {
                return false;
            };
            let out_var = Expr::var(&*out_name, out_sort);
            self.encode.flattened_field_env.insert((dest_local, field_idx), coerced.clone());
            constraints.push(out_var.eq(coerced));
        }

        let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(
            from_app,
            target,
            &new_output_args,
            stmt_constraints,
            constraints,
        );
        true
    }

    pub(super) fn codegen_raw_ptr_to_raw_parts_call(&mut self, dcx: &DispatchCallContext<'_>) {
        let DispatchCallContext {
            func,
            args,
            destination,
            target,
            from_app,
            stmt_constraints,
            bb_idx,
            modified_locals,
            ..
        } = dcx;

        let Some(target) = target else {
            self.record_diverging_call_drop(func, Some(*bb_idx), "misc::ptr_to_raw_parts", None);
            return;
        };

        let dest_local = destination.local;
        let Some(arg) = args.first() else {
            emit_sound_fallback_goto(
                self,
                from_app,
                *target,
                modified_locals,
                &[dest_local],
                stmt_constraints,
            );
            return;
        };

        let raw_expr = self
            .resolve_ref_operand(arg, modified_locals)
            .or_else(|| self.translate_operand_with_modified(arg, modified_locals));
        let Some(data_expr) = raw_expr.as_ref().and_then(extract_pointer_expr) else {
            emit_sound_fallback_goto(
                self,
                from_app,
                *target,
                modified_locals,
                &[dest_local],
                stmt_constraints,
            );
            return;
        };
        let Some(metadata_expr) =
            self.raw_ptr_to_raw_parts_metadata_expr(arg, dest_local, modified_locals)
        else {
            emit_sound_fallback_goto(
                self,
                from_app,
                *target,
                modified_locals,
                &[dest_local],
                stmt_constraints,
            );
            return;
        };

        if self.try_emit_raw_ptr_to_raw_parts_flattened_destination(
            dest_local,
            data_expr.clone(),
            metadata_expr.clone(),
            from_app,
            *target,
            stmt_constraints,
            modified_locals,
        ) {
            return;
        }

        let result_expr = self.build_tuple_result_expr(vec![data_expr, metadata_expr]);

        let Some(result_expr) = result_expr else {
            emit_sound_fallback_goto(
                self,
                from_app,
                *target,
                modified_locals,
                &[dest_local],
                stmt_constraints,
            );
            return;
        };

        let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
        if let Some(flat_constraints) =
            self.build_flattened_destination_constraints(dest_local, result_expr.clone())
        {
            self.emit_goto_rule_extra(
                from_app,
                *target,
                &new_output_args,
                stmt_constraints,
                flat_constraints,
            );
            return;
        }

        if let Some((_, dest_var)) = self.resolve_destination(dest_local)
            && let Some(eq) = self.make_coerced_eq_constraint(
                &dest_var,
                result_expr,
                dest_var.sort(),
                dest_local,
                "misc::ptr_to_raw_parts",
            )
        {
            self.emit_goto_rule_extra(from_app, *target, &new_output_args, stmt_constraints, [eq]);
            return;
        }

        emit_sound_fallback_goto(
            self,
            from_app,
            *target,
            modified_locals,
            &[dest_local],
            stmt_constraints,
        );
    }

    /// Part of #4153: `NonNull::from_raw_parts(data_ptr, metadata)` — reassemble
    /// a wide `NonNull<dyn Trait>` from a thin pointer and explicit metadata.
    ///
    /// This is the inverse of `to_raw_parts()`. The call has two arguments:
    /// - arg 0: thin `NonNull<()>` data pointer (BV64)
    /// - arg 1: dyn-trait metadata / vtable discriminant (BV64)
    ///
    /// `NonNull<dyn Trait>` is usually represented in CHC as a BV64 data
    /// pointer plus a vtable side state var. Only destinations that are actually
    /// pointer-pair-wide should receive `vtable[127:64] ++ data_ptr[63:0]`.
    pub(super) fn codegen_nonnull_from_raw_parts_call(&mut self, dcx: &DispatchCallContext<'_>) {
        let DispatchCallContext {
            func,
            args,
            destination,
            target,
            from_app,
            stmt_constraints,
            bb_idx,
            modified_locals,
            ..
        } = dcx;

        let Some(target) = target else {
            self.record_diverging_call_drop(
                func,
                Some(*bb_idx),
                "misc::nonnull_from_raw_parts",
                None,
            );
            return;
        };

        let dest_local = destination.local;

        // Resolve arg 0: thin data pointer.
        let data_expr = args.first().and_then(|arg| {
            self.translate_operand_with_modified(arg, modified_locals)
                .or_else(|| self.resolve_ref_operand(arg, modified_locals))
        });

        // Resolve arg 1: metadata (vtable discriminant for dyn traits).
        let metadata_expr = args.get(1).and_then(|arg| {
            self.translate_operand_with_modified(arg, modified_locals)
                .or_else(|| self.resolve_ref_operand(arg, modified_locals))
        });

        let (Some(data_expr), Some(metadata_expr)) = (data_expr, metadata_expr) else {
            debug!(
                fn_name = %self.fn_name,
                "nonnull_from_raw_parts: could not resolve data/metadata args"
            );
            emit_sound_fallback_goto(
                self,
                from_app,
                *target,
                modified_locals,
                &[dest_local],
                stmt_constraints,
            );
            return;
        };

        // Extract the thin pointer BV from the data argument. The operand
        // may be a NonNull<()> wrapper — extract_pointer_expr peels it.
        let thin_ptr = extract_pointer_expr(&data_expr).unwrap_or(data_expr);

        let src_local = args.first().and_then(|arg| match arg {
            rustc_public::mir::Operand::Copy(p) | rustc_public::mir::Operand::Move(p)
                if p.projection.is_empty() =>
            {
                Some(p.local)
            }
            _ => None,
        });
        propagate_nonnull_from_raw_parts_identity(self, dest_local, src_local, &thin_ptr);

        // Coerce both halves to POINTER_WIDTH before concatenation.
        let thin_ptr = coerce_bitvec_width_safe(thin_ptr, POINTER_WIDTH, SignExtension::ZeroExtend);
        let vtable_bv = coerce_bitvec_width_safe(
            metadata_expr.clone(),
            POINTER_WIDTH,
            SignExtension::ZeroExtend,
        );

        // Propagate vtable side channel for downstream dyn dispatch.
        let vtable_constraint = self.capture_known_vtable_constraint(dest_local, metadata_expr);

        if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
            let dest_sort = dest_var.sort().clone();
            let result_expr =
                if dest_sort.is_bitvec() && dest_sort.bitvec_width() == Some(POINTER_WIDTH) {
                    thin_ptr
                } else {
                    vtable_bv.concat(thin_ptr)
                };
            if let Some(eq) = self.make_coerced_eq_constraint(
                &dest_var,
                result_expr,
                &dest_sort,
                dest_local,
                "misc::nonnull_from_raw_parts",
            ) {
                let mut extra: Vec<Expr> = vec![eq];
                if let Some(vc) = vtable_constraint {
                    extra.push(vc);
                }
                let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
                self.emit_goto_rule_extra(
                    from_app,
                    *target,
                    &new_output_args,
                    stmt_constraints,
                    extra,
                );
                return;
            }
        }

        // Fail closed: destination unresolvable.
        self.clear_known_vtable_discriminant(dest_local);
        self.known_alloc_ids.remove(&dest_local);
        self.ref_resolution.ref_targets.remove(&dest_local);
        self.ref_resolution.call_forwarded_raw_ptrs.remove(&dest_local);
        debug!(
            fn_name = %self.fn_name,
            "nonnull_from_raw_parts: coercion failed; emitting sound fallback"
        );
        emit_sound_fallback_goto(
            self,
            from_app,
            *target,
            modified_locals,
            &[dest_local],
            stmt_constraints,
        );
    }
}
