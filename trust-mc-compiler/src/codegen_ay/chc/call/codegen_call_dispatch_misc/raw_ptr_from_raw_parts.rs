// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Raw `ptr::from_raw_parts(data, metadata)` reconstruction for slice/str/dyn raw pointers.
//! Extracted from raw_parts_result.rs to keep misc dispatch helpers under size limits.
//! Part of #4187.

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::{Operand, ProjectionElem, TerminatorKind};
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind, UintTy};
use tracing::debug;

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_call_coerce::emit_sound_fallback_goto;
use super::super::codegen_call_ptr_identity::trace_pointer_identity_ref_target;
use super::super::codegen_ctx::types::RefTarget;
use super::super::codegen_rules::CodegenRules;
use super::super::dyn_coercion::extract_pointer_expr;
use crate::codegen_ay::names::{self, struct_sort};
use crate::codegen_ay::provenance::Loc;
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe, ptr_sort};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn clear_raw_ptr_from_raw_parts_metadata(&mut self, dest_local: usize) {
        self.ref_resolution.const_ref_values.remove(&dest_local);
        self.ref_resolution.const_ref_slice_views.remove(&dest_local);
        self.ref_resolution.subslice_len.remove(&dest_local);
        self.ref_resolution.subslice_offset.remove(&dest_local);
    }

    fn raw_ptr_from_raw_parts_source_local(
        &self,
        src_local: Option<usize>,
        ptr_expr: &Expr,
    ) -> Option<usize> {
        let resolved_src = src_local.map(|local| self.resolve_provenance_local(local));
        let expr_source = ChcCtx::try_extract_obj_id(ptr_expr)
            .and_then(|obj_id| self.heap_state.local_idx_for_obj_id(obj_id));

        match resolved_src {
            Some(local)
                if self.ref_resolution.const_ref_values.contains_key(&local)
                    || self.ref_resolution.const_ref_slice_views.contains_key(&local)
                    || self.ref_resolution.ref_targets.contains_key(&local) =>
            {
                Some(local)
            }
            _ => expr_source.or(resolved_src),
        }
    }

    fn raw_ptr_from_raw_parts_ref_target(
        &self,
        src_local: Option<usize>,
        ptr_expr: &Expr,
    ) -> Option<RefTarget> {
        src_local
            .and_then(|local| self.ref_resolution.ref_targets.get(&local).cloned())
            .or_else(|| src_local.and_then(|local| trace_pointer_identity_ref_target(self, local)))
            .or_else(|| {
                self.raw_ptr_from_raw_parts_source_local(src_local, ptr_expr)
                    .and_then(|local| self.ref_resolution.ref_targets.get(&local).cloned())
            })
    }

    fn raw_ptr_from_raw_parts_projection_offset(
        &mut self,
        ref_target: &RefTarget,
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<Expr> {
        let mut offset = Expr::bitvec_const(0u64, POINTER_WIDTH);
        for projection in &ref_target.projections {
            match projection {
                ProjectionElem::ConstantIndex { offset: idx, min_length, from_end } => {
                    // #from_end needs the slice's runtime length -> fail closed (projection_path.rs)
                    let Some(actual) =
                        super::super::constant_index_offset(*idx, *min_length, *from_end)
                    else {
                        return None;
                    };
                    offset = offset.bvadd(Expr::bitvec_const(actual as u128, POINTER_WIDTH));
                }
                ProjectionElem::Index(index_local) => {
                    let idx = self.resolve_local_expr(*index_local, modified_locals)?;
                    let idx =
                        coerce_bitvec_width_safe(idx, POINTER_WIDTH, SignExtension::ZeroExtend);
                    offset = offset.bvadd(idx);
                }
                ProjectionElem::Deref => {}
                _ => return None,
            }
        }
        Some(offset)
    }

    fn raw_ptr_from_raw_parts_pointer_byte_offset(
        &mut self,
        source_local: usize,
        ptr_expr: &Expr,
    ) -> Option<Expr> {
        let byte_offset = Self::try_extract_constant_addr(ptr_expr)
            .map(|(_, offset)| offset as usize)
            .or_else(|| Self::raw_ptr_pointer_constant_byte_delta(ptr_expr))?;
        let source_ty = self.resolve_body_ty(self.body.locals()[source_local].ty);
        let elem_ty = self.get_array_element_ty(source_ty)?;
        let elem_size = self.get_type_size(elem_ty)?;
        if elem_size == 0 || byte_offset % elem_size != 0 {
            return None;
        }
        Some(Expr::bitvec_const((byte_offset / elem_size) as u128, POINTER_WIDTH))
    }

    fn raw_ptr_pointer_constant_byte_delta(ptr_expr: &Expr) -> Option<usize> {
        match ptr_expr.value() {
            ExprValue::BvConcat(_, low) => Self::raw_ptr_bvadd_constant_delta(low),
            ExprValue::BvExtract { expr: inner, high: 63, low: 0 } => {
                Self::raw_ptr_pointer_constant_byte_delta(inner)
            }
            _ => Self::raw_ptr_bvadd_constant_delta(ptr_expr),
        }
    }

    fn raw_ptr_bvadd_constant_delta(expr: &Expr) -> Option<usize> {
        let ExprValue::BvAdd(lhs, rhs) = expr.value() else {
            return None;
        };
        Self::const_usize_after_eval(rhs).or_else(|| Self::const_usize_after_eval(lhs))
    }

    fn const_usize_after_eval(expr: &Expr) -> Option<usize> {
        Self::const_usize_from_expr(expr).or_else(|| {
            trust_mc_core::chc_const_prop::eval::try_eval_to_const(expr)
                .and_then(|folded| Self::const_usize_from_expr(&folded))
        })
    }

    fn raw_ptr_pointer_add_element_delta_for_local(
        &mut self,
        local: usize,
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<usize> {
        let mut count_operand = None;
        for block in &self.body.blocks {
            let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
            else {
                continue;
            };
            if destination.local != local || !destination.projection.is_empty() {
                continue;
            }
            let callee =
                self.resolve_callee_path(func).or_else(|| self.resolve_fn_def_name(func))?;
            if !(callee.contains("::add") || callee.ends_with("::offset")) {
                continue;
            }
            count_operand = args.get(1).cloned();
            break;
        }

        let delta_expr = self.translate_operand_with_modified(&count_operand?, modified_locals)?;
        Self::const_usize_from_expr(&delta_expr)
    }

    fn propagate_raw_ptr_from_raw_parts_identity(
        &mut self,
        dest_local: usize,
        src_local: Option<usize>,
        ptr_expr: &Expr,
    ) {
        let source_local = self.raw_ptr_from_raw_parts_source_local(src_local, ptr_expr);

        if let Some(obj_id) = source_local
            .and_then(|sl| self.known_alloc_ids.get(&sl).copied())
            .or_else(|| source_local.and_then(|sl| self.trace_deref_store_alloc_id(sl)))
            .or_else(|| src_local.and_then(|sl| self.known_alloc_ids.get(&sl).copied()))
            .or_else(|| src_local.and_then(|sl| self.trace_deref_store_alloc_id(sl)))
        {
            self.known_alloc_ids.insert(dest_local, obj_id);
        } else {
            self.known_alloc_ids.remove(&dest_local);
        }

        let ref_target = source_local
            .and_then(|sl| self.ref_resolution.ref_targets.get(&sl).cloned())
            .or_else(|| source_local.and_then(|sl| trace_pointer_identity_ref_target(self, sl)))
            .or_else(|| src_local.and_then(|sl| self.ref_resolution.ref_targets.get(&sl).cloned()))
            .or_else(|| src_local.and_then(|sl| trace_pointer_identity_ref_target(self, sl)))
            .or_else(|| {
                ChcCtx::try_extract_obj_id(ptr_expr).and_then(|obj_id| {
                    self.heap_state
                        .local_idx_for_obj_id(obj_id)
                        .map(|local| RefTarget::with_projections(local, vec![]))
                })
            });
        if let Some(ref_target) = ref_target {
            debug!(
                dest = dest_local,
                src = ?src_local,
                target = ref_target.local,
                "raw_ptr_from_raw_parts: propagated ref_target"
            );
            self.ref_resolution.ref_targets.insert(dest_local, ref_target);
            self.ref_resolution.call_forwarded_raw_ptrs.insert(dest_local);
        } else {
            debug!(
                dest = dest_local,
                src = ?src_local,
                "raw_ptr_from_raw_parts: no ref_target propagated"
            );
            self.ref_resolution.ref_targets.remove(&dest_local);
            self.ref_resolution.call_forwarded_raw_ptrs.remove(&dest_local);
        }
    }

    fn propagate_raw_ptr_from_raw_parts_backing(
        &mut self,
        dest_local: usize,
        src_local: Option<usize>,
        ptr_expr: &Expr,
        modified_locals: &std::collections::HashSet<usize>,
    ) {
        let projected_ref_target = self.raw_ptr_from_raw_parts_ref_target(src_local, ptr_expr);
        if let Some(offset) =
            src_local.and_then(|local| self.ref_resolution.subslice_offset.get(&local).cloned())
            && !Self::is_zero_pointer_width_bitvec(&offset)
        {
            self.ref_resolution.subslice_offset.insert(dest_local, offset);
        } else if let Some(ref_target) = projected_ref_target.as_ref()
            && !ref_target.projections.is_empty()
            && let Some(offset) =
                self.raw_ptr_from_raw_parts_projection_offset(ref_target, modified_locals)
        {
            self.ref_resolution.subslice_offset.insert(dest_local, offset);
        } else if let Some(src_local) = src_local
            && let Some(delta) =
                self.raw_ptr_pointer_add_element_delta_for_local(src_local, modified_locals)
        {
            self.ref_resolution
                .subslice_offset
                .insert(dest_local, Expr::bitvec_const(delta as u128, POINTER_WIDTH));
        }

        let Some(source_local) = projected_ref_target
            .as_ref()
            .map(|target| target.local)
            .or_else(|| self.raw_ptr_from_raw_parts_source_local(src_local, ptr_expr))
        else {
            self.ref_resolution.const_ref_values.remove(&dest_local);
            self.ref_resolution.const_ref_slice_views.remove(&dest_local);
            return;
        };

        if !self.ref_resolution.subslice_offset.contains_key(&dest_local)
            && let Some(offset) =
                self.raw_ptr_from_raw_parts_pointer_byte_offset(source_local, ptr_expr)
            && !Self::is_zero_pointer_width_bitvec(&offset)
        {
            self.ref_resolution.subslice_offset.insert(dest_local, offset);
        }

        let Some(data_expr) = self.ref_resolution.const_ref_values.get(&source_local).cloned()
        else {
            self.ref_resolution.const_ref_values.remove(&dest_local);
            self.ref_resolution.const_ref_slice_views.remove(&dest_local);
            return;
        };
        self.ref_resolution.const_ref_values.insert(dest_local, data_expr.clone());

        if let Some(slice_view) =
            self.ref_resolution.const_ref_slice_views.get(&source_local).cloned()
        {
            self.ref_resolution.const_ref_slice_views.insert(dest_local, slice_view);
            return;
        }

        let Some(len_expr) = self.ref_resolution.subslice_len.get(&dest_local).cloned() else {
            self.ref_resolution.const_ref_slice_views.remove(&dest_local);
            return;
        };
        let Some(array_sort) = data_expr.sort().array_sort() else {
            self.ref_resolution.const_ref_slice_views.remove(&dest_local);
            return;
        };

        let elem_sort = array_sort.element_sort.clone();
        let slice_name = names::slice_sort_name(&names::sort_short_name(&elem_sort));
        let ctor_name = names::cons_name(&slice_name);
        let slice_sort = struct_sort(
            slice_name.clone(),
            [
                ("fld_ptr", ptr_sort()),
                ("fld_len", ptr_sort()),
                ("fld_data", data_expr.sort().clone()),
            ],
        );
        let slice_view = Expr::datatype_constructor(
            slice_name,
            ctor_name,
            vec![ptr_expr.clone(), len_expr, data_expr],
            slice_sort,
        );
        self.ref_resolution.const_ref_slice_views.insert(dest_local, slice_view);
    }

    fn seed_raw_ptr_from_raw_parts_metadata(
        &mut self,
        dest_local: usize,
        src_local: Option<usize>,
        ptr_expr: &Expr,
        metadata_operand: &Operand,
        metadata_expr: &Expr,
        modified_locals: &std::collections::HashSet<usize>,
    ) {
        self.clear_raw_ptr_from_raw_parts_metadata(dest_local);

        if let Some(offset) =
            src_local.and_then(|local| self.ref_resolution.subslice_offset.get(&local).cloned())
            && !Self::is_zero_pointer_width_bitvec(&offset)
        {
            self.ref_resolution.subslice_offset.insert(dest_local, offset);
        } else if let Some(ref_target) = self.raw_ptr_from_raw_parts_ref_target(src_local, ptr_expr)
            && !ref_target.projections.is_empty()
            && let Some(offset) =
                self.raw_ptr_from_raw_parts_projection_offset(&ref_target, modified_locals)
        {
            self.ref_resolution.subslice_offset.insert(dest_local, offset);
        } else if let Some(src_local) = src_local
            && let Some(delta) =
                self.raw_ptr_pointer_add_element_delta_for_local(src_local, modified_locals)
        {
            self.ref_resolution
                .subslice_offset
                .insert(dest_local, Expr::bitvec_const(delta as u128, POINTER_WIDTH));
        } else if let Some(source_local) =
            self.raw_ptr_from_raw_parts_source_local(src_local, ptr_expr)
            && let Some(offset) = self.ref_resolution.subslice_offset.get(&source_local).cloned()
        {
            self.ref_resolution.subslice_offset.insert(dest_local, offset);
        } else if let Some(source_local) =
            self.raw_ptr_from_raw_parts_source_local(src_local, ptr_expr)
            && let Some(offset) =
                self.raw_ptr_from_raw_parts_pointer_byte_offset(source_local, ptr_expr)
            && !Self::is_zero_pointer_width_bitvec(&offset)
        {
            self.ref_resolution.subslice_offset.insert(dest_local, offset);
        }

        let Ok(metadata_ty) = metadata_operand.ty(self.body.locals()) else {
            return;
        };
        if matches!(metadata_ty.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::Usize))) {
            let len = coerce_bitvec_width_safe(
                metadata_expr.clone(),
                POINTER_WIDTH,
                SignExtension::ZeroExtend,
            );
            self.ref_resolution.subslice_len.insert(dest_local, len);
            debug!(
                dest = dest_local,
                "raw_ptr_from_raw_parts: seeded subslice_len from metadata operand"
            );
        }
    }

    fn raw_ptr_from_raw_parts_state_value(
        &self,
        dest_sort: &Sort,
        data_expr: &Expr,
        metadata_operand: &Operand,
        metadata_expr: &Expr,
    ) -> Expr {
        let metadata_is_usize = metadata_operand
            .ty(self.body.locals())
            .is_ok_and(|ty| matches!(ty.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::Usize))));
        let dest_is_wide_bv = dest_sort.bitvec_width().is_some_and(|width| width > POINTER_WIDTH);

        if metadata_is_usize && dest_is_wide_bv {
            let metadata_bv = coerce_bitvec_width_safe(
                metadata_expr.clone(),
                POINTER_WIDTH,
                SignExtension::ZeroExtend,
            );
            let data_bv = coerce_bitvec_width_safe(
                data_expr.clone(),
                POINTER_WIDTH,
                SignExtension::ZeroExtend,
            );
            metadata_bv.concat(data_bv)
        } else {
            data_expr.clone()
        }
    }

    fn raw_ptr_from_raw_parts_dest_is_dyn(&mut self, dest_local: usize) -> bool {
        let dest_ty = self.resolve_body_ty(self.body.locals()[dest_local].ty);
        let pointee = match dest_ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
            | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => pointee,
            _ => return false,
        };
        let pointee = self.resolve_body_ty(pointee);
        super::super::dyn_coercion::find_dyn_trait_tail_ty(self, pointee).is_some()
    }

    fn raw_ptr_from_raw_parts_metadata_is_dyn(&self, metadata_operand: &Operand) -> bool {
        let metadata_ty = metadata_operand.ty(self.body.locals()).ok();
        metadata_ty.is_some_and(raw_parts_ty_mentions_dyn_trait)
    }

    /// Part of #4187: `ptr::from_raw_parts(data_ptr, metadata)` for slice/str/dyn
    /// raw pointers is modeled as the thin pointer value plus side-channel metadata
    /// on the destination local.
    pub(super) fn codegen_raw_ptr_from_raw_parts_call(&mut self, dcx: &DispatchCallContext<'_>) {
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
                "misc::raw_ptr_from_raw_parts",
                None,
            );
            return;
        };

        let dest_local = destination.local;
        let Some(metadata_operand) = args.get(1) else {
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

        let data_expr = args.first().and_then(|arg| {
            self.translate_operand_with_modified(arg, modified_locals)
                .or_else(|| self.resolve_ref_operand(arg, modified_locals))
                // `from_raw_parts` re-packs this half into the destination's
                // pointer DATUM, so the wave-11 tag ends at this crossing.
                .map(|expr| extract_pointer_expr(&expr).map(Loc::into_expr).unwrap_or(expr))
        });
        let metadata_expr = self
            .translate_operand_with_modified(metadata_operand, modified_locals)
            .or_else(|| self.resolve_ref_operand(metadata_operand, modified_locals));

        let (Some(data_expr), Some(metadata_expr)) = (data_expr, metadata_expr) else {
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

        let src_local = args.first().and_then(|arg| match arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        });
        self.seed_raw_ptr_from_raw_parts_metadata(
            dest_local,
            src_local,
            &data_expr,
            metadata_operand,
            &metadata_expr,
            modified_locals,
        );
        self.propagate_raw_ptr_from_raw_parts_identity(dest_local, src_local, &data_expr);
        self.propagate_raw_ptr_from_raw_parts_backing(
            dest_local,
            src_local,
            &data_expr,
            modified_locals,
        );

        if let Some((_, dest_var)) = self.resolve_destination(dest_local)
            && let Some(eq) = {
                let result_expr = self.raw_ptr_from_raw_parts_state_value(
                    dest_var.sort(),
                    &data_expr,
                    metadata_operand,
                    &metadata_expr,
                );
                self.make_coerced_eq_constraint(
                    &dest_var,
                    result_expr,
                    dest_var.sort(),
                    dest_local,
                    "misc::raw_ptr_from_raw_parts",
                )
            }
        {
            let mut extra = vec![eq];
            let dest_is_dyn = self.raw_ptr_from_raw_parts_dest_is_dyn(dest_local);
            let metadata_is_dyn = self.raw_ptr_from_raw_parts_metadata_is_dyn(metadata_operand);
            if (dest_is_dyn || metadata_is_dyn)
                && let Some(vc) =
                    self.capture_known_vtable_constraint(dest_local, metadata_expr.clone())
            {
                extra.push(vc);
            }
            let new_output_args = self.build_output_args(modified_locals, &[dest_local]);
            self.emit_goto_rule_extra(from_app, *target, &new_output_args, stmt_constraints, extra);
            return;
        }

        self.clear_raw_ptr_from_raw_parts_metadata(dest_local);
        self.known_alloc_ids.remove(&dest_local);
        self.ref_resolution.ref_targets.remove(&dest_local);
        self.ref_resolution.call_forwarded_raw_ptrs.remove(&dest_local);
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

fn raw_parts_ty_mentions_dyn_trait(ty: Ty) -> bool {
    if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
        return true;
    }

    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _))
        | TyKind::RigidTy(RigidTy::RawPtr(inner, _))
        | TyKind::RigidTy(RigidTy::Slice(inner))
        | TyKind::RigidTy(RigidTy::Array(inner, _)) => raw_parts_ty_mentions_dyn_trait(inner),
        TyKind::RigidTy(RigidTy::Adt(_, args)) => args.0.iter().any(|arg| match arg {
            GenericArgKind::Type(inner) => raw_parts_ty_mentions_dyn_trait(*inner),
            _ => false,
        }),
        TyKind::RigidTy(RigidTy::Tuple(fields)) => {
            fields.iter().any(|field| raw_parts_ty_mentions_dyn_trait(*field))
        }
        _ => false,
    }
}
