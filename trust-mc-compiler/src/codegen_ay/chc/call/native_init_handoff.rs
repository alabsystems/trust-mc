// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Checked ownership transfer at the native unsafe initialization boundaries.
//! A certificate is made by a real whole-payload write, not by the helper's
//! unsafe precondition or a later reconstruction of its source locals.

use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_call_vec_ops::ProjectedVecState;
use super::codegen_rules::CodegenRules;
use super::codegen_types::CodegenTypes;
use super::native_init_custody::scalar;
use super::{ChcCtx, chc_call_context::DispatchCallContext};
use crate::codegen_ay::chc::stmt::stmt_accumulator::StmtAccumulator;
use crate::codegen_ay::provenance::Loc;
use crate::codegen_ay::shared::{
    mono_ty,
    native_box_init::{NativeInitKind, native_init_boundary},
};
use crate::kani_middle::abi::LayoutOf;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Operand, Place, ProjectionElem, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use rustc_public::{CrateDef, rustc_internal};
use std::collections::HashMap;

#[derive(Clone)]
pub(in crate::codegen_ay::chc) struct NativeInitStore {
    pub(super) allocation: u32,
    pub(super) payload: Ty,
    pub(super) address: Expr,
    pub(super) statement: usize,
}

impl ChcCtx<'_, '_> {
    pub(super) fn initialized_payload_shape(&self, ty: Ty) -> bool {
        scalar(ty)
            || matches!(ty.kind(),TyKind::RigidTy(RigidTy::Array(elem,n)) if scalar(elem) && n.eval_target_usize().is_ok_and(|n|n>0&&n<=64))
    }

    pub(super) fn native_init_event_value(value: &Expr, constraints: &[Expr]) -> Option<Expr> {
        use crate::codegen_ay::chc::expr::codegen_expr_box_deref::freeze_outputs;
        let mut definitions = HashMap::new();
        if constraints.len() > 16_384 {
            return None;
        }
        for constraint in constraints {
            if let ExprValue::Eq(lhs, rhs) = constraint.value()
                && let ExprValue::Var { name } = lhs.value()
                && name.ends_with("__out")
            {
                if definitions.get(name).is_some_and(|old| old != rhs) {
                    return None;
                }
                definitions.insert(name.clone(), rhs.clone());
            }
        }
        let mut value = value.clone();
        for _ in 0..32 {
            if !super::native_drop_memory::has_output_or_binder(&value) {
                return Some(value);
            }
            value = freeze_outputs(&value, &definitions)?;
        }
        None
    }

    /// Exact Box value, never the address of the Box's carrier storage.
    pub(super) fn native_init_owned_address(
        &mut self,
        boxed_place: &Place,
    ) -> Option<(Expr, Ty, Ty)> {
        if !boxed_place.projection.is_empty() || !self.inline_walk_frames.is_empty() {
            return None;
        }
        let boxed = self.normalized_box_ty(boxed_place.ty(self.body.locals()).ok()?)?;
        let native =
            crate::codegen_ay::shared::native_box_uninit::native_uninit_box(self.tcx, boxed)?;
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = boxed.kind() else {
            return None;
        };
        let carrier = mono_ty::field_ty(def.variants().first()?.fields().first()?, &args)?;
        let target =
            Ty::from_rigid_kind(RigidTy::RawPtr(native.maybe, rustc_public::mir::Mutability::Mut));
        let operand = Operand::Copy(Place {
            local: boxed_place.local,
            projection: vec![ProjectionElem::Field(0, carrier)],
        });
        let address = self.host_native_thin_box_address(&operand, target)?;
        let checked = self.checked_native_box_deallocation(carrier, target, address)?;
        self.heap_state.pending_checks.extend(checked.checks);
        Some((checked.value, native.maybe, native.payload))
    }

    pub(in crate::codegen_ay::chc) fn try_native_initialized_payload_store(
        &mut self,
        lhs: &Place,
        rhs: &Rvalue,
        value: &Expr,
        bb: usize,
        statement: usize,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        if self.track_level != crate::args::ChcTrackLevel::Mem
            || !self.inline_walk_frames.is_empty()
        {
            return false;
        }
        let Some(owner) = self.native_init_pointer_owner(lhs.local) else {
            return false;
        };
        let Some((address, maybe, payload)) = self.native_init_owned_address(&owner) else {
            return false;
        };
        let [
            ProjectionElem::Deref,
            ProjectionElem::Field(1, manually),
            ProjectionElem::Field(0, actual),
        ] = lhs.projection.as_slice()
        else {
            return false;
        };
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = manually.kind() else {
            return false;
        };
        if !self.native_init_rhs_is_defined_at(rhs, bb, statement) {
            // A later good overwrite cannot repair UB/unknown validity in an
            // earlier RHS evaluation. Retain the debt at this event itself.
            self.record_sound_fallback_reason("native_init_payload_source_validity_unmodeled");
            return false;
        }
        if Some(rustc_internal::internal(self.tcx, def.def_id()))
            != self.tcx.lang_items().manually_drop()
            || mono_ty::field_ty(def.variants()[0].fields().first().unwrap(), &args)
                != Some(payload)
            || *actual != payload
            || !self.initialized_payload_shape(payload)
            // The compiler represents a union's fields as Union(count): every
            // native field begins at zero. LayoutOf::field_offset intentionally
            // handles only Arbitrary fields and cannot answer this case.
            || !matches!(maybe.layout().ok().map(|layout|layout.shape().fields),Some(rustc_public::abi::FieldsShape::Union(count)) if count.get()==2)
            || LayoutOf::new(*manually).field_offset(0) != Some(0)
            || LayoutOf::new(*manually).size_of()!=LayoutOf::new(payload).size_of()
            || LayoutOf::new(*manually).align_of()!=LayoutOf::new(payload).align_of()
            || !self.native_init_pointer_is_closed(lhs.local, Some(lhs), &address)
            || Some(value.sort()) != Self::translate_ty(payload).as_ref()
        {
            return false;
        }
        let Some(value) = Self::native_init_event_value(value, acc.constraints) else {
            self.record_sound_fallback_reason("native_init_payload_value_snapshot_unmodeled");
            return false;
        };
        let Some((allocation, 0)) = Self::try_extract_constant_addr(&address) else {
            return false;
        };
        if !self.native_init_shadow_write(allocation, payload, acc.constraints) {
            return false;
        }
        let before = self.heap_state.effect_mark();
        self.with_coherent_object_stores(|ctx| {
            if let Some(c) =
                ctx.build_memory_store(Loc::of_address(address.clone()), value.clone(), payload)
            {
                acc.constraints.push(c);
            }
            ctx.mirror_array_elements_to_flat_memory(&value, payload, &address, acc.constraints);
        });
        if self.heap_state.effect_mark() == before {
            self.record_sound_fallback_reason("native_init_payload_store_effect_unmodeled");
            return false;
        }
        self.native_init_stores
            .insert(bb, NativeInitStore { allocation, payload, address, statement });
        true
    }

    pub(in crate::codegen_ay::chc) fn try_native_initialized_handoff(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) -> bool {
        let Ok(ty) = dcx.func.ty(self.body.locals()) else {
            return false;
        };
        let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() else {
            return false;
        };
        let Ok(instance) = Instance::resolve(def, &args) else {
            return false;
        };
        let Some(boundary) = native_init_boundary(self.tcx, &instance) else {
            return false;
        };
        let Some(target) = *dcx.target else {
            self.record_sound_fallback_reason("native_initialized_handoff_nonreturning_unmodeled");
            return false;
        };
        let result = (|| {
            if !self.inline_walk_frames.is_empty()
                || crate::kani_middle::transform::unit_has_stubs()
                || self.track_level != crate::args::ChcTrackLevel::Mem
                || !dcx.destination.projection.is_empty()
            {
                return None;
            }
            let [Operand::Copy(owner) | Operand::Move(owner)] = dcx.args else {
                return None;
            };
            if owner.ty(self.body.locals()).ok()? != boundary.input
                || dcx.destination.ty(self.body.locals()).ok()? != boundary.output
            {
                return None;
            }
            let (address, _, payload) = self.native_init_owned_address(owner)?;
            let (event, certificate) = self
                .native_init_stores
                .iter()
                .find(|(event, certificate)| {
                    certificate.payload == payload
                        && certificate.address == address
                        && self.native_init_event_dominates(**event, dcx.bb_idx)
                })
                .map(|(event, certificate)| (*event, certificate.clone()))?;
            if certificate.payload != payload
                || payload != boundary.payload
                || certificate.address != address
            {
                return None;
            }
            if !crate::codegen_ay::shared::native_box_uninit::native_allocation_site_is_single_execution(self.body,dcx.bb_idx){return None;}
            if event == dcx.bb_idx {
                for statement in
                    self.body.blocks[dcx.bb_idx].statements.iter().skip(certificate.statement + 1)
                {
                    if matches!(&statement.kind,StatementKind::Assign(lhs,_) if !lhs.projection.is_empty())
                    {
                        return None;
                    }
                    if matches!(&statement.kind, StatementKind::Intrinsic(_)) {
                        return None;
                    }
                }
            }
            let mut extra = Vec::new();
            let mut dests = vec![dcx.destination.local];
            match boundary.kind {
                NativeInitKind::VecArray => {
                    let TyKind::RigidTy(RigidTy::Array(element, n)) = payload.kind() else {
                        return None;
                    };
                    let n = n.eval_target_usize().ok()?;
                    if n == 0 || n > 64 || !scalar(element) {
                        return None;
                    }
                    let len = Expr::bitvec_const(n, 64);
                    let data = self.native_initialized_array_data(payload, &address)?;
                    let local = dcx.destination.local;
                    if let Some(name) = self.collections.len_state.get_len_var(local).cloned() {
                        self.collection_len_set(
                            &name,
                            len.clone(),
                            &mut super::call_accumulator::CallAccumulator::new(
                                &mut extra, &mut dests,
                            ),
                        );
                    }
                    if let Some(name) = self.collections.len_state.get_cap_var(local).cloned() {
                        self.collection_cap_set(
                            &name,
                            len.clone(),
                            &mut super::call_accumulator::CallAccumulator::new(
                                &mut extra, &mut dests,
                            ),
                        );
                    }
                    if self.collections.projection_locals.get(&local).copied()
                        == Some(super::codegen_ctx::types::CollectionProjectionKind::Vec)
                    {
                        if !self.constrain_projected_vec_fields_for_call(
                            local,
                            ProjectedVecState { ptr: address, len: len.clone(), cap: len, data },
                            &mut extra,
                            &mut dests,
                        ) {
                            return None;
                        }
                    } else {
                        let idx = self.try_state_idx_for_local(local)?;
                        let (name, sort) = self.state_var_mgr.output_state_vars.get(idx)?.clone();
                        let dt = sort.datatype_name()?;
                        extra.push(Self::build_vec_datatype_eq(
                            dt,
                            vec![address, len.clone(), len, data],
                            &name,
                            &sort,
                        ));
                    }
                }
                NativeInitKind::BoxSized => {
                    // The pointer changes its payload type, not its allocation.
                    // Downstream native Box origin transport is installed below.
                    let (_, out) = self.resolve_destination(dcx.destination.local)?;
                    if out.sort() != address.sort() {
                        return None;
                    }
                    extra.push(out.eq(address));
                    self.known_alloc_ids.insert(dcx.destination.local, certificate.allocation);
                }
                NativeInitKind::BoxSlice => return None,
            }
            Some((extra, dests, certificate.allocation))
        })();
        if let Some((extra, dests, allocation)) = result {
            self.native_init_stores.retain(|_, certificate| certificate.allocation != allocation);
            self.emit_alloc_pending_checks(dcx.from_app, dcx.stmt_constraints, dcx.bb_idx);
            let output = self.build_output_args(dcx.modified_locals, &dests);
            self.emit_goto_rule_extra(dcx.from_app, target, &output, dcx.stmt_constraints, extra);
        } else {
            self.record_sound_fallback_reason("native_initialized_handoff_without_custody");
            emit_sound_fallback_goto(
                self,
                dcx.from_app,
                target,
                dcx.modified_locals,
                &[dcx.destination.local],
                dcx.stmt_constraints,
            );
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn native_init_snapshot_refuses_conflicting_output_definitions() {
        let value = Expr::var("source__out", ay_bindings::Sort::bitvec(32));
        let one = value.clone().eq(Expr::bitvec_const(1u32, 32));
        let nine = value.clone().eq(Expr::bitvec_const(9u32, 32));
        assert_eq!(ChcCtx::native_init_event_value(&value, &[one.clone(), nine]), None);
        assert_eq!(
            ChcCtx::native_init_event_value(&value, &[one.clone(), one]),
            Some(Expr::bitvec_const(1u32, 32))
        );
    }
}
