// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The actual core MaybeUninit::write writes a whole T before returning &mut T.
//! Resolve that reference through a typed native Box borrow, never Box storage.

use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_rules::CodegenRules;
use super::codegen_types::CodegenTypes;
use super::{ChcCtx, chc_call_context::DispatchCallContext, native_init_handoff::NativeInitStore};
use crate::codegen_ay::provenance::Loc;
use rustc_public::mir::{Operand, mono::Instance};
use rustc_public::ty::{RigidTy, TyKind};

impl ChcCtx<'_, '_> {
    pub(in crate::codegen_ay::chc) fn try_native_maybe_uninit_write(
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
        let Some(native) = crate::codegen_ay::native_maybe_uninit_write(self.tcx, &instance) else {
            return false;
        };
        let ordinary_typed_call = matches!(dcx.args,[receiver,value]
            if matches!(receiver.ty(self.body.locals()).ok().map(|ty|ty.kind()),Some(TyKind::RigidTy(RigidTy::Ref(_,actual,rustc_public::mir::Mutability::Mut))) if actual==native.maybe)
            && value.ty(self.body.locals()).ok()==Some(native.payload)
            && matches!(dcx.destination.ty(self.body.locals()).ok().map(|ty|ty.kind()),Some(TyKind::RigidTy(RigidTy::Ref(_,actual,rustc_public::mir::Mutability::Mut))) if actual==native.payload)
            && !crate::codegen_ay::native_maybe_write_box_receiver(self.tcx,&self.body.blocks,self.body.locals(),receiver,native.maybe));
        if ordinary_typed_call {
            return false;
        }
        let Some(target) = *dcx.target else {
            return false;
        };
        let result = (|| {
            if self.track_level!=crate::args::ChcTrackLevel::Mem||!self.inline_walk_frames.is_empty()||crate::kani_middle::transform::unit_has_stubs()||!dcx.destination.projection.is_empty()||!self.initialized_payload_shape(native.payload)
                ||!crate::codegen_ay::shared::native_box_uninit::native_allocation_site_is_single_execution(self.body,dcx.bb_idx){return None;}
            let [receiver, value] = dcx.args else {
                return None;
            };
            let (Operand::Copy(receiver_place) | Operand::Move(receiver_place)) = receiver else {
                return None;
            };
            if !receiver_place.projection.is_empty()
                || !matches!(receiver.ty(self.body.locals()).ok()?.kind(),TyKind::RigidTy(RigidTy::Ref(_,actual,rustc_public::mir::Mutability::Mut)) if actual==native.maybe)
                || value.ty(self.body.locals()).ok()? != native.payload
                || !matches!(dcx.destination.ty(self.body.locals()).ok()?.kind(),TyKind::RigidTy(RigidTy::Ref(_,actual,rustc_public::mir::Mutability::Mut)) if actual==native.payload)
                || self.local_has_multiple_whole_definitions(dcx.destination.local)
            {
                return None;
            }
            let owner = self.native_init_pointer_owner(receiver_place.local)?;
            let (address, maybe, payload) = self.native_init_owned_address(&owner)?;
            if maybe != native.maybe
                || payload != native.payload
                || !self.native_init_pointer_is_closed(receiver_place.local, None, &address)
            {
                return None;
            }
            let statement = self.body.blocks[dcx.bb_idx].statements.len();
            if !self.native_init_operand_is_defined_at(value, dcx.bb_idx, statement) {
                return None;
            }
            let value = self.translate_operand_with_modified(value, dcx.modified_locals)?;
            if Some(value.sort()) != Self::translate_ty(payload).as_ref() {
                return None;
            }
            let value = Self::native_init_event_value(&value, dcx.stmt_constraints)?;
            let (_, out) = self.resolve_destination(dcx.destination.local)?;
            if out.sort() != address.sort() {
                return None;
            }
            let Some((allocation, 0)) = Self::try_extract_constant_addr(&address) else {
                return None;
            };
            let mut extra = vec![out.eq(address.clone())];
            if self.uninit_checks
                && super::native_init_shadow::shadow_output_bound(dcx.stmt_constraints)
            {
                self.record_sound_fallback_reason("native_init_shadow_order_unmodeled");
                return None;
            }
            if !self.native_init_shadow_write(allocation, payload, &mut extra) {
                return None;
            }
            let before = self.heap_state.effect_mark();
            self.with_coherent_object_stores(|ctx| {
                if let Some(c) =
                    ctx.build_memory_store(Loc::of_address(address.clone()), value.clone(), payload)
                {
                    extra.push(c);
                }
                ctx.mirror_array_elements_to_flat_memory(&value, payload, &address, &mut extra);
            });
            if self.heap_state.effect_mark() == before {
                self.record_sound_fallback_reason("native_init_payload_store_effect_unmodeled");
                return None;
            }
            extra.append(&mut self.heap_state.drain_store_chains(&self.diagnostics));
            self.native_init_stores
                .insert(dcx.bb_idx, NativeInitStore { allocation, payload, address, statement });
            self.known_alloc_ids.insert(dcx.destination.local, allocation);
            Some(extra)
        })();
        if let Some(extra) = result {
            self.emit_alloc_pending_checks(dcx.from_app, dcx.stmt_constraints, dcx.bb_idx);
            let output = self.build_output_args(dcx.modified_locals, &[dcx.destination.local]);
            self.emit_goto_rule_extra(dcx.from_app, target, &output, dcx.stmt_constraints, extra);
        } else {
            self.record_sound_fallback_reason("native_maybe_write_without_custody_or_valid_value");
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
