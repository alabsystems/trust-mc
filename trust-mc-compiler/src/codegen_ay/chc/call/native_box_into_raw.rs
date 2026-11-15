// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Release a native Box's ownership while retaining its checked allocation.

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_rules::CodegenRules;
use crate::codegen_ay::shared::mono_ty;
#[cfg(not(trust_toolchain))]
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Operand, Place, ProjectionElem};
use rustc_public::ty::{RigidTy, TyKind};

impl ChcCtx<'_, '_> {
    pub(in crate::codegen_ay::chc) fn try_native_box_into_raw(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) -> bool {
        let Ok(ty) = dcx.func.ty(self.body.locals()) else { return false };
        let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() else { return false };
        let Ok(instance) = Instance::resolve(def, &args) else { return false };
        let Some((input, output)) =
            crate::codegen_ay::shared::native_box_raw::native_box_into_raw_identity(
                self.tcx, &instance,
            )
        else {
            return false;
        };
        let Some(target) = *dcx.target else {
            self.record_sound_fallback_reason("native_box_into_raw_without_custody");
            return false;
        };
        let checked = (|| {
            if self.track_level != crate::args::ChcTrackLevel::Mem
                || !self.inline_walk_frames.is_empty()
                || crate::kani_middle::transform::unit_has_stubs()
                || self.native_box_uses_custom_allocator()
                || !dcx.destination.projection.is_empty()
            {
                return None;
            }
            let [Operand::Copy(owner) | Operand::Move(owner)] = dcx.args else { return None };
            if !owner.projection.is_empty()
                || owner.ty(self.body.locals()).ok()? != input
                || dcx.destination.ty(self.body.locals()).ok()? != output
            {
                return None;
            }
            let TyKind::RigidTy(RigidTy::Adt(def, args)) = input.kind() else { return None };
            let carrier = mono_ty::field_ty(def.variants().first()?.fields().first()?, &args)?;
            let operand = Operand::Copy(Place {
                local: owner.local,
                projection: vec![ProjectionElem::Field(0, carrier)],
            });
            // This resolver accepts only a unique, acyclic typed allocation
            // birth. Pointer bits or a forged Box::from_raw are not custody.
            let address = self.host_native_thin_box_address(&operand, output)?;
            let checked = self.checked_native_box_deref(carrier, output, address)?;
            let (allocation, offset) = Self::try_extract_constant_addr(&checked.value)?;
            if offset != 0 {
                return None;
            }
            let (_, destination) = self.resolve_destination(dcx.destination.local)?;
            if destination.sort() != checked.value.sort() {
                return None;
            }
            Some((checked, allocation, destination))
        })();
        let local = dcx.destination.local;
        if let Some((checked, allocation, destination)) = checked {
            let equality = destination.eq(checked.value);
            self.heap_state.pending_checks.extend(checked.checks);
            self.emit_alloc_pending_checks(dcx.from_app, dcx.stmt_constraints, dcx.bb_idx);
            if !self.local_has_multiple_whole_definitions(local) {
                self.record_alloc_dest(local, Some(allocation));
            } else {
                self.known_alloc_ids.remove(&local);
                self.ref_resolution.alloc_result_locals.remove(&local);
            }
            // Ownership release does not deallocate or modify the payload.
            let output = self.build_output_args(dcx.modified_locals, &[local]);
            self.emit_goto_rule_extra(
                dcx.from_app,
                target,
                &output,
                dcx.stmt_constraints,
                vec![equality],
            );
        } else {
            self.known_alloc_ids.remove(&local);
            self.ref_resolution.alloc_result_locals.remove(&local);
            self.record_sound_fallback_reason("native_box_into_raw_without_custody");
            emit_sound_fallback_goto(
                self,
                dcx.from_app,
                target,
                dcx.modified_locals,
                &[local],
                dcx.stmt_constraints,
            );
        }
        true
    }
}
