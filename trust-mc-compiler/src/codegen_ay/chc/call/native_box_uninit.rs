// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native deferred-initialization allocation; payload initialization is separate.

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_rules::CodegenRules;
use crate::codegen_ay::stubs::StubKind;
use rustc_public::mir::mono::Instance;
use rustc_public::ty::{RigidTy, TyKind};

impl ChcCtx<'_, '_> {
    pub(in crate::codegen_ay::chc) fn try_native_box_new_uninit(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) -> bool {
        let Some(target) = *dcx.target else { return false };
        let Ok(ty) = dcx.func.ty(self.body.locals()) else { return false };
        let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() else { return false };
        let Ok(instance) = Instance::resolve(def, &args) else { return false };
        let Some(native) = crate::codegen_ay::native_box_new_uninit(self.tcx, &instance) else {
            return false;
        };
        if crate::codegen_ay::shared::native_box_uninit::native_box_new_uninit_site(
            self.tcx, self.body, dcx.bb_idx,
        )
        .is_none()
            || !self.inline_walk_frames.is_empty()
        {
            self.record_sound_fallback_reason("native_uninit_box_site_unmodeled");
            emit_sound_fallback_goto(
                self,
                dcx.from_app,
                target,
                dcx.modified_locals,
                &[dcx.destination.local],
                dcx.stmt_constraints,
            );
            return true;
        }
        let local = dcx.destination.local;
        let Some((_, destination)) = self.resolve_destination(local) else {
            self.record_sound_fallback_reason("native_uninit_box_destination_unmodeled");
            emit_sound_fallback_goto(
                self,
                dcx.from_app,
                target,
                dcx.modified_locals,
                &[local],
                dcx.stmt_constraints,
            );
            return true;
        };
        if destination.sort() != &crate::codegen_ay::types::ptr_sort() {
            self.record_sound_fallback_reason("native_uninit_box_destination_unmodeled");
            emit_sound_fallback_goto(
                self,
                dcx.from_app,
                target,
                dcx.modified_locals,
                &[local],
                dcx.stmt_constraints,
            );
            return true;
        }
        let Some(mut allocation) =
            self.translate_native_uninit_allocation(native.size, native.align, dcx.modified_locals)
        else {
            self.record_sound_fallback_reason("native_uninit_box_allocation_unresolved");
            emit_sound_fallback_goto(
                self,
                dcx.from_app,
                target,
                dcx.modified_locals,
                &[local],
                dcx.stmt_constraints,
            );
            return true;
        };
        let Some(value) = allocation.result.take() else {
            self.record_sound_fallback_reason("native_uninit_box_result_unmodeled");
            emit_sound_fallback_goto(
                self,
                dcx.from_app,
                target,
                dcx.modified_locals,
                &[local],
                dcx.stmt_constraints,
            );
            return true;
        };
        let equal = destination.eq(value.clone());
        if self.memory_safety_checks {
            for check in allocation.safety_checks {
                self.emit_error_rule_for_condition(
                    dcx.from_app,
                    check,
                    dcx.stmt_constraints,
                    dcx.bb_idx,
                );
            }
        }
        self.record_alloc_dest(local, allocation.alloc_obj_id);
        #[cfg(all(trust_toolchain, version("1.101")))]
        if let Some(locals) = self.native_uninit_allocation_custody(local, &value) {
            self.native_init_authorized_locals.extend(locals);
        } else {
            self.record_sound_fallback_reason("native_uninit_payload_protocol_unmodeled");
        }
        let mut extra = allocation.heap_constraints;
        extra.push(equal);
        self.append_alloc_shadow_constraints(
            StubKind::RustAlloc,
            allocation.alloc_obj_id,
            &mut extra,
        );
        self.emit_alloc_pending_checks(dcx.from_app, dcx.stmt_constraints, target);
        let output = self.build_output_args(dcx.modified_locals, &[local]);
        self.emit_goto_rule_extra(dcx.from_app, target, &output, dcx.stmt_constraints, extra);
        true
    }
}
