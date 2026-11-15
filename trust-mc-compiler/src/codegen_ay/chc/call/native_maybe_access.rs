// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Do not turn the unsafe MaybeUninit initializedness precondition into an
//! assumption by replaying its unchecked native body. These accessor/frame
//! certificates are separate from the supported Box/Vec ownership transfer.

use super::codegen_call_coerce::emit_sound_fallback_goto;
use super::{ChcCtx, chc_call_context::DispatchCallContext};
use rustc_public::mir::mono::Instance;
use rustc_public::ty::{RigidTy, TyKind};

impl ChcCtx<'_, '_> {
    pub(in crate::codegen_ay::chc) fn try_native_maybe_unsafe_access(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) -> bool {
        if !self.inline_walk_frames.is_empty() {
            return false;
        }
        let Ok(ty) = dcx.func.ty(self.body.locals()) else {
            return false;
        };
        let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() else {
            return false;
        };
        let Ok(instance) = Instance::resolve(def, &args) else {
            return false;
        };
        if !crate::codegen_ay::native_maybe_unsafe_accessor(self.tcx, &instance) {
            return false;
        }
        self.record_sound_fallback_reason(
            "native_maybe_unsafe_accessor_without_initialization_certificate",
        );
        let Some(target) = *dcx.target else {
            return false;
        };
        emit_sound_fallback_goto(
            self,
            dcx.from_app,
            target,
            dcx.modified_locals,
            &[dcx.destination.local],
            dcx.stmt_constraints,
        );
        true
    }
}
