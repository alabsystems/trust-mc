// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Reject MaybeUninit memory without an initializedness/ownership certificate.
//! A dead load or a later good store cannot excuse an earlier undefined read.

use super::ChcCtx;
use crate::callee_body::CalleeBody;
use crate::codegen_ay::shared::native_maybe_memory::{
    native_maybe_memory_constant, native_maybe_memory_type,
};
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::ty::{RigidTy, TyKind};

impl ChcCtx<'_, '_> {
    /// Book before a pure-call summary could discard an undefined prefix.
    /// Keep dispatching the user's actual body and all its effects afterward.
    pub(super) fn book_native_maybe_user_callee(
        &self,
        dcx: &super::chc_call_context::DispatchCallContext<'_>,
    ) {
        let Ok(ty) = dcx.func.ty(self.body.locals()) else {
            return;
        };
        let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() else {
            return;
        };
        if !def.krate().is_local {
            return;
        }
        let Ok(instance) = Instance::resolve(def, &args) else {
            return;
        };
        if matches!(instance.kind, rustc_public::mir::mono::InstanceKind::Virtual { .. }) {
            return;
        }
        if instance.callee_body().is_some_and(|body| {
            crate::codegen_ay::shared::native_maybe_memory::body_has_native_maybe_memory(
                self.tcx, &body,
            )
        }) {
            self.record_sound_fallback_reason(
                "native_maybe_callee_without_initializedness_provenance",
            );
        }
    }
    pub(in crate::codegen_ay::chc) fn book_unmodeled_native_maybe_memory(&self) {
        let unknown = self.body.locals().iter().enumerate().any(|(index, local)| {
            native_maybe_memory_type(self.tcx, self.resolve_body_ty(local.ty))
                && !self.native_init_authorized_locals.contains(&index)
        });
        if unknown || native_maybe_memory_constant(self.tcx, self.body) {
            self.record_sound_fallback_reason(
                "native_maybe_memory_without_initializedness_provenance",
            );
        }
    }
}
