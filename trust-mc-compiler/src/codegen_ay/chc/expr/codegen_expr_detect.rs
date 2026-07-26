// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Kani API detection helpers for CHC codegen.
//!
//! Extracted from codegen_expr_assert.rs per R1:2316 code_structure audit.
//! Handles: detect_kani_hook, detect_kani_model, detect_kani_intrinsic.
//!
//! These functions resolve a MIR call operand to a Kani function marker
//! and classify it as a Hook, Model, or Intrinsic.

use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::mir::mono::Instance;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::kani_middle::attributes;
use crate::kani_middle::kani_functions::{
    KaniFunction, KaniHook, KaniIntrinsic, KaniModel, try_get_kani_function,
};

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Detects if a function call is to a Kani hook (assert, assume, etc.).
    ///
    /// Returns the KaniHook if detected, None otherwise.
    pub(in crate::codegen_ay::chc) fn detect_kani_hook(&self, func: &Operand) -> Option<KaniHook> {
        let (fn_def, fn_marker) = self.resolve_kani_marker(func)?;
        let fn_name = fn_def.name();
        debug!("detect_kani_hook: fn_name={}, fn_marker={:?}", fn_name, fn_marker);

        if let Some(KaniFunction::Hook(hook)) = try_get_kani_function(&fn_marker) {
            return Some(hook);
        }
        None
    }

    /// Detects if a function call is to a Kani model (Any, etc.).
    ///
    /// Part of #1889: kani::any() uses KaniModel::Any, not KaniHook::AnyRaw.
    /// Returns the KaniModel if detected, None otherwise.
    pub(in crate::codegen_ay::chc) fn detect_kani_model(
        &self,
        func: &Operand,
    ) -> Option<KaniModel> {
        let (fn_def, fn_marker) = self.resolve_kani_marker(func)?;
        let fn_name = fn_def.name();
        debug!("detect_kani_model: fn_name={}, fn_marker={:?}", fn_name, fn_marker);

        if let Some(KaniFunction::Model(model)) = try_get_kani_function(&fn_marker) {
            return Some(model);
        }
        None
    }

    /// Detects if a function call is to a Kani intrinsic (IsInitialized, ValidValue, etc.).
    ///
    /// Part of #1229: These intrinsics are normally transformed by IntrinsicGeneratorPass,
    /// but may appear as direct calls when the transformed body isn't inlined.
    pub(in crate::codegen_ay::chc) fn detect_kani_intrinsic(
        &self,
        func: &Operand,
    ) -> Option<KaniIntrinsic> {
        let (fn_def, fn_marker) = self.resolve_kani_marker(func)?;
        let _fn_name = fn_def.name();

        if let Some(KaniFunction::Intrinsic(intrinsic)) = try_get_kani_function(&fn_marker) {
            return Some(intrinsic);
        }
        None
    }

    /// Resolve a function operand to its FnDef and Kani marker string.
    ///
    /// Shared extraction of the resolve-instance-then-check-marker pattern
    /// common to all three detect_kani_* functions.
    fn resolve_kani_marker(&self, func: &Operand) -> Option<(rustc_public::ty::FnDef, String)> {
        let func_ty = func.ty(self.body.locals()).ok()?;
        let (fn_def, fn_args) = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
            _ => return None, // external enum: TyKind
        };

        let instance_opt = Instance::resolve(fn_def, &fn_args).ok();
        let fn_marker = instance_opt
            .as_ref()
            .and_then(|instance| attributes::fn_marker(instance.def))
            .or_else(|| attributes::fn_marker(fn_def))?;

        Some((fn_def, fn_marker))
    }
}
