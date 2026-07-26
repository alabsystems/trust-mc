// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR body traversal helpers for `block_on` / `block_on_with_spawn` dispatch.
//!
//! These are read-only helpers that resolve callee paths, instances, and
//! future/coroutine types from MIR bodies. Extracted from `codegen_call_block_on.rs`
//! to keep the main dispatch file under the 500-line limit.
//!
//! Part of #4075.

use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::mir::mono::Instance;
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, TyKind};

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn coroutine_body_for_future_ty(
        &self,
        ty: rustc_public::ty::Ty,
    ) -> Option<rustc_public::mir::Body> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Coroutine(def, _)) => def.body(),
            _ => None,
        }
    }

    pub(in crate::codegen_ay::chc) fn collect_spawn_future_tys(
        &self,
        body: &rustc_public::mir::Body,
    ) -> Vec<rustc_public::ty::Ty> {
        body.blocks
            .iter()
            .filter_map(|block| {
                let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                    &block.terminator.kind
                else {
                    return None;
                };
                let callee_path = self.resolve_body_callee_path(body, func)?;
                if callee_path != "spawn" && !callee_path.ends_with("::spawn") {
                    return None;
                }
                let arg_ty = args.first()?.ty(body.locals()).ok()?;
                Some(self.resolve_body_ty(arg_ty))
            })
            .collect()
    }

    pub(in crate::codegen_ay::chc) fn body_has_call_suffix(
        &self,
        body: &rustc_public::mir::Body,
        suffix: &str,
    ) -> bool {
        body.blocks.iter().any(|block| {
            let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
            else {
                return false;
            };
            self.resolve_body_callee_path(body, func)
                .is_some_and(|path| path == suffix || path.ends_with(&format!("::{suffix}")))
        })
    }

    pub(in crate::codegen_ay::chc) fn resolve_body_call_instance_by_suffix(
        &self,
        body: &rustc_public::mir::Body,
        suffix: &str,
    ) -> Option<Instance> {
        body.blocks.iter().find_map(|block| {
            let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
            else {
                return None;
            };
            let callee_path = self.resolve_body_callee_path(body, func)?;
            if callee_path != suffix && !callee_path.ends_with(&format!("::{suffix}")) {
                return None;
            }
            let func_ty = func.ty(body.locals()).ok()?;
            let (fn_def, fn_args) = match func_ty.kind() {
                TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
                _ => return None,
            };
            Instance::resolve(fn_def, &fn_args).ok()
        })
    }

    pub(in crate::codegen_ay::chc) fn resolve_future_trait_def_id_from_body(
        &self,
        body: &rustc_public::mir::Body,
    ) -> Option<rustc_span::def_id::DefId> {
        body.blocks.iter().find_map(|block| {
            let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
            else {
                return None;
            };
            let callee_path = self.resolve_body_callee_path(body, func)?;
            if !callee_path.ends_with("::poll") || !callee_path.contains("Future") {
                return None;
            }
            let func_ty = func.ty(body.locals()).ok()?;
            let (fn_def, _) = match func_ty.kind() {
                TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
                _ => return None,
            };
            self.resolve_parent_trait_def_id(fn_def)
        })
    }

    pub(in crate::codegen_ay::chc) fn resolve_body_callee_path(
        &self,
        body: &rustc_public::mir::Body,
        func: &Operand,
    ) -> Option<String> {
        let func_ty = func.ty(body.locals()).ok()?;
        let (fn_def, fn_args) = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
            _ => return None,
        };
        let instance_opt = Instance::resolve(fn_def, &fn_args).ok();
        let def_id =
            instance_opt.as_ref().map_or_else(|| fn_def.def_id(), |instance| instance.def.def_id());
        let internal_def_id = rustc_internal::internal(self.tcx, def_id);
        Some(self.tcx.def_path_str(internal_def_id))
    }
}
