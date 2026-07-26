// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Kani-family call dispatch helpers for CHC call terminators.
//!
//! Dispatches Kani hooks/intrinsics/models to the dedicated handlers in
//! `codegen_call_kani.rs`.
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_kani::CallKani;
use super::codegen_call_kani_model::CallKaniModel;
use crate::kani_middle::kani_functions::{KaniHook, KaniModel};
use rustc_public::ty::{FloatTy, IntTy, RigidTy, TyKind, UintTy};
use tracing::debug;

/// Extension trait for Kani-family dispatch in call-terminator codegen.
pub(in crate::codegen_ay::chc) trait CallDispatchKani {
    fn try_dispatch_call_kani(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchKani for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_kani(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        // Kani hooks: assert, assume, cover
        if let Some(kani_hook) = self.detect_kani_hook(dcx.func) {
            debug!("kani_hook match: {:?} in bb{}", kani_hook, dcx.bb_idx);
            self.codegen_call_kani_hook(dcx, kani_hook);
            return true;
        }

        // Kani intrinsics: IsInitialized, ValidValue, etc.
        if let Some(kani_intrinsic) = self.detect_kani_intrinsic(dcx.func) {
            self.codegen_call_kani_intrinsic(dcx, kani_intrinsic);
            return true;
        }

        // Kani models: any()
        if let Some(kani_model) = self.detect_kani_model(dcx.func) {
            self.codegen_call_kani_model(dcx, kani_model);
            return true;
        }

        // Part of #3222: Unmarked kani functions (any_raw_internal, any_raw_array).
        // After rustc MIR inlining, kani::any() (AnyModel, inline(always)) is
        // inlined away, leaving a direct call to any_raw_internal which has no
        // kanitool marker. Without this fallback, the CHC function inliner
        // processes the call and its nested any_raw() call bypasses Kani
        // dispatch, producing a nondet value without the memory mirror needed
        // for raw-pointer dereference soundness.
        let callee_path = dcx.callee_path.clone().or_else(|| self.resolve_callee_path(dcx.func));
        if let Some(ref callee) = callee_path {
            if self.try_dispatch_unmarked_kani_hook_by_path(dcx, callee) {
                return true;
            }
            if callee.contains("kani::")
                && (callee.contains("any_raw_internal") || callee.contains("any_raw_array"))
            {
                debug!("unmarked kani function detected: {callee}, routing to KaniModel::Any");
                self.codegen_call_kani_model(dcx, KaniModel::Any);
                return true;
            }
            // Synthetic and transformed contract models can lose their tool marker
            // after instance resolution. Keep `write_any_slice` on the model path so
            // it havocs the pointed-to slice instead of inlining the Rust stub body.
            if is_unmarked_write_any_slice_model_path(callee) {
                debug!(
                    "unmarked write_any_slice detected: {callee}, routing to KaniModel::WriteAnySlice"
                );
                self.codegen_call_kani_model(dcx, KaniModel::WriteAnySlice);
                return true;
            }
            // Part of #3270: When rustc MIR inlining is inconsistent (e.g., inlines
            // 3 of 4 kani::any() calls but not the 4th), the non-inlined call retains
            // the original <T as kani::Arbitrary>::any callee path without kanitool
            // marker attributes. Detect this pattern by callee path to avoid leaving
            // the destination local unconstrained and missing the Mem-level memory
            // mirror store that typed-memory dereferences rely on.
            if callee.contains("kani::Arbitrary") && callee.rsplit("::").next() == Some("any") {
                debug!("unmarked Arbitrary::any detected: {callee}, routing to KaniModel::Any");
                self.codegen_call_kani_model(dcx, KaniModel::Any);
                return true;
            }
            // Part of #4024: zero-length arrays and arrays of ZSTs lower
            // through `kani::*::any_array::<N>()` in the real `array-zst.rs`
            // harness. Trait resolution may retain the `Arbitrary` path or
            // resolve to the concrete impl item; either way, those result types
            // are singleton values, so route them through the canonical
            // Any-model path instead of leaving the later array comparison to
            // fall back.
            if callee.contains("kani::") && callee.rsplit("::").next() == Some("any_array") {
                let dest_ty = self.body.locals()[dcx.destination.local].ty;
                if super::codegen_call_kani_model_dst::is_zst_ty(dest_ty)
                    || is_raw_compatible_any_array_ty(dest_ty)
                {
                    debug!(
                        "unmarked kani any_array detected for raw-compatible array type: {callee}, routing to KaniModel::Any"
                    );
                    self.codegen_call_kani_model(dcx, KaniModel::Any);
                    return true;
                }
            }
        }

        false
    }
}

fn is_unmarked_write_any_slice_model_path(callee: &str) -> bool {
    callee.rsplit("::").next() == Some("write_any_slice")
        && (callee_path_has_segment(callee, "kani")
            || callee_path_has_segment(callee, "kani_core")
            || callee_path_has_segment(callee, "kani_models"))
}

fn callee_path_has_segment(callee: &str, segment: &str) -> bool {
    callee.split("::").any(|part| part == segment)
}

fn is_raw_compatible_any_array_ty(ty: rustc_public::ty::Ty) -> bool {
    let TyKind::RigidTy(RigidTy::Array(elem_ty, _)) = ty.kind() else {
        return false;
    };
    is_raw_compatible_any_elem_ty(elem_ty)
}

fn is_raw_compatible_any_elem_ty(ty: rustc_public::ty::Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(RigidTy::Bool)
            | TyKind::RigidTy(RigidTy::Int(
                IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I64 | IntTy::I128 | IntTy::Isize
            ))
            | TyKind::RigidTy(RigidTy::Uint(
                UintTy::U8 | UintTy::U16 | UintTy::U32 | UintTy::U64 | UintTy::U128 | UintTy::Usize
            ))
            | TyKind::RigidTy(RigidTy::Float(
                FloatTy::F16 | FloatTy::F32 | FloatTy::F64 | FloatTy::F128
            ))
    )
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn try_dispatch_unmarked_kani_hook_by_path(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        callee: &str,
    ) -> bool {
        // Part of #3930: compiler-inserted validity checks can retain the
        // concrete `kani::safety_check*` callee path while dropping marker
        // metadata. Route those paths explicitly so CHC suppresses the
        // fallthrough unwind edge and uses the hook-specific encoding.
        if !callee.contains("kani::") {
            return false;
        }
        let hook = match callee.rsplit("::").next() {
            Some("safety_check") => Some(KaniHook::SafetyCheck),
            Some("safety_check_no_assume") => Some(KaniHook::SafetyCheckNoAssume),
            _ => None,
        };
        let Some(hook) = hook else {
            return false;
        };
        debug!("unmarked Kani hook detected by path: {callee} -> {hook:?}");
        self.codegen_call_kani_hook(dcx, hook);
        true
    }
}

#[cfg(test)]
mod tests {
    use super::is_unmarked_write_any_slice_model_path;

    #[test]
    fn recognizes_kani_write_any_slice_model_paths() {
        assert!(is_unmarked_write_any_slice_model_path(
            "kani_core::kani_lib::mem::write_any_slice"
        ));
        assert!(is_unmarked_write_any_slice_model_path("crate::kani::internal::write_any_slice"));
        assert!(is_unmarked_write_any_slice_model_path("fixture::kani_models::write_any_slice"));
    }

    #[test]
    fn rejects_non_kani_write_any_slice_paths() {
        assert!(!is_unmarked_write_any_slice_model_path("user_crate::write_any_slice"));
        assert!(!is_unmarked_write_any_slice_model_path("user_crate::kani_write_any_slice"));
        assert!(!is_unmarked_write_any_slice_model_path("user_crate::kani::write_any_slim"));
    }
}
