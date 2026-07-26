// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Monomorphization-time validation of generic SIMD intrinsic instantiations.
//!
//! rustc only type-checks generic SIMD intrinsics (`simd_extract`, `simd_insert`,
//! `simd_shuffle`, `simd_eq`, ...) against their monomorphized signature during
//! *codegen* (E0511 "invalid monomorphization of ... intrinsic", see
//! `generic_simd_intrinsic` in `rustc_codegen_llvm`). trust-mc replaces rustc
//! codegen, so without this pass an ill-typed instantiation (e.g.
//! `simd_extract::<i64x2, i32>`) sails through to the AY lowering, which soundly
//! over-approximates it — producing a verification verdict for a program rustc
//! (and Kani, whose codegen visits the call) rejects outright.
//!
//! This pass replays rustc's checks over every reachable (collected) function
//! body and emits the identical `rustc_codegen_ssa` E0511 diagnostics, so
//! trust-mc refuses exactly the programs rustc refuses.
//!
//! Honesty rule: only checks rustc itself performs are replayed, using rustc's
//! own `Ty::is_simd` / `Ty::simd_size_and_type` queries and the shared
//! `InvalidMonomorphization` diagnostic structs — well-typed SIMD code is
//! untouched. rustc checks *not* replayed here (e.g. constant shuffle-index
//! bounds) simply keep their current behavior; this pass never rejects a
//! program rustc accepts.

use rustc_codegen_ssa::errors::InvalidMonomorphization;
use rustc_middle::ty::{self, Ty as TyInternal, TyCtxt};
use rustc_public::mir::mono::MonoItem;
use rustc_public::mir::{Body, TerminatorKind};
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, TyKind};
use rustc_span::{Span, Symbol};

/// Replay rustc's monomorphization-time generic-SIMD-intrinsic checks (E0511)
/// over all reachable function bodies.
///
/// Errors are emitted into `tcx.dcx()`; the caller is responsible for
/// aborting (`check_reachable_items` ends with `abort_if_errors`). Exact
/// duplicate diagnostics (same span + message, e.g. the same ill-typed call
/// site reached through several instantiations of its enclosing function) are
/// deduplicated by the diagnostic context itself, matching rustc's output.
pub(crate) fn check_simd_intrinsic_monomorphizations(tcx: TyCtxt, items: &[MonoItem]) {
    for item in items {
        let MonoItem::Fn(instance) = item else { continue };
        let Some(body) = instance.body() else { continue };
        check_body(tcx, &body);
    }
}

/// Names of the generic SIMD intrinsics whose monomorphized signature this
/// pass validates (the subset of rustc's `generic_simd_intrinsic` checks that
/// trust-mc replays).
fn is_checked_simd_intrinsic(name: &str) -> bool {
    matches!(
        name,
        "simd_eq"
            | "simd_ne"
            | "simd_lt"
            | "simd_le"
            | "simd_gt"
            | "simd_ge"
            | "simd_shuffle"
            | "simd_insert"
            | "simd_insert_dyn"
            | "simd_extract"
            | "simd_extract_dyn"
    )
}

/// Scan one monomorphized body for calls to checked SIMD intrinsics and
/// validate each instantiation.
fn check_body(tcx: TyCtxt, body: &Body) {
    for bb in &body.blocks {
        let TerminatorKind::Call { func, args, destination, .. } = &bb.terminator.kind else {
            continue;
        };
        let Ok(func_ty) = func.ty(body.locals()) else { continue };
        let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func_ty.kind() else { continue };
        let Some(intrinsic) = def.as_intrinsic() else { continue };
        let name = intrinsic.fn_name();
        if !is_checked_simd_intrinsic(&name) {
            continue;
        }
        // Monomorphized argument / return types at the call site (these are the
        // same types rustc's backend sees via `args[i].layout.ty` / `ret_ty`).
        let Some(in_ty) = internal_operand_ty(tcx, body, args, 0) else { continue };
        let Ok(ret_ty_stable) = destination.ty(body.locals()) else { continue };
        let ret_ty = rustc_internal::internal(tcx, ret_ty_stable);
        let arg2_ty = internal_operand_ty(tcx, body, args, 2);
        let span = rustc_internal::internal(tcx, bb.terminator.span);
        check_simd_call(tcx, &name, span, in_ty, ret_ty, arg2_ty);
    }
}

/// Monomorphized internal type of the `idx`-th call argument, if present.
fn internal_operand_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body,
    args: &[rustc_public::mir::Operand],
    idx: usize,
) -> Option<TyInternal<'tcx>> {
    let stable_ty = args.get(idx)?.ty(body.locals()).ok()?;
    Some(rustc_internal::internal(tcx, stable_ty))
}

/// Validate a single checked-SIMD-intrinsic call, mirroring the check order and
/// diagnostics of rustc's `generic_simd_intrinsic` exactly.
fn check_simd_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    name_str: &str,
    span: Span,
    in_ty: TyInternal<'tcx>,
    ret_ty: TyInternal<'tcx>,
    arg2_ty: Option<TyInternal<'tcx>>,
) {
    let dcx = tcx.dcx();
    let name = Symbol::intern(name_str);

    // Every checked intrinsic takes a SIMD vector as its first argument
    // (rustc: `require_simd!(args[0].layout.ty, SimdInput)`).
    if !in_ty.is_simd() {
        dcx.emit_err(InvalidMonomorphization::SimdInput { span, name, ty: in_ty });
        return;
    }
    let (in_len, in_elem) = in_ty.simd_size_and_type(tcx);

    match name_str {
        "simd_eq" | "simd_ne" | "simd_lt" | "simd_le" | "simd_gt" | "simd_ge" => {
            if !ret_ty.is_simd() {
                dcx.emit_err(InvalidMonomorphization::SimdReturn { span, name, ty: ret_ty });
                return;
            }
            let (out_len, out_ty) = ret_ty.simd_size_and_type(tcx);
            if in_len != out_len {
                dcx.emit_err(InvalidMonomorphization::ReturnLengthInputType {
                    span,
                    name,
                    in_len,
                    in_ty,
                    ret_ty,
                    out_len,
                });
                return;
            }
            // rustc requires the comparison result vector to have (LLVM-level)
            // integer elements; float / pointer elements are rejected.
            if !matches!(out_ty.kind(), ty::Int(_) | ty::Uint(_)) {
                dcx.emit_err(InvalidMonomorphization::ReturnIntegerType {
                    span,
                    name,
                    ret_ty,
                    out_ty,
                });
            }
        }
        "simd_shuffle" => {
            let Some(idx_ty) = arg2_ty else { return };
            // rustc: the index operand must itself be a SIMD vector of `u32`.
            if !(idx_ty.is_simd()
                && matches!(idx_ty.simd_size_and_type(tcx).1.kind(), ty::Uint(ty::UintTy::U32)))
            {
                dcx.emit_err(InvalidMonomorphization::SimdShuffle { span, name, ty: idx_ty });
                return;
            }
            let n: u64 = idx_ty.simd_size_and_type(tcx).0;
            if !ret_ty.is_simd() {
                dcx.emit_err(InvalidMonomorphization::SimdReturn { span, name, ty: ret_ty });
                return;
            }
            let (out_len, out_ty) = ret_ty.simd_size_and_type(tcx);
            if out_len != n {
                dcx.emit_err(InvalidMonomorphization::ReturnLength {
                    span,
                    name,
                    in_len: n,
                    ret_ty,
                    out_len,
                });
                return;
            }
            if in_elem != out_ty {
                dcx.emit_err(InvalidMonomorphization::ReturnElement {
                    span,
                    name,
                    in_elem,
                    in_ty,
                    ret_ty,
                    out_ty,
                });
            }
        }
        "simd_insert" | "simd_insert_dyn" => {
            let Some(val_ty) = arg2_ty else { return };
            if in_elem != val_ty {
                dcx.emit_err(InvalidMonomorphization::InsertedType {
                    span,
                    name,
                    in_elem,
                    in_ty,
                    out_ty: val_ty,
                });
            }
        }
        "simd_extract" | "simd_extract_dyn" => {
            if ret_ty != in_elem {
                dcx.emit_err(InvalidMonomorphization::ReturnType {
                    span,
                    name,
                    in_elem,
                    in_ty,
                    ret_ty,
                });
            }
        }
        _ => unreachable!("filtered by is_checked_simd_intrinsic"),
    }
}

#[cfg(test)]
mod tests {
    use super::is_checked_simd_intrinsic;

    /// The checked set: exactly the intrinsics whose E0511 checks are replayed.
    #[test]
    fn checked_set_contains_cluster_intrinsics() {
        for name in ["simd_extract", "simd_insert", "simd_shuffle", "simd_eq", "simd_ne", "simd_lt"]
        {
            assert!(is_checked_simd_intrinsic(name), "{name} must be checked");
        }
    }

    /// Arithmetic / reduction / cast SIMD intrinsics are NOT in the checked set:
    /// their ill-typed instantiations are not part of the replayed subset, and
    /// well-typed uses (simd_add etc.) must keep verifying untouched.
    #[test]
    fn checked_set_excludes_unreplayed_intrinsics() {
        for name in [
            "simd_add",
            "simd_sub",
            "simd_mul",
            "simd_div",
            "simd_reduce_add_ordered",
            "simd_cast",
            "simd_select",
            "simd_select_bitmask",
            "simd_shuffle_const_generic",
            "transmute",
            "not_an_intrinsic",
        ] {
            assert!(!is_checked_simd_intrinsic(name), "{name} must not be checked");
        }
    }
}
