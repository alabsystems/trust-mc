// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! fc-interior-mut cluster regression guards.
//!
//! A flattened cell VALUE (e.g. the bv32 payload of `Cell<u32>` reached
//! through contract instrumentation) must never be widened into a bv64
//! ADDRESS. Three coordinated guards:
//! - `make_coerced_eq_constraint` refuses narrow-bitvec widening into a
//!   raw-pointer-typed call destination (value-as-address fabrication);
//! - `normalize_deref_address_expr` refuses to zero-extend sub-pointer-width
//!   expressions into deref addresses;
//! - `recover_unsafe_cell_referent_address` recovers the referent's REAL
//!   memory-mirror (obj_id, offset) via ref-resolution where possible.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::args::ChcTrackLevel;
use crate::codegen_ay::chc::codegen_call_coerce::CallCoerce;
use crate::codegen_ay::chc::codegen_ctx::RefTarget;

fn mem_level_ctx<'tcx, 'body>(
    tcx: TyCtxt<'tcx>,
    body: &'body rustc_public::mir::Body,
    fn_name: &str,
) -> ChcCtx<'tcx, 'body> {
    ChcCtx::new(
        tcx,
        body,
        fn_name,
        ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
    )
}

/// Find the first local whose type matches `pred`, or panic.
fn find_local_by_ty(
    body: &rustc_public::mir::Body,
    pred: impl Fn(&TyKind) -> bool,
    what: &str,
) -> usize {
    body.locals()
        .iter()
        .position(|decl| pred(&decl.ty.kind()))
        .unwrap_or_else(|| panic!("no local with expected type: {what}"))
}

const PTR_IDENT_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_ptr_ident(p: *mut u32, x: u32) -> *mut u32 {
        let _y = x.wrapping_add(1);
        p
    }
"#;

/// `make_coerced_eq_constraint` must refuse to widen a bv32 VALUE into a
/// bv64 raw-pointer destination (the fc-interior-mut fabrication: a cell
/// payload zero-extended into an obj_id=0 address), while keeping direct
/// pointer-width equality and non-pointer widening intact.
#[test]
fn test_make_coerced_eq_refuses_value_as_address_widening() {
    with_test_ay_ctx_for_source(PTR_IDENT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_ident");
        let body = instance.body().expect("function body");
        let mut chc_ctx = mem_level_ctx(ctx.tcx, &body, "probe_ptr_ident");

        let ptr_local = find_local_by_ty(
            &body,
            |k| matches!(k, TyKind::RigidTy(RigidTy::RawPtr(..))),
            "raw pointer local",
        );
        let val_local = find_local_by_ty(
            &body,
            |k| matches!(k, TyKind::RigidTy(RigidTy::Uint(UintTy::U32))),
            "u32 local",
        );

        let dest_sort = ay_bindings::Sort::bitvec(64);
        let dest_var = Expr::var("test_dest_ptr", dest_sort.clone());
        let narrow_value = Expr::var("test_cell_value", ay_bindings::Sort::bitvec(32));

        // Narrow bitvec into raw-pointer dest: REFUSED (fabricated address).
        let refused = chc_ctx.make_coerced_eq_constraint(
            &dest_var,
            narrow_value.clone(),
            &dest_sort,
            ptr_local,
            "test::value_as_address",
        );
        assert!(
            refused.is_none(),
            "bv32 value widened into raw-pointer dest must be refused, got {refused:?}"
        );

        // Pointer-width result into raw-pointer dest: allowed (real identity).
        let real_ptr = Expr::var("test_real_ptr", ay_bindings::Sort::bitvec(64));
        let allowed = chc_ctx.make_coerced_eq_constraint(
            &dest_var,
            real_ptr,
            &dest_sort,
            ptr_local,
            "test::real_pointer_identity",
        );
        assert!(allowed.is_some(), "pointer-width identity constraint must be kept");

        // Narrow widening into a NON-pointer (u32) dest local: legacy behavior
        // preserved (plain integer widening is not an address fabrication).
        let widened = chc_ctx.make_coerced_eq_constraint(
            &dest_var,
            narrow_value,
            &dest_sort,
            val_local,
            "test::integer_widening",
        );
        assert!(widened.is_some(), "non-pointer dest widening must keep legacy behavior");
    });
}

/// `normalize_deref_address_expr` must return None for sub-pointer-width
/// expressions (routing callers to their sound fallback lanes) and pass
/// pointer-width addresses through unchanged.
#[test]
fn test_normalize_deref_address_refuses_narrow_value() {
    with_test_ay_ctx_for_source(PTR_IDENT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_ident");
        let body = instance.body().expect("function body");
        let chc_ctx = mem_level_ctx(ctx.tcx, &body, "probe_ptr_ident");

        let ptr_local = find_local_by_ty(
            &body,
            |k| matches!(k, TyKind::RigidTy(RigidTy::RawPtr(..))),
            "raw pointer local",
        );
        let ptr_ty = body.locals()[ptr_local].ty;

        let narrow = Expr::var("test_narrow_value", ay_bindings::Sort::bitvec(32));
        assert!(
            chc_ctx.normalize_deref_address_expr(narrow, ptr_ty).is_none(),
            "bv32 value must not be widened into a deref address"
        );

        let thin = Expr::var("test_thin_ptr", ay_bindings::Sort::bitvec(64));
        let normalized = chc_ctx.normalize_deref_address_expr(thin, ptr_ty);
        assert_eq!(
            normalized.and_then(|e| e.sort().bitvec_width()),
            Some(64),
            "pointer-width address must pass through"
        );
    });
}

const REF_RECOVERY_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_ref_recovery(x: u32) -> u32 {
        let r = &x;
        *r
    }
"#;

/// Referent-address recovery: an unprojected reference operand with a
/// tracked ref_targets entry must recover the referent's memory-mirror
/// address (pointer-width, constant (obj_id, offset)), and locals without
/// ref-resolution info must recover nothing (fail-closed lane).
#[test]
fn test_recover_referent_address_via_ref_targets() {
    with_test_ay_ctx_for_source(REF_RECOVERY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_recovery");
        let body = instance.body().expect("function body");
        let mut chc_ctx = mem_level_ctx(ctx.tcx, &body, "probe_ref_recovery");

        let ref_local = find_local_by_ty(
            &body,
            |k| matches!(k, TyKind::RigidTy(RigidTy::Ref(..))),
            "reference local",
        );
        let val_local = find_local_by_ty(
            &body,
            |k| matches!(k, TyKind::RigidTy(RigidTy::Uint(UintTy::U32))),
            "u32 local",
        );

        chc_ctx
            .ref_resolution
            .ref_targets
            .insert(ref_local, RefTarget::with_projections(val_local, Vec::new()));

        let modified = HashSet::new();
        let operand = Operand::Copy(Place { local: ref_local, projection: Vec::new() });
        let recovered = chc_ctx.recover_unsafe_cell_referent_address(&operand, &modified);
        let addr = recovered.expect("tracked reference must recover a referent address");
        assert_eq!(
            addr.sort().bitvec_width(),
            Some(64),
            "recovered referent address must be pointer-width, got {:?}",
            addr.sort()
        );

        // Untracked local: no fabrication — recovery must fail closed.
        chc_ctx.ref_resolution.ref_targets.clear();
        let operand = Operand::Copy(Place { local: ref_local, projection: Vec::new() });
        assert!(
            chc_ctx.recover_unsafe_cell_referent_address(&operand, &modified).is_none(),
            "untracked reference must not fabricate an address"
        );
    });
}

/// Reg-level contexts have no split-pointer address model; recovery must
/// bail out instead of allocating mirror addresses that nothing maintains.
#[test]
fn test_recover_referent_address_requires_mem_level() {
    with_test_ay_ctx_for_source(REF_RECOVERY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_recovery");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_ref_recovery",
            ChcConfig { track_level: ChcTrackLevel::Reg, ..ChcConfig::default() },
        );

        let ref_local = find_local_by_ty(
            &body,
            |k| matches!(k, TyKind::RigidTy(RigidTy::Ref(..))),
            "reference local",
        );
        let val_local = find_local_by_ty(
            &body,
            |k| matches!(k, TyKind::RigidTy(RigidTy::Uint(UintTy::U32))),
            "u32 local",
        );
        chc_ctx
            .ref_resolution
            .ref_targets
            .insert(ref_local, RefTarget::with_projections(val_local, Vec::new()));

        let modified = HashSet::new();
        let operand = Operand::Copy(Place { local: ref_local, projection: Vec::new() });
        assert!(
            chc_ctx.recover_unsafe_cell_referent_address(&operand, &modified).is_none(),
            "recovery must be Mem-level only"
        );
    });
}

const SLOT_RECOVERY_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Holder<'a> {
        pub p: &'a u32,
    }

    pub fn probe_slot_recovery(h: &Holder<'_>) -> u32 {
        *h.p
    }
"#;

/// Projected pointer-slot recovery: for an operand naming a pointer-typed
/// slot (e.g. a contract modifies-tuple field `(*t).0`), recovery loads the
/// pointer value from typed memory at the slot's address — a pointer-width
/// expression that is either the mirrored real pointer or unconstrained
/// (fail-closed), never a widened payload value.
#[test]
fn test_recover_referent_address_via_projected_slot() {
    with_test_ay_ctx_for_source(SLOT_RECOVERY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slot_recovery");
        let body = instance.body().expect("function body");
        let mut chc_ctx = mem_level_ctx(ctx.tcx, &body, "probe_slot_recovery");

        let holder_ref_local = find_local_by_ty(
            &body,
            |k| {
                matches!(
                    k,
                    TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                        if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Adt(..)))
                )
            },
            "&Holder local",
        );
        let inner_ref_ty = body
            .locals()
            .iter()
            .find_map(|decl| match decl.ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                    if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::U32))) =>
                {
                    Some(decl.ty)
                }
                _ => None,
            })
            .expect("&u32 local for field type");

        // Operand shape `(*h).p` — the slot holding the &u32 pointer.
        let place = Place {
            local: holder_ref_local,
            projection: vec![
                rustc_public::mir::ProjectionElem::Deref,
                rustc_public::mir::ProjectionElem::Field(0, inner_ref_ty),
            ],
        };
        let modified = HashSet::new();
        let operand = Operand::Copy(place);
        let recovered = chc_ctx.recover_unsafe_cell_referent_address(&operand, &modified);
        let addr = recovered.expect("pointer-typed slot must recover via typed-memory load");
        assert_eq!(
            addr.sort().bitvec_width(),
            Some(64),
            "slot-recovered pointer must be pointer-width, got {:?}",
            addr.sort()
        );
    });
}
