// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `Allocator::allocate` never fails (C6), the store trace crosses an
//! allocation's `Ok` payload and `NonNull`'s data-pointer accessors, and a
//! constant array is seeded under its own key too (C4). Decision
//! TRUSTMC-OPEN-REDS, docs/DECISION_QUEUE.md.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;

const SOURCE: &str = r#"
    #![feature(allocator_api)]
    #![allow(dead_code)]
    use std::alloc::{AllocError, Allocator, Global, Layout};
    pub fn probe_allocate_never_errs() {
        match Global.allocate(Layout::new::<u32>()) {
            Ok(_) => {}
            Err(_) => panic!("allocation failed"),
        }
    }
    pub fn probe_const_array() -> u8 {
        let r: &[u8; 2] = &[13, 42];
        r[1]
    }
    pub fn probe_types(r: Result<std::ptr::NonNull<[u8]>, AllocError>, pair: Option<(u8, u8)>) {}
"#;

/// The `Err` arm of an allocation is unreachable: no error is derivable.
#[test]
fn test_allocate_err_arm_is_unreachable() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_name = "probe_allocate_never_errs";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());
        assert!(!vc.rules.is_empty(), "{fn_name} produces rules");
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        assert_z3_result(&smt, "unsat");
    });
}

/// `[13u8, 42]` is seeded at its elements under `u8`'s key AND the array's
/// own key (`slice_u8`), which a read of the whole array uses.
#[test]
fn test_const_array_elements_are_seeded_under_the_array_key() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_name = "probe_const_array";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();
        let array_key = ChcCtx::type_key_for_ty(
            rustc_public::ty::Ty::try_new_array(rustc_public::ty::Ty::unsigned_ty(UintTy::U8), 2)
                .unwrap(),
        )
        .into_owned();
        let seeded: Vec<(u64, u64)> = chc_ctx
            .ref_resolution
            .const_ref_memory_inits
            .iter()
            .filter(|(key, sort, _, _, _)| **key == *array_key && sort.bitvec_width() == Some(8))
            .filter_map(|(_, _, value, _, offset)| match value.value() {
                ExprValue::BitVecConst { value, .. } => {
                    Some((*offset, u64::try_from(value).unwrap()))
                }
                _ => None,
            })
            .collect();
        assert!(
            seeded.contains(&(0, 13)) && seeded.contains(&(1, 42)),
            "the elements under {array_key}: {seeded:?}"
        );
    });
}

/// `Result<NonNull<[u8]>, AllocError>`'s `Ok` payload is the whole value (a
/// niche layout), so reading it keeps the pointer; a pair's field does not.
#[test]
fn test_niche_payload_read_is_transparent() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_types");
        let (result_ty, option_ty) = (sig.inputs()[0], sig.inputs()[1]);
        use crate::rustc_public_bridge::IndexedVal;
        // The type of variant `v`'s field 0, by the one field-type rule.
        let payload = |ty: rustc_public::ty::Ty, v: usize| -> rustc_public::ty::Ty {
            let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else { panic!("{ty:?}") };
            let variant = def.variants_iter().nth(v).unwrap();
            let field = variant.fields().into_iter().next().unwrap();
            crate::codegen_ay::shared::mono_ty::field_ty(&field, &args).unwrap()
        };
        let read = |ty: rustc_public::ty::Ty, v: usize| {
            ChcCtx::field_chain_is_transparent(
                ty,
                &[
                    rustc_public::mir::ProjectionElem::Downcast(
                        rustc_public::ty::VariantIdx::to_val(v),
                    ),
                    rustc_public::mir::ProjectionElem::Field(0, payload(ty, v)),
                ],
            )
        };
        assert!(read(result_ty, 0), "Ok's NonNull<[u8]> is the Result's bits");
        assert!(!read(option_ty, 1), "Some's (u8, u8) is not Option's bits");
    });
}
