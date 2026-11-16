// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Vec representation belongs to its definition, not a user's type name.
#![cfg(trust_toolchain)]

use super::common::*;
use super::test_trust_box_new::with_native_box_ctx;

#[test]
fn native_vec_type_sort_uses_definition_identity() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::vec::Vec as NativeAlias;
        mod nongeneric {
            #[repr(C)] pub struct Vec { pub value: u64, pub other: u64 }
        }
        mod generic {
            #[repr(C)] pub struct Vec<T> { pub value: T, pub other: u16 }
        }
        mod mimic { pub mod alloc { pub mod vec {
            #[repr(C)] pub struct Vec { pub value: u64, pub other: u32 }
        } } }
        pub fn probe_vec_type_authority(
            _: std::vec::Vec<u64>, _: NativeAlias<u64>, _: nongeneric::Vec,
            _: generic::Vec<u8>, _: mimic::alloc::vec::Vec,
        ) {}
    "#;
    with_native_box_ctx(SOURCE, |ctx| {
        let signature = fn_sig_by_suffix(ctx.tcx, "probe_vec_type_authority");
        assert_eq!(signature.inputs().len(), 5);
        crate::codegen_ay::take_type_sort_fallback_count();
        let native = ChcCtx::translate_ty(signature.inputs()[0]).expect("actual native Vec");
        assert_eq!(native.datatype_sort().unwrap().constructors[0].fields.len(), 4);
        assert_eq!(ChcCtx::translate_ty(signature.inputs()[1]), Some(native));
        let native_key = ChcCtx::type_key_for_ty(signature.inputs()[0]).into_owned();
        let mut keys = std::collections::HashSet::new();
        for (&ty, widths) in signature.inputs()[2..].iter().zip([[64, 64], [8, 16], [64, 32]]) {
            let sort = ChcCtx::translate_ty(ty).expect("ordinary user Vec fields");
            let datatype = sort.datatype_sort().expect("ordinary ADT representation");
            assert_eq!(datatype.constructors.len(), 1);
            let fields = &datatype.constructors[0].fields;
            assert_eq!(fields.len(), 2, "user Vec must retain both declared fields");
            for (field, width) in fields.iter().zip(widths) {
                assert_eq!(field.sort, Sort::bitvec(width), "declared monomorphic field");
            }
            let key = ChcCtx::type_key_for_ty(ty).into_owned();
            assert_ne!(key, native_key, "a user Vec is not native Vec storage");
            assert!(keys.insert(key), "different user definitions retain distinct keys");
        }
        assert_eq!(crate::codegen_ay::take_type_sort_fallback_count(), 0);
    });
}

#[test]
fn native_vec_collection_side_state_uses_definition_identity() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::vec::Vec as NativeAlias;
        mod fake { pub struct Vec { pub value: u64, pub other: u64 } }
        mod generic { pub struct Vec<T> { pub value: T } }
        mod mimic { pub mod alloc { pub mod vec {
            pub struct Vec { pub value: u64 }
        } } }
        mod carrier { pub struct Vec { pub actual: std::vec::Vec<u8> } }
        pub fn collection_identity(_: std::vec::Vec<u8>, _: NativeAlias<u8>,
            _: &mut std::vec::Vec<u8>, _: fake::Vec, _: generic::Vec<u64>,
            _: mimic::alloc::vec::Vec, _: carrier::Vec) {}
    "#;
    with_native_box_ctx(SOURCE, |ctx| {
        let signature = fn_sig_by_suffix(ctx.tcx, "collection_identity");
        assert_eq!(signature.inputs().len(), 7);
        for &ty in &signature.inputs()[..3] {
            assert_eq!(ChcCtx::detect_collection_type(ty).map(|(kind, _)| kind), Some("vec"));
            // This predicate describes the stored value, so references carry
            // only their pointer and are not recursively owned collections.
            if !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(..))) {
                assert!(crate::codegen_ay::chc::stmt::ty_holds_collection(ty, 0));
            }
        }
        for &ty in &signature.inputs()[3..6] {
            assert!(
                ChcCtx::detect_collection_type(ty).is_none(),
                "a user Vec has no native sidecar"
            );
            assert!(
                !crate::codegen_ay::chc::stmt::ty_holds_collection(ty, 0),
                "a name cannot invent collection state for ordinary fields"
            );
        }
        let carrier = signature.inputs()[6];
        assert!(ChcCtx::detect_collection_type(carrier).is_none());
        assert!(
            crate::codegen_ay::chc::stmt::ty_holds_collection(carrier, 0),
            "a user Vec holding an actual Vec must retain the nested collection boundary"
        );
        let body = find_instance_by_suffix(ctx.tcx, "collection_identity").body().unwrap();
        let mut context = ChcCtx::new(
            ctx.tcx,
            &body,
            "collection_identity",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        context.declare_block_relations();
        for local in 1..=3 {
            assert!(context.collections.len_state.get_len_var(local).is_some());
            assert!(context.collections.len_state.get_cap_var(local).is_some());
        }
        for local in 4..=6 {
            assert!(context.collections.len_state.get_len_var(local).is_none());
            assert!(context.collections.len_state.get_cap_var(local).is_none());
            assert!(context.collections.len_state.get_present_var(local).is_none());
        }
    });
}
