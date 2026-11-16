// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Wrapper models require compiler-library identity; user ADTs keep their fields.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::codegen_types_adt_sort::CodegenTypesAdtSort;
use super::common::*;
use crate::codegen_ay::emit_chc;
use crate::kani_middle::std_abstraction::{NativeWrapperKind as Wrapper, native_wrapper_kind};

const SOURCE: &str = r#"
    #![feature(ptr_metadata)]
    #![allow(dead_code, unused_variables, stable_features)]

    mod exports {
        pub use std::sync::Mutex as MutexAlias;
        pub use std::ptr::NonNull as NonNullAlias;
    }
    pub fn probe_real(
        cell: std::cell::Cell<u32>, unsafe_cell: std::cell::UnsafeCell<u32>,
        ref_cell: std::cell::RefCell<u32>, md: std::mem::ManuallyDrop<u32>,
        mu: std::mem::MaybeUninit<u32>, mutex: std::sync::Mutex<u32>,
        rwlock: std::sync::RwLock<u32>, poison: std::sync::PoisonError<u32>,
        rc: std::rc::Rc<u32>, arc: std::sync::Arc<u32>,
        rc_weak: std::rc::Weak<u32>, arc_weak: std::sync::Weak<u32>,
        boxed: Box<u32>, nonnull: std::ptr::NonNull<u32>,
        nonzero: std::num::NonZeroU32, metadata: std::ptr::DynMetadata<dyn Send>,
        phantom: std::marker::PhantomData<u32>, cow: std::borrow::Cow<'static, str>,
    ) {}
    pub fn probe_guards<'a>(
        a: std::sync::MutexGuard<'a, u32>, b: std::sync::RwLockReadGuard<'a, u32>,
        c: std::sync::RwLockWriteGuard<'a, u32>, d: std::cell::Ref<'a, u32>,
        e: std::cell::RefMut<'a, u32>,
    ) {}
    pub fn probe_aliases(
        a: core::cell::Cell<u32>, b: std::cell::Cell<u32>,
        c: core::cell::RefCell<u32>, d: std::cell::RefCell<u32>,
        e: core::mem::ManuallyDrop<u32>, f: std::mem::ManuallyDrop<u32>,
        g: std::sync::Mutex<u32>, h: exports::MutexAlias<u32>,
        i: core::ptr::NonNull<u32>, j: exports::NonNullAlias<u32>,
    ) {}

    mod user {
        macro_rules! shadow {
            ($name:ident) => {
                #[repr(C)]
                pub struct $name<T> { pub tag: u32, pub value: T }
            }
        }
        shadow!(Mutex); shadow!(RefCell); shadow!(Cell); shadow!(UnsafeCell);
        shadow!(ManuallyDrop); shadow!(MaybeUninit); shadow!(NonNull);
        shadow!(NonZero); shadow!(NonZeroPretender); shadow!(Unique);
        shadow!(Box); shadow!(Rc); shadow!(Arc); shadow!(Weak);
        shadow!(RcInner); shadow!(ArcInner); shadow!(DynMetadata);
        shadow!(MutexGuard); shadow!(RwLock); shadow!(RwLockReadGuard);
        shadow!(RwLockWriteGuard); shadow!(PoisonError); shadow!(OnceBox);
        shadow!(AtomicPtr); shadow!(PhantomData); shadow!(Cow);
        pub mod cell { shadow!(Ref); shadow!(RefMut); }
        pub mod sys { pub mod sync { pub mod mutex { shadow!(Mutex); } } }
        pub mod alloc { pub mod raw_vec { shadow!(Mutex); } }

        pub fn probe_user(
            a: Mutex<u32>, b: RefCell<u32>, c: Cell<u32>, d: UnsafeCell<u32>,
            e: ManuallyDrop<u32>, f: MaybeUninit<u32>, g: NonNull<u32>,
            h: NonZero<u32>, i: NonZeroPretender<u32>, j: Unique<u32>,
            k: Box<u32>, l: Rc<u32>, m: Arc<u32>, n: Weak<u32>,
            o: RcInner<u32>, p: ArcInner<u32>, q: DynMetadata<u32>,
            r: MutexGuard<u32>, s: RwLock<u32>, t: RwLockReadGuard<u32>,
            u: RwLockWriteGuard<u32>, v: PoisonError<u32>, w: OnceBox<u32>,
            x: AtomicPtr<u32>, y: PhantomData<u32>, z: Cow<u32>,
            aa: cell::Ref<u32>, ab: cell::RefMut<u32>,
            ac: sys::sync::mutex::Mutex<u32>, ad: alloc::raw_vec::Mutex<u32>,
        ) {}
        const NON_NULL_VALUE: NonNull<u32> = NonNull { tag: 7, value: 11 };
        #[inline(never)]
        fn constant_fields(value: NonNull<u32>) -> bool {
            value.tag == 7 && value.value == 11
        }
        pub fn nonnull_constant_safe() { assert!(constant_fields(NON_NULL_VALUE)); }
        pub fn nonnull_constant_bug() { assert!(!constant_fields(NON_NULL_VALUE)); }
        #[inline(never)]
        fn move_mutex(value: Mutex<u32>) -> Mutex<u32> { value }
        #[inline(never)]
        fn move_refcell(value: RefCell<u32>) -> RefCell<u32> { value }
        #[inline(never)]
        fn view_mutex(value: &Mutex<u32>, expected: u32) -> bool {
            value.tag == 7 && value.value == expected
        }
        #[inline(never)]
        fn view_refcell(value: &RefCell<u32>, expected: u32) -> bool {
            value.tag == 7 && value.value == expected
        }
        pub fn mutex_move_safe(value: u32) {
            let original = Mutex { tag: 7u32, value };
            let moved = move_mutex(original);
            assert!(moved.tag == 7 && moved.value == value);
        }
        pub fn mutex_move_bug(value: u32) {
            let original = Mutex { tag: 7u32, value };
            let moved = move_mutex(original);
            assert!(moved.tag == 8 && moved.value == value);
        }
        pub fn mutex_ref_safe(value: u32) {
            let original = Mutex { tag: 7u32, value };
            let view = &original;
            assert!(view_mutex(view, value));
        }
        pub fn mutex_ref_bug(value: u32) {
            let original = Mutex { tag: 7u32, value };
            let view = &original;
            assert!(!view_mutex(view, value));
        }
        pub fn refcell_move_safe(value: u32) {
            let original = RefCell { tag: 7u32, value };
            let moved = move_refcell(original);
            assert!(moved.tag == 7 && moved.value == value);
        }
        pub fn refcell_move_bug(value: u32) {
            let original = RefCell { tag: 7u32, value };
            let moved = move_refcell(original);
            assert!(moved.tag == 8 && moved.value == value);
        }
        pub fn refcell_ref_safe(value: u32) {
            let original = RefCell { tag: 7u32, value };
            let view = &original;
            assert!(view_refcell(view, value));
        }
        pub fn refcell_ref_bug(value: u32) {
            let original = RefCell { tag: 7u32, value };
            let view = &original;
            assert!(!view_refcell(view, value));
        }
    }
    pub fn native_md_safe(value: u32) {
        let wrapped = std::mem::ManuallyDrop::new(value);
        assert!(*wrapped == value);
    }
    pub fn native_md_bug(value: u32) {
        let wrapped = std::mem::ManuallyDrop::new(value);
        assert!(*wrapped != value);
    }
    pub fn native_cell_safe(value: u32) {
        let wrapped = std::cell::Cell::new(value);
        assert!(wrapped.get() == value);
    }
    pub fn native_cell_bug(value: u32) {
        let wrapped = std::cell::Cell::new(value);
        assert!(wrapped.get() != value);
    }
"#;

fn wrapper_kind(ctx: TyCtxt<'_>, ty: rustc_public::ty::Ty) -> Option<Wrapper> {
    let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else { panic!("ADT parameter") };
    native_wrapper_kind(ctx, def)
}

#[test]
fn real_wrappers_and_reexports_keep_their_identity_and_models() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let signature = fn_sig_by_suffix(ctx.tcx, "probe_real");
        let expected = [
            Wrapper::Cell,
            Wrapper::UnsafeCell,
            Wrapper::RefCell,
            Wrapper::ManuallyDrop,
            Wrapper::MaybeUninit,
            Wrapper::Mutex,
            Wrapper::RwLock,
            Wrapper::PoisonError,
            Wrapper::Rc,
            Wrapper::Arc,
            Wrapper::RcWeak,
            Wrapper::ArcWeak,
            Wrapper::Box,
            Wrapper::NonNull,
            Wrapper::NonZero,
            Wrapper::DynMetadata,
            Wrapper::PhantomData,
            Wrapper::Cow,
        ];
        assert_eq!(signature.inputs().len(), expected.len());
        for (&ty, expected) in signature.inputs().iter().zip(expected) {
            assert_eq!(wrapper_kind(ctx.tcx, ty), Some(expected), "{ty:?}");
        }
        for index in [0, 1, 3, 4, 5, 6, 7, 14] {
            assert_eq!(ChcCtx::translate_ty(signature.inputs()[index]), Some(Sort::bitvec(32)));
        }
        // RefCell's borrow state remains a real part of its value sort. Its
        // existing logical payload memory key does not grant physical layout.
        let refcell_sort = ChcCtx::translate_ty(signature.inputs()[2]).unwrap();
        assert!(refcell_sort.datatype_sort().unwrap().constructors[0].fields.len() >= 2);
        let guards = fn_sig_by_suffix(ctx.tcx, "probe_guards");
        for (&ty, expected) in guards.inputs().iter().zip([
            Wrapper::MutexGuard,
            Wrapper::RwLockReadGuard,
            Wrapper::RwLockWriteGuard,
            Wrapper::Ref,
            Wrapper::RefMut,
        ]) {
            assert_eq!(wrapper_kind(ctx.tcx, ty), Some(expected), "{ty:?}");
        }
        let aliases = fn_sig_by_suffix(ctx.tcx, "probe_aliases");
        for pair in aliases.inputs().chunks_exact(2) {
            assert_eq!(pair[0], pair[1], "re-exports resolve to the same definition");
            assert_eq!(ChcCtx::translate_ty(pair[0]), ChcCtx::translate_ty(pair[1]));
            assert_eq!(ChcCtx::type_key_for_ty(pair[0]), ChcCtx::type_key_for_ty(pair[1]));
            if wrapper_kind(ctx.tcx, pair[0]) == Some(Wrapper::NonNull) {
                let TyKind::RigidTy(RigidTy::Adt(def, _)) = pair[0].kind() else {
                    panic!("NonNull alias is an ADT")
                };
                assert!(ChcCtx::is_opaque_alloc_infra(def));
            }
        }
    });
}

#[cfg(trust_toolchain)]
#[test]
fn real_nonpoison_wrappers_keep_their_existing_models() {
    const NONPOISON: &str = r#"
        #![feature(sync_nonpoison, nonpoison_mutex, nonpoison_rwlock)]
        #![allow(dead_code, unused_variables, stable_features)]
        mod exports { pub use std::sync::nonpoison::Mutex as MutexAlias; }
        pub fn probe_nonpoison<'a>(
            a: std::sync::nonpoison::Mutex<u32>,
            b: std::sync::nonpoison::RwLock<u32>,
            c: std::sync::nonpoison::MutexGuard<'a, u32>,
            d: std::sync::nonpoison::RwLockReadGuard<'a, u32>,
            e: std::sync::nonpoison::RwLockWriteGuard<'a, u32>,
            f: exports::MutexAlias<u32>,
        ) {}
    "#;
    with_test_ay_ctx_for_source(NONPOISON, |ctx| {
        let signature = fn_sig_by_suffix(ctx.tcx, "probe_nonpoison");
        assert_eq!(signature.inputs().len(), 6);
        for (&ty, expected) in signature.inputs().iter().zip([
            Wrapper::Mutex,
            Wrapper::RwLock,
            Wrapper::MutexGuard,
            Wrapper::RwLockReadGuard,
            Wrapper::RwLockWriteGuard,
            Wrapper::Mutex,
        ]) {
            assert_eq!(wrapper_kind(ctx.tcx, ty), Some(expected), "{ty:?}");
        }
        for index in [0, 1, 5] {
            assert_eq!(ChcCtx::translate_ty(signature.inputs()[index]), Some(Sort::bitvec(32)));
        }
        assert_eq!(signature.inputs()[0], signature.inputs()[5]);
    });
}

#[test]
fn user_wrappers_keep_both_fields_distinct_keys_and_actual_layout() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_user");
        let body = instance.body().unwrap();
        let signature = fn_sig_by_suffix(ctx.tcx, "probe_user");
        assert_eq!(signature.inputs().len(), 30);
        let mut chc = ChcCtx::new(ctx.tcx, &body, "probe_user", ChcConfig::default());
        let mut keys = std::collections::HashSet::new();
        for &ty in signature.inputs() {
            assert_eq!(wrapper_kind(ctx.tcx, ty), None, "user type: {ty:?}");
            let sort = ChcCtx::translate_ty(ty).expect("ordinary user ADT");
            let datatype = sort.datatype_sort().expect("user wrapper retains its structure");
            assert_eq!(datatype.constructors.len(), 1, "{ty:?}");
            assert_eq!(datatype.constructors[0].fields.len(), 2, "{ty:?}");
            let key = ChcCtx::type_key_for_ty(ty).into_owned();
            assert_ne!(key, "u32", "the wrapper is not its payload: {ty:?}");
            assert!(keys.insert(key), "different user definitions keep distinct keys: {ty:?}");
            assert_eq!(chc.get_type_size(ty), Some(8), "two repr(C) u32 fields: {ty:?}");
            assert_eq!(chc.get_type_align(ty), Some(4), "actual field alignment: {ty:?}");
        }
    });
}

#[test]
fn user_mutex_refcell_moves_and_references_keep_safe_bug_truth() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in [
            "mutex_move_safe",
            "mutex_move_bug",
            "mutex_ref_safe",
            "mutex_ref_bug",
            "refcell_move_safe",
            "refcell_move_bug",
            "refcell_ref_safe",
            "refcell_ref_bug",
            "nonnull_constant_safe",
            "nonnull_constant_bug",
        ] {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.body().unwrap();
            if let Some(dir) = std::env::var_os("WRAPPER_ORIGIN_ARTIFACT_DIR") {
                std::fs::create_dir_all(&dir).unwrap();
                std::fs::write(
                    std::path::Path::new(&dir).join(format!("{name}.mir")),
                    format!("{body:#?}"),
                )
                .unwrap();
            }
            if name.contains("_move_") {
                let crosses_call = body.blocks.iter().any(|block| {
                    let rustc_public::mir::TerminatorKind::Call { args, .. } = &block.terminator.kind else {
                        return false;
                    };
                    args.iter().any(|arg| {
                        let (Operand::Copy(place) | Operand::Move(place)) = arg else {
                            return false;
                        };
                        if !place.projection.is_empty() {
                            return false;
                        }
                        let Ok(ty) = place.ty(body.locals()) else { return false };
                        matches!(ty.kind(), TyKind::RigidTy(RigidTy::Adt(def, _)) if def.krate().is_local)
                    })
                });
                assert!(crosses_call, "whole user wrapper must cross a real call: {name}");
            }
            let (vc, _, diagnostics) = ChcCtx::new(
                ctx.tcx,
                &body,
                name,
                ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
            )
            .translate_with_diagnostics();
            let smt = emit_chc(&vc).to_string();
            if let Some(dir) = std::env::var_os("WRAPPER_ORIGIN_ARTIFACT_DIR") {
                std::fs::write(std::path::Path::new(&dir).join(format!("{name}.smt2")), &smt)
                    .unwrap();
            }
            let verdict = run_z3_on_smt2_with_timeout(&smt, 30);
            eprintln!("WRAPPER_ORIGIN {name}: {verdict:?}");
            assert_eq!(
                verdict.as_deref(),
                Ok(if name.ends_with("safe") { "unsat" } else { "sat" }),
                "{name}"
            );
            assert_eq!(diagnostics.place_translation_drop.get(), 0, "{name}");
            assert_eq!(diagnostics.sound_havoc_drop.get(), 0, "{name}");
            assert!(vc.approximation_identity_complete, "{name}");
        }
    });
}

#[test]
fn native_cell_and_manuallydrop_constructors_keep_safe_bug_truth() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in ["native_md_safe", "native_md_bug", "native_cell_safe", "native_cell_bug"] {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.body().unwrap();
            let (vc, _, diagnostics) = ChcCtx::new(
                ctx.tcx,
                &body,
                name,
                ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
            )
            .translate_with_diagnostics();
            let verdict = run_z3_on_smt2_with_timeout(&emit_chc(&vc).to_string(), 30);
            eprintln!("WRAPPER_ORIGIN {name}: {verdict:?}");
            assert_eq!(
                verdict.as_deref(),
                Ok(if name.ends_with("safe") { "unsat" } else { "sat" }),
                "{name}"
            );
            assert_eq!(diagnostics.place_translation_drop.get(), 0, "{name}");
            assert_eq!(diagnostics.sound_havoc_drop.get(), 0, "{name}");
        }
    });
}
