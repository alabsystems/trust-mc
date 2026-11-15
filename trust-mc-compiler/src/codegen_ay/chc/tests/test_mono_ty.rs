// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Rule A (`codegen_ay/shared/mono_ty.rs`, design trust-mc-reds-final §3.6
//! test A5): the type of a field is instantiated at its ADT's own arguments
//! and normalized, or refused; the parameter test is deep; the panicking
//! queries are reached only through the module and refuse what they cannot
//! take. The Trust standard library's
//! `Atomic<T: AtomicPrimitive> { v: UnsafeCell<T::Storage> }` is the motivating
//! shape: its declared field type is an associated-type projection of the
//! ADT's own parameter.
//!
//! The rule is the same code on both toolchains (`mono_ty` has no
//! `cfg(trust_toolchain)` arm), but the motivating ADT is not: the frozen
//! `nightly-2025-12-03` std declares `AtomicU8` as a plain
//! `struct AtomicU8 { v: UnsafeCell<u8> }` (its `atomic_int!` macro), which
//! names no parameter, so nothing in that std has the shape. The test source
//! therefore restates it as `MirrorAtomic<T: MirrorPrimitive>`, and every test
//! runs on each ADT [`subjects`] names: the mirror on every toolchain, std's
//! `AtomicU8` on the Trust toolchain, where std has the shape.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_middle::ty::TypeVisitableExt;
use rustc_public::ty::{GenericArgKind, GenericArgs, Ty};

const SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::sync::atomic::AtomicU8;
    pub struct R<'a> { pub r: &'a u8 }
    pub fn probe_atomic(a: AtomicU8) -> AtomicU8 { a }
    pub fn probe_param<T>(t: T) -> T { t }
    pub fn probe_string(s: String) -> String { s }
    pub fn probe_region(r: R<'static>) -> R<'static> { r }
    pub fn generic_id<T>(t: T) -> T { t }
    pub fn use_generic_id() -> String { generic_id::<String>(String::new()) }
    // The Trust std's `Atomic` shape, restated: a field whose declared type is
    // a projection of the ADT's own parameter. `String` has no impl.
    pub trait MirrorPrimitive { type Storage; }
    impl MirrorPrimitive for u8 { type Storage = u8; }
    pub struct MirrorAtomic<T: MirrorPrimitive> { v: core::cell::UnsafeCell<T::Storage> }
    pub fn probe_mirror(a: MirrorAtomic<u8>) -> MirrorAtomic<u8> { a }
"#;

/// An ADT of the motivating shape at `u8`: its type, definition and
/// arguments, with a label for assertion messages.
struct Subject {
    label: &'static str,
    ty: Ty,
    def: rustc_public::ty::AdtDef,
    args: GenericArgs,
}

impl Subject {
    /// The field `v`, whose declared type names the projection.
    fn field(&self) -> rustc_public::ty::FieldDef {
        assert_eq!(self.def.variants().len(), 1, "{}: one variant", self.label);
        self.def.variants()[0].fields()[0].clone()
    }

    /// `UnsafeCell<<T as ..>::Storage>`: the DECLARED type of `v`, under the
    /// ADT's own binder.
    fn declared_storage_cell(&self) -> Ty {
        self.field().ty()
    }
}

/// The input type of the probe `fn_suffix`, which must be an ADT.
fn subject(tcx: rustc_middle::ty::TyCtxt<'_>, label: &'static str, fn_suffix: &str) -> Subject {
    let ty = fn_sig_by_suffix(tcx, fn_suffix).inputs()[0];
    let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
        panic!("{label} should be an ADT: {ty:?}");
    };
    Subject { label, ty, def, args }
}

/// The ADTs of the motivating shape on this toolchain (module docs): the
/// test source's `MirrorAtomic<u8>` everywhere, and std's `AtomicU8`
/// (= `Atomic<u8>`) where std declares it that way, the Trust toolchain.
fn subjects(tcx: rustc_middle::ty::TyCtxt<'_>) -> Vec<Subject> {
    #[allow(unused_mut)]
    let mut subjects = vec![subject(tcx, "MirrorAtomic<u8>", "probe_mirror")];
    #[cfg(trust_toolchain)]
    subjects.push(subject(tcx, "std AtomicU8", "probe_atomic"));
    subjects
}

/// The type parameter `T` of `probe_param`.
fn param_t(tcx: rustc_middle::ty::TyCtxt<'_>) -> Ty {
    let t = fn_sig_by_suffix(tcx, "probe_param").inputs()[0];
    assert!(matches!(t.kind(), TyKind::Param(_)), "expected a type parameter: {t:?}");
    t
}

fn is_alias(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::Alias(..))
}

/// (a) The field's type at `[u8]` is `UnsafeCell<S>` with `S` the storage
/// the projection normalizes to: no alias, no parameter.
#[test]
fn test_field_ty_normalizes_the_atomic_storage_projection() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for subject in subjects(ctx.tcx) {
            let label = subject.label;
            let field = subject.field();
            assert!(is_alias_inside(field.ty()), "{label}: the declared type names the projection");
            let ty =
                mono_ty::field_ty(&field, &subject.args).expect("the field at [u8] instantiates");
            let TyKind::RigidTy(RigidTy::Adt(cell, cell_args)) = ty.kind() else {
                panic!("{label}: expected UnsafeCell<..>, got {ty:?}");
            };
            assert_eq!(cell.trimmed_name(), "UnsafeCell", "{label}");
            let Some(GenericArgKind::Type(storage)) = cell_args.0.first() else {
                panic!("{label}: UnsafeCell without a type argument: {ty:?}");
            };
            assert!(
                !is_alias(*storage),
                "{label}: the storage projection is normalized: {storage:?}"
            );
            assert!(!mono_ty::has_unresolved_params(ty), "{label}");
            assert!(
                ChcCtx::translate_ty(ty).is_some(),
                "{label}: the instantiated field type translates"
            );
        }

        // The control for the module docs' claim: this std's `AtomicU8` field
        // names no projection, so it is no subject here.
        #[cfg(not(trust_toolchain))]
        {
            let std_atomic = subject(ctx.tcx, "std AtomicU8", "probe_atomic");
            assert!(
                !is_alias_inside(std_atomic.declared_storage_cell()),
                "the frozen nightly's AtomicU8 now has the Atomic<T> shape: make it a subject"
            );
        }
    });
}

fn is_alias_inside(ty: Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(_, args)) => args.0.iter().any(|arg| match arg {
            GenericArgKind::Type(t) => is_alias(*t) || is_alias_inside(*t),
            _ => false,
        }),
        _ => is_alias(ty),
    }
}

/// (b) At `[T]` the projection does not normalize: `None`, and no panic
/// (rustc's panicking normalizer ICE'd here).
#[test]
fn test_field_ty_refuses_a_projection_of_a_free_parameter() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for subject in subjects(ctx.tcx) {
            let field = subject.field();
            let args = GenericArgs(vec![GenericArgKind::Type(param_t(ctx.tcx))]);
            assert!(mono_ty::field_ty(&field, &args).is_none(), "{}", subject.label);
        }
    });
}

/// (c) The parameter test is deep (inside an alias) and ignores lifetimes.
#[test]
fn test_has_unresolved_params_is_deep_and_ignores_regions() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for subject in subjects(ctx.tcx) {
            let declared = subject.declared_storage_cell();
            assert!(
                mono_ty::has_unresolved_params(declared),
                "{}: T inside the projection counts",
                subject.label
            );
        }
        assert!(mono_ty::has_unresolved_params(param_t(ctx.tcx)));

        // `R<'a>`'s declared field `&'a u8` names only a lifetime parameter.
        let r = fn_sig_by_suffix(ctx.tcx, "probe_region").inputs()[0];
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = r.kind() else { panic!("R is an ADT") };
        let declared_ref = def.variants()[0].fields()[0].ty();
        let internal = rustc_public::rustc_internal::internal(ctx.tcx, declared_ref);
        assert!(internal.has_param(), "the declared field names 'a (the control)");
        assert!(!mono_ty::has_unresolved_params(declared_ref), "a lifetime does not count");
    });
}

/// (d) Peeling a pointer-like wrapper off the declared storage cell returns
/// without an ICE (its one-field storage read went through `ty_with_args`).
#[test]
fn test_peel_pointer_like_wrapper_takes_the_declared_storage_cell() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for subject in subjects(ctx.tcx) {
            let declared = subject.declared_storage_cell();
            let peeled =
                crate::codegen_ay::chc::dyn_coercion::peel_pointer_like_wrapper_ty(declared);
            assert_eq!(
                peeled, declared,
                "{}: not a pointer-like wrapper: unchanged",
                subject.label
            );
        }
    });
}

/// (e) The drop glue of a type that still names a parameter is refused, with
/// no ICE; a monomorphic type's glue resolves.
#[test]
fn test_drop_glue_refuses_unresolved_params() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for subject in subjects(ctx.tcx) {
            let label = subject.label;
            let declared = subject.declared_storage_cell();
            assert!(mono_ty::drop_in_place(declared).is_none(), "{label}");
            assert!(mono_ty::drop_glue_body(declared).is_none(), "{label}");
            let glue = mono_ty::drop_in_place(subject.ty).expect("the ADT at u8 is monomorphic");
            assert!(glue.is_empty_shim(), "{label}: an atomic has no drop glue");
        }
    });
}

/// M-A5: the body binder takes the `try_` normalizer, so a projection that
/// does not normalize under a non-empty instance (`<String as
/// AtomicPrimitive>::Storage`, or `<String as MirrorPrimitive>::Storage`,
/// inside `generic_id::<String>`) is `None`, not an ICE; a type naming a
/// parameter the instance does not supply is `None` too.
#[test]
fn test_body_ty_refuses_instead_of_panicking() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let string = fn_sig_by_suffix(ctx.tcx, "probe_string").inputs()[0];
        let instance =
            resolve_single_type_generic_instance_by_suffix(ctx.tcx, "generic_id", string);
        assert!(!instance.args().0.is_empty());

        // `T` of `generic_id` is `String`.
        let t = instance.body().unwrap().locals()[1].ty;
        assert_eq!(mono_ty::body_ty(instance, t), Some(string));

        // The declared storage cell names the ADT's parameter #0; under
        // `generic_id::<String>` it is `<String as ..>::Storage`.
        for subject in subjects(ctx.tcx) {
            let declared = subject.declared_storage_cell();
            assert!(mono_ty::body_ty(instance, declared).is_none(), "{}", subject.label);
        }
    });
}
