// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Thin re-export shim for `trust_mc-codegen-shared` crate.
//!
//! All logic has been extracted to the standalone `trust_mc-codegen-shared` crate
//! (Part of #2997). This module preserves existing import paths
//! (`crate::codegen_ay::shared::*`) so that consumers don't need changes.

pub(in crate::codegen_ay) mod compare_loops;
pub(in crate::codegen_ay) mod const_pointer;
mod inline_limits;
pub(in crate::codegen_ay) mod kani_any_loops;
pub(in crate::codegen_ay) mod mono_ty;
pub(in crate::codegen_ay) mod native_box_call;
pub(in crate::codegen_ay) mod native_box_drop;
#[cfg(all(trust_toolchain, version("1.101")))]
pub(in crate::codegen_ay) mod native_box_init;
pub(in crate::codegen_ay) mod native_box_raw;
pub(in crate::codegen_ay) mod native_box_uninit;
#[cfg(all(trust_toolchain, version("1.101")))]
pub(in crate::codegen_ay) mod native_maybe_memory;
pub(in crate::codegen_ay) mod string_identity;
pub(in crate::codegen_ay) mod string_view;
pub(in crate::codegen_ay) mod transmute_layout;
pub(in crate::codegen_ay) mod vec_capacity;
pub(in crate::codegen_ay) mod vec_query_identity;

// Re-export all public items from the extracted crate.
pub(in crate::codegen_ay) use self::inline_limits::*;
pub(in crate::codegen_ay) use trust_mc_codegen_shared::*;

/// Does the call `func` (an operand of a body whose locals are `locals`) run
/// an item of the crate under verification: a user function, or the user's
/// impl of a std trait (`impl Iterator for Chain`)?
///
/// The stub registry matches std's methods by the TEXT of the callee's path
/// (`Chain<` and `next` for `<core::iter::Chain<A, B> as Iterator>::next`),
/// so a user `struct Chain<T>` whose `next` yields one element was read as
/// std's chain adapter: `it.next() == Some(5)` was certified a Genuine
/// failure and a second `next()` returning `None` verified as `Some` (walker
/// fail-closed repair round 5, `user_type_named_like_std_dual.rs`). The std
/// models model std's own items; a call that resolves into the local crate
/// is walked as the code it is.
pub(in crate::codegen_ay) fn callee_is_local_item(
    func: &rustc_public::mir::Operand,
    locals: &[rustc_public::mir::LocalDecl],
) -> bool {
    if local_kani_standin_for_tests(func, locals) {
        return false;
    }
    use rustc_public::CrateDef;
    use rustc_public::mir::mono::Instance;
    use rustc_public::ty::{RigidTy, TyKind};
    let Ok(ty) = func.ty(locals) else {
        return false;
    };
    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() else {
        return false;
    };
    match Instance::resolve(def, &args) {
        Ok(instance) => instance.def.krate().is_local,
        Err(_) => def.krate().is_local,
    }
}

/// Unit tests only: the engine's in-process test compiler does not link the
/// `kani` library crate, so its probes stand the library in with a local
/// `mod kani` (`kani::mem::is_inbounds`, ...), and the models keyed on the
/// library's paths are exercised through it. Such a stand-in is read as the
/// library's item. Never in a real build: there a local item under `kani::`
/// shadows the library and is the user's own code (`callee_is_local_item`).
fn local_kani_standin_for_tests(
    func: &rustc_public::mir::Operand,
    locals: &[rustc_public::mir::LocalDecl],
) -> bool {
    if !cfg!(test) {
        return false;
    }
    use rustc_public::CrateDef;
    use rustc_public::ty::{RigidTy, TyKind};
    let Ok(ty) = func.ty(locals) else {
        return false;
    };
    let TyKind::RigidTy(RigidTy::FnDef(def, _)) = ty.kind() else {
        return false;
    };
    let name = def.name();
    name.split("::").any(|segment| segment == "kani")
}
