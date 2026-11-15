// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The identity of a function-pointer value (design 3, D1, in
//! `docs/chc-hole-fix-designs-2026-09-24.md`).
//!
//! A reified function pointer is encoded as a constant, and a call through
//! the pointer is dispatched on that constant. The constant must therefore
//! name one function exactly: two different functions must never share it,
//! or a call through one pointer walks the other's body.
//!
//! Before this module the key was `def.trimmed_name()` plus the generic
//! arguments, and `m1::op2` and `m2::op2` both trim to `op2`. They got one id,
//! the candidate list kept only the first, and a call through `m2::op2`
//! walked `m1::op2` (`walker_fn_ptr_target_dual.rs::bug_samename_*`), while
//! `n1::op3 as fn(..) != n2::op3 as fn(..)` got a Genuine counterexample
//! (`safe_samename_distinct_ptrs`). The key is now the mangled name of the
//! instance the reification resolves to, which is unique per instance:
//! `Instance::resolve_for_fn_ptr` for a function item (what the reachability
//! collector uses for the same cast) and the `FnOnce` instance of a closure
//! (`Instance::resolve_closure`, as the collector does for
//! `ClosureFnPointer`). Both the CHC and the BMC encoders use it.

use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::ty::{ClosureDef, ClosureKind, FnDef, GenericArgs, RigidTy, Ty, TyKind};

/// Object ids from this base up are fn-pointer identities; heap objects are
/// numbered from 1, so no address the encoder produces for an allocation can
/// equal an identity.
pub(crate) const FN_PTR_OBJ_BASE: u64 = 0x0F00_0000;

/// The CHC pointer value that is the identity of the instance whose mangled
/// name is `mangled`: a pointer into object `FN_PTR_OBJ_BASE + h[55:32]` at
/// offset `h[31:0]`, for `h` the 64-bit FNV-1a hash of the name.
///
/// A pure function of the instance, so a pointer a constant or a static
/// holds (`GlobalAlloc::Function`, read with no encoder state at hand) gets
/// the same value as the same function reified in code. The two used to
/// differ (a counter for reifications, a bare hash for allocations): `SF ==
/// f` for `static SF: fn(..) = add; let f: fn(..) = add;` failed, certified
/// Genuine (`walker_fn_ptr_completeness_dual.rs::safe_static_eq_reified`).
/// Two instances collide with probability about `n² / 2^57`; the encoder
/// checks every value it hands out against the ones it already has.
pub(crate) fn fn_ptr_identity_value(mangled: &str) -> u64 {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in mangled.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    let object = FN_PTR_OBJ_BASE + ((hash >> 32) & 0x00FF_FFFF);
    (object << 32) | (hash & 0xFFFF_FFFF)
}

/// The identity of the function a constant or static allocation points to.
pub(crate) fn fn_ptr_identity_of_instance(instance: &Instance) -> u64 {
    fn_ptr_identity_value(&instance.mangled_name())
}

/// What a reified function pointer designates.
#[derive(Clone, Debug)]
pub(crate) enum FnPtrTargetKind {
    /// A function item: the instance a `ReifyFnPointer` cast resolves to.
    Item { def: FnDef, args: GenericArgs, instance: Instance },
    /// A non-capturing closure coerced by `ClosureFnPointer`.
    Closure { def: ClosureDef, args: GenericArgs },
}

/// A function-pointer target with its identity key.
#[derive(Clone, Debug)]
pub(crate) struct FnPtrTarget {
    pub(crate) kind: FnPtrTargetKind,
    /// Unique per instance (see the module doc).
    pub(crate) key: String,
}

impl FnPtrTarget {
    /// Whether a call through the pointer uses the RustCall closure layout
    /// (local 1 is the environment).
    pub(crate) fn is_closure(&self) -> bool {
        matches!(self.kind, FnPtrTargetKind::Closure { .. })
    }

    /// The MIR body a call through the pointer runs, if one is available.
    ///
    /// A closure's `FnOnce` instance is usually a shim without a body, so the
    /// closure's own body is tried through each kind, as the host fn-pointer
    /// route always did.
    pub(crate) fn target_body(&self) -> Option<rustc_public::mir::Body> {
        use crate::callee_body::CalleeBody;
        match &self.kind {
            FnPtrTargetKind::Item { def, args, instance } => instance
                .callee_body()
                .or_else(|| Instance::resolve(*def, args).ok().and_then(|inst| inst.callee_body())),
            FnPtrTargetKind::Closure { def, args } => {
                [ClosureKind::Fn, ClosureKind::FnMut, ClosureKind::FnOnce].into_iter().find_map(
                    |kind| {
                        Instance::resolve_closure(*def, args, kind)
                            .ok()
                            .and_then(|inst| inst.callee_body())
                    },
                )
            }
        }
    }

    /// The pointer value that is this target's identity
    /// ([`fn_ptr_identity_value`] of the instance's mangled name).
    pub(crate) fn identity_value(&self) -> u64 {
        let mangled = self
            .key
            .strip_prefix("fn:")
            .or_else(|| self.key.strip_prefix("closure:"))
            .unwrap_or(&self.key);
        fn_ptr_identity_value(mangled)
    }

    /// A short human-readable name for debug output.
    pub(crate) fn label(&self) -> String {
        match &self.kind {
            FnPtrTargetKind::Item { instance, .. } => instance.name(),
            FnPtrTargetKind::Closure { def, .. } => format!("closure {}", def.name()),
        }
    }
}

/// The target a `ReifyFnPointer` or `ClosureFnPointer` cast of an operand of
/// type `ty` designates, or `None` when `ty` is neither a function item nor a
/// closure, or does not resolve.
pub(crate) fn fn_ptr_target_of_ty(ty: Ty) -> Option<FnPtrTarget> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => {
            let instance = Instance::resolve_for_fn_ptr(def, &args)
                .or_else(|_| Instance::resolve(def, &args))
                .ok()?;
            let key = format!("fn:{}", instance.mangled_name());
            Some(FnPtrTarget { kind: FnPtrTargetKind::Item { def, args, instance }, key })
        }
        TyKind::RigidTy(RigidTy::Closure(def, args)) => {
            let key = match Instance::resolve_closure(def, &args, ClosureKind::FnOnce) {
                Ok(instance) => format!("closure:{}", instance.mangled_name()),
                // The closure's def id is unique too; its arguments separate
                // the instantiations.
                Err(_) => format!("closure:{:?}:{:?}", def.def_id(), args),
            };
            Some(FnPtrTarget { kind: FnPtrTargetKind::Closure { def, args }, key })
        }
        _ => None,
    }
}
