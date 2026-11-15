// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Exposed native MaybeUninit storage needs initializedness provenance even
//! when its loaded value is unused. Types identify the domain, never validity.

use super::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::{Body, MirVisitor, visit::Location};
use rustc_public::ty::{GenericArgKind, MirConst, RigidTy, Ty, TyKind};
use rustc_public::{CrateDef, rustc_internal};
use std::collections::HashSet;

struct Types<'tcx> {
    tcx: TyCtxt<'tcx>,
    budget: usize,
    seen: HashSet<(Ty, u8)>,
}
impl Types<'_> {
    fn enter(&mut self, ty: Ty, mode: u8) -> Option<bool> {
        if !self.seen.insert((ty, mode)) {
            return Some(false);
        }
        let Some(left) = self.budget.checked_sub(1) else {
            return Some(true);
        };
        self.budget = left;
        None
    }
    fn maybe(&self, ty: Ty) -> bool {
        matches!(ty.kind(),TyKind::RigidTy(RigidTy::Adt(def,_)) if Some(rustc_internal::internal(self.tcx,def.def_id()))==self.tcx.lang_items().maybe_uninit())
    }
    fn pointer_payload(&self, ty: Ty) -> Option<Ty> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _) | RigidTy::Ref(_, inner, _)) => Some(inner),
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                let id = rustc_internal::internal(self.tcx, def.def_id());
                let wrapper = def.is_box()
                    || crate::kani_middle::std_abstraction::is_sysroot_core_definition_at(
                        self.tcx,
                        id,
                        &["ptr", "non_null", "NonNull"],
                    )
                    || crate::kani_middle::std_abstraction::is_sysroot_core_definition_at(
                        self.tcx,
                        id,
                        &["ptr", "unique", "Unique"],
                    )
                    || crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(
                        self.tcx,
                        id,
                        &["boxed", "BoxRaw"],
                    );
                if !wrapper {
                    return None;
                }
                match args.0.first() {
                    Some(GenericArgKind::Type(payload)) => Some(*payload),
                    _ => None,
                }
            }
            _ => None,
        }
    }
    /// Pointer fields are words, not their opaque reachable implementation.
    /// A BTreeMap<u32,u32> is not a MaybeUninit value because its private
    /// capacity nodes use MaybeUninit internally. A directly named Maybe
    /// pointer/reference still retains that memory's initialization boundary.
    fn direct(&mut self, ty: Ty) -> bool {
        if let Some(answer) = self.enter(ty, 0) {
            return answer;
        }
        if self.maybe(ty) {
            return true;
        }
        if let Some(inner) = self.pointer_payload(ty) {
            return self.direct(inner);
        }
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Array(inner, _) | RigidTy::Slice(inner)) => self.direct(inner),
            TyKind::RigidTy(RigidTy::Tuple(types)) => types.into_iter().any(|ty| self.direct(ty)),
            _ => false,
        }
    }
    fn value(&mut self, ty: Ty) -> bool {
        if let Some(answer) = self.enter(ty, 1) {
            return answer;
        }
        if self.maybe(ty) {
            return true;
        }
        if let Some(inner) = self.pointer_payload(ty) {
            return self.direct(inner);
        }
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                // Public element types retain their Maybe domain even when
                // an opaque owner (Vec/Rc/etc.) erases its buffer to bytes.
                // A phantom-only parameter stores no corresponding memory.
                for argument in &args.0 {
                    let GenericArgKind::Type(argument) = argument else {
                        continue;
                    };
                    let mut probe =
                        Types { tcx: self.tcx, budget: self.budget, seen: HashSet::new() };
                    let maybe = probe.value(*argument);
                    self.budget = probe.budget;
                    if maybe && self.data_storage(ty) {
                        return true;
                    }
                }
                def.variants().iter().any(|v| {
                    v.fields().iter().any(|field| {
                        mono_ty::field_ty(field, &args).is_none_or(|ty| self.value(ty))
                    })
                })
            }
            TyKind::RigidTy(RigidTy::Array(inner, _) | RigidTy::Slice(inner)) => self.value(inner),
            TyKind::RigidTy(RigidTy::Tuple(types)) => types.into_iter().any(|ty| self.value(ty)),
            _ => false,
        }
    }
    fn data_storage(&mut self, ty: Ty) -> bool {
        if let Some(answer) = self.enter(ty, 3) {
            return answer;
        }
        match ty.kind() {
            TyKind::RigidTy(
                RigidTy::RawPtr(..)
                | RigidTy::Ref(..)
                | RigidTy::Bool
                | RigidTy::Char
                | RigidTy::Int(_)
                | RigidTy::Uint(_)
                | RigidTy::Float(_),
            ) => true,
            TyKind::RigidTy(RigidTy::Adt(def, args)) => def.variants().iter().any(|v| {
                v.fields().iter().any(|field| {
                    mono_ty::field_ty(field, &args).is_none_or(|ty| self.data_storage(ty))
                })
            }),
            TyKind::RigidTy(RigidTy::Array(inner, _) | RigidTy::Slice(inner)) => {
                self.data_storage(inner)
            }
            TyKind::RigidTy(RigidTy::Tuple(types)) => {
                types.into_iter().any(|ty| self.data_storage(ty))
            }
            _ => false,
        }
    }
    fn exposed(&mut self, ty: Ty) -> bool {
        if let Some(answer) = self.enter(ty, 2) {
            return answer;
        }
        if let Some(inner) = self.pointer_payload(ty) {
            self.exposed(inner)
        } else {
            self.value(ty)
        }
    }
}

pub(crate) fn native_maybe_memory_type(tcx: TyCtxt<'_>, ty: Ty) -> bool {
    Types { tcx, budget: 1024, seen: HashSet::new() }.exposed(ty)
}

pub(crate) fn native_maybe_memory_constant(tcx: TyCtxt<'_>, body: &Body) -> bool {
    struct Constants<'tcx> {
        tcx: TyCtxt<'tcx>,
        found: bool,
    }
    impl MirVisitor for Constants<'_> {
        fn visit_mir_const(&mut self, value: &MirConst, _location: Location) {
            self.found |= native_maybe_memory_type(self.tcx, value.ty());
        }
    }
    let mut visitor = Constants { tcx, found: false };
    visitor.visit_body(body);
    visitor.found
}

/// Inline frames have no initializedness sidecar for these exposed carriers.
/// Inspect the frame's actual types, never host-local numbers or sort names.
pub(crate) fn body_has_native_maybe_memory(tcx: TyCtxt<'_>, body: &Body) -> bool {
    body.locals().iter().any(|local| native_maybe_memory_type(tcx, local.ty))
        || native_maybe_memory_constant(tcx, body)
}
