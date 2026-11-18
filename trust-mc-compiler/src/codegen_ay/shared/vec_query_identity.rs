// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Candidate query routing is text-based; semantic permission is definition-based.

use rustc_middle::ty::TyCtxt;
use rustc_public::mir::{
    LocalDecl, Mutability, Operand,
    mono::{Instance, InstanceKind},
};
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind, UintTy};
use rustc_public::{CrateDef, rustc_internal};

use crate::codegen_ay::stubs::StubKind;
use crate::kani_middle::std_abstraction::{
    is_sysroot_alloc_definition, is_sysroot_alloc_definition_at, is_sysroot_core_definition_at,
};

/// Other stub families retain their existing admission. This predicate grants
/// only the six Vec query categories below, never layout or byte-view custody.
pub(in crate::codegen_ay) fn vec_query_stub_is_authorized(
    tcx: TyCtxt<'_>,
    func: &Operand,
    locals: &[LocalDecl],
    stub: StubKind,
) -> bool {
    if !matches!(
        stub,
        StubKind::VecLen
            | StubKind::VecCapacity
            | StubKind::VecIsEmpty
            | StubKind::VecAsPtr
            | StubKind::VecAsMutPtr
            | StubKind::VecAsSlice
    ) {
        return true;
    }
    (|| {
        // Transitive unit replacements can change the library operation too.
        if crate::kani_middle::transform::unit_has_stubs() { return None; }
        let func_ty = func.ty(locals).ok()?;
        // Instance resolution is a concrete-call API. Refuse a polymorphic
        // operand before asking rustc to select an implementation for it.
        if super::mono_ty::has_unresolved_params(func_ty) { return None; }
        let TyKind::RigidTy(RigidTy::FnDef(original, args)) = func_ty.kind()
        else { return None; };
        let instance = Instance::resolve(original, &args).ok()?;
        if matches!(instance.kind, InstanceKind::Virtual { .. }) { return None; }
        let id = rustc_internal::internal(tcx, instance.def.def_id());
        if !is_sysroot_alloc_definition(tcx, id) { return None; }
        let implementation = tcx.parent(id);
        if !matches!(tcx.def_kind(implementation), rustc_hir::def::DefKind::Impl { .. }) {
            return None;
        }
        let signature = instance.ty().kind().fn_sig()?.skip_binder();
        let [input] = signature.inputs() else { return None; };
        let TyKind::RigidTy(RigidTy::Ref(_, owner, receiver_mutability)) = input.kind()
        else { return None; };
        let TyKind::RigidTy(RigidTy::Adt(adt, owner_args)) = owner.kind()
        else { return None; };
        let owner_id = rustc_internal::internal(tcx, adt.def_id());
        if !is_sysroot_alloc_definition_at(tcx, owner_id, &["vec", "Vec"])
            || super::mono_ty::has_unresolved_params(owner)
        { return None; }
        let Some(GenericArgKind::Type(element)) = owner_args.0.first() else { return None; };
        let self_ty = crate::rustc_compat::skip_normalization(
            tcx.type_of(implementation).instantiate_identity(),
        );
        if !matches!(self_ty.kind(), rustc_middle::ty::Adt(actual, _) if actual.did() == owner_id)
        { return None; }
        let method = tcx.item_name(id);
        let mutable = matches!(method.as_str(), "as_mut_ptr" | "as_mut_slice" | "deref_mut");
        if receiver_mutability != if mutable { Mutability::Mut } else { Mutability::Not } {
            return None;
        }
        let original_id = rustc_internal::internal(tcx, original.def_id());
        let trait_ref = crate::rustc_compat::impl_opt_trait_ref(tcx, implementation);
        match method.as_str() {
            "deref" | "deref_mut" => {
                if stub != StubKind::VecAsSlice { return None; }
                let expected = if mutable { "DerefMut" } else { "Deref" };
                let trait_ref = crate::rustc_compat::skip_normalization(
                    trait_ref?.instantiate_identity(),
                );
                if !is_sysroot_core_definition_at(tcx, trait_ref.def_id, &["ops", "deref", expected])
                { return None; }
                // MIR can carry the canonical core trait method, resolved to
                // alloc's actual Vec impl. Ordinary inherent queries require
                // exact original/resolved agreement below.
                if original_id != id
                    && (tcx.parent(original_id) != trait_ref.def_id
                        || tcx.item_name(original_id) != method
                        || !is_sysroot_core_definition_at(
                            tcx, original_id, &["ops", "deref", expected, method.as_str()],
                        ))
                { return None; }
            }
            _ if trait_ref.is_none() && original_id == id => {}
            _ => return None,
        }
        let output = signature.output();
        let valid = match (stub, method.as_str()) {
            (StubKind::VecLen, "len") | (StubKind::VecCapacity, "capacity") =>
                matches!(output.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::Usize))),
            (StubKind::VecIsEmpty, "is_empty") =>
                matches!(output.kind(), TyKind::RigidTy(RigidTy::Bool)),
            (StubKind::VecAsPtr, "as_ptr") | (StubKind::VecAsMutPtr, "as_mut_ptr") =>
                matches!(output.kind(), TyKind::RigidTy(RigidTy::RawPtr(actual, mutability))
                    if actual == *element && mutability == if mutable { Mutability::Mut } else { Mutability::Not }),
            (StubKind::VecAsSlice, "as_slice" | "as_mut_slice" | "deref" | "deref_mut") =>
                matches!(output.kind(), TyKind::RigidTy(RigidTy::Ref(_, actual, mutability))
                    if matches!(actual.kind(), TyKind::RigidTy(RigidTy::Slice(value)) if value == *element)
                        && mutability == if mutable { Mutability::Mut } else { Mutability::Not }),
            _ => false,
        };
        valid.then_some(())
    })().is_some()
}
