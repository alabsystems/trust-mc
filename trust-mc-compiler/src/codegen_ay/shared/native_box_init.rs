// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Unsafe native initialization boundaries. Recognition deliberately includes
//! unsupported payloads/allocators; those must not bypass the checked model.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};
use rustc_public::{CrateDef, rustc_internal};

#[derive(Clone, Copy, Debug)]
pub(crate) enum NativeInitKind {
    BoxSized,
    BoxSlice,
    VecArray,
}
#[derive(Clone, Copy)]
pub(crate) struct NativeInitBoundary {
    pub kind: NativeInitKind,
    pub input: Ty,
    pub payload: Ty,
    pub output: Ty,
}

#[derive(Clone, Copy)]
pub(crate) struct NativeMaybeWrite {
    pub maybe: Ty,
    pub payload: Ty,
}

/// These methods REQUIRE initialized T values. Recognize even unsupported
/// receivers, arrays, slices and active-stub units so unchecked MIR replay
/// cannot silently discharge that precondition.
pub(crate) fn native_maybe_unsafe_accessor(tcx: TyCtxt<'_>, instance: &Instance) -> bool {
    (||{
        if !cfg!(all(trust_toolchain,version("1.101")))||matches!(instance.kind,InstanceKind::Virtual{..}){return None;}
        let id=rustc_internal::internal(tcx,instance.def.def_id());
        if id.is_local(){return None;}
        let name=tcx.opt_item_name(id)?;
        if !matches!(name.as_str(),"assume_init"|"assume_init_read"|"assume_init_ref"|"assume_init_mut"|"assume_init_drop"|"array_assume_init"){return None;}
        let signature=instance.ty().kind().fn_sig()?.skip_binder();
        if signature.safety!=rustc_public::mir::Safety::Unsafe||signature.c_variadic{return None;}
        let [input]=signature.inputs() else{return None;};let output=signature.output();
        let maybe_id=tcx.lang_items().maybe_uninit()?;let owner=tcx.parent(id);
        if id.krate!=maybe_id.krate||!matches!(tcx.def_kind(owner),rustc_hir::def::DefKind::Impl{..})||crate::rustc_compat::impl_opt_trait_ref(tcx,owner).is_some(){return None;}
        let self_ty=crate::rustc_compat::skip_normalization(tcx.type_of(owner).instantiate_identity());
        let sized_owner=matches!(self_ty.kind(),rustc_middle::ty::Adt(adt,_) if adt.did()==maybe_id);
        let slice_owner=matches!(self_ty.kind(),rustc_middle::ty::Slice(element) if matches!(element.kind(),rustc_middle::ty::Adt(adt,_) if adt.did()==maybe_id));
        let reference=|ty:Ty|match ty.kind(){TyKind::RigidTy(RigidTy::Ref(_,inner,mutability))=>Some((inner,mutability)),_=>None};
        let unit=matches!(output.kind(),TyKind::RigidTy(RigidTy::Tuple(types)) if types.is_empty());
        if name.as_str()=="array_assume_init" {
            if !sized_owner{return None;}
            let (TyKind::RigidTy(RigidTy::Array(maybe,n)),TyKind::RigidTy(RigidTy::Array(actual,m)))=(input.kind(),output.kind()) else{return None;};
            return (n==m&&native_maybe_uninit_payload(tcx,maybe)==Some(actual)).then_some(());
        }
        if name.as_str()=="assume_init"{
            return (sized_owner&&native_maybe_uninit_payload(tcx,*input)==Some(output)).then_some(());
        }
        let (inner,mutability)=reference(*input)?;
        let (payload,slice)=if sized_owner{(native_maybe_uninit_payload(tcx,inner)?,false)}else if slice_owner{
            let TyKind::RigidTy(RigidTy::Slice(maybe))=inner.kind() else{return None;};(native_maybe_uninit_payload(tcx,maybe)?,true)
        }else{return None;};
        let target=if slice{Ty::from_rigid_kind(RigidTy::Slice(payload))}else{payload};
        let not=rustc_public::mir::Mutability::Not;let mutable=rustc_public::mir::Mutability::Mut;
        let valid=match name.as_str(){
            "assume_init_read"=>!slice&&mutability==not&&output==payload,
            "assume_init_ref"=>mutability==not&&reference(output)==Some((target,not)),
            "assume_init_mut"=>mutability==mutable&&reference(output)==Some((target,mutable)),
            "assume_init_drop"=>mutability==mutable&&unit,
            _=>false,
        };valid.then_some(())
    })().is_some()
}

/// The actual inherent core MaybeUninit::write, including its mutable receiver
/// and returned reference. Unsupported payloads are recognized for refusal.
pub(crate) fn native_maybe_uninit_write(
    tcx: TyCtxt<'_>,
    instance: &Instance,
) -> Option<NativeMaybeWrite> {
    if !cfg!(all(trust_toolchain, version("1.101")))
        || matches!(instance.kind, InstanceKind::Virtual { .. })
    {
        return None;
    }
    let id = rustc_internal::internal(tcx, instance.def.def_id());
    if id.is_local() || tcx.opt_item_name(id)?.as_str() != "write" {
        return None;
    }
    let signature = instance.ty().kind().fn_sig()?.skip_binder();
    let [input, value] = signature.inputs() else {
        return None;
    };
    let TyKind::RigidTy(RigidTy::Ref(_, maybe, rustc_public::mir::Mutability::Mut)) = input.kind()
    else {
        return None;
    };
    let payload = native_maybe_uninit_payload(tcx, maybe)?;
    if *value != payload {
        return None;
    }
    let output = signature.output();
    if !matches!(output.kind(),TyKind::RigidTy(RigidTy::Ref(_,actual,rustc_public::mir::Mutability::Mut)) if actual==payload)
    {
        return None;
    }
    let maybe_id = tcx.lang_items().maybe_uninit()?;
    let owner = tcx.parent(id);
    if id.krate != maybe_id.krate
        || !matches!(tcx.def_kind(owner), rustc_hir::def::DefKind::Impl { .. })
        || crate::rustc_compat::impl_opt_trait_ref(tcx, owner).is_some()
    {
        return None;
    }
    let self_ty =
        crate::rustc_compat::skip_normalization(tcx.type_of(owner).instantiate_identity());
    if !matches!(self_ty.kind(),rustc_middle::ty::Adt(adt,_) if adt.did()==maybe_id) {
        return None;
    }
    Some(NativeMaybeWrite { maybe, payload })
}

/// Preprocessing admission ONLY: preserve the safe write API when its receiver
/// may be a native Box payload. This grants no address/initialization authority;
/// codegen separately requires a unique checked allocation and closed custody.
/// Stack MaybeUninit writes keep their existing real-body preprocessing route.
pub(crate) fn native_maybe_write_box_receiver(
    tcx: TyCtxt<'_>,
    blocks: &[rustc_public::mir::BasicBlock],
    locals: &[rustc_public::mir::LocalDecl],
    receiver: &rustc_public::mir::Operand,
    maybe: Ty,
) -> bool {
    use rustc_public::mir::{CastKind, Operand, ProjectionElem, Rvalue, StatementKind};
    fn trace(
        tcx: TyCtxt<'_>,
        blocks: &[rustc_public::mir::BasicBlock],
        locals: &[rustc_public::mir::LocalDecl],
        local: usize,
        maybe: Ty,
        seen: &mut Vec<usize>,
        budget: &mut usize,
    ) -> bool {
        if seen.len() >= 32 || seen.contains(&local) {
            return false;
        }
        seen.push(local);
        for block in blocks {
            for statement in &block.statements {
                let Some(left) = budget.checked_sub(1) else {
                    return false;
                };
                *budget = left;
                let StatementKind::Assign(lhs, rhs) = &statement.kind else {
                    continue;
                };
                if lhs.local != local || !lhs.projection.is_empty() {
                    continue;
                }
                let found = match rhs {
                    Rvalue::Cast(
                        CastKind::BoxDerefTransmute,
                        Operand::Copy(p) | Operand::Move(p),
                        target,
                    ) if matches!(p.projection.as_slice(), [ProjectionElem::Field(0, _)]) => {
                        matches!(target.kind(),TyKind::RigidTy(RigidTy::RawPtr(actual,_)) if actual==maybe)
                            && locals
                                .get(p.local)
                                .and_then(|l| boxed(tcx, l.ty))
                                .is_some_and(|(inner, _, _)| inner == maybe)
                    }
                    Rvalue::Ref(_, rustc_public::mir::BorrowKind::Mut { .. }, p)
                        if p.projection.as_slice() == [ProjectionElem::Deref] =>
                    {
                        trace(tcx, blocks, locals, p.local, maybe, seen, budget)
                    }
                    Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..)
                        if p.projection.is_empty() =>
                    {
                        trace(tcx, blocks, locals, p.local, maybe, seen, budget)
                    }
                    _ => false,
                };
                if found {
                    return true;
                }
            }
        }
        seen.pop();
        false
    }
    let (Operand::Copy(place) | Operand::Move(place)) = receiver else {
        return false;
    };
    place.projection.is_empty()
        && trace(tcx, blocks, locals, place.local, maybe, &mut Vec::new(), &mut 16_384)
}
fn boxed(tcx: TyCtxt<'_>, ty: Ty) -> Option<(Ty, Ty, rustc_hir::def_id::DefId)> {
    let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
        return None;
    };
    let id = rustc_internal::internal(tcx, def.def_id());
    if !crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(
        tcx,
        id,
        &["boxed", "Box"],
    ) {
        return None;
    }
    let [GenericArgKind::Type(payload), GenericArgKind::Type(allocator)] = args.0.as_slice() else {
        return None;
    };
    Some((*payload, *allocator, id))
}
pub(crate) fn native_maybe_uninit_payload(tcx: TyCtxt<'_>, ty: Ty) -> Option<Ty> {
    let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
        return None;
    };
    if Some(rustc_internal::internal(tcx, def.def_id())) != tcx.lang_items().maybe_uninit() {
        return None;
    }
    let [GenericArgKind::Type(payload)] = args.0.as_slice() else {
        return None;
    };
    Some(*payload)
}
pub(crate) fn native_init_boundary(
    tcx: TyCtxt<'_>,
    instance: &Instance,
) -> Option<NativeInitBoundary> {
    if !cfg!(all(trust_toolchain, version("1.101")))
        || matches!(instance.kind, InstanceKind::Virtual { .. })
    {
        return None;
    }
    let id = rustc_internal::internal(tcx, instance.def.def_id());
    if id.is_local() {
        return None;
    }
    let signature = instance.ty().kind().fn_sig()?.skip_binder();
    let [input] = signature.inputs() else {
        return None;
    };
    let output = signature.output();
    let (maybe, allocator, box_id) = boxed(tcx, *input)?;
    if id.krate != box_id.krate {
        return None;
    }
    if tcx.is_diagnostic_item(rustc_span::Symbol::intern("box_assume_init_into_vec_unsafe"), id) {
        let payload = native_maybe_uninit_payload(tcx, maybe)?;
        let TyKind::RigidTy(RigidTy::Array(element, _)) = payload.kind() else {
            return None;
        };
        let TyKind::RigidTy(RigidTy::Adt(vec, args)) = output.kind() else {
            return None;
        };
        let vec_id = rustc_internal::internal(tcx, vec.def_id());
        if !crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(
            tcx,
            vec_id,
            &["vec", "Vec"],
        ) {
            return None;
        }
        let [GenericArgKind::Type(actual), GenericArgKind::Type(actual_allocator)] =
            args.0.as_slice()
        else {
            return None;
        };
        if *actual != element || *actual_allocator != allocator {
            return None;
        }
        return Some(NativeInitBoundary {
            kind: NativeInitKind::VecArray,
            input: *input,
            payload,
            output,
        });
    }
    let owner = tcx.parent(id);
    if tcx.opt_item_name(id)?.as_str() != "assume_init"
        || !matches!(tcx.def_kind(owner), rustc_hir::def::DefKind::Impl { .. })
        || crate::rustc_compat::impl_opt_trait_ref(tcx, owner).is_some()
    {
        return None;
    }
    let self_ty =
        crate::rustc_compat::skip_normalization(tcx.type_of(owner).instantiate_identity());
    if !matches!(self_ty.kind(),rustc_middle::ty::Adt(adt,_) if adt.did()==box_id) {
        return None;
    }
    let (payload, output_allocator, output_box) = boxed(tcx, output)?;
    if output_allocator != allocator || output_box != box_id {
        return None;
    }
    let kind = if native_maybe_uninit_payload(tcx, maybe) == Some(payload) {
        NativeInitKind::BoxSized
    } else if let (
        TyKind::RigidTy(RigidTy::Slice(maybe)),
        TyKind::RigidTy(RigidTy::Slice(payload)),
    ) = (maybe.kind(), payload.kind())
    {
        if native_maybe_uninit_payload(tcx, maybe) != Some(payload) {
            return None;
        }
        NativeInitKind::BoxSlice
    } else {
        return None;
    };
    // Concrete capabilities are checked separately, never by this recognizer.
    Some(NativeInitBoundary { kind, input: *input, payload, output })
}
