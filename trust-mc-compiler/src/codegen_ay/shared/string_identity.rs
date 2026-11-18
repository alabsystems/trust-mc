// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A registry spelling proposes a String model; actual definitions authorize it.

use crate::codegen_ay::stubs::StubKind;
use crate::kani_middle::std_abstraction::{
    is_sysroot_alloc_definition, is_sysroot_alloc_definition_at, is_sysroot_core_definition,
    is_sysroot_core_definition_at,
};
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::{
    LocalDecl, Mutability, Operand,
    mono::{Instance, InstanceKind},
};
use rustc_public::ty::{AdtDef, GenericArgKind, RigidTy, Ty, TyKind, UintTy};
use rustc_public::{CrateDef, rustc_internal};

pub(in crate::codegen_ay) fn is_native_string_adt(tcx: TyCtxt<'_>, def: AdtDef) -> bool {
    is_sysroot_alloc_definition_at(
        tcx,
        rustc_internal::internal(tcx, def.def_id()),
        &["string", "String"],
    )
}

/// The pinned native String constructor delegates to Vec<u8>::new, whose
/// RawVec stores the element alignment as an address without provenance.
/// This is a pointer bit pattern, never an allocation or dereference permit.
pub(in crate::codegen_ay) fn native_empty_string_alignment(
    tcx: TyCtxt<'_>,
    ty: Ty,
) -> Option<usize> {
    let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else { return None };
    if !is_native_string_adt(tcx, def) {
        return None;
    }
    let variants = def.variants();
    let [variant] = variants.as_slice() else { return None };
    let fields = variant.fields();
    let [field] = fields.as_slice() else { return None };
    if field.name.as_str() != "vec" {
        return None;
    }
    let vec_ty = super::mono_ty::field_ty(field, &args)?;
    let TyKind::RigidTy(RigidTy::Adt(vec_def, vec_args)) = vec_ty.kind() else { return None };
    if !is_sysroot_alloc_definition_at(
        tcx,
        rustc_internal::internal(tcx, vec_def.def_id()),
        &["vec", "Vec"],
    ) {
        return None;
    }
    let Some(GenericArgKind::Type(element)) = vec_args.0.first() else { return None };
    if !matches!(element.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::U8))) {
        return None;
    }
    let alignment = crate::kani_middle::abi::LayoutOf::new(*element).align_of()?;
    (alignment != 0 && alignment.is_power_of_two()).then_some(alignment)
}

/// Raw transport of a native String (also inside a wrapper) exposes model
/// header words. Until full allocation/lifecycle custody exists, that is a
/// refusal boundary. Exhaustion is conservative; no display spelling is used.
pub(in crate::codegen_ay) fn type_contains_native_string(tcx: TyCtxt<'_>, ty: Ty) -> bool {
    let mut pending = vec![ty];
    let mut seen = Vec::new();
    let mut work = 4096usize;
    while let Some(ty) = pending.pop() {
        let Some(left) = work.checked_sub(1) else {
            return true;
        };
        work = left;
        if seen.contains(&ty) {
            continue;
        }
        if seen.len() >= 32 {
            return true;
        }
        seen.push(ty);
        match ty.kind() {
            TyKind::RigidTy(
                RigidTy::Ref(_, inner, _)
                | RigidTy::RawPtr(inner, _)
                | RigidTy::Array(inner, _)
                | RigidTy::Slice(inner),
            ) => pending.push(inner),
            TyKind::RigidTy(RigidTy::Tuple(fields)) => {
                if fields.len() > work {
                    return true;
                }
                pending.extend(fields);
            }
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                if is_native_string_adt(tcx, def) {
                    return true;
                }
                for variant in def.variants() {
                    let Some(left) = work.checked_sub(1) else { return true };
                    work = left;
                    for field in variant.fields() {
                        let Some(left) = work.checked_sub(1) else {
                            return true;
                        };
                        work = left;
                        let Some(field_ty) = super::mono_ty::field_ty(&field, &args) else {
                            return true;
                        };
                        pending.push(field_ty);
                    }
                }
            }
            _ => {}
        }
    }
    false
}

pub(in crate::codegen_ay) fn is_string_stub(stub: StubKind) -> bool {
    use StubKind::*;
    matches!(
        stub,
        StringNew
            | StringFrom
            | StringFromRawParts
            | StringLen
            | StringIsEmpty
            | StringPush
            | StringPushStr
            | StringClear
            | StringClone
            | StringTruncate
            | StringFromUtf8Lossy
            | StringEq
            | StringContains
            | StringStartsWith
            | StringEndsWith
            | StringIsAscii
            | StringAsStr
            | StringIntoBoxedStr
            | StringFromUtf8
            | StringIntoBytes
            | SplitWhitespace
            | SplitWhitespaceNext
            | CowToString
            | DisplayToString
            | FmtFormat
    )
}

fn native_string(tcx: TyCtxt<'_>, ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Adt(def, _)) if is_native_string_adt(tcx, def))
}
fn strip_refs(mut ty: Ty) -> Option<Ty> {
    for _ in 0..16 {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => ty = inner,
            _ => return Some(ty),
        }
    }
    None
}
fn reference(ty: Ty, mutability: Mutability) -> Option<Ty> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, actual)) if actual == mutability => Some(inner),
        _ => None,
    }
}
fn str_ref(ty: Ty, mutability: Mutability) -> bool {
    reference(ty, mutability)
        .is_some_and(|inner| matches!(inner.kind(), TyKind::RigidTy(RigidTy::Str)))
}
fn usize_ty(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::Usize)))
}
fn unit(ty: Ty) -> bool {
    matches!(ty.kind(),TyKind::RigidTy(RigidTy::Tuple(fields)) if fields.is_empty())
}
fn u8_ty(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::U8)))
}
fn native_vec_u8(tcx: TyCtxt<'_>, ty: Ty) -> bool {
    matches!(ty.kind(),TyKind::RigidTy(RigidTy::Adt(def,args))
        if is_sysroot_alloc_definition_at(tcx,rustc_internal::internal(tcx,def.def_id()), &["vec","Vec"])
            && matches!(args.0.first(),Some(GenericArgKind::Type(element)) if u8_ty(*element)))
}
fn slice_u8_ref(ty: Ty) -> bool {
    reference(ty, Mutability::Not).is_some_and(
        |inner| matches!(inner.kind(),TyKind::RigidTy(RigidTy::Slice(element)) if u8_ty(element)),
    )
}
fn native_cow_str(tcx: TyCtxt<'_>, ty: Ty) -> bool {
    matches!(ty.kind(),TyKind::RigidTy(RigidTy::Adt(def,args))
        if is_sysroot_alloc_definition_at(tcx,rustc_internal::internal(tcx,def.def_id()), &["borrow","Cow"])
            && args.0.iter().any(|a|matches!(a,GenericArgKind::Type(t) if matches!(t.kind(),TyKind::RigidTy(RigidTy::Str)))))
}
fn native_box_str(tcx: TyCtxt<'_>, ty: Ty) -> bool {
    matches!(ty.kind(),TyKind::RigidTy(RigidTy::Adt(def,args))
        if is_sysroot_alloc_definition_at(tcx,rustc_internal::internal(tcx,def.def_id()), &["boxed","Box"])
            && matches!(args.0.first(),Some(GenericArgKind::Type(t)) if matches!(t.kind(),TyKind::RigidTy(RigidTy::Str))))
}
fn native_utf8_result(tcx: TyCtxt<'_>, ty: Ty) -> bool {
    let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else { return false };
    if !is_sysroot_core_definition_at(
        tcx,
        rustc_internal::internal(tcx, def.def_id()),
        &["result", "Result"],
    ) {
        return false;
    }
    let types: Vec<_> = args
        .0
        .iter()
        .filter_map(|a| if let GenericArgKind::Type(t) = a { Some(*t) } else { None })
        .collect();
    matches!(types.as_slice(),[ok,error] if native_string(tcx,*ok)
        && matches!(error.kind(),TyKind::RigidTy(RigidTy::Adt(def,_)) if
            is_sysroot_alloc_definition_at(tcx,rustc_internal::internal(tcx,def.def_id()), &["string","FromUtf8Error"])))
}

pub(in crate::codegen_ay) fn string_stub_is_authorized(
    tcx: TyCtxt<'_>,
    func: &Operand,
    locals: &[LocalDecl],
    stub: StubKind,
) -> bool {
    !is_string_stub(stub) || string_call_is_authorized(tcx, func, locals, Some(stub), true)
}

/// Unmodeled inherent String operations remain refusal boundaries even with
/// replacement maps. This grants no native model, pointer or mutable view.
pub(crate) fn native_string_unmodeled_operation(
    tcx: TyCtxt<'_>,
    func: &Operand,
    locals: &[LocalDecl],
    models_allowed: bool,
) -> bool {
    string_call_is_authorized(tcx, func, locals, None, models_allowed)
}

/// Preserve only calls whose actual definition/signature has a native model.
/// Method spelling proposes a bounded candidate list; the shared authorizer is
/// the authority. Renaming a real definition does not change this boundary.
pub(crate) fn native_string_call_boundary(
    tcx: TyCtxt<'_>,
    func: &Operand,
    locals: &[LocalDecl],
) -> bool {
    let Ok(ty) = func.ty(locals) else {
        return false;
    };
    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() else {
        return false;
    };
    let _ = args;
    let method = tcx.item_name(rustc_internal::internal(tcx, def.def_id()));
    string_stub_candidates(method.as_str())
        .iter()
        .any(|stub| string_stub_is_authorized(tcx, func, locals, *stub))
}

fn string_stub_candidates(method: &str) -> &'static [StubKind] {
    use StubKind::*;
    match method {
        "new" | "default" => &[StringNew],
        "len" => &[StringLen],
        "is_empty" => &[StringIsEmpty],
        "as_str" | "as_mut_str" | "deref" | "deref_mut" => &[StringAsStr],
        "clone" | "to_owned" => &[StringClone],
        "to_string" => &[StringClone, CowToString, DisplayToString],
        "from" | "from_utf8_unchecked" => &[StringFrom],
        "from_raw_parts" => &[StringFromRawParts],
        "from_utf8" => &[StringFromUtf8],
        "from_utf8_lossy" => &[StringFromUtf8Lossy],
        "into_bytes" => &[StringIntoBytes],
        "into_boxed_str" => &[StringIntoBoxedStr],
        "eq" => &[StringEq],
        "push" => &[StringPush],
        "push_str" => &[StringPushStr],
        "clear" => &[StringClear],
        "truncate" => &[StringTruncate],
        "contains" => &[StringContains],
        "starts_with" => &[StringStartsWith],
        "ends_with" => &[StringEndsWith],
        "is_ascii" => &[StringIsAscii],
        "format" => &[FmtFormat],
        _ => &[],
    }
}

fn string_call_is_authorized(
    tcx: TyCtxt<'_>,
    func: &Operand,
    locals: &[LocalDecl],
    stub: Option<StubKind>,
    models_allowed: bool,
) -> bool {
    (|| {
        if stub.is_some() && crate::kani_middle::transform::unit_has_stubs() {
            return None;
        }
        let ty = func.ty(locals).ok()?;
        if super::mono_ty::has_unresolved_params(ty) {
            return None;
        }
        let TyKind::RigidTy(RigidTy::FnDef(original, args)) = ty.kind() else { return None };
        let original_id = rustc_internal::internal(tcx, original.def_id());
        if stub.is_none() {
            // Cheap candidate rejection precedes instance resolution. Refusal
            // applies only to actual inherent methods of the real String.
            if !is_sysroot_alloc_definition(tcx, original_id) {
                return None;
            }
            let owner = tcx.parent(original_id);
            if !matches!(tcx.def_kind(owner), rustc_hir::def::DefKind::Impl { .. })
                || crate::rustc_compat::impl_opt_trait_ref(tcx, owner).is_some()
            {
                return None;
            }
            let owner_ty =
                crate::rustc_compat::skip_normalization(tcx.type_of(owner).instantiate_identity());
            if !matches!(owner_ty.kind(), rustc_middle::ty::Adt(def, _)
                if is_sysroot_alloc_definition_at(tcx, def.did(), &["string", "String"]))
            {
                return None;
            }
        }
        let instance = Instance::resolve(original, &args).ok()?;
        string_instance_is_authorized(tcx, original_id, instance, stub, models_allowed)
    })()
    .is_some()
}

/// Known function-pointer targets have an actual resolved instance, not a new
/// FnDef operand. Refuse the same unsupported operation before walking its body.
pub(crate) fn native_string_unmodeled_operation_instance(
    tcx: TyCtxt<'_>,
    instance: Instance,
    models_allowed: bool,
) -> bool {
    let original_id = rustc_internal::internal(tcx, instance.def.def_id());
    string_instance_is_authorized(tcx, original_id, instance, None, models_allowed).is_some()
}

fn string_instance_is_authorized(
    tcx: TyCtxt<'_>,
    original_id: rustc_hir::def_id::DefId,
    instance: Instance,
    stub: Option<StubKind>,
    models_allowed: bool,
) -> Option<()> {
    if matches!(instance.kind, InstanceKind::Virtual { .. })
        || (stub.is_some() && crate::kani_middle::transform::unit_has_stubs())
    {
        return None;
    }
    let id = rustc_internal::internal(tcx, instance.def.def_id());
    let signature = instance.ty().kind().fn_sig()?.skip_binder();
    let inputs = signature.inputs();
    let output = signature.output();
    let method = tcx.item_name(id);
    // The format free function has no impl owner. Its exact definition and
    // result are sufficient here; formatting's existing approximation stays.
    if stub == Some(StubKind::FmtFormat) {
        return (original_id==id && is_sysroot_alloc_definition_at(tcx,id,&["fmt","format"])
                && inputs.len()==1 && native_string(tcx,output)
                && matches!(inputs[0].kind(),TyKind::RigidTy(RigidTy::Adt(def,_)) if
                    is_sysroot_core_definition_at(tcx,rustc_internal::internal(tcx,def.def_id()), &["fmt","Arguments"]))).then_some(());
    }
    let implementation = tcx.parent(id);
    if !matches!(tcx.def_kind(implementation), rustc_hir::def::DefKind::Impl { .. }) {
        return None;
    }
    if !is_sysroot_alloc_definition(tcx, id) && !is_sysroot_core_definition(tcx, id) {
        return None;
    }
    let internal_instance = rustc_internal::internal(tcx, instance);
    let self_ty = crate::rustc_compat::skip_normalization(
        tcx.type_of(implementation).instantiate(tcx, internal_instance.args),
    );
    let mut self_ty = self_ty;
    for _ in 0..16 {
        if let rustc_middle::ty::Ref(_, inner, _) = self_ty.kind() {
            self_ty = *inner;
        } else {
            break;
        }
    }
    let string_owner = matches!(self_ty.kind(),rustc_middle::ty::Adt(def,_) if
            is_sysroot_alloc_definition_at(tcx,def.did(), &["string","String"]));
    let str_owner = matches!(self_ty.kind(), rustc_middle::ty::Str);
    let trait_ref = crate::rustc_compat::impl_opt_trait_ref(tcx, implementation);
    let Some(stub) = stub else {
        if original_id != id || trait_ref.is_some() || !string_owner {
            return None;
        }
        // Unmodeled inherent operations can escape an unqualified data
        // pointer or mutate only a child Vec cache. Typed header reads do
        // not grant that authority. Keep an explicit refusal until native
        // pointer/lifecycle or parent writeback custody exists. Canonical
        // trait Drop is not inherent and never receives this classification.
        let modeled = models_allowed
            && string_stub_candidates(method.as_str()).iter().any(|stub| {
                string_instance_is_authorized(tcx, original_id, instance, Some(*stub), true)
                    .is_some()
            });
        return (!modeled).then_some(());
    };
    let trait_path: Option<&[&str]> = match (stub, method.as_str()) {
        (StubKind::StringNew, "default") => Some(&["default", "Default"]),
        (StubKind::StringClone, "clone") => Some(&["clone", "Clone"]),
        (StubKind::StringClone, "to_owned") => Some(&["borrow", "ToOwned"]),
        (StubKind::StringClone, "to_string") => Some(&["string", "ToString"]),
        (StubKind::StringFrom, "from") => Some(&["convert", "From"]),
        (StubKind::StringEq, "eq") => Some(&["cmp", "PartialEq"]),
        (StubKind::StringAsStr, "deref") => Some(&["ops", "deref", "Deref"]),
        (StubKind::StringAsStr, "deref_mut") => Some(&["ops", "deref", "DerefMut"]),
        (StubKind::CowToString | StubKind::DisplayToString, "to_string") => {
            Some(&["string", "ToString"])
        }
        _ => None,
    };
    match (trait_path, trait_ref) {
        (Some(path), Some(trait_ref)) => {
            let trait_ref =
                crate::rustc_compat::skip_normalization(trait_ref.instantiate_identity());
            let alloc_trait = matches!(stub, StubKind::CowToString | StubKind::DisplayToString)
                || matches!(method.as_str(), "to_owned" | "to_string");
            if !(if alloc_trait {
                is_sysroot_alloc_definition_at(tcx, trait_ref.def_id, path)
            } else {
                is_sysroot_core_definition_at(tcx, trait_ref.def_id, path)
            }) {
                return None;
            }
            if original_id != id {
                let mut method_path = path.to_vec();
                method_path.push(method.as_str());
                if tcx.parent(original_id) != trait_ref.def_id
                    || !(if alloc_trait {
                        is_sysroot_alloc_definition_at(tcx, original_id, &method_path)
                    } else {
                        is_sysroot_core_definition_at(tcx, original_id, &method_path)
                    })
                {
                    return None;
                }
            }
        }
        (None, None) if original_id == id => {}
        _ => return None,
    }
    let string_receiver = |mutability| {
        inputs
            .first()
            .and_then(|t| reference(*t, mutability))
            .is_some_and(|t| native_string(tcx, t))
    };
    let bool_output = matches!(output.kind(), TyKind::RigidTy(RigidTy::Bool));
    use StubKind::*;
    let valid = match (stub, method.as_str()) {
        (StringNew, "new" | "default") => {
            string_owner && inputs.is_empty() && native_string(tcx, output)
        }
        (StringLen, "len") => {
            string_owner
                && inputs.len() == 1
                && string_receiver(Mutability::Not)
                && usize_ty(output)
        }
        (StringIsEmpty, "is_empty") => {
            string_owner && inputs.len() == 1 && string_receiver(Mutability::Not) && bool_output
        }
        (StringAsStr, "as_str" | "deref") => {
            string_owner
                && inputs.len() == 1
                && string_receiver(Mutability::Not)
                && str_ref(output, Mutability::Not)
        }
        (StringAsStr, "as_mut_str" | "deref_mut") => {
            string_owner
                && inputs.len() == 1
                && string_receiver(Mutability::Mut)
                && str_ref(output, Mutability::Mut)
        }
        (StringClone, "clone") => {
            string_owner
                && inputs.len() == 1
                && string_receiver(Mutability::Not)
                && native_string(tcx, output)
        }
        (StringClone, "to_owned") => {
            (string_owner || str_owner)
                && inputs.len() == 1
                && native_string(tcx, output)
                && (str_ref(inputs[0], Mutability::Not) || string_receiver(Mutability::Not))
        }
        (StringClone, "to_string") => {
            string_owner
                && inputs.len() == 1
                && string_receiver(Mutability::Not)
                && native_string(tcx, output)
        }
        (StringClear, "clear") => {
            string_owner && inputs.len() == 1 && string_receiver(Mutability::Mut) && unit(output)
        }
        (StringPush, "push") => {
            string_owner
                && inputs.len() == 2
                && string_receiver(Mutability::Mut)
                && matches!(inputs[1].kind(), TyKind::RigidTy(RigidTy::Char))
                && unit(output)
        }
        (StringPushStr, "push_str") => {
            string_owner
                && inputs.len() == 2
                && string_receiver(Mutability::Mut)
                && str_ref(inputs[1], Mutability::Not)
                && unit(output)
        }
        (StringTruncate, "truncate") => {
            string_owner
                && inputs.len() == 2
                && string_receiver(Mutability::Mut)
                && usize_ty(inputs[1])
                && unit(output)
        }
        (StringFrom, "from") => {
            string_owner
                && inputs.len() == 1
                && str_ref(inputs[0], Mutability::Not)
                && native_string(tcx, output)
        }
        (StringFrom, "from_utf8_unchecked") => {
            string_owner
                && inputs.len() == 1
                && native_vec_u8(tcx, inputs[0])
                && native_string(tcx, output)
        }
        (StringFromRawParts, "from_raw_parts") => {
            string_owner
                && inputs.len() == 3
                && matches!(inputs[0].kind(),TyKind::RigidTy(RigidTy::RawPtr(t,Mutability::Mut)) if u8_ty(t))
                && usize_ty(inputs[1])
                && usize_ty(inputs[2])
                && native_string(tcx, output)
        }
        (StringIntoBytes, "into_bytes") => {
            string_owner
                && inputs.len() == 1
                && native_string(tcx, inputs[0])
                && native_vec_u8(tcx, output)
        }
        (StringIntoBoxedStr, "into_boxed_str") => {
            string_owner
                && inputs.len() == 1
                && native_string(tcx, inputs[0])
                && native_box_str(tcx, output)
        }
        (StringFromUtf8, "from_utf8") => {
            string_owner
                && inputs.len() == 1
                && native_vec_u8(tcx, inputs[0])
                && native_utf8_result(tcx, output)
        }
        (StringFromUtf8Lossy, "from_utf8_lossy") => {
            string_owner
                && inputs.len() == 1
                && slice_u8_ref(inputs[0])
                && native_cow_str(tcx, output)
        }
        (StringEq, "eq") => {
            (string_owner || str_owner)
                && inputs.len() == 2
                && bool_output
                && inputs.iter().all(|t| {
                    strip_refs(*t).is_some_and(|t| {
                        native_string(tcx, t) || matches!(t.kind(), TyKind::RigidTy(RigidTy::Str))
                    })
                })
        }
        (StringContains, "contains")
        | (StringStartsWith, "starts_with")
        | (StringEndsWith, "ends_with") => {
            str_owner
                && inputs.len() == 2
                && str_ref(inputs[0], Mutability::Not)
                && bool_output
                && (str_ref(inputs[1], Mutability::Not)
                    || matches!(inputs[1].kind(), TyKind::RigidTy(RigidTy::Char)))
        }
        (StringIsAscii, "is_ascii") => {
            str_owner && inputs.len() == 1 && str_ref(inputs[0], Mutability::Not) && bool_output
        }
        (CowToString, "to_string") => {
            inputs.len() == 1
                && native_string(tcx, output)
                && reference(inputs[0], Mutability::Not).is_some_and(|t| native_cow_str(tcx, t))
        }
        (DisplayToString, "to_string") => {
            inputs.len() == 1
                && native_string(tcx, output)
                && reference(inputs[0], Mutability::Not).is_some_and(|t| {
                    native_string(tcx, t)
                        || native_cow_str(tcx, t)
                        || matches!(
                            t.kind(),
                            TyKind::RigidTy(
                                RigidTy::Bool
                                    | RigidTy::Char
                                    | RigidTy::Int(_)
                                    | RigidTy::Uint(_)
                                    | RigidTy::Float(_)
                                    | RigidTy::Str
                            )
                        )
                })
        }
        // Other overloads and unimplemented iterator/foreign Display
        // signatures refuse rather than inherit a name-based model.
        _ => false,
    };
    valid.then_some(())
}
