// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_public::CrateDef;

use crate::codegen_ay::chc::ChcCtx;

/// Returns true when ALL concrete dyn-trait candidates for this dyn type are
/// trivially no-drop. Used to suppress sound-fallback recording when the
/// dyn-coercion candidate set proves no Drop side effects exist.
///
/// Part of #3872: local refinement over the existing dyn-coercion candidate
/// machinery from #3589. Does NOT change the global `ty_trivially_no_drop`
/// policy for `RigidTy::Dynamic` — only uses the resolved candidate set.
fn all_concrete_dyn_candidates_trivially_no_drop(
    ctx: &ChcCtx<'_, '_>,
    dyn_ty: rustc_public::ty::Ty,
) -> bool {
    let Some(trait_def_id) =
        super::super::super::dyn_coercion::extract_dyn_trait_def_id(ctx, dyn_ty)
    else {
        return false;
    };
    let candidates =
        super::super::super::dyn_coercion::collect_dyn_trait_candidates(ctx, trait_def_id);
    if candidates.is_empty() {
        return false;
    }
    candidates.iter().all(|c| ty_trivially_no_drop(c.concrete_ty))
}

/// Returns true when the type has no Drop side effects in CHC encoding.
///
/// Part of #3495: Extended to recognize tuples, arrays, slices, and
/// single-variant ADTs (structs) whose fields are all no-drop. This prevents
/// spurious `record_sound_fallback` on types like `RangeFrom<usize>` which
/// appear in subslice indexing MIR and have compiler-generated Drop
/// terminators despite having no actual Drop impl.
pub(in crate::codegen_ay::chc) fn ty_trivially_no_drop(ty: rustc_public::ty::Ty) -> bool {
    ty_no_drop_rec_with(ty, 0, &|_| false)
}

pub(super) fn ty_trivially_no_drop_with_dyn_candidates(
    ctx: &ChcCtx<'_, '_>,
    ty: rustc_public::ty::Ty,
) -> bool {
    ty_no_drop_rec_with(ty, 0, &|dyn_ty| all_concrete_dyn_candidates_trivially_no_drop(ctx, dyn_ty))
}

fn ty_no_drop_rec_with<F>(ty: rustc_public::ty::Ty, depth: usize, dyn_ty_is_no_drop: &F) -> bool
where
    F: Fn(rustc_public::ty::Ty) -> bool,
{
    use rustc_public::ty::{RigidTy, TyKind};

    // Guard against infinite recursion on self-referential types.
    if depth > 8 {
        return false;
    }

    match ty.kind() {
        // Primitives, references, pointers, function pointers, Never, Str.
        TyKind::RigidTy(
            RigidTy::Bool
            | RigidTy::Char
            | RigidTy::Int(_)
            | RigidTy::Uint(_)
            | RigidTy::Float(_)
            | RigidTy::Ref(..)
            | RigidTy::RawPtr(..)
            | RigidTy::FnPtr(..)
            | RigidTy::Never
            | RigidTy::Str,
        ) => true,

        // Part of #3703 finding 3: the global policy keeps dyn Trait drops
        // visible as sound fallbacks. #3872 adds a local refinement that can
        // prove exact no-drop semantics for a concrete dyn candidate set.
        TyKind::RigidTy(RigidTy::Dynamic(..)) => dyn_ty_is_no_drop(ty),

        // Tuples: no drop if all elements are no-drop.
        TyKind::RigidTy(RigidTy::Tuple(elems)) => {
            elems.iter().all(|e| ty_no_drop_rec_with(*e, depth + 1, dyn_ty_is_no_drop))
        }

        // Arrays/Slices: no drop if the element type is no-drop.
        TyKind::RigidTy(RigidTy::Array(elem, _)) => {
            ty_no_drop_rec_with(elem, depth + 1, dyn_ty_is_no_drop)
        }
        TyKind::RigidTy(RigidTy::Slice(elem)) => {
            ty_no_drop_rec_with(elem, depth + 1, dyn_ty_is_no_drop)
        }

        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            adt_no_drop_with(ty, def, args, depth, dyn_ty_is_no_drop)
        }

        // Part of #134: Closures capture fields in a compiler-generated struct.
        // If all captured fields (upvar types) are no-drop, the closure is no-drop.
        // Upvar types are encoded as a tuple in the generic args after the FnPtr arg.
        TyKind::RigidTy(RigidTy::Closure(_, args)) => {
            closure_upvar_tys_no_drop_with(&args, depth, dyn_ty_is_no_drop)
        }

        // FnDef types are zero-sized function items — they have no Drop.
        TyKind::RigidTy(RigidTy::FnDef(..)) => true,

        _ => false,
    }
}

/// Returns true when a closure's captured upvar types are all no-drop.
/// Extracts the upvar tuple from the closure's generic args (same layout as
/// codegen_types.rs:159-186).
fn closure_upvar_tys_no_drop_with<F>(
    args: &rustc_public::ty::GenericArgs,
    depth: usize,
    dyn_ty_is_no_drop: &F,
) -> bool
where
    F: Fn(rustc_public::ty::Ty) -> bool,
{
    use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};

    // Find the upvar tuple: the Tuple type after the FnPtr in the args list,
    // or the last Tuple type as fallback.
    let upvar_tys: Option<Vec<rustc_public::ty::Ty>> = args
        .0
        .iter()
        .enumerate()
        .find_map(|(pos, arg)| {
            if matches!(arg, GenericArgKind::Type(ty)
                if matches!(ty.kind(), TyKind::RigidTy(RigidTy::FnPtr(_))))
            {
                match args.0.get(pos + 1) {
                    Some(GenericArgKind::Type(ty)) => match ty.kind() {
                        TyKind::RigidTy(RigidTy::Tuple(tys)) => Some(tys),
                        _ => None,
                    },
                    _ => None,
                }
            } else {
                None
            }
        })
        .or_else(|| {
            args.0.iter().rev().find_map(|arg| match arg {
                GenericArgKind::Type(ty) => match ty.kind() {
                    TyKind::RigidTy(RigidTy::Tuple(tys)) => Some(tys),
                    _ => None,
                },
                _ => None,
            })
        });

    match upvar_tys {
        Some(tys) => tys.iter().all(|t| ty_no_drop_rec_with(*t, depth + 1, dyn_ty_is_no_drop)),
        // No upvar tuple found — non-capturing closure, no Drop.
        None => true,
    }
}

/// ADT-specific no-drop check, extracted from `ty_no_drop_rec` for size.
/// Returns true when ALL variants' fields are no-drop (covers structs and enums).
fn adt_no_drop_with<F>(
    ty: rustc_public::ty::Ty,
    def: rustc_public::ty::AdtDef,
    args: rustc_public::ty::GenericArgs,
    depth: usize,
    dyn_ty_is_no_drop: &F,
) -> bool
where
    F: Fn(rustc_public::ty::Ty) -> bool,
{
    use rustc_public::mir::mono::Instance;
    use rustc_public::ty::TyKind;

    // Part of #3348: Collection types have Drop impls that only deallocate
    // heap memory — no program-visible side effects in CHC mode.
    // Part of #3589: Rc/Arc drops only decrement refcount and deallocate.
    let name = def.trimmed_name();
    // Part of #3189: RawVec is Vec's internal allocator wrapper — its Drop only
    // calls dealloc. MIR drop elaboration generates Drop(RawVec) after
    // destructuring Vec, so it must be listed here alongside Vec.
    // RawVecInner is the non-generic inner type used by RawVec since Rust 1.80.
    // Part of #3945: HashMap cleanup paths can elaborate to hashbrown's raw
    // table carriers after inlining. Their Drop impls only deallocate backing
    // storage, so CHC should treat them like HashMap/RawVec rather than
    // relationizing panic-only cleanup tails as semantic.
    // Part of #4268: Mutex/RwLock Drop impls only destroy the platform mutex
    // (pthread_mutex_t), which has no semantic effect in CHC verification.
    // Adding them here prevents the recursive no-drop check from failing on
    // types like Arc<Mutex<[u8]>> where the Mutex wrapper triggers
    // resolve_drop_in_place to return a non-empty shim (due to Drop impl),
    // even though the Drop has no program-visible side effects. MutexGuard
    // and RwLockReadGuard/RwLockWriteGuard also have no semantic Drop effects
    // in verification (they just release the platform lock).
    // Note: RefCell is NOT listed here. RefCell<T> has compiler-generated
    // drop glue that must recurse into T's Drop when T implements Drop.
    // Classifying RefCell as trivially-no-drop would skip the inner T's Drop,
    // which is semantically wrong for harnesses testing Drop side effects.
    if matches!(
        name.as_str(),
        "Vec"
            | "RawVec"
            | "RawVecInner"
            | "HashMap"
            | "RawTable"
            | "RawTableInner"
            | "BTreeMap"
            | "String"
            | "VecDeque"
            | "BTreeSet"
            | "HashSet"
            | "BinaryHeap"
            | "Rc"
            | "Arc"
            | "Mutex"
            | "RwLock"
            | "MutexGuard"
            | "RwLockReadGuard"
            | "RwLockWriteGuard"
    ) {
        return true;
    }

    // Part of #3942: If the type still has unresolved generic params (e.g.,
    // `MaybeUninit<[u8; BYTES/#0]>` from cross-function const generics),
    // `resolve_drop_in_place` triggers a rustc ICE. Conservatively return false.
    if ty_has_unresolved_params(ty) {
        return false;
    }
    if !Instance::resolve_drop_in_place(ty).is_empty_shim() {
        return false;
    }

    // Part of #134: Generalize to ALL variants. An ADT (struct or enum) is
    // no-drop if every variant's fields resolve to no-drop types. This covers
    // single-variant structs, Option<T>, Result<T,E>, Ordering, and other
    // standard enums that don't have custom Drop impls — their drop glue only
    // recurses into fields. Types with custom Drop impls that have side effects
    // (e.g., Concrete1 in drop_concrete.rs) are handled by MIR-level drop
    // resolution (body_inline.rs) before the CHC encoder sees them. Types with
    // dealloc-only Drop impls are caught by the allowlist above.
    let variants = def.variants();
    variants.iter().all(|variant| {
        // Part of #3589: f.ty() returns unsubstituted generic types (e.g., `T`
        // not `dyn Identity` for `Outer<dyn Identity>`). Resolve ParamTy first.
        variant.fields().iter().all(|f| {
            let field_ty = f.ty();
            let resolved = if let TyKind::Param(param) = field_ty.kind() {
                args.0
                    .get(param.index as usize)
                    .and_then(|ga| match ga {
                        rustc_public::ty::GenericArgKind::Type(t) => Some(*t),
                        _ => None,
                    })
                    .unwrap_or(field_ty)
            } else {
                field_ty
            };
            ty_no_drop_rec_with(resolved, depth + 1, dyn_ty_is_no_drop)
        })
    })
}

/// Returns true when `ty` is `Box<T>` where `T` is an unsized type whose
/// allocation is not registered by `exchange_malloc` (dyn Trait, str, [T]).
///
/// Part of #3159: Used to skip dealloc safety *assertions* (obj_valid guard,
/// offset==0 guard) while preserving the obj_valid=false store. Safety
/// assertions produce false counterexamples when the pointer comes from an
/// opaque allocation that never set obj_valid.
///
/// Part of #3655: Extended from dyn-only to all unsized inner types. Box<str>
/// and Box<[T]> allocations come from String/Vec stubs that don't register
/// obj_valid — the same false-CTREX pattern as Box<dyn Trait>.
pub(super) fn is_box_with_dyn_inner(ty: rustc_public::ty::Ty) -> bool {
    use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};

    if let TyKind::RigidTy(RigidTy::Adt(_, args)) = ty.kind() {
        if let Some(GenericArgKind::Type(inner_ty)) = args.0.first() {
            return matches!(
                inner_ty.kind(),
                TyKind::RigidTy(RigidTy::Dynamic(..) | RigidTy::Str | RigidTy::Slice(..))
            );
        }
    }
    false
}

/// Returns true if the type contains unresolved generic params (type or const).
/// Part of #3942: prevents rustc ICE when `resolve_drop_in_place` encounters
/// types like `MaybeUninit<[u8; BYTES/#0]>` from cross-function const generics.
fn ty_has_unresolved_params(ty: rustc_public::ty::Ty) -> bool {
    use rustc_public::ty::{GenericArgKind, RigidTy, TyConstKind, TyKind};
    match ty.kind() {
        TyKind::Param(_) => true,
        TyKind::RigidTy(RigidTy::Array(elem, len)) => {
            ty_has_unresolved_params(elem) || matches!(len.kind(), TyConstKind::Param(_))
        }
        TyKind::RigidTy(RigidTy::Slice(elem)) => ty_has_unresolved_params(elem),
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => ty_has_unresolved_params(pointee),
        TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => ty_has_unresolved_params(pointee),
        TyKind::RigidTy(RigidTy::Tuple(fields)) => {
            fields.iter().any(|f| ty_has_unresolved_params(*f))
        }
        TyKind::RigidTy(RigidTy::Adt(_, ref args)) => args.0.iter().any(|arg| match arg {
            GenericArgKind::Type(arg_ty) => ty_has_unresolved_params(*arg_ty),
            GenericArgKind::Const(c) => matches!(c.kind(), TyConstKind::Param(_)),
            _ => false,
        }),
        _ => false,
    }
}
