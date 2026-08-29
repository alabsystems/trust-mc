// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Handler-boundary predicates for the function inline pass.

use rustc_public::CrateDef;
use rustc_public::ty::{FloatTy, GenericArgKind, GenericArgs, IntTy, RigidTy, TyKind, UintTy};

pub(super) fn is_handler_backed_slice_contains(fn_name: &str) -> bool {
    if !fn_name.ends_with("::contains") {
        return false;
    }

    (fn_name.contains("slice::") || fn_name.contains("<["))
        && !fn_name.contains("HashMap")
        && !fn_name.contains("BTreeMap")
        && !fn_name.contains("BTreeSet")
        && !fn_name.contains("HashSet")
        && !fn_name.contains("Vec")
        && !fn_name.contains("String")
}

pub(super) fn is_handler_backed_range_contains(fn_name: &str) -> bool {
    if !fn_name.contains("::contains") {
        return false;
    }

    fn_name.contains("RangeBounds")
        || fn_name.contains("RangeInclusive")
        || fn_name.contains("ops::range::Range")
}

/// Check if a function is a slice accessor method with a dedicated CHC stub.
///
/// `slice::first()` has a semantic CHC stub (`SliceFirst`) that produces
/// canonical encodings. If inlined, the body produces representations that
/// diverge from promoted constant encodings (e.g., ZST `&()` address mismatch).
/// Part of #4113.
pub(super) fn is_handler_backed_slice_accessor(fn_name: &str) -> bool {
    if !fn_name.ends_with("::first") {
        return false;
    }
    (fn_name.contains("slice::") || fn_name.contains("<["))
        && !fn_name.contains("HashMap")
        && !fn_name.contains("BTreeMap")
        && !fn_name.contains("BTreeSet")
        && !fn_name.contains("HashSet")
        && !fn_name.contains("Vec")
        && !fn_name.contains("String")
}

/// `kani::any::<char>()` must reach the AY codegen handler, not be inlined.
///
/// `Arbitrary for char` is written in Rust as
///
/// ```ignore
/// let val = u32::any();
/// assume(val <= 0xD7FF || (val >= 0xE000 && val <= 0x10FFFF));
/// unsafe { char::from_u32_unchecked(val) }
/// ```
///
/// Inlining that hands codegen a `from_u32_unchecked` it does not model, so the
/// constrained `val` is dropped and the resulting `char` is a free 32-bit
/// value. Every harness taking a `char` was then explored over impossible
/// inputs:
///
/// ```ignore
/// let c: char = kani::any();
/// assert!(c as u32 <= 0x10FFFF);   // FAILED — no char can exceed this
/// ```
///
/// Codegen already knows how to do this correctly: `codegen_kani_any` emits a
/// fresh symbolic value and `assert_char_validity_for_ty` constrains it to the
/// two legal ranges — the same constraint the library body states, applied
/// where it cannot be lost. Keeping the call intact is what lets that run, the
/// same reason raw-compatible arrays are held back below.
pub(super) fn any_model_char(fn_args: &GenericArgs) -> bool {
    fn_args
        .0
        .iter()
        .find_map(|arg| match arg {
            GenericArgKind::Type(ty) => Some(*ty),
            _ => None,
        })
        .is_some_and(|ty| matches!(ty.kind(), TyKind::RigidTy(RigidTy::Char)))
}

/// `kani::any::<NonZeroX>()` must reach the AY codegen handler, for the same
/// reason as [`any_model_char`].
///
/// `Arbitrary for NonZeroU8` and friends are written as
///
/// ```ignore
/// let val = u8::any();
/// assume(val != 0);
/// unsafe { NonZeroU8::new_unchecked(val) }
/// ```
///
/// Inlining hands codegen a `new_unchecked` it does not model, the `assume` is
/// dropped with the value it constrained, and the niche type admits the one
/// value it exists to exclude:
///
/// ```ignore
/// let n: NonZeroU8 = kani::any();
/// assert!(n.get() != 0);          // FAILED
/// ```
///
/// `assert_nonzero_validity_for_ty` applies exactly this constraint when the
/// call reaches codegen intact.
pub(super) fn any_model_nonzero(fn_args: &GenericArgs) -> bool {
    fn_args
        .0
        .iter()
        .find_map(|arg| match arg {
            GenericArgKind::Type(ty) => Some(*ty),
            _ => None,
        })
        .is_some_and(|ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, _)) => def.trimmed_name() == "NonZero",
            _ => false,
        })
}

pub(super) fn any_model_raw_compatible_array(fn_args: &GenericArgs) -> bool {
    fn_args
        .0
        .iter()
        .find_map(|arg| match arg {
            GenericArgKind::Type(ty) => Some(*ty),
            _ => None,
        })
        .is_some_and(is_raw_compatible_any_array_ty)
}

fn is_raw_compatible_any_array_ty(ty: rustc_public::ty::Ty) -> bool {
    let TyKind::RigidTy(RigidTy::Array(elem_ty, _)) = ty.kind() else {
        return false;
    };
    is_raw_compatible_any_elem_ty(elem_ty)
}

fn is_raw_compatible_any_elem_ty(ty: rustc_public::ty::Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(RigidTy::Bool)
            | TyKind::RigidTy(RigidTy::Int(
                IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I64 | IntTy::I128 | IntTy::Isize
            ))
            | TyKind::RigidTy(RigidTy::Uint(
                UintTy::U8 | UintTy::U16 | UintTy::U32 | UintTy::U64 | UintTy::U128 | UintTy::Usize
            ))
            | TyKind::RigidTy(RigidTy::Float(
                FloatTy::F16 | FloatTy::F32 | FloatTy::F64 | FloatTy::F128
            ))
    )
}
