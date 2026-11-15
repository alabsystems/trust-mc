// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The loops Kani runs to compare a wrapper of values with `==`, for the
//! comparisons both lanes model as one value comparison.
//!
//! `Option`, `Result` and `Box`, references and tuples compare their parts
//! with no loop of their own (`Option::eq` is a `match`, `core/src/option.rs`;
//! a reference compares its pointees; a tuple its fields in turn). A part that
//! is an array `[P; N]` of a primitive or unit `P` runs Kani's `memcmp`, one
//! pass per byte (`N * max(size_of::<P>(), 1)`, the bound both lanes already
//! use for a bare array); a `str`, slice, `Vec` or `String` part runs a loop as
//! long as its length. The BMC lane checked none of these, so
//! `Some([1u16, 2, 3, 4]) == Some([1, 2, 3, 4])` and `Some("hello") ==
//! Some("hello")` under `#[kani::unwind(3)]` verified clean where Kani fails
//! `unwinding assertion loop 0`, and the CHC lane had no bound for them, so
//! `Some([1u8, 2, 3, 4]) == ..` under `unwind(5)`, which Kani proves, failed
//! closed (walker fail-closed review, round 1 of the repair after the merge
//! with main; `model_call_unwind_wrapped_eq_dual.rs`).
//!
//! The loops stop early, so the passes they take depend on the data (round 2;
//! measured on Kani, `probes/cal1_cmp_exit.rs`): `memcmp` returns at the first
//! differing byte, the element loop of a slice comparison (floats, and the
//! array or slice of any element that is not bytewise-comparable) at the first
//! differing element, and a `str`, slice or `Vec` comparison runs no loop at
//! all when the lengths differ. Each loop's unwinding assertion fails exactly
//! when it completes `U` passes: when it has at least `U` units (bytes or
//! elements) and the first `U` compare equal. [`compare_reach`] states that
//! condition over the two values; a float array runs one pass per ELEMENT,
//! not per byte.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::ty::{FloatTy, GenericArgKind, RigidTy, Ty, TyKind};

use crate::codegen_ay::types::POINTER_WIDTH;

/// Recursion bound for nested types.
const MAX_COMPARE_TYPE_DEPTH: usize = 8;

/// What the loops of a `==` on a type are.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay) enum CompareLoops {
    /// It runs no loop.
    LoopFree,
    /// Every loop it runs takes at most this many passes.
    AtMost(u64),
    /// It runs a loop as long as a `str`, slice, `Vec` or `String` part.
    LengthOfAPart,
    /// A type whose comparison is not one of the library's above.
    Unknown,
}

impl CompareLoops {
    fn join(self, other: Self) -> Self {
        use CompareLoops::*;
        match (self, other) {
            (Unknown, _) | (_, Unknown) => Unknown,
            (LengthOfAPart, _) | (_, LengthOfAPart) => LengthOfAPart,
            (AtMost(a), AtMost(b)) => AtMost(a.max(b)),
            (AtMost(a), LoopFree) | (LoopFree, AtMost(a)) => AtMost(a),
            (LoopFree, LoopFree) => LoopFree,
        }
    }

    /// The bound as a pass count: `0` for no loop.
    pub(in crate::codegen_ay) fn constant_bound(self) -> Option<u64> {
        match self {
            CompareLoops::LoopFree => Some(0),
            CompareLoops::AtMost(n) => Some(n),
            CompareLoops::LengthOfAPart | CompareLoops::Unknown => None,
        }
    }
}

/// Is `ty` one of the wrappers this module reads (`Option`, `Result`, `Box`,
/// a reference or a non-empty tuple)? The array, slice, `str` and `Vec`
/// comparisons themselves have their own rows in each lane.
pub(in crate::codegen_ay) fn is_compared_wrapper(ty: Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(..)) => true,
        TyKind::RigidTy(RigidTy::Tuple(tys)) => !tys.is_empty(),
        TyKind::RigidTy(RigidTy::Adt(def, _)) => {
            library_wrapper(&def.name()) || has_derived_partial_eq(def)
        }
        _ => false,
    }
}

/// Is `def` a type of the crate under verification whose `PartialEq` is
/// `#[derive(PartialEq)]`'s? Only the derive implements
/// `StructuralPartialEq`, whose implementation by hand is unstable
/// (`core::marker`). The derived `eq` compares the fields in order, each with
/// its own `==`, after the discriminant for an enum: it runs no loop of its
/// own, so its loops are its fields'. Without it `Some(S { a: [1u8, 2, 3, 4] })
/// == ..` under `unwind(6)` failed closed where main and Kani prove it
/// (walker fail-closed review, round 2 of the repair after the merge with
/// main, `model_call_unwind_early_exit_dual.rs`).
fn has_derived_partial_eq(def: rustc_public::ty::AdtDef) -> bool {
    let krate = def.krate();
    if !krate.is_local {
        return false;
    }
    krate.trait_impls().iter().any(|imp| {
        let trait_ref = imp.trait_impl().value;
        trait_ref.def_id.name().ends_with("marker::StructuralPartialEq")
            && matches!(
                trait_ref.self_ty().kind(),
                TyKind::RigidTy(RigidTy::Adt(self_def, _)) if self_def == def
            )
    })
}

/// The loops of `==` on `ty` (see the module docs); `size_of` is the lane's
/// layout query, in bytes.
pub(in crate::codegen_ay) fn compare_loops(
    ty: Ty,
    size_of: &dyn Fn(Ty) -> Option<u64>,
) -> CompareLoops {
    go(ty, size_of, 0)
}

fn go(ty: Ty, size_of: &dyn Fn(Ty) -> Option<u64>, depth: usize) -> CompareLoops {
    if depth > MAX_COMPARE_TYPE_DEPTH {
        return CompareLoops::Unknown;
    }
    match ty.kind() {
        TyKind::RigidTy(
            RigidTy::Bool | RigidTy::Char | RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_),
        ) => CompareLoops::LoopFree,
        TyKind::RigidTy(RigidTy::Tuple(tys)) => tys
            .iter()
            .map(|ty| go(*ty, size_of, depth + 1))
            .fold(CompareLoops::LoopFree, CompareLoops::join),
        TyKind::RigidTy(RigidTy::Array(elem, len))
            if matches!(elem.kind(), TyKind::RigidTy(RigidTy::Float(_))) =>
        {
            // Floats are not bytewise-comparable: `SpecArrayEq`'s default
            // compares the slices, one pass per element.
            match len.eval_target_usize().ok() {
                Some(0) => CompareLoops::LoopFree,
                Some(passes) => CompareLoops::AtMost(passes),
                None => CompareLoops::Unknown,
            }
        }
        TyKind::RigidTy(RigidTy::Array(elem, len)) => {
            let primitive_or_unit = matches!(
                elem.kind(),
                TyKind::RigidTy(
                    RigidTy::Bool
                        | RigidTy::Char
                        | RigidTy::Int(_)
                        | RigidTy::Uint(_)
                        | RigidTy::Float(_)
                )
            ) || matches!(elem.kind(), TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty());
            if !primitive_or_unit {
                return CompareLoops::Unknown;
            }
            let (Some(len), Some(bytes)) = (len.eval_target_usize().ok(), size_of(elem)) else {
                return CompareLoops::Unknown;
            };
            match len.checked_mul(bytes.max(1)) {
                Some(0) => CompareLoops::LoopFree,
                Some(passes) => CompareLoops::AtMost(passes),
                None => CompareLoops::Unknown,
            }
        }
        TyKind::RigidTy(RigidTy::Str | RigidTy::Slice(_)) => CompareLoops::LengthOfAPart,
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => go(inner, size_of, depth + 1),
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let name = def.name();
            if matches!(
                name.as_str(),
                "std::vec::Vec"
                    | "alloc::vec::Vec"
                    | "std::string::String"
                    | "alloc::string::String"
            ) {
                return CompareLoops::LengthOfAPart;
            }
            if !library_wrapper(&name) {
                if !has_derived_partial_eq(def) {
                    return CompareLoops::Unknown;
                }
                // The derived `eq`: the fields of each variant, in turn.
                let mut loops = CompareLoops::LoopFree;
                for variant in def.variants_iter() {
                    for field in variant.fields() {
                        let Some(field_ty) = super::mono_ty::field_ty(&field, &args) else {
                            return CompareLoops::Unknown;
                        };
                        loops = loops.join(go(field_ty, size_of, depth + 1));
                    }
                }
                return loops;
            }
            // The compared parts: `Option<T>` and `Box<T, A>` compare their
            // `T` (never the allocator), `Result<T, E>` its `T` or its `E`.
            let parts = if name.ends_with("Result") { 2 } else { 1 };
            args.0
                .iter()
                .filter_map(|arg| match arg {
                    GenericArgKind::Type(ty) => Some(*ty),
                    _ => None,
                })
                .take(parts)
                .map(|ty| go(ty, size_of, depth + 1))
                .fold(CompareLoops::LoopFree, CompareLoops::join)
        }
        _ => CompareLoops::Unknown,
    }
}

fn library_wrapper(name: &str) -> bool {
    matches!(
        name,
        "std::option::Option"
            | "core::option::Option"
            | "std::result::Result"
            | "core::result::Result"
            | "std::boxed::Box"
            | "alloc::boxed::Box"
    )
}

/// The most leading units [`compare_reach`] compares one by one.
const MAX_REACH_UNITS: u64 = 256;

/// The most elements [`value_eq`] compares one by one.
const MAX_EQ_ELEMS: u64 = 64;

/// Whether the loops Kani runs for `a == b`, two values of type `ty`, reach
/// Kani's unwinding assertion under `#[kani::unwind(unwind)]` (see the module
/// docs).
#[derive(Clone, Debug)]
pub(in crate::codegen_ay) struct CompareReach {
    /// True exactly when some loop completes `unwind` passes, or, when
    /// `exact` is false, implied by that.
    pub(in crate::codegen_ay) reaches: Expr,
    /// The condition is Kani's own; otherwise it over-approximates it (a
    /// tuple part whose equality the lane cannot state is read as equal).
    pub(in crate::codegen_ay) exact: bool,
}

/// [`CompareReach`] for `a == b` on `ty`, or `None` for a type or a value
/// shape this does not read (the caller keeps its data-independent bound).
/// `a` and `b` are the compared values themselves (for a `str` or slice, the
/// lane's slice datatype). `size_of` is the lane's layout query, in bytes.
pub(in crate::codegen_ay) fn compare_reach(
    ty: Ty,
    a: &Expr,
    b: &Expr,
    unwind: u64,
    size_of: &dyn Fn(Ty) -> Option<u64>,
) -> Option<CompareReach> {
    if unwind == 0 || unwind > MAX_REACH_UNITS {
        return None;
    }
    let (reaches, exact) = reach(ty, a, b, unwind, size_of, 0)?;
    Some(CompareReach { reaches, exact })
}

/// [`CompareReach`] for `raw_eq::<T>(a, b)` (Kani's `memcmp` over
/// `size_of::<T>()` bytes, whatever `T`'s own `==` does): an array of
/// bytewise-comparable elements, or one such element; `None` otherwise.
pub(in crate::codegen_ay) fn raw_eq_reach(
    ty: Ty,
    a: &Expr,
    b: &Expr,
    unwind: u64,
    size_of: &dyn Fn(Ty) -> Option<u64>,
) -> Option<CompareReach> {
    if unwind == 0 || unwind > MAX_REACH_UNITS || a.sort() != b.sort() {
        return None;
    }
    if is_bytewise_primitive(ty) {
        let size = size_of(ty)?;
        if size < unwind {
            return Some(CompareReach { reaches: Expr::bool_const(false), exact: true });
        }
        let width = a.sort().bitvec_width()?;
        if u64::from(width) != size * 8 {
            return None;
        }
        let high = u32::try_from(unwind * 8 - 1).ok()?;
        let reaches = a.clone().extract(high, 0).eq(b.clone().extract(high, 0));
        return Some(CompareReach { reaches, exact: true });
    }
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Array(elem, _)) if is_bytewise_primitive(elem) => {
            compare_reach(ty, a, b, unwind, size_of)
        }
        _ => None,
    }
}

/// Is `expr` the constant `false`?
pub(in crate::codegen_ay) fn is_const_false(expr: &Expr) -> bool {
    matches!(expr.value(), ay_bindings::ExprValue::BoolConst(false))
}

fn is_bytewise_primitive(ty: Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(RigidTy::Bool | RigidTy::Char | RigidTy::Int(_) | RigidTy::Uint(_))
    )
}

fn is_float(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Float(_)))
}

fn is_unit(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty())
}

fn bv(n: u64) -> Expr {
    Expr::bitvec_const(n, POINTER_WIDTH)
}

fn reach(
    ty: Ty,
    a: &Expr,
    b: &Expr,
    unwind: u64,
    size_of: &dyn Fn(Ty) -> Option<u64>,
    depth: usize,
) -> Option<(Expr, bool)> {
    if depth > MAX_COMPARE_TYPE_DEPTH || a.sort() != b.sort() {
        return None;
    }
    let never = || Some((Expr::bool_const(false), true));
    match ty.kind() {
        TyKind::RigidTy(
            RigidTy::Bool | RigidTy::Char | RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_),
        ) => never(),
        TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty() => never(),
        TyKind::RigidTy(RigidTy::Array(elem, len)) => {
            let n = len.eval_target_usize().ok()?;
            a.sort().array_sort()?;
            if is_bytewise_primitive(elem) {
                // Kani's `memcmp` over the array's bytes.
                let size = size_of(elem)?;
                if n.checked_mul(size)? < unwind {
                    return never();
                }
                Some((prefix_bytes_equal(a, b, size, unwind)?, true))
            } else if is_float(elem) {
                // The slice comparison's element loop.
                if n < unwind {
                    return never();
                }
                let mut all = Expr::bool_const(true);
                for i in 0..unwind {
                    all = all.and(float_eq(&array_elem(a, i)?, &array_elem(b, i)?)?);
                }
                Some((all, true))
            } else if is_unit(elem) {
                Some((Expr::bool_const(n >= unwind), true))
            } else {
                None
            }
        }
        TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Str | RigidTy::Slice(_))) =>
        {
            // A wide reference held in a wrapper is the lane's slice value.
            reach(inner, a, b, unwind, size_of, depth + 1)
        }
        TyKind::RigidTy(RigidTy::Str) => slice_reach(
            None,
            &SliceView::of_datatype(a)?,
            &SliceView::of_datatype(b)?,
            unwind,
            size_of,
        ),
        TyKind::RigidTy(RigidTy::Slice(elem)) => slice_reach(
            Some(elem),
            &SliceView::of_datatype(a)?,
            &SliceView::of_datatype(b)?,
            unwind,
            size_of,
        ),
        TyKind::RigidTy(RigidTy::Tuple(tys)) => {
            let fields = datatype_fields(a, tys.len())?;
            let mut equal_so_far = Expr::bool_const(true);
            let mut exact = true;
            let mut any = Expr::bool_const(false);
            for (k, part_ty) in tys.iter().enumerate() {
                let (a_k, b_k) = (fields.select(a, k)?, fields.select(b, k)?);
                let (part, part_exact) = reach(*part_ty, &a_k, &b_k, unwind, size_of, depth + 1)?;
                exact &= part_exact;
                if !is_const_false(&part) {
                    any = any.or(equal_so_far.clone().and(part));
                }
                match value_eq(*part_ty, &a_k, &b_k, size_of, depth + 1) {
                    Some(eq) => equal_so_far = equal_so_far.and(eq),
                    // Read as equal: the later parts' loops may then run.
                    None => exact = false,
                }
            }
            Some((any, exact))
        }
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let name = def.name();
            let type_args: Vec<Ty> = args
                .0
                .iter()
                .filter_map(|arg| match arg {
                    GenericArgKind::Type(ty) => Some(*ty),
                    _ => None,
                })
                .collect();
            match name.as_str() {
                "std::option::Option" | "core::option::Option" => {
                    let payload_ty = *type_args.first()?;
                    let view = OptionView::of(a)?;
                    let (a_p, b_p) = (view.payload(a)?, view.payload(b)?);
                    let (part, exact) = reach(payload_ty, &a_p, &b_p, unwind, size_of, depth + 1)?;
                    if is_const_false(&part) {
                        return never();
                    }
                    Some((view.is_some(a)?.and(view.is_some(b)?).and(part), exact))
                }
                "std::result::Result" | "core::result::Result" => {
                    let (ok_ty, err_ty) = (*type_args.first()?, *type_args.get(1)?);
                    let view = ResultView::of(a)?;
                    let (a_ok, b_ok) = (view.payload(a, true)?, view.payload(b, true)?);
                    let (a_err, b_err) = (view.payload(a, false)?, view.payload(b, false)?);
                    let (ok, ok_exact) = reach(ok_ty, &a_ok, &b_ok, unwind, size_of, depth + 1)?;
                    let (err, err_exact) =
                        reach(err_ty, &a_err, &b_err, unwind, size_of, depth + 1)?;
                    let exact = ok_exact && err_exact;
                    let both_ok = view.is_variant(a, true)?.and(view.is_variant(b, true)?);
                    let both_err = view.is_variant(a, false)?.and(view.is_variant(b, false)?);
                    Some(match (is_const_false(&ok), is_const_false(&err)) {
                        (true, true) => (Expr::bool_const(false), true),
                        (true, false) => (both_err.and(err), exact),
                        (false, true) => (both_ok.and(ok), exact),
                        (false, false) => (both_ok.and(ok).or(both_err.and(err)), exact),
                    })
                }
                "std::vec::Vec" | "alloc::vec::Vec" => slice_reach(
                    Some(*type_args.first()?),
                    &SliceView::of_datatype(a)?,
                    &SliceView::of_datatype(b)?,
                    unwind,
                    size_of,
                ),
                "std::string::String" | "alloc::string::String" => slice_reach(
                    None,
                    &SliceView::of_datatype(a)?,
                    &SliceView::of_datatype(b)?,
                    unwind,
                    size_of,
                ),
                _ => None,
            }
        }
        _ => None,
    }
}

/// One side of a `str`, slice or `Vec` comparison: its length, and its
/// elements as `data[offset + i]`.
#[derive(Clone, Debug)]
pub(in crate::codegen_ay) struct SliceView {
    pub(in crate::codegen_ay) len: Expr,
    pub(in crate::codegen_ay) data: Expr,
    pub(in crate::codegen_ay) offset: Expr,
}

impl SliceView {
    /// A slice, `str` or `Vec` value of the lanes' datatype shape: `fld_len`
    /// and `fld_data`, the data indexed from the slice's own start (the BMC
    /// lane's views are; a shifted sub-slice reaching a comparison fails
    /// closed there, `bmc_subslice_consumer_fail_closed`).
    pub(in crate::codegen_ay) fn of_datatype(value: &Expr) -> Option<Self> {
        Some(Self {
            len: field_by_name(value, "fld_len")?,
            data: field_by_name(value, "fld_data")?,
            offset: bv(0),
        })
    }
}

/// Rust's `==` on two slice views whose elements' `==` is their encodings'
/// equality: equal lengths, and equal elements at every index below them,
/// `len_a == len_b && forall i . i < len_a => a[off_a + i] == b[off_b + i]`
/// with `i` bound as `bound_name`. `None` when the views are not of one
/// shape, or an element is itself encoded with an SMT array (its `=` would
/// be extensional over indices Rust never reads).
///
/// Never the two views' datatype equality: that compares `fld_ptr`, and the
/// whole `fld_data` array past the length, so `[1i32, 2]` and `[1, 2, 0]`
/// compared by their element arrays could come out EQUAL and two equal
/// slices of distinct allocations UNEQUAL
/// (`tools/soundness-duals/slice_eq_length_dual.rs`).
///
/// `known_len` is a length the caller has established one of the two views
/// to have (read from the constructor that built it). Up to
/// `MAX_EQ_ELEMS` the elements are then compared one by one,
/// `len_a == len_b && a[off_a] == b[off_b] && ...` for the `k` indices below
/// it: the same predicate, as `len_a == len_b` forces both lengths to `k`,
/// and quantifier-free. AY answers `unknown` for a satisfiable query that
/// holds the quantified form, so a reachable violation behind an `==` that
/// holds (`equal_d2_safe`'s dual, `assert!(a != b)` on equal slices) was
/// never reported.
pub(in crate::codegen_ay) fn slice_view_eq(
    a: &SliceView,
    b: &SliceView,
    bound_name: &str,
    known_len: Option<u64>,
) -> Option<Expr> {
    if a.len.sort().bitvec_width() != Some(POINTER_WIDTH)
        || a.len.sort() != b.len.sort()
        || a.data.sort() != b.data.sort()
        || a.offset.sort().bitvec_width() != Some(POINTER_WIDTH)
        || b.offset.sort().bitvec_width() != Some(POINTER_WIDTH)
    {
        return None;
    }
    let array = a.data.sort().array_sort()?;
    if array.index_sort.bitvec_width() != Some(POINTER_WIDTH)
        || sort_holds_array(&array.element_sort, MAX_COMPARE_TYPE_DEPTH)
    {
        return None;
    }
    let lengths = a.len.clone().eq(b.len.clone());
    if let Some(k) = known_len.filter(|k| *k <= MAX_EQ_ELEMS) {
        let at = |view: &SliceView, i: u64| view.data.clone().select(view.offset.clone().bvadd(bv(i)));
        return Some((0..k).fold(lengths, |all, i| all.and(at(a, i).eq(at(b, i)))));
    }
    let index_sort = ay_bindings::Sort::bitvec(POINTER_WIDTH);
    let i = Expr::var(bound_name, index_sort.clone());
    let at = |view: &SliceView| view.data.clone().select(view.offset.clone().bvadd(i.clone()));
    let body = i.clone().bvult(a.len.clone()).implies(at(a).eq(at(b)));
    let elements = Expr::forall(vec![(bound_name.to_string(), index_sort)], body);
    Some(lengths.and(elements))
}

/// [`CompareReach`] for a `str`, slice or `Vec` comparison of elements
/// `elem` (`None` for `str`): no loop when the lengths differ, else the units
/// of the first `unwind` bytes (bytewise elements, `compare_bytes`) or
/// elements (floats and units, the element loop) compare equal.
pub(in crate::codegen_ay) fn slice_compare_reach(
    elem: Option<Ty>,
    a: &SliceView,
    b: &SliceView,
    unwind: u64,
    size_of: &dyn Fn(Ty) -> Option<u64>,
) -> Option<CompareReach> {
    if unwind == 0 || unwind > MAX_REACH_UNITS {
        return None;
    }
    let (reaches, exact) = slice_reach(elem, a, b, unwind, size_of)?;
    Some(CompareReach { reaches, exact })
}

fn slice_reach(
    elem: Option<Ty>,
    a: &SliceView,
    b: &SliceView,
    unwind: u64,
    size_of: &dyn Fn(Ty) -> Option<u64>,
) -> Option<(Expr, bool)> {
    if a.len.sort().bitvec_width() != Some(POINTER_WIDTH)
        || a.len.sort() != b.len.sort()
        || a.data.sort() != b.data.sort()
        || a.offset.sort().bitvec_width() != Some(POINTER_WIDTH)
        || b.offset.sort().bitvec_width() != Some(POINTER_WIDTH)
    {
        return None;
    }
    let index_width = a.data.sort().array_sort()?.index_sort.bitvec_width()?;
    if index_width != POINTER_WIDTH {
        return None;
    }
    let at = |view: &SliceView, i: u64| view.data.clone().select(view.offset.clone().bvadd(bv(i)));
    let lengths =
        |min_len: u64| a.len.clone().eq(b.len.clone()).and(a.len.clone().bvuge(bv(min_len)));
    let elem_kind = match elem {
        None => Some(1),
        Some(elem) if is_bytewise_primitive(elem) => size_of(elem).filter(|&size| size > 0),
        Some(elem) if is_float(elem) || is_unit(elem) => None,
        Some(_) => return None,
    };
    match elem_kind {
        Some(size) => {
            // `compare_bytes` over the bytes, after the length check.
            let (whole, rest) = (unwind / size, unwind % size);
            let mut cond = lengths(unwind.div_ceil(size));
            for i in 0..whole {
                cond = cond.and(at(a, i).eq(at(b, i)));
            }
            if rest > 0 {
                let (x, y) = (at(a, whole), at(b, whole));
                if u64::from(x.sort().bitvec_width()?) != size * 8 {
                    return None;
                }
                let high = u32::try_from(rest * 8 - 1).ok()?;
                cond = cond.and(x.extract(high, 0).eq(y.extract(high, 0)));
            }
            Some((cond, true))
        }
        None => {
            // The element loop: one pass per element.
            let elem = elem?;
            let mut cond = lengths(unwind);
            if is_float(elem) {
                for i in 0..unwind {
                    cond = cond.and(float_eq(&at(a, i), &at(b, i))?);
                }
            }
            Some((cond, true))
        }
    }
}

/// The first `unwind` bytes of two arrays of `size`-byte bytewise elements
/// (little-endian, as `memcmp` reads them) are equal.
fn prefix_bytes_equal(a: &Expr, b: &Expr, size: u64, unwind: u64) -> Option<Expr> {
    let size = size.max(1);
    let (whole, rest) = (unwind / size, unwind % size);
    let mut all = Expr::bool_const(true);
    for i in 0..whole {
        all = all.and(array_elem(a, i)?.eq(array_elem(b, i)?));
    }
    if rest > 0 {
        let (x, y) = (array_elem(a, whole)?, array_elem(b, whole)?);
        let width = x.sort().bitvec_width()?;
        if u64::from(width) != size * 8 {
            return None;
        }
        let high = u32::try_from(rest * 8 - 1).ok()?;
        all = all.and(x.extract(high, 0).eq(y.extract(high, 0)));
    }
    Some(all)
}

fn array_elem(array: &Expr, i: u64) -> Option<Expr> {
    let index_width = array.sort().array_sort()?.index_sort.bitvec_width()?;
    Some(array.clone().select(Expr::bitvec_const(i, index_width)))
}

/// `x == y` for two floats as Rust compares them: NaN equals nothing, and
/// `+0 == -0`. A floating-point sort compares with `fp.eq`; a bit pattern
/// (`f32` / `f64` as a 32- or 64-bit vector) by its bits.
fn float_eq(x: &Expr, y: &Expr) -> Option<Expr> {
    if x.sort() != y.sort() {
        return None;
    }
    if x.sort().is_floating_point() {
        return Some(x.clone().fp_eq(y.clone()));
    }
    let (abs_mask, infinity): (u128, u128) = match x.sort().bitvec_width()? {
        32 => (0x7fff_ffff, 0x7f80_0000),
        64 => (0x7fff_ffff_ffff_ffff, 0x7ff0_0000_0000_0000),
        _ => return None,
    };
    let width = x.sort().bitvec_width()?;
    let abs = |v: &Expr| v.clone().bvand(Expr::bitvec_const(abs_mask, width));
    let nan = |v: &Expr| abs(v).bvugt(Expr::bitvec_const(infinity, width));
    let zero = Expr::bitvec_const(0u64, width);
    let both_zero = abs(x).eq(zero.clone()).and(abs(y).eq(zero));
    Some(nan(x).not().and(nan(y).not()).and(x.clone().eq(y.clone()).or(both_zero)))
}

/// `a == b` on `ty`, as Rust's `PartialEq` decides it, or `None`.
fn value_eq(
    ty: Ty,
    a: &Expr,
    b: &Expr,
    size_of: &dyn Fn(Ty) -> Option<u64>,
    depth: usize,
) -> Option<Expr> {
    if depth > MAX_COMPARE_TYPE_DEPTH || a.sort() != b.sort() {
        return None;
    }
    // A type whose `==` is its encoding's equality, encoded without an SMT
    // array (whose equality is extensional over indices Rust never reads).
    if eq_is_encoding_eq(ty) && !sort_holds_array(a.sort(), MAX_COMPARE_TYPE_DEPTH) {
        return Some(a.clone().eq(b.clone()));
    }
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Bool | RigidTy::Char | RigidTy::Int(_) | RigidTy::Uint(_)) => {
            Some(a.clone().eq(b.clone()))
        }
        TyKind::RigidTy(RigidTy::Float(FloatTy::F32 | FloatTy::F64)) => float_eq(a, b),
        TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty() => Some(Expr::bool_const(true)),
        TyKind::RigidTy(RigidTy::Array(elem, len)) => {
            let n = len.eval_target_usize().ok()?;
            if n > MAX_EQ_ELEMS {
                return None;
            }
            let mut all = Expr::bool_const(true);
            for i in 0..n {
                let (x, y) = (array_elem(a, i)?, array_elem(b, i)?);
                all = all.and(value_eq(elem, &x, &y, size_of, depth + 1)?);
            }
            Some(all)
        }
        TyKind::RigidTy(RigidTy::Tuple(tys)) => {
            let fields = datatype_fields(a, tys.len())?;
            let mut all = Expr::bool_const(true);
            for (k, part_ty) in tys.iter().enumerate() {
                let (x, y) = (fields.select(a, k)?, fields.select(b, k)?);
                all = all.and(value_eq(*part_ty, &x, &y, size_of, depth + 1)?);
            }
            Some(all)
        }
        TyKind::RigidTy(RigidTy::Adt(def, args))
            if matches!(def.name().as_str(), "std::option::Option" | "core::option::Option") =>
        {
            let payload_ty = args.0.iter().find_map(|arg| match arg {
                GenericArgKind::Type(ty) => Some(*ty),
                _ => None,
            })?;
            let view = OptionView::of(a)?;
            let (x, y) = (view.payload(a)?, view.payload(b)?);
            let payload_eq = value_eq(payload_ty, &x, &y, size_of, depth + 1)?;
            let (some_a, some_b) = (view.is_some(a)?, view.is_some(b)?);
            Some(
                some_a
                    .clone()
                    .not()
                    .and(some_b.clone().not())
                    .or(some_a.and(some_b).and(payload_eq)),
            )
        }
        TyKind::RigidTy(RigidTy::Adt(def, args))
            if matches!(def.name().as_str(), "std::result::Result" | "core::result::Result") =>
        {
            let mut parts = args.0.iter().filter_map(|arg| match arg {
                GenericArgKind::Type(ty) => Some(*ty),
                _ => None,
            });
            let (ok_ty, err_ty) = (parts.next()?, parts.next()?);
            let view = ResultView::of(a)?;
            let ok_eq = value_eq(
                ok_ty,
                &view.payload(a, true)?,
                &view.payload(b, true)?,
                size_of,
                depth + 1,
            )?;
            let err_eq = value_eq(
                err_ty,
                &view.payload(a, false)?,
                &view.payload(b, false)?,
                size_of,
                depth + 1,
            )?;
            let both_ok = view.is_variant(a, true)?.and(view.is_variant(b, true)?);
            let both_err = view.is_variant(a, false)?.and(view.is_variant(b, false)?);
            Some(both_ok.and(ok_eq).or(both_err.and(err_eq)))
        }
        _ => None,
    }
}

/// Does an SMT array occur in `sort` (conservative past `depth`)?
fn sort_holds_array(sort: &ay_bindings::Sort, depth: usize) -> bool {
    if depth == 0 {
        return true;
    }
    match sort.inner() {
        ay_bindings::SortInner::Array(_) => true,
        ay_bindings::SortInner::Datatype(dt) => dt
            .constructors
            .iter()
            .flat_map(|ctor| ctor.fields.iter())
            .any(|field| sort_holds_array(&field.sort, depth - 1)),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// When a lane may decide `==` by the equality of two encodings.
//
// Both lanes encode a float as its bit pattern, a reference or a pointer
// wrapper (`Box`, `Vec`, `String`) as an address, and any value as the bits of
// its fields. SMT equality of two such encodings is Rust's `==` only when
// every comparison under it compares bits: a `bool`, a `char`, an integer or
// `()`, through arrays, tuples and `#[derive(PartialEq)]` types. It is not for
// a float (`NaN != NaN`, `+0.0 == -0.0`), for a reference or a pointer
// wrapper (`==` compares what they point at), or for a hand-written
// `PartialEq`. The CHC lane's array, slice, `Vec` and `Option` comparisons,
// and the BMC lane's `PartialEq` calls, compared the encodings for every
// element type: `[0.0f32] == [-0.0f32]`, `Some(0.0f32) == Some(-0.0)`,
// `[&x] == [&y]` with `x == y`, and `[Parity(1)] == [Parity(3)]` under a
// `PartialEq` that compares parities, all of which Kani proves, failed with
// certified counterexamples, and `[f32::NAN] == [f32::NAN]` verified clean
// where Kani fails (walker fail-closed review, round 3 of the repair after
// the merge with main; `value_eq_semantics_dual.rs`).
// ---------------------------------------------------------------------------

/// Is Rust's `==` on two values of `ty` the equality of their encodings? See
/// the section comment. `ty` must be monomorphic; anything this does not
/// classify answers `false`.
pub(in crate::codegen_ay) fn eq_is_encoding_eq(ty: Ty) -> bool {
    encoding_eq(ty, 0)
}

fn encoding_eq(ty: Ty, depth: usize) -> bool {
    if depth > MAX_COMPARE_TYPE_DEPTH {
        return false;
    }
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Bool | RigidTy::Char | RigidTy::Int(_) | RigidTy::Uint(_)) => true,
        TyKind::RigidTy(RigidTy::Tuple(tys)) => tys.iter().all(|t| encoding_eq(*t, depth + 1)),
        TyKind::RigidTy(RigidTy::Array(elem, _)) => encoding_eq(elem, depth + 1),
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let name = def.name();
            let derived = matches!(
                name.as_str(),
                "std::option::Option"
                    | "core::option::Option"
                    | "std::result::Result"
                    | "core::result::Result"
            ) || implements_structural_partial_eq(def);
            derived
                && def.variants_iter().all(|variant| {
                    variant.fields().iter().all(|field| {
                        super::mono_ty::field_ty(field, &args)
                            .is_some_and(|t| encoding_eq(t, depth + 1))
                    })
                })
        }
        _ => false,
    }
}

/// Does `def` implement `StructuralPartialEq`, which only
/// `#[derive(PartialEq)]` (and the standard library itself) can? For a type
/// of another crate the answer is read once per crate and kept by the type's
/// path: a library crate is the same in every compilation.
fn implements_structural_partial_eq(def: rustc_public::ty::AdtDef) -> bool {
    use std::cell::RefCell;
    use std::collections::{HashMap, HashSet};
    if def.krate().is_local {
        return has_derived_partial_eq(def);
    }
    thread_local! {
        static STRUCTURAL: RefCell<HashMap<String, HashSet<String>>> =
            RefCell::new(HashMap::new());
    }
    let krate = def.krate();
    STRUCTURAL.with(|cache| {
        let mut cache = cache.borrow_mut();
        let paths = cache.entry(krate.name.clone()).or_insert_with(|| {
            krate
                .trait_impls()
                .iter()
                .filter_map(|imp| {
                    let trait_ref = imp.trait_impl().value;
                    if !trait_ref.def_id.name().ends_with("marker::StructuralPartialEq") {
                        return None;
                    }
                    match trait_ref.self_ty().kind() {
                        TyKind::RigidTy(RigidTy::Adt(self_def, _)) => Some(self_def.name()),
                        _ => None,
                    }
                })
                .collect()
        });
        paths.contains(&def.name())
    })
}

/// Rust's `a == b` on two values of `ty`, from the lane's encodings of them:
/// their equality when [`eq_is_encoding_eq`] holds (and no SMT array is in
/// the way), else built part by part (a float by its value, an array element
/// by element, a tuple, an `Option` or a `Result` by its parts). `None` for a
/// type or an encoding this does not read; the caller then leaves the
/// comparison unconstrained.
pub(in crate::codegen_ay) fn rust_value_eq(ty: Ty, a: &Expr, b: &Expr) -> Option<Expr> {
    value_eq(ty, a, b, &|_| None, 0)
}

/// The element type a sequence comparison compares, behind any references:
/// `T` for `[T]`, `[T; N]` and `Vec<T>`, `u8` for `str` and `String`.
pub(in crate::codegen_ay) fn compared_elem_ty(ty: Ty) -> Option<Ty> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => compared_elem_ty(inner),
        TyKind::RigidTy(RigidTy::Slice(elem) | RigidTy::Array(elem, _)) => Some(elem),
        TyKind::RigidTy(RigidTy::Str) => Some(Ty::unsigned_ty(rustc_public::ty::UintTy::U8)),
        TyKind::RigidTy(RigidTy::Adt(def, args)) => match def.name().as_str() {
            "std::vec::Vec" | "alloc::vec::Vec" => args.0.iter().find_map(|arg| match arg {
                GenericArgKind::Type(elem) => Some(*elem),
                _ => None,
            }),
            "std::string::String" | "alloc::string::String" => {
                Some(Ty::unsigned_ty(rustc_public::ty::UintTy::U8))
            }
            _ => None,
        },
        _ => None,
    }
}

/// The comparison a call performs, by its callee's path: `==` (negated for
/// `ne`) or an order (`PartialOrd`, `Ord`, and the slice impls they reach).
/// `None` for anything else, `raw_eq` and the other intrinsics included,
/// which compare bytes by definition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay) enum ComparisonCall {
    Eq { negated: bool },
    Order,
}

pub(in crate::codegen_ay) fn comparison_call(path: &str) -> Option<ComparisonCall> {
    if path.contains("intrinsics::") {
        return None;
    }
    let method = path.rsplit("::").next()?;
    if path.contains("cmp::PartialEq")
        || path.contains("SlicePartialEq")
        || path.contains("SpecArrayEq")
    {
        return match method {
            "eq" | "equal" | "spec_eq" => Some(ComparisonCall::Eq { negated: false }),
            "ne" | "spec_ne" => Some(ComparisonCall::Eq { negated: true }),
            _ => None,
        };
    }
    if path.contains("cmp::PartialOrd")
        || path.contains("cmp::Ord")
        || path.contains("SlicePartialOrd")
        || path.contains("SliceOrd")
    {
        return matches!(
            method,
            "lt" | "le"
                | "gt"
                | "ge"
                | "partial_cmp"
                | "cmp"
                | "max"
                | "min"
                | "clamp"
                | "partial_compare"
                | "compare"
        )
        .then_some(ComparisonCall::Order);
    }
    None
}

/// `ty` behind all its references: `==` and the orders compare pointees.
pub(in crate::codegen_ay) fn peel_refs(mut ty: Ty) -> Ty {
    for _ in 0..MAX_COMPARE_TYPE_DEPTH {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => ty = inner,
            _ => break,
        }
    }
    ty
}

/// May the lanes' comparison fast paths decide this comparison of two values
/// of `compared` (the type of the call's first argument, any references
/// included)? They compare encodings, and, for a `str`, a slice, an array or
/// a `Vec`, the encodings of its elements, so `==` needs [`eq_is_encoding_eq`]
/// of the element and, elsewhere, no float and no hand-written `PartialEq`
/// anywhere in the value; an order of a sequence needs integer elements. A
/// comparison the fast paths may not decide is built exactly
/// ([`rust_value_eq`]), walked through its own body, or left unconstrained.
pub(in crate::codegen_ay) fn comparison_is_faithful(kind: ComparisonCall, compared: Ty) -> bool {
    let compared = peel_refs(compared);
    if is_text(compared) {
        return true;
    }
    match kind {
        ComparisonCall::Eq { .. } => match sequence_elem(compared) {
            Some(elem) => eq_is_encoding_eq(elem),
            None => !reads_float_or_custom_eq(compared, 0),
        },
        ComparisonCall::Order => sequence_elem(compared).is_none_or(ord_is_encoding_ord),
    }
}

fn is_text(ty: Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Str) => true,
        TyKind::RigidTy(RigidTy::Adt(def, _)) => {
            matches!(def.name().as_str(), "std::string::String" | "alloc::string::String")
        }
        _ => false,
    }
}

/// The element of a slice, an array, a `Vec` or a `VecDeque`.
fn sequence_elem(ty: Ty) -> Option<Ty> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Slice(elem) | RigidTy::Array(elem, _)) => Some(elem),
        TyKind::RigidTy(RigidTy::Adt(def, args))
            if matches!(
                def.name().as_str(),
                "std::vec::Vec"
                    | "alloc::vec::Vec"
                    | "std::collections::VecDeque"
                    | "alloc::collections::VecDeque"
                    | "alloc::collections::vec_deque::VecDeque"
                    | "std::collections::vec_deque::VecDeque"
            ) =>
        {
            first_type_arg(&args)
        }
        _ => None,
    }
}

fn first_type_arg(args: &rustc_public::ty::GenericArgs) -> Option<Ty> {
    args.0.iter().find_map(|arg| match arg {
        GenericArgKind::Type(ty) => Some(*ty),
        _ => None,
    })
}

/// Does `==` on `ty` read a float, or call a `PartialEq` written by hand in
/// the crate under verification, or compare a sequence whose elements' `==`
/// is not their encodings'? A library type compares its type arguments
/// (`Option`, `Box`, a map, ...); a derived type its fields.
fn reads_float_or_custom_eq(ty: Ty, depth: usize) -> bool {
    if depth > MAX_COMPARE_TYPE_DEPTH {
        return true;
    }
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Float(_)) => true,
        TyKind::RigidTy(
            RigidTy::Bool
            | RigidTy::Char
            | RigidTy::Int(_)
            | RigidTy::Uint(_)
            | RigidTy::Str
            | RigidTy::Never
            | RigidTy::RawPtr(..)
            | RigidTy::FnPtr(..),
        ) => false,
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => reads_float_or_custom_eq(inner, depth + 1),
        TyKind::RigidTy(RigidTy::Array(elem, _) | RigidTy::Slice(elem)) => !eq_is_encoding_eq(elem),
        TyKind::RigidTy(RigidTy::Tuple(tys)) => {
            tys.iter().any(|t| reads_float_or_custom_eq(*t, depth + 1))
        }
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            if is_text(ty) {
                return false;
            }
            if let Some(elem) = sequence_elem(ty) {
                return !eq_is_encoding_eq(elem);
            }
            if def.krate().is_local {
                if !has_derived_partial_eq(def) {
                    return true;
                }
                return def.variants_iter().any(|variant| {
                    variant.fields().iter().any(|field| {
                        super::mono_ty::field_ty(field, &args)
                            .is_none_or(|t| reads_float_or_custom_eq(t, depth + 1))
                    })
                });
            }
            args.0.iter().any(|arg| match arg {
                GenericArgKind::Type(t) => reads_float_or_custom_eq(*t, depth + 1),
                _ => false,
            })
        }
        _ => true,
    }
}

/// Is the order of two values of `ty` the order of their integer encodings,
/// as the lanes' lexicographic array and slice orders read each element: a
/// `bool`, a `char` or an integer? A float is not (a negative float's bits
/// order above a positive one's, and `NaN` is unordered).
pub(in crate::codegen_ay) fn ord_is_encoding_ord(ty: Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(RigidTy::Bool | RigidTy::Char | RigidTy::Int(_) | RigidTy::Uint(_))
    )
}

fn field_by_name(value: &Expr, field: &str) -> Option<Expr> {
    let dt = value.sort().datatype_sort()?;
    if dt.constructors.len() != 1 {
        return None;
    }
    let f = dt.constructors[0].fields.iter().find(|f| f.name == field)?;
    value.clone().try_field_select(&dt.name, &f.name, f.sort.clone()).ok()
}

/// The fields of a one-constructor datatype of `arity` fields, in order.
struct DatatypeFields {
    name: String,
    fields: Vec<(String, ay_bindings::Sort)>,
}

fn datatype_fields(value: &Expr, arity: usize) -> Option<DatatypeFields> {
    let dt = value.sort().datatype_sort()?;
    if dt.constructors.len() != 1 || dt.constructors[0].fields.len() != arity {
        return None;
    }
    Some(DatatypeFields {
        name: dt.name.clone(),
        fields: dt.constructors[0]
            .fields
            .iter()
            .map(|f| (f.name.clone(), f.sort.clone()))
            .collect(),
    })
}

impl DatatypeFields {
    fn select(&self, value: &Expr, k: usize) -> Option<Expr> {
        let (field, sort) = self.fields.get(k)?;
        value.clone().try_field_select(&self.name, field, sort.clone()).ok()
    }
}

/// An `Option` value's datatype: `None` and a one-field `Some`.
struct OptionView {
    name: String,
    some: String,
    field: String,
    field_sort: ay_bindings::Sort,
}

impl OptionView {
    fn of(value: &Expr) -> Option<Self> {
        let dt = value.sort().datatype_sort()?;
        if dt.constructors.len() != 2 {
            return None;
        }
        let some = dt.constructors.iter().find(|ctor| ctor.fields.len() == 1)?;
        if !dt.constructors.iter().any(|ctor| ctor.fields.is_empty()) {
            return None;
        }
        Some(Self {
            name: dt.name.clone(),
            some: some.name.clone(),
            field: some.fields[0].name.clone(),
            field_sort: some.fields[0].sort.clone(),
        })
    }

    fn is_some(&self, value: &Expr) -> Option<Expr> {
        value.clone().try_is_constructor(&self.name, &self.some).ok()
    }

    fn payload(&self, value: &Expr) -> Option<Expr> {
        value.clone().try_field_select(&self.name, &self.field, self.field_sort.clone()).ok()
    }
}

/// A `Result` value's datatype: one-field `Ok` and `Err`, told apart by name.
struct ResultView {
    name: String,
    ok: (String, String, ay_bindings::Sort),
    err: (String, String, ay_bindings::Sort),
}

impl ResultView {
    fn of(value: &Expr) -> Option<Self> {
        let dt = value.sort().datatype_sort()?;
        if dt.constructors.len() != 2 || dt.constructors.iter().any(|c| c.fields.len() != 1) {
            return None;
        }
        let pick = |tag: &str| {
            let ctor = dt.constructors.iter().find(|c| c.name.contains(tag))?;
            Some((ctor.name.clone(), ctor.fields[0].name.clone(), ctor.fields[0].sort.clone()))
        };
        let (ok, err) = (pick("Ok")?, pick("Err")?);
        if ok.0 == err.0 {
            return None;
        }
        Some(Self { name: dt.name.clone(), ok, err })
    }

    fn is_variant(&self, value: &Expr, ok: bool) -> Option<Expr> {
        let ctor = if ok { &self.ok.0 } else { &self.err.0 };
        value.clone().try_is_constructor(&self.name, ctor).ok()
    }

    fn payload(&self, value: &Expr, ok: bool) -> Option<Expr> {
        let (_, field, sort) = if ok { &self.ok } else { &self.err };
        value.clone().try_field_select(&self.name, field, sort.clone()).ok()
    }
}

#[cfg(test)]
mod slice_view_eq_tests {
    use super::*;
    use ay_bindings::{ExprValue, Sort};

    fn make_view(len: Expr, data_name: &str, offset: u64) -> SliceView {
        let idx = Sort::bitvec(POINTER_WIDTH);
        let elem = Sort::bitvec(32);
        SliceView {
            len,
            data: Expr::var(data_name, Sort::array(idx, elem)),
            offset: Expr::bitvec_const(offset, POINTER_WIDTH),
        }
    }

    fn contains_forall(expr: &Expr) -> bool {
        match expr.value() {
            ExprValue::Forall { .. } => true,
            ExprValue::Not(inner) => contains_forall(inner),
            ExprValue::And(xs) | ExprValue::Or(xs) => xs.iter().any(contains_forall),
            ExprValue::Eq(a, b) | ExprValue::Implies(a, b) => {
                contains_forall(a) || contains_forall(b)
            }
            _ => false,
        }
    }

    #[test]
    fn known_length_unrolls_without_quantifier() {
        let a = make_view(Expr::bitvec_const(2u64, POINTER_WIDTH), "arr_a", 0);
        let b = make_view(Expr::bitvec_const(2u64, POINTER_WIDTH), "arr_b", 1);
        let eq = slice_view_eq(&a, &b, "__idx_0", Some(2)).expect("slice_view_eq");
        assert!(!contains_forall(&eq), "known_len <= MAX_EQ_ELEMS must be quantifier-free: {eq}");
    }

    #[test]
    fn symbolic_length_emits_bounded_forall_with_length_equality() {
        let ptr_sort = Sort::bitvec(POINTER_WIDTH);
        let a = make_view(Expr::var("len_a", ptr_sort.clone()), "arr_a", 0);
        let b = make_view(Expr::var("len_b", ptr_sort), "arr_b", 0);
        let eq = slice_view_eq(&a, &b, "__idx_1", None).expect("slice_view_eq");
        assert!(contains_forall(&eq), "symbolic length must keep bounded forall: {eq}");
    }
}
