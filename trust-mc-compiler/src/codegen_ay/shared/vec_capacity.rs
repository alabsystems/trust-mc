// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The capacity std's `RawVec` gives a `Vec` when it reserves room for more
//! elements, for both lanes' Vec models.
//!
//! Every growth path of the frozen nightly's `Vec` (`push`, `insert`,
//! `extend_from_slice`, `extend` from a `TrustedLen` iterator such as a range,
//! `resize`, `append`, `reserve`) reserves through `RawVecInner::reserve` or
//! `grow_one`, which call `grow_amortized` when the capacity is short:
//!
//! ```text
//! required = len + additional
//! cap'     = max(2 * cap, required, MIN_NON_ZERO_CAP)
//! MIN_NON_ZERO_CAP = 8 if size_of::<T>() == 1, 4 if <= 1024, else 1
//! ```
//!
//! (`alloc/src/raw_vec/mod.rs`, `min_non_zero_cap`), and `reserve_exact`
//! calls `grow_exact`, `cap' = required`. Both lanes modelled every growth as
//! `max(cap, required)`, the exact reservation, so `Vec::<u8>::new()` after
//! one `push` had capacity 1 where std has 8: `v.capacity() == 1` verified
//! clean where Kani fails, and `v.capacity() == 8`, which Kani proves, failed
//! certified Genuine (walker fail-closed review, round 2 of the repair after
//! the merge with main, `vec_capacity_growth_dual.rs`).
//!
//! A zero-sized element's capacity is `usize::MAX` and never grows; the
//! lanes keep their own reading of it.
//!
//! Every rule here reads the element's size from its own layout
//! ([`vec_elem_layout_size`]), the size `RawVec` itself is instantiated
//! with. The CHC lane's heap model reads sizes through `get_type_size`,
//! which first strips `Cell`, `RefCell`, `Mutex`, `RwLock` and their guards,
//! and the capacity model had borrowed it: `RefCell<()>` (8 bytes) read as
//! zero-sized, so `capacity()` was `usize::MAX`; `RefCell<u8>` (16 bytes)
//! read as 1 byte, so the first push gave 8 where std gives 4; and
//! `RefCell<[u8; 1020]>` (1028 bytes) read as 1020, so it gave 4 where std
//! gives 1. Each was a CHC missed bug or a certified false certificate
//! (walker fail-closed review, round 3 of the repair after the merge with
//! main, `vec_capacity_elem_layout_dual.rs`).

use ay_bindings::{Expr, ExprValue};
use rustc_public::CrateDef;
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};

use crate::codegen_ay::shared::mono_ty;
use crate::codegen_ay::types::POINTER_WIDTH;

/// The size in bytes, from its own layout, of the element of the Vec that
/// `ty` names: `Vec<T>` or `RawVec<T>` (also behind references and raw
/// pointers) gives `size_of::<T>()`, `String` gives 1. `None` for any other
/// type, or an element whose type still names a parameter. `ty` must be
/// monomorphic as far as the caller can make it (the CHC lane passes it
/// through `resolve_body_ty`).
pub(in crate::codegen_ay) fn vec_elem_layout_size(ty: Ty) -> Option<u64> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => {
            vec_elem_layout_size(inner)
        }
        TyKind::RigidTy(RigidTy::Adt(def, args)) => match def.trimmed_name().as_str() {
            "Vec" | "RawVec" => match args.0.first() {
                Some(GenericArgKind::Type(elem)) if !mono_ty::has_unresolved_params(*elem) => {
                    elem.layout().ok().map(|layout| layout.shape().size.bytes() as u64)
                }
                _ => None,
            },
            "String" => Some(1),
            _ => None,
        },
        _ => None,
    }
}

/// Which of `RawVec`'s two growth rules a reservation takes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay) enum VecGrowth {
    /// `grow_amortized`: `push`, `insert`, `extend*`, `resize`, `append`,
    /// `reserve`, `grow_one`.
    Amortized,
    /// `grow_exact`: `reserve_exact`.
    Exact,
}

/// `RawVec`'s `min_non_zero_cap` for an element of `elem_size` bytes.
pub(in crate::codegen_ay) fn min_non_zero_cap(elem_size: u64) -> u64 {
    if elem_size == 1 {
        8
    } else if elem_size <= 1024 {
        4
    } else {
        1
    }
}

/// The capacity after a reservation for `required` elements in all, from
/// `old_cap`, for a sized element of `elem_size` bytes: `old_cap` when it is
/// at least `required`, else what `growth` allocates. `None` for a
/// zero-sized element (the caller keeps its own model).
pub(in crate::codegen_ay) fn reserved_capacity(
    old_cap: &Expr,
    required: &Expr,
    elem_size: u64,
    growth: VecGrowth,
) -> Option<Expr> {
    if elem_size == 0 {
        return None;
    }
    let min_cap = min_non_zero_cap(elem_size);
    if let (Some(cap), Some(req)) = (const_u64(old_cap), const_u64(required)) {
        let grown = if req <= cap {
            cap
        } else {
            match growth {
                VecGrowth::Exact => req,
                VecGrowth::Amortized => cap.saturating_mul(2).max(req).max(min_cap),
            }
        };
        return Some(Expr::bitvec_const(grown, POINTER_WIDTH));
    }
    let grown = match growth {
        VecGrowth::Exact => required.clone(),
        VecGrowth::Amortized => {
            // `2 * cap` cannot wrap: a capacity is at most `isize::MAX`.
            let doubled = old_cap.clone().bvadd(old_cap.clone());
            let at_least_required = bv_max(doubled, required.clone());
            bv_max(at_least_required, Expr::bitvec_const(min_cap, POINTER_WIDTH))
        }
    };
    Some(Expr::ite(old_cap.clone().bvult(required.clone()), grown, old_cap.clone()))
}

fn bv_max(a: Expr, b: Expr) -> Expr {
    Expr::ite(a.clone().bvuge(b.clone()), a, b)
}

fn const_u64(expr: &Expr) -> Option<u64> {
    match expr.value() {
        ExprValue::BitVecConst { value, .. } => u64::try_from(value).ok(),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bv(n: u64) -> Expr {
        Expr::bitvec_const(n, POINTER_WIDTH)
    }

    fn folded(old: u64, required: u64, size: u64, growth: VecGrowth) -> u64 {
        const_u64(&reserved_capacity(&bv(old), &bv(required), size, growth).unwrap()).unwrap()
    }

    #[test]
    fn amortized_growth_matches_raw_vec() {
        // Vec::<u8>::new(); push: grow_amortized(0, 1) -> max(0, 1, 8).
        assert_eq!(folded(0, 1, 1, VecGrowth::Amortized), 8);
        // Vec::<u32>::new(); push: min 4.
        assert_eq!(folded(0, 1, 4, VecGrowth::Amortized), 4);
        // with_capacity(2) of u32, third push: max(4, 3, 4).
        assert_eq!(folded(2, 3, 4, VecGrowth::Amortized), 4);
        // extend_from_slice of 20 bytes into an empty Vec<u8>: required wins.
        assert_eq!(folded(0, 20, 1, VecGrowth::Amortized), 20);
        // a large element: min 1.
        assert_eq!(folded(0, 1, 2048, VecGrowth::Amortized), 1);
        // no growth when the capacity covers the requirement.
        assert_eq!(folded(8, 5, 1, VecGrowth::Amortized), 8);
    }

    #[test]
    fn exact_growth_is_the_requirement() {
        assert_eq!(folded(0, 3, 1, VecGrowth::Exact), 3);
        assert_eq!(folded(8, 3, 1, VecGrowth::Exact), 8);
    }

    #[test]
    fn zero_sized_elements_are_left_to_the_caller() {
        assert!(reserved_capacity(&bv(0), &bv(1), 0, VecGrowth::Amortized).is_none());
    }
}
