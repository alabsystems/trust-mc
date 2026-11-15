// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! What an `Iterator::sum` call adds, read from the RUST types of the call.
//!
//! Both lanes stub `Iterator::sum` (`StubKind::IterSum`) instead of encoding
//! the `Sum` impl it calls. Until AY alignment review round 2 (2026-10-02)
//! the stubs decided the arithmetic from the destination's SMT SORT alone and
//! added the elements with `bvadd` whenever that sort was a bitvector. A sort
//! does not say what the program adds:
//!
//! * `f16`/`f32`/`f64`/`f128` are bitvectors too, so a float sum was the
//!   INTEGER sum of the IEEE bit patterns. `[f32::MAX, f32::MAX].iter().sum()`
//!   came out finite, `is_infinite()` was refuted and a program Kani fails
//!   was proved, in both lanes; `[1.5f32, 2.25].iter().sum() == 3.75` was a
//!   counterexample certified Genuine.
//! * std's integer `Sum` adds under `#[rustc_inherit_overflow_checks]`, so an
//!   overflowing sum panics. The `bvadd` wrapped silently and no overflow
//!   check was emitted: `[200u8, 100].iter().sum::<u8>()` was proved.
//! * `Saturating<T>` (std, since 1.91) saturates, and a user may implement
//!   `Sum<&Local> for u32` with any body at all. Both have bitvector sorts in
//!   the CHC lane and were summed with `bvadd`: a saturating sum and a
//!   max-taking user `Sum` were each proved where Kani fails, and their safe
//!   twins were counterexamples certified Genuine.
//!
//! [`classify_iter_sum`] therefore reads the call itself: the destination
//! type `S` and the item type `A` of the `<S as Sum<A>>::sum` impl that
//! `Iterator::sum` calls, from the monomorphised body of the callee. Only
//! std's own impls are encoded, and only when `A` is `S` or `&S`; everything
//! else is [`SumSummand::Unknown`]. Each lane over-approximates an unknown
//! impl's VALUE with a havoc that cannot certify a counterexample, and fails
//! closed on its PANICS: the impl's body is not encoded, so whatever it could
//! panic on is not checked (BMC: the demoting fallback; CHC: a conservative
//! error rule, `reduce.rs`).
//!
//! What a classified impl can panic on is a fact about the impl, not about
//! the sort a lane gives the destination: a lane that cannot encode the value
//! at that sort havocs the value, and still reports exactly the impl's own
//! panics (an integer sum's overflow; none for `Wrapping`, `Saturating` or a
//! float). std's `Saturating<uN>` sum is classified for that reason: it was
//! `Unknown`, and the CHC lane's conservative rule for an unmodelled impl
//! then reported a panic an impl built on `saturating_add` cannot raise, so a
//! Kani-SUCCESSFUL harness that merely reached a `Saturating` sum could not
//! be proved (AY alignment round 8, review round 4, finding 1).
//!
//! The call is read from its own `func` operand, never looked up by its
//! destination place: rustc writes the arms of an `if`/`match` that each end
//! in `.sum()` into ONE local, so two different `Iterator::sum` calls share a
//! destination, and a lookup by place could not say which one it was
//! encoding (AY alignment round 8, review round 3, finding 1).

use crate::callee_body::CalleeBody;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Body, Operand, Place, TerminatorKind};
use rustc_public::ty::{GenericArgKind, GenericArgs, RigidTy, Ty, TyKind};

use crate::codegen_ay::types::{
    float_ty_to_bitvec_width, int_ty_to_bitvec_width, uint_ty_to_bitvec_width,
};

/// What one `Iterator::sum` call adds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay) enum SumSummand {
    /// A primitive integer of `width` bits summed by std's
    /// `impl Sum<T | &T> for T`: `fold(0, |a, b| a + b)` under the crate's
    /// overflow checks, so an overflowing step is an "attempt to add with
    /// overflow".
    Int { width: u32, signed: bool },
    /// A primitive float summed by std's impl: `fold(-0.0, |a, b| a + b)` in
    /// IEEE 754 round-to-nearest-even. The identity is NEGATIVE zero: an empty
    /// float sum is `-0.0`.
    Float { width: u32 },
    /// `core::num::Wrapping<int>` summed by std's impl: modular addition, which
    /// never panics.
    WrappingInt { width: u32 },
    /// `core::num::Saturating<uN>` summed by std's impl
    /// (`saturating_integer_sum_product!`, `core/src/iter/traits/accum.rs`):
    /// `fold(Saturating(0), |a, b| a + b)`, whose `+` is `uN::saturating_add`.
    /// Each step is `a + b`, or all ones when that carries out; it never
    /// panics. std implements it for the unsigned integers only.
    SaturatingUint { width: u32 },
    /// Anything else (a user `Sum` impl, `Duration`, `Option<T>`, an iterator
    /// that overrides `sum`, or a call this module could not read): the stub
    /// does not know the arithmetic and must not encode one.
    Unknown,
}

impl SumSummand {
    /// The bitvector width of the destination, when the arithmetic is known.
    pub(in crate::codegen_ay) fn width(self) -> Option<u32> {
        match self {
            Self::Int { width, .. }
            | Self::Float { width }
            | Self::WrappingInt { width }
            | Self::SaturatingUint { width } => Some(width),
            Self::Unknown => None,
        }
    }

    /// The bit pattern of the empty sum (`Sum::sum` of no items), when known:
    /// `0` for the integer kinds and `-0.0` (only the sign bit set) for a float.
    pub(in crate::codegen_ay) fn identity_bits(self) -> Option<(u128, u32)> {
        match self {
            Self::Int { width, .. }
            | Self::WrappingInt { width }
            | Self::SaturatingUint { width } => Some((0, width)),
            Self::Float { width } => Some((1u128 << (width - 1), width)),
            Self::Unknown => None,
        }
    }
}

/// Classify the `Iterator::sum` call `func(..) -> destination` of `body`:
/// `func` is the call's own callee operand, `destination` the place it writes.
/// Fails closed to [`SumSummand::Unknown`] on any shape it does not recognise.
pub(in crate::codegen_ay) fn classify_iter_sum(
    body: &Body,
    func: &Operand,
    destination: &Place,
) -> SumSummand {
    classify_iter_sum_inner(body, func, destination).unwrap_or(SumSummand::Unknown)
}

fn classify_iter_sum_inner(body: &Body, func: &Operand, destination: &Place) -> Option<SumSummand> {
    let locals = body.locals();
    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func.ty(locals).ok()?.kind() else {
        return None;
    };
    if !is_core_item(def.krate().name.as_str(), &def.name(), "Iterator::sum") {
        return None;
    }
    // `Iterator::sum::<Self, S>`: the sum's type is the method's own generic
    // `S`. The destination must have that type; a destination read against a
    // body that is not the call's own would not, and is refused.
    let Some(GenericArgKind::Type(sum_ty)) = args.0.get(1) else {
        return None;
    };
    let sum_ty = *sum_ty;
    if destination.ty(locals).ok()? != sum_ty {
        return None;
    }

    // `Iterator::sum::<Self, S>` is `<S as Sum<Self::Item>>::sum(self)`; the
    // monomorphised body names the impl's item type. An iterator that
    // overrides `sum` resolves to its own body, which carries no such call.
    let instance = Instance::resolve(def, &args).ok()?;
    let callee_body = instance.callee_body()?;
    let callee_locals = callee_body.locals();
    let mut item_ty: Option<Ty> = None;
    for block in &callee_body.blocks {
        let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
            continue;
        };
        let Ok(func_ty) = func.ty(callee_locals) else {
            continue;
        };
        let TyKind::RigidTy(RigidTy::FnDef(sum_def, sum_args)) = func_ty.kind() else {
            continue;
        };
        if !is_core_item(sum_def.krate().name.as_str(), &sum_def.name(), "Sum::sum") {
            continue;
        }
        // Trait-method generics: [Self = S, A, I].
        let (Some(GenericArgKind::Type(self_ty)), Some(GenericArgKind::Type(a))) =
            (sum_args.0.first(), sum_args.0.get(1))
        else {
            return None;
        };
        if *self_ty != sum_ty || item_ty.is_some_and(|seen| seen != *a) {
            return None;
        }
        item_ty = Some(*a);
    }
    let item_ty = item_ty?;
    if !item_is_self_or_ref(item_ty, sum_ty) {
        return None;
    }
    summand_of_std_sum_type(sum_ty)
}

/// Is `item` the type `sum` itself, or a shared reference to it? Those are
/// the only item types std implements `Sum` over for the types below.
fn item_is_self_or_ref(item: Ty, sum: Ty) -> bool {
    if item == sum {
        return true;
    }
    matches!(item.kind(), TyKind::RigidTy(RigidTy::Ref(_, inner, _)) if inner == sum)
}

/// The arithmetic of std's `Sum` impl for `ty`, for the types it is encoded for.
fn summand_of_std_sum_type(ty: Ty) -> Option<SumSummand> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Int(int_ty)) => {
            Some(SumSummand::Int { width: int_ty_to_bitvec_width(int_ty), signed: true })
        }
        TyKind::RigidTy(RigidTy::Uint(uint_ty)) => {
            Some(SumSummand::Int { width: uint_ty_to_bitvec_width(uint_ty), signed: false })
        }
        TyKind::RigidTy(RigidTy::Float(float_ty)) => {
            Some(SumSummand::Float { width: float_ty_to_bitvec_width(float_ty) })
        }
        TyKind::RigidTy(RigidTy::Adt(def, args))
            if is_core_item(def.krate().name.as_str(), &def.name(), "Wrapping") =>
        {
            let Some(GenericArgKind::Type(inner)) = args.0.first() else {
                return None;
            };
            let width = match inner.kind() {
                TyKind::RigidTy(RigidTy::Int(int_ty)) => int_ty_to_bitvec_width(int_ty),
                TyKind::RigidTy(RigidTy::Uint(uint_ty)) => uint_ty_to_bitvec_width(uint_ty),
                _ => return None,
            };
            Some(SumSummand::WrappingInt { width })
        }
        // std's `Sum` for `Saturating` exists for the unsigned integers only;
        // any other inner type is refused rather than guessed.
        TyKind::RigidTy(RigidTy::Adt(def, args))
            if is_core_item(def.krate().name.as_str(), &def.name(), "Saturating") =>
        {
            let Some(GenericArgKind::Type(inner)) = args.0.first() else {
                return None;
            };
            let TyKind::RigidTy(RigidTy::Uint(uint_ty)) = inner.kind() else {
                return None;
            };
            Some(SumSummand::SaturatingUint { width: uint_ty_to_bitvec_width(uint_ty) })
        }
        _ => None,
    }
}

/// Is the item defined in `core` and does its printed path end with the
/// path segments `suffix` (whole segments: `Wrapping` does not match
/// `MyWrapping`)? The printed path may name a `std` re-export, so the crate
/// is checked, not the prefix.
fn is_core_item(krate: &str, path: &str, suffix: &str) -> bool {
    krate == "core"
        && (path == suffix || path.strip_suffix(suffix).is_some_and(|head| head.ends_with("::")))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen_ay::context::with_test_ay_ctx_for_source;
    use crate::codegen_ay::test_fixtures::find_instance_by_suffix;

    const TWO_SUMS_SOURCE: &str = r#"#![allow(dead_code)]
use std::num::Saturating;

pub fn two_sums_one_place(c: bool, a: [u8; 2]) -> u8 {
    if c { a.iter().sum() } else { a.iter().copied().sum() }
}

pub fn match_arm_sums(k: u8, a: [i16; 2]) -> i16 {
    match k % 3 {
        0 => a.iter().sum(),
        1 => a.iter().copied().sum(),
        _ => a.into_iter().sum(),
    }
}

#[derive(Clone, Copy)]
pub struct W(u8);

impl<'a> core::iter::Sum<&'a W> for u8 {
    fn sum<I: Iterator<Item = &'a W>>(it: I) -> u8 {
        it.fold(0u8, |a, w| a + w.0)
    }
}

pub fn std_and_user_sums(c: bool, a: [u8; 2], w: [W; 2]) -> u8 {
    if c { a.iter().sum() } else { w.iter().sum() }
}

pub fn saturating_sum(a: [Saturating<u8>; 2]) -> Saturating<u8> {
    a.iter().sum()
}

pub fn saturating_sum_by_value(a: [Saturating<u64>; 2]) -> Saturating<u64> {
    a.iter().copied().sum()
}

pub fn wrapping_sum(a: [core::num::Wrapping<i16>; 2]) -> core::num::Wrapping<i16> {
    a.iter().sum()
}
"#;

    /// Every `Iterator::sum` call of `fn_name`'s body, classified from its own
    /// callee operand, with the local its destination place writes (whole).
    fn classified_sums(source: &'static str, fn_name: &'static str) -> Vec<(usize, SumSummand)> {
        let mut out = Vec::new();
        let out_ref = &mut out;
        with_test_ay_ctx_for_source(source, move |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            for block in &body.blocks {
                let TerminatorKind::Call { func, destination, .. } = &block.terminator.kind else {
                    continue;
                };
                let Ok(func_ty) = func.ty(body.locals()) else {
                    continue;
                };
                let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func_ty.kind() else {
                    continue;
                };
                if is_core_item(def.krate().name.as_str(), &def.name(), "Iterator::sum") {
                    assert!(destination.projection.is_empty(), "a sum into a projection");
                    out_ref.push((destination.local, classify_iter_sum(&body, func, destination)));
                }
            }
        });
        out
    }

    /// rustc writes the arms of an `if` that each end in `.sum()` into ONE
    /// local. Both calls are std's `u8` sum and must be classified so; a lookup
    /// by destination place (the encoding before AY alignment round 8 review
    /// round 3) saw two different `Iterator::sum` instances writing one place
    /// and refused both as `Unknown`.
    #[test]
    fn two_sums_writing_one_place_are_each_classified() {
        let sums = classified_sums(TWO_SUMS_SOURCE, "two_sums_one_place");
        assert_eq!(sums.len(), 2, "expected two Iterator::sum calls, got {sums:?}");
        assert_eq!(sums[0].0, sums[1].0, "the probe's two sums must write one place: {sums:?}");
        for (_, summand) in &sums {
            assert_eq!(*summand, SumSummand::Int { width: 8, signed: false });
        }
    }

    /// Three arms, three iterator types (`Iter`, `Copied<Iter>`,
    /// `array::IntoIter`), one destination.
    #[test]
    fn match_arm_sums_writing_one_place_are_each_classified() {
        let sums = classified_sums(TWO_SUMS_SOURCE, "match_arm_sums");
        assert_eq!(sums.len(), 3, "expected three Iterator::sum calls, got {sums:?}");
        for (_, summand) in &sums {
            assert_eq!(*summand, SumSummand::Int { width: 16, signed: true });
        }
    }

    /// A std sum and a user `impl Sum<&W> for u8` writing one place: each call
    /// is what it is, the std one encoded and the user one `Unknown`.
    #[test]
    fn a_std_sum_beside_a_user_impl_keeps_its_own_classification() {
        let sums = classified_sums(TWO_SUMS_SOURCE, "std_and_user_sums");
        assert_eq!(sums.len(), 2, "expected two Iterator::sum calls, got {sums:?}");
        assert_eq!(sums[0].0, sums[1].0, "the probe's two sums must write one place: {sums:?}");
        let mut kinds: Vec<SumSummand> = sums.iter().map(|(_, summand)| *summand).collect();
        kinds.sort_by_key(|summand| *summand == SumSummand::Unknown);
        assert_eq!(kinds, [SumSummand::Int { width: 8, signed: false }, SumSummand::Unknown]);
    }

    /// std's `Sum<&Saturating<u8>>` and `Sum<Saturating<u64>>` are classified
    /// as the saturating sums they are. Both were `Unknown`, and the CHC lane's
    /// conservative rule for an unmodelled impl then reported a panic that
    /// `saturating_add` cannot raise (AY alignment round 8, review round 4,
    /// finding 1).
    #[test]
    fn a_saturating_sum_is_classified() {
        let by_ref = classified_sums(TWO_SUMS_SOURCE, "saturating_sum");
        assert_eq!(by_ref.len(), 1, "expected one Iterator::sum call, got {by_ref:?}");
        assert_eq!(by_ref[0].1, SumSummand::SaturatingUint { width: 8 });
        let by_value = classified_sums(TWO_SUMS_SOURCE, "saturating_sum_by_value");
        assert_eq!(by_value.len(), 1, "expected one Iterator::sum call, got {by_value:?}");
        assert_eq!(by_value[0].1, SumSummand::SaturatingUint { width: 64 });
    }

    /// `Wrapping<i16>`: signed inner types are std's too.
    #[test]
    fn a_wrapping_sum_is_classified() {
        let sums = classified_sums(TWO_SUMS_SOURCE, "wrapping_sum");
        assert_eq!(sums.len(), 1, "expected one Iterator::sum call, got {sums:?}");
        assert_eq!(sums[0].1, SumSummand::WrappingInt { width: 16 });
    }

    #[test]
    fn identity_of_a_float_sum_is_negative_zero() {
        assert_eq!(SumSummand::Float { width: 32 }.identity_bits(), Some((0x8000_0000, 32)));
        assert_eq!(
            SumSummand::Float { width: 64 }.identity_bits(),
            Some((0x8000_0000_0000_0000, 64))
        );
        assert_eq!(SumSummand::Float { width: 16 }.identity_bits(), Some((0x8000, 16)));
        assert_eq!(SumSummand::Int { width: 8, signed: false }.identity_bits(), Some((0, 8)));
        assert_eq!(SumSummand::WrappingInt { width: 128 }.identity_bits(), Some((0, 128)));
        assert_eq!(SumSummand::SaturatingUint { width: 32 }.identity_bits(), Some((0, 32)));
        assert_eq!(SumSummand::Unknown.identity_bits(), None);
    }

    #[test]
    fn only_whole_trailing_segments_of_core_items_match() {
        assert!(is_core_item("core", "std::num::Wrapping", "Wrapping"));
        assert!(is_core_item("core", "core::num::wrapping::Wrapping", "Wrapping"));
        assert!(is_core_item("core", "std::iter::Iterator::sum", "Iterator::sum"));
        assert!(is_core_item("core", "std::iter::Sum::sum", "Sum::sum"));
        assert!(!is_core_item("core", "std::num::Saturating", "Wrapping"));
        assert!(is_core_item("core", "std::num::Saturating", "Saturating"));
        assert!(!is_core_item("my_crate", "my_crate::Saturating", "Saturating"));
        assert!(!is_core_item("core", "std::num::MyWrapping", "Wrapping"));
        assert!(!is_core_item("my_crate", "my_crate::Wrapping", "Wrapping"));
        assert!(!is_core_item("core", "std::iter::MySum::sum", "Sum::sum"));
    }
}
