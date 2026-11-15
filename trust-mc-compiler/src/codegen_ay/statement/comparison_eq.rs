// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! PartialEq, PartialOrd, and min/max/clamp comparison codegen.
//!
//! Extracted from `comparison.rs` — Part of #4206.

use crate::codegen_ay::option_like_eq::option_like_datatype_eq;
use crate::codegen_ay::shared::mono_ty;
use crate::codegen_ay::types::{ptr_sort, unwrap_single_field_datatype_to_sort};
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::{BasicBlockIdx, Operand, Place, ProjectionElem};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::{debug, warn};

use super::codegen_place_value::RefValueSource;
use super::comparison::try_wrap_bv_as_option_some;
use super::{IntoOption, StatementCodegen};

mod partial_ord_array;

/// Reference levels `PartialOrd` / `Ord` peel before they read a compared value.
/// `<&A as PartialOrd<&B>>::lt` is `A::lt(*self, *other)`, so every reference
/// level of the compared type is looked through; deeper nesting fails closed.
const ORD_REFERENCE_PEEL_DEPTH: usize = 8;

/// One side of a `PartialOrd` / `Ord` call, read through its reference levels.
enum OrdOperand {
    /// The compared value.
    Value(Expr),
    /// Only an address was reachable: ordering it would order pointers where
    /// Rust orders pointees.
    AddressOnly,
    /// Codegen produced nothing (the pre-existing `None` path).
    Missing,
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Rewrite a `&&..&T` operand of `PartialOrd`/`Ord` to the `&T` place its
    /// comparison reads: `<&A as PartialOrd<&B>>::lt(self, other)` is
    /// `PartialOrd::lt(*self, *other)`, never an address order. Returns `None`
    /// when a level cannot be peeled (a constant operand, a projection other
    /// than `Deref`, or deeper nesting than [`ORD_REFERENCE_PEEL_DEPTH`]).
    ///
    /// Unlike `codegen_partial_eq_value`, a raw pointer under the references is
    /// peeled too: `&&*const T` orders the two POINTERS, and one deref would
    /// order the addresses of the variables holding them.
    fn peel_ord_reference_levels(&self, operand: &Operand) -> Option<Operand> {
        let mut current = operand.clone();
        for _ in 0..ORD_REFERENCE_PEEL_DEPTH {
            let ty = current.ty(self.body.locals()).into_option()?;
            let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) = ty.kind() else {
                return Some(current);
            };
            if !matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Ref(..))) {
                return Some(current);
            }
            let place = match &current {
                Operand::Copy(place) | Operand::Move(place) => place.clone(),
                _ => return None,
            };
            if place.projection.iter().any(|elem| !matches!(elem, ProjectionElem::Deref)) {
                return None;
            }
            let mut projection = place.projection;
            projection.push(ProjectionElem::Deref);
            current = Operand::Copy(Place { local: place.local, projection });
        }
        None
    }

    /// The value one side of a `PartialOrd`/`Ord` call compares.
    fn ord_operand_value(&mut self, operand: &Operand) -> OrdOperand {
        let Some(peeled) = self.peel_ord_reference_levels(operand) else {
            return OrdOperand::AddressOnly;
        };
        let peeled_a_level = &peeled != operand;
        let is_reference = peeled
            .ty(self.body.locals())
            .into_option()
            .is_some_and(|ty| matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(..))));
        if !is_reference {
            return self.codegen_operand(&peeled).map_or(OrdOperand::Missing, OrdOperand::Value);
        }
        match self.get_value_through_ref_source(&peeled) {
            // The deref did not happen: the expression is the reference's own
            // pointer. After peeling a level that pointer is an inner
            // reference's address, which an order never compares.
            Some((_, RefValueSource::Reference)) if peeled_a_level => OrdOperand::AddressOnly,
            Some((value, _)) => OrdOperand::Value(value),
            None => OrdOperand::Missing,
        }
    }

    /// Does `ty` hold a shared or mutable reference inside a tuple, array,
    /// struct or enum field? A structural order on such a value compares the
    /// reference's address, where the derived `PartialOrd` compares the
    /// pointee. Raw pointers order by address and do not count. A type that
    /// cannot be walked within the depth bound counts as holding one.
    fn ord_compared_type_holds_reference(ty: Ty, depth: usize) -> bool {
        let Some(depth) = depth.checked_sub(1) else {
            return true;
        };
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(..)) => true,
            TyKind::RigidTy(RigidTy::Tuple(elems)) => {
                elems.iter().any(|elem| Self::ord_compared_type_holds_reference(*elem, depth))
            }
            TyKind::RigidTy(RigidTy::Array(elem, _) | RigidTy::Slice(elem)) => {
                Self::ord_compared_type_holds_reference(elem, depth)
            }
            TyKind::RigidTy(RigidTy::Adt(def, args)) => def.variants_iter().any(|variant| {
                variant.fields().iter().any(|field| {
                    mono_ty::field_ty(field, &args)
                        .is_none_or(|t| Self::ord_compared_type_holds_reference(t, depth))
                })
            }),
            _ => false,
        }
    }

    /// The type a `PartialOrd`/`Ord` side compares: the pointee of its
    /// reference operand after peeling.
    fn ord_compared_type(&self, operand: &Operand) -> Option<Ty> {
        let peeled = self.peel_ord_reference_levels(operand)?;
        let ty = peeled.ty(self.body.locals()).into_option()?;
        Some(match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => pointee,
            _ => ty,
        })
    }

    /// The values `PartialOrd` / `Ord` compare: every reference level of an
    /// operand is looked through, so `<&A as PartialOrd<&B>>::lt(&&p, &&q)`
    /// orders the pointers `p` and `q`, never the addresses of the variables
    /// holding them. That address order is arbitrary: inside the MIR-inlined
    /// `<*const T as Ord>::cmp` it failed `smaller.cmp(&bigger) ==
    /// Ordering::Less` certified Genuine
    /// (kani/PointerComparison/ptr_comparison.rs::check_thin_ptr). A side that
    /// is only an address after peeling, or a compared type that holds a
    /// reference, leaves the result a fresh value of the destination's sort,
    /// recorded as a sound approximation (`Err(Some(()))`: the caller
    /// continues). `Err(None)` is the pre-existing "could not encode".
    pub(super) fn ord_operand_values(
        &mut self,
        args: &[Operand],
        destination: &Place,
    ) -> Result<Vec<Expr>, Option<()>> {
        let holds_reference = args.iter().any(|arg| {
            self.ord_compared_type(arg).is_some_and(|ty| {
                Self::ord_compared_type_holds_reference(ty, ORD_REFERENCE_PEEL_DEPTH)
            })
        });
        // An order of a sequence of floats (or of anything but integers) is
        // not its encodings' lexicographic order: `[-1.0f32] < [1.0]`, which
        // Kani proves, failed certified, and `[1.0f32] < [-1.0]` verified
        // clean (`shared::compare_loops::comparison_is_faithful`; walker
        // fail-closed review, round 3 of the repair after the merge with
        // main, `value_eq_semantics_dual.rs`). Its result is left fresh.
        let unfaithful = args
            .first()
            .and_then(|arg| arg.ty(self.body.locals()).into_option())
            .is_some_and(|ty| {
                !crate::codegen_ay::shared::compare_loops::comparison_is_faithful(
                    crate::codegen_ay::shared::compare_loops::ComparisonCall::Order,
                    ty,
                )
            });
        if unfaithful {
            let Some(sort) = self.infer_sort_from_place(destination) else {
                return Err(None);
            };
            let name = self.ctx.fresh_name("ay_ord_not_encoding_faithful");
            let fresh = self.ctx.declare_var(&name, sort);
            self.ctx.bmc_sound_havoc("ord_not_encoding_faithful");
            self.bind_ssa_result(destination, fresh);
            return Err(Some(()));
        }
        let mut values = Vec::with_capacity(args.len());
        let mut address_only = holds_reference;
        if !holds_reference {
            for arg in args {
                match self.ord_operand_value(arg) {
                    OrdOperand::Value(value) => values.push(value),
                    OrdOperand::AddressOnly => {
                        address_only = true;
                        break;
                    }
                    OrdOperand::Missing => return Err(None),
                }
            }
        }
        if address_only {
            let Some(sort) = self.infer_sort_from_place(destination) else {
                return Err(None);
            };
            let name = self.ctx.fresh_name("ay_ord_reference_level");
            let fresh = self.ctx.declare_var(&name, sort);
            self.ctx.bmc_sound_havoc("ord_reference_level_unresolved");
            self.bind_ssa_result(destination, fresh);
            return Err(Some(()));
        }
        Ok(values)
    }

    /// #3133's bridge wraps a bare payload bitvec as `Some(payload)`. A bare
    /// payload is what a flattened Option (#2076) degrades to once its `{base}.0`
    /// discriminant is out of reach (an array element store, an indexed read), so
    /// the variant is ASSUMED, not known: `a[1] = None` on a `[Some(0u8); 2]`
    /// array read back as `Some(0)` and `assert_eq!(a[1], Some(0))` PROVED.
    /// Record the assumption as fallback data so a proof resting on it is demoted.
    fn record_option_variant_assumed_some(&mut self, site: &'static str) {
        self.ctx.unsupported_with_fallback("option_eq_variant_assumed_some", site);
    }

    /// The value `PartialEq::eq`/`ne` compares for one of its two arguments.
    ///
    /// `fn eq(&self, other: &Rhs)` hands codegen REFERENCES, so ONE deref reaches
    /// the compared value — but only while `Self` is not itself a reference.
    /// `impl<A: PartialEq<B>> PartialEq<&B> for &A` compares `*a` with `*b`, so at
    /// `Self = &Option<u8>` the argument is `&&Option<u8>` and the compared values
    /// are TWO derefs down. Every further `&` layer strips the same way.
    ///
    /// Stripping only the one layer left a POINTER on both sides, and the #703
    /// sort-mismatch guard cannot see it: two pointers are both bitvecs of equal
    /// width, so `lhs.eq(rhs)` compared ADDRESSES. Two distinct locals have
    /// distinct addresses, so the comparison folded to FALSE —
    /// `assert!(&&o == &&c)` reported FAILED and `assert!(!(&&o == &&c))` was
    /// PROVED. That is a missed bug, measured on 7 harnesses across
    /// `review_r02_double_ref_eq`, `review_r03_ref_in_aggregate`,
    /// `review_r19_ref_levels` and `joined_enum_constant_payloads`.
    ///
    /// SOUNDNESS: only `Ref` layers are stripped, and an argument that reaches a
    /// raw pointer is left to the existing lane — `*const T`'s own `PartialEq` IS
    /// address equality, so folding those derefs away would be the mirror bug.
    /// When the deeper deref cannot be performed this returns None, which the
    /// caller turns into the fail-closed unsupported fallback (an unconstrained
    /// result), never an address comparison.
    pub(in crate::codegen_ay::statement) fn codegen_partial_eq_value(
        &mut self,
        operand: &Operand,
    ) -> Option<Expr> {
        let Some(ty) = operand.ty(self.body.locals()).into_option() else {
            return self.codegen_ord_operand_value(operand);
        };
        // A raw pointer anywhere under the argument keeps the old lane: address
        // equality is the right answer there, and `operand_is_raw_pointer_like`
        // is the same test the `Ord` lane uses to reach it.
        if self.operand_is_raw_pointer_like(operand) {
            return self.codegen_ord_operand_value(operand);
        }
        let TyKind::RigidTy(RigidTy::Ref(_, mut pointee, _)) = ty.kind() else {
            return self.codegen_ord_operand_value(operand);
        };
        let mut depth = 1usize;
        while let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = pointee.kind() {
            pointee = inner;
            depth += 1;
        }
        // FAIL CLOSED before either lane: an aggregate holding an
        // address-encoded reference cannot be compared structurally at all.
        if Self::eq_would_compare_addresses(pointee) {
            warn!(
                value_ty = ?pointee,
                "codegen_partial_eq: aggregate holds an address-encoded reference; \
                 structural equality would compare addresses, not values"
            );
            return None;
        }
        if depth == 1 {
            // `Self` is not a reference: one deref is the whole story, and the
            // existing lane carries the flattened-Option reconstruction with it.
            return self.codegen_ord_operand_value(operand);
        }
        self.codegen_value_through_ref_layers(operand, depth, pointee)
    }

    /// Whether structural equality on `ty` would compare an ADDRESS where Rust
    /// compares a VALUE.
    ///
    /// A `&T` field of a sized `T` encodes as `ptr_sort()` — a bare address
    /// (sort_inference.rs:53). Derived `PartialEq` on a tuple holding one
    /// compares `*a.0` with `*b.0`, but datatype equality compares the stored
    /// addresses, and two distinct locals never share one: `(&o, 1) == (&c, 1)`
    /// folded to FALSE, which PROVED `assert!(!((&o, 1) == (&c, 1)))`.
    ///
    /// `&str`, `&[T]` and `&dyn Trait` are NOT address-encoded — they carry
    /// slice and trait-object datatype sorts — so their structural comparison
    /// is untouched. A `*const T` field is excluded for the opposite reason:
    /// its own `PartialEq` IS address equality, so comparing the stored
    /// pointer is already right.
    ///
    /// SCOPE: tuples, arrays and slices, at any nesting depth — `((&o, 1u8), 2u8)` reached the
    /// same missed bug through an outer tuple whose own elements are a tuple
    /// and a `u8`, so a direct-elements-only test is not enough (measured:
    /// `nested_tuple_ref_eq_must_fail`).
    ///
    /// `struct`s are deliberately NOT covered. A struct with a derived
    /// `PartialEq` holding `&Option<u8>` was MEASURED to compare correctly
    /// (`struct_derive_ref_eq_must_fail`/`_safe` both match), so refusing it
    /// would trade a real verdict for an unknown and buy nothing.
    /// `negative/review_r20_struct_ref_eq.rs` holds that measurement, and the
    /// array and `Option<&T>` shapes beside it.
    fn eq_would_compare_addresses(ty: Ty) -> bool {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Tuple(elems)) => {
                elems.iter().any(|elem| Self::eq_element_is_address_encoded(*elem))
            }
            // `[&o] == [&c]` compares an SMT ARRAY of addresses, the same defect
            // one container out (measured: `array_of_ref_eq_must_fail`).
            TyKind::RigidTy(RigidTy::Array(elem, _)) => Self::eq_element_is_address_encoded(elem),
            TyKind::RigidTy(RigidTy::Slice(elem)) => Self::eq_element_is_address_encoded(elem),
            _ => false,
        }
    }

    /// An aggregate element that is, or transitively holds, an address-encoded
    /// reference. `Option<&T>` is deliberately absent: it was MEASURED to
    /// compare correctly (`option_of_ref_eq_must_fail`/`_safe` both match), so
    /// enum payloads are not walked.
    fn eq_element_is_address_encoded(ty: Ty) -> bool {
        Self::ty_is_address_encoded_reference(ty) || Self::eq_would_compare_addresses(ty)
    }

    /// A reference whose encoding is a bare address rather than a value.
    fn ty_is_address_encoded_reference(ty: Ty) -> bool {
        if !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(..))) {
            return false;
        }
        Self::infer_sort_from_ty(ty).is_some_and(|sort| sort == ptr_sort())
    }

    /// `operand` dereferenced `depth` times, or None when that cannot be done.
    ///
    /// `apply_projection_chain` resolves a `Deref` at ANY position through
    /// `ref_pointees`, so the wanted value is `place` with `depth` derefs
    /// APPENDED. Appended, not prepended: for `((*_1).0)` the value is
    /// `*((*_1).0)`, whereas a leading `Deref` would spell `(**_1).0`.
    fn codegen_value_through_ref_layers(
        &mut self,
        operand: &Operand,
        depth: usize,
        value_ty: Ty,
    ) -> Option<Expr> {
        let (Operand::Copy(place) | Operand::Move(place)) = operand else {
            // A constant `&&T` is folded by `codegen_operand`'s provenance walk,
            // which already follows every layer it can.
            return self.codegen_ord_operand_value(operand);
        };
        let mut projection = place.projection.clone();
        for _ in 0..depth {
            projection.push(ProjectionElem::Deref);
        }
        let deref_place = Place { local: place.local, projection };
        let expr = self.codegen_place(&deref_place)?;
        // FAIL CLOSED. `codegen_place`'s typed-memory lane can hand back a base
        // ADDRESS without reporting that it did (the reason `RefValueSource`
        // exists), and an address that happens to share a sort with the value
        // would reintroduce exactly the bug this walk removes. Accept the term
        // only when its sort is the one the VALUE type asks for.
        let expected = Self::infer_sort_from_ty(value_ty)?;
        if *expr.sort() != expected {
            warn!(
                ?value_ty,
                got = ?expr.sort(),
                want = ?expected,
                "codegen_partial_eq: deref through reference layers did not yield the value"
            );
            return None;
        }
        Some(expr)
    }

    /// Rust's `==` on the two slices a `PartialEq::eq`/`ne` call compares
    /// (`<[T] as PartialEq>::eq`, or a call on references to them such as
    /// `<&[T] as PartialEq<&[T]>>::eq`); `None` when the call compares no
    /// slice, two slices of different element types, or elements whose `==`
    /// is not their encodings' (a float, a reference, a hand-written
    /// `PartialEq`: `comparison_is_faithful`), which the lanes below handle.
    ///
    /// Each slice is read from its wide reference, the `&[T]` its last
    /// reference level holds: the lane's slice datatype, whose `fld_len` is
    /// the slice's own length. It is compared by that length and the elements
    /// below it ([`compare_loops::slice_view_eq`]). The pointee the lanes
    /// below read is the backing array (a `&[T]` made from `&[T; N]` reads
    /// the whole SMT array) or the whole slice datatype, and `=` on either
    /// compares indices past the length, and on the datatype the address:
    /// `[1i32, 2]` against `[1, 2, 0]` came out of unconstrained array tails,
    /// so `assert!(a != b)` failed with a certified counterexample, and at two
    /// reference levels the comparison was not built at all
    /// (`tools/soundness-duals/slice_eq_length_dual.rs`).
    ///
    /// A side the lane cannot read, or a view that starts past its source's
    /// index 0 (a shifted sub-slice keeps the source's `fld_data`), leaves the
    /// result a fresh boolean recorded as a sound havoc.
    fn slice_partial_eq(&mut self, args: &[Operand]) -> Option<Expr> {
        use crate::codegen_ay::shared::compare_loops::{self, ComparisonCall};
        let lhs_ty = args.first()?.ty(self.body.locals()).into_option()?;
        let rhs_ty = args.get(1)?.ty(self.body.locals()).into_option()?;
        let compared = compare_loops::peel_refs(lhs_ty);
        if !matches!(compared.kind(), TyKind::RigidTy(RigidTy::Slice(_)))
            || compare_loops::peel_refs(rhs_ty) != compared
            || !compare_loops::comparison_is_faithful(
                ComparisonCall::Eq { negated: false },
                lhs_ty,
            )
        {
            return None;
        }
        let lhs = self.slice_eq_view(&args[0]);
        let rhs = self.slice_eq_view(&args[1]);
        let eq = lhs.zip(rhs).and_then(|((lhs_wide, lhs), (rhs_wide, rhs))| {
            let bound = self.ctx.fresh_name("slice_eq_idx");
            let known_len =
                self.slice_built_len(&lhs_wide).or_else(|| self.slice_built_len(&rhs_wide));
            let eq = compare_loops::slice_view_eq(&lhs, &rhs, &bound, known_len)?;
            Some((eq, lhs_wide, rhs_wide))
        });
        Some(match eq {
            Some((eq, lhs_wide, rhs_wide)) => {
                // The unwinding check reads the loops' passes from the two
                // slices (`compare_loops::compare_reach`).
                self.compared_values = Some((lhs_wide, rhs_wide));
                eq
            }
            None => {
                warn!("codegen_partial_eq: a slice side has no readable view; result left fresh");
                let name = self.ctx.fresh_name("ay_slice_eq_unread");
                let fresh = self.ctx.declare_var(&name, ay_bindings::Sort::bool());
                self.ctx.bmc_sound_havoc("slice_eq_view_unread");
                fresh
            }
        })
    }

    /// The length of the slice `wide` when the constructor that built it
    /// states it as a constant, reached through SSA definitions only (an SSA
    /// name is defined once, so its definition is the value `wide` denotes;
    /// the current env value of a base may be a later one). `None` for any
    /// other shape: a merged or havocked slice, a symbolic length.
    fn slice_built_len(&self, wide: &Expr) -> Option<u64> {
        let built = self.deep_resolve_value(wide);
        let len = self.deep_resolve_value(&Self::ctor_field(&built, "fld_len")?);
        Self::concrete_bv_u64(&len)
    }

    /// One side of a slice `==`: the wide reference at its last reference
    /// level, and that slice's view. `None` when the value is not a slice
    /// datatype, or the view starts past its source's index 0.
    fn slice_eq_view(
        &mut self,
        operand: &Operand,
    ) -> Option<(Expr, crate::codegen_ay::shared::compare_loops::SliceView)> {
        let mut ty = operand.ty(self.body.locals()).into_option()?;
        let mut levels = 0usize;
        while let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = ty.kind() {
            ty = inner;
            levels += 1;
        }
        let wide = match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let mut wide_place = place.clone();
                let mut shifted = self.shifted_subslice_view_base(&wide_place);
                for _ in 1..levels {
                    wide_place.projection.push(ProjectionElem::Deref);
                    shifted |= self.shifted_subslice_view_base(&wide_place);
                }
                if shifted {
                    return None;
                }
                if levels == 1 {
                    self.codegen_operand(operand)?
                } else {
                    self.codegen_place(&wide_place)?
                }
            }
            Operand::Constant(_) if levels == 1 => self.codegen_operand(operand)?,
            _ => return None,
        };
        let view = crate::codegen_ay::shared::compare_loops::SliceView::of_datatype(&wide)?;
        Some((wide, view))
    }

    /// `==` on the values a `PartialEq::eq`/`ne` call compares (`lhs` and
    /// `rhs`, read one reference level down), when it is not the equality of
    /// their encodings (a float, a reference or a hand-written `PartialEq` in
    /// them; `shared::compare_loops::comparison_is_faithful`): Rust's `==`
    /// where it can be built from the values, else a fresh boolean recorded
    /// as a sound havoc. `None` when the encodings' equality is Rust's.
    /// `Some(0.0f32) == Some(-0.0)`, which Kani proves, failed certified
    /// (walker fail-closed review, round 3 of the repair after the merge
    /// with main, `value_eq_semantics_dual.rs`).
    fn unfaithful_partial_eq(&mut self, args: &[Operand], lhs: &Expr, rhs: &Expr) -> Option<Expr> {
        use crate::codegen_ay::shared::compare_loops;
        let arg_ty = args.first()?.ty(self.body.locals()).into_option()?;
        if compare_loops::comparison_is_faithful(
            compare_loops::ComparisonCall::Eq { negated: false },
            arg_ty,
        ) {
            return None;
        }
        // The values were read one level down: they are the compared values
        // only when that level is the last reference.
        let exact = match arg_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
                if !matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Ref(..))) =>
            {
                compare_loops::rust_value_eq(pointee, lhs, rhs)
            }
            _ => None,
        };
        Some(exact.unwrap_or_else(|| {
            let name = self.ctx.fresh_name("ay_eq_not_encoding_faithful");
            let fresh = self.ctx.declare_var(&name, ay_bindings::Sort::bool());
            self.ctx.bmc_sound_havoc("eq_not_encoding_faithful");
            fresh
        }))
    }

    /// Codegen PartialEq::eq method call.
    ///
    /// For types implementing PartialEq (including Option, Result, structs),
    /// translates to SMT equality. The method signature is `fn eq(&self, other: &Rhs) -> bool`,
    /// so `args[0]` is `&self` and `args[1]` is `&other`.
    ///
    /// Part of #407: Option/datatype equality comparison.
    /// Part of #408: ZST array equality - always returns true for ZST types.
    ///
    /// REQUIRES: args.len() >= 2
    /// ENSURES: destination gets boolean result of equality comparison
    pub(super) fn codegen_partial_eq(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.compared_values = None;
        if args.len() < 2 {
            return None;
        }

        // #408: Check for ZST types first - equality on ZST always returns true
        // This handles zero-length arrays, arrays of unit type, and unit type itself
        let is_zst_0 = self.is_raw_eq_zst(&args[0]);
        let is_zst_1 = self.is_raw_eq_zst(&args[1]);
        debug!("codegen_partial_eq: is_zst_0={}, is_zst_1={}", is_zst_0, is_zst_1);
        let is_zst = is_zst_0 && is_zst_1;
        if is_zst {
            debug!("codegen_partial_eq: ZST detected, returning true");
            self.bind_ssa_result(destination, Expr::bool_const(true));
            return target;
        }

        if let Some(eq) = self.slice_partial_eq(args) {
            self.bind_ssa_result(destination, eq);
            return target;
        }

        // PartialEq::eq takes &self and &other, so args are references.
        // Use get_value_through_ref to dereference and get actual values.
        let lhs = self.codegen_partial_eq_value(&args[0])?;
        let rhs = self.codegen_partial_eq_value(&args[1])?;
        self.compared_values = Some((lhs.clone(), rhs.clone()));
        let lhs = unwrap_single_field_datatype_to_sort(&lhs, rhs.sort()).unwrap_or(lhs);
        let rhs = unwrap_single_field_datatype_to_sort(&rhs, lhs.sort()).unwrap_or(rhs);

        // #3133: Normalize Option Datatype↔BV mismatches. When iter.next() returns
        // a Datatype Option and the comparison target is a bare BV from flattened
        // encoding, wrap the BV in Some() to bridge the sort mismatch.
        let (lhs, rhs) = if lhs.sort() != rhs.sort() {
            if let Some(wrapped) = try_wrap_bv_as_option_some(lhs.sort(), &rhs) {
                self.record_option_variant_assumed_some("codegen_partial_eq_or_ne");
                (lhs, wrapped)
            } else if let Some(wrapped) = try_wrap_bv_as_option_some(rhs.sort(), &lhs) {
                self.record_option_variant_assumed_some("codegen_partial_eq_or_ne");
                (wrapped, rhs)
            } else {
                (lhs, rhs)
            }
        } else {
            (lhs, rhs)
        };

        debug!("codegen_partial_eq: lhs.sort={:?}, rhs.sort={:?}", lhs.sort(), rhs.sort());

        if let Some(eq) = self.unfaithful_partial_eq(args, &lhs, &rhs) {
            self.bind_ssa_result(destination, eq);
            return target;
        }

        // #703: Check for sort mismatch before comparison. This can happen when
        // get_value_through_ref fails to dereference (returning pointer bitvec)
        // while the other side successfully dereferences (returning array/struct).
        // Return None to signal unsupported construct rather than panicking.
        // #1043: Allow Int/BitVec mixed comparisons (BigInt types)
        if lhs.sort() != rhs.sort() {
            let both_bitvec = lhs.sort().is_bitvec() && rhs.sort().is_bitvec();
            let int_bitvec_mix = (lhs.sort().is_int() || rhs.sort().is_int())
                && (lhs.sort().is_int() || lhs.sort().is_bitvec())
                && (rhs.sort().is_int() || rhs.sort().is_bitvec());
            if !both_bitvec && !int_bitvec_mix {
                warn!(
                    lhs_sort = ?lhs.sort(),
                    rhs_sort = ?rhs.sort(),
                    "codegen_partial_eq: sort mismatch, cannot compare"
                );
                return None;
            }
        }

        // Use SMT equality - works for all sorts including datatypes
        // Coerce to match widths for bitvector comparisons
        let eq_result = if lhs.sort().is_bitvec() && rhs.sort().is_bitvec() {
            // Part of #3041: For equal-width bitvecs, signedness is irrelevant —
            // equality is bitwise identical regardless of signed/unsigned interpretation,
            // and coerce_to_match_widths_typed is a no-op when widths match.
            // Skip the signedness check to avoid false demotion from signedness_fallback.
            if lhs.sort().bitvec_width() == rhs.sort().bitvec_width() {
                lhs.eq(rhs)
            } else {
                let is_signed = self.operand_signedness(&args[0]).unwrap_or_else(|| {
                    crate::codegen_ay::shared::signedness_fallback("codegen_partial_eq")
                });
                let (lhs_coerced, rhs_coerced) =
                    Self::coerce_to_match_widths_typed(lhs, rhs, is_signed);
                lhs_coerced.eq(rhs_coerced)
            }
        } else {
            // #1043: Handle Int/BitVec mixed comparisons (BigInt types)
            if lhs.sort().is_int() || rhs.sort().is_int() {
                // Part of #2757: Use signed bv2int when operand is signed.
                let is_signed = self.operand_signedness(&args[0]).unwrap_or_else(|| {
                    crate::codegen_ay::shared::signedness_fallback("codegen_partial_eq_int_mix")
                });
                let lhs_int = if lhs.sort().is_int() {
                    lhs
                } else if lhs.sort().is_bitvec() {
                    if is_signed { lhs.bv2int_signed() } else { lhs.bv2int() }
                } else {
                    lhs
                };
                let rhs_int = if rhs.sort().is_int() {
                    rhs
                } else if rhs.sort().is_bitvec() {
                    if is_signed { rhs.bv2int_signed() } else { rhs.bv2int() }
                } else {
                    rhs
                };
                lhs_int.eq(rhs_int)
            } else {
                // For datatypes and other sorts, direct equality
                option_like_datatype_eq(&lhs, &rhs, true).unwrap_or_else(|| lhs.eq(rhs))
            }
        };

        self.bind_ssa_result(destination, eq_result);

        target
    }

    /// Codegen PartialEq::ne method call (not equal).
    ///
    /// Similar to codegen_partial_eq but returns negated result.
    ///
    /// Part of #407: Option/datatype inequality comparison.
    /// Part of #408: ZST array inequality - always returns false for ZST types.
    ///
    /// REQUIRES: args.len() >= 2
    /// ENSURES: destination gets boolean result of inequality comparison
    pub(super) fn codegen_partial_ne(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.compared_values = None;
        if args.len() < 2 {
            return None;
        }

        // #408: Check for ZST types first - inequality on ZST always returns false
        // This handles zero-length arrays, arrays of unit type, and unit type itself
        let is_zst = self.is_raw_eq_zst(&args[0]) && self.is_raw_eq_zst(&args[1]);
        if is_zst {
            debug!("codegen_partial_ne: ZST detected, returning false");
            self.bind_ssa_result(destination, Expr::bool_const(false));
            return target;
        }

        if let Some(eq) = self.slice_partial_eq(args) {
            self.bind_ssa_result(destination, eq.not());
            return target;
        }

        let lhs = self.codegen_partial_eq_value(&args[0])?;
        let rhs = self.codegen_partial_eq_value(&args[1])?;
        self.compared_values = Some((lhs.clone(), rhs.clone()));
        let lhs = unwrap_single_field_datatype_to_sort(&lhs, rhs.sort()).unwrap_or(lhs);
        let rhs = unwrap_single_field_datatype_to_sort(&rhs, lhs.sort()).unwrap_or(rhs);

        // #3133: Same Option Datatype↔BV normalization as codegen_partial_eq.
        let (lhs, rhs) = if lhs.sort() != rhs.sort() {
            if let Some(wrapped) = try_wrap_bv_as_option_some(lhs.sort(), &rhs) {
                self.record_option_variant_assumed_some("codegen_partial_eq_or_ne");
                (lhs, wrapped)
            } else if let Some(wrapped) = try_wrap_bv_as_option_some(rhs.sort(), &lhs) {
                self.record_option_variant_assumed_some("codegen_partial_eq_or_ne");
                (wrapped, rhs)
            } else {
                (lhs, rhs)
            }
        } else {
            (lhs, rhs)
        };

        debug!("codegen_partial_ne: lhs.sort={:?}, rhs.sort={:?}", lhs.sort(), rhs.sort());

        if let Some(eq) = self.unfaithful_partial_eq(args, &lhs, &rhs) {
            self.bind_ssa_result(destination, eq.not());
            return target;
        }

        // #703: Check for sort mismatch before comparison (same as codegen_partial_eq)
        // #1043: Allow Int/BitVec mixed comparisons (BigInt types)
        if lhs.sort() != rhs.sort() {
            let both_bitvec = lhs.sort().is_bitvec() && rhs.sort().is_bitvec();
            let int_bitvec_mix = (lhs.sort().is_int() || rhs.sort().is_int())
                && (lhs.sort().is_int() || lhs.sort().is_bitvec())
                && (rhs.sort().is_int() || rhs.sort().is_bitvec());
            if !both_bitvec && !int_bitvec_mix {
                warn!(
                    lhs_sort = ?lhs.sort(),
                    rhs_sort = ?rhs.sort(),
                    "codegen_partial_ne: sort mismatch, cannot compare"
                );
                return None;
            }
        }

        // Use SMT inequality - works for all sorts including datatypes
        let ne_result = if lhs.sort().is_bitvec() && rhs.sort().is_bitvec() {
            // Part of #3041: Same equal-width optimization as codegen_partial_eq.
            if lhs.sort().bitvec_width() == rhs.sort().bitvec_width() {
                lhs.ne(rhs)
            } else {
                let is_signed = self.operand_signedness(&args[0]).unwrap_or_else(|| {
                    crate::codegen_ay::shared::signedness_fallback("codegen_partial_ne")
                });
                let (lhs_coerced, rhs_coerced) =
                    Self::coerce_to_match_widths_typed(lhs, rhs, is_signed);
                lhs_coerced.ne(rhs_coerced)
            }
        } else {
            // #1043: Handle Int/BitVec mixed comparisons (BigInt types)
            if lhs.sort().is_int() || rhs.sort().is_int() {
                // Part of #2757: Use signed bv2int when operand is signed.
                let is_signed = self.operand_signedness(&args[0]).unwrap_or_else(|| {
                    crate::codegen_ay::shared::signedness_fallback("codegen_partial_ne_int_mix")
                });
                let lhs_int = if lhs.sort().is_int() {
                    lhs
                } else if lhs.sort().is_bitvec() {
                    if is_signed { lhs.bv2int_signed() } else { lhs.bv2int() }
                } else {
                    lhs
                };
                let rhs_int = if rhs.sort().is_int() {
                    rhs
                } else if rhs.sort().is_bitvec() {
                    if is_signed { rhs.bv2int_signed() } else { rhs.bv2int() }
                } else {
                    rhs
                };
                lhs_int.ne(rhs_int)
            } else {
                // For datatypes and other sorts, direct inequality
                option_like_datatype_eq(&lhs, &rhs, false).unwrap_or_else(|| lhs.ne(rhs))
            }
        };
        self.bind_ssa_result(destination, ne_result);

        target
    }

    /// Codegen PartialOrd comparison operations (lt, le, gt, ge).
    ///
    /// Part of #1482: Handle primitive PartialOrd trait methods for comparison.
    ///
    /// REQUIRES: args.len() >= 2
    /// ENSURES: destination gets boolean result of ordered comparison
    pub(super) fn codegen_partial_ord_cmp(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        op: &str,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        let (lhs, rhs) = match self.ord_operand_values(&args[..2], destination) {
            Ok(mut values) => {
                let rhs = values.pop()?;
                (values.pop()?, rhs)
            }
            Err(Some(())) => return target,
            Err(None) => return None,
        };
        let raw_pointer = self.operand_is_raw_pointer_like(&args[0])
            || self.operand_is_raw_pointer_like(&args[1]);

        debug!(
            "codegen_partial_ord_cmp({op}): lhs.sort={:?}, rhs.sort={:?}",
            lhs.sort(),
            rhs.sort()
        );

        if let Some(cmp_result) =
            self.codegen_slice_or_array_partial_ord_cmp(&args[0], &args[1], &lhs, &rhs, op)
        {
            self.bind_ssa_result(destination, cmp_result);
            return target;
        }

        if raw_pointer {
            let cmp_result =
                self.codegen_total_order_relation_expr(lhs, rhs, &args[0], true, op)?;
            self.bind_ssa_result(destination, cmp_result);
            return target;
        }

        // Check for bitvec or int types
        let cmp_result = if lhs.sort().is_bitvec() && rhs.sort().is_bitvec() {
            // Determine signedness from operand type
            let is_signed = self.operand_signedness(&args[0]).unwrap_or_else(|| {
                crate::codegen_ay::shared::signedness_fallback("codegen_partial_ord_cmp")
            });
            let (lhs_coerced, rhs_coerced) =
                Self::coerce_to_match_widths_typed(lhs, rhs, is_signed);

            match op {
                "lt" if is_signed => lhs_coerced.bvslt(rhs_coerced),
                "lt" => lhs_coerced.bvult(rhs_coerced),
                "le" if is_signed => lhs_coerced.bvsle(rhs_coerced),
                "le" => lhs_coerced.bvule(rhs_coerced),
                "gt" if is_signed => lhs_coerced.bvsgt(rhs_coerced),
                "gt" => lhs_coerced.bvugt(rhs_coerced),
                "ge" if is_signed => lhs_coerced.bvsge(rhs_coerced),
                "ge" => lhs_coerced.bvuge(rhs_coerced),
                _ => {
                    // external enum: BinOp
                    warn!("codegen_partial_ord_cmp: unknown op {op}");
                    // Part of #3211: Track constraint drop in demotion pipeline.
                    self.ctx.unsupported_with_fallback(
                        "partial_ord_cmp_unknown_op",
                        "unknown comparison op for bitvec",
                    );
                    return None;
                }
            }
        } else if lhs.sort().is_int() || rhs.sort().is_int() {
            // Integer (BigInt) comparison
            // Part of #2757: Use signed bv2int when operand is signed.
            let is_signed = self.operand_signedness(&args[0]).unwrap_or_else(|| {
                crate::codegen_ay::shared::signedness_fallback("codegen_partial_ord_cmp_int_mix")
            });
            let lhs_int = if lhs.sort().is_int() {
                lhs
            } else if lhs.sort().is_bitvec() {
                if is_signed { lhs.bv2int_signed() } else { lhs.bv2int() }
            } else {
                return None;
            };
            let rhs_int = if rhs.sort().is_int() {
                rhs
            } else if rhs.sort().is_bitvec() {
                if is_signed { rhs.bv2int_signed() } else { rhs.bv2int() }
            } else {
                return None;
            };

            match op {
                "lt" => lhs_int.int_lt(rhs_int),
                "le" => lhs_int.int_le(rhs_int),
                "gt" => lhs_int.int_gt(rhs_int),
                "ge" => lhs_int.int_ge(rhs_int),
                _ => {
                    // external enum: BinOp
                    warn!("codegen_partial_ord_cmp: unknown op {op}");
                    // Part of #3211: Track constraint drop in demotion pipeline.
                    self.ctx.unsupported_with_fallback(
                        "partial_ord_cmp_unknown_op",
                        "unknown comparison op for int",
                    );
                    return None;
                }
            }
        } else {
            warn!(
                lhs_sort = ?lhs.sort(),
                rhs_sort = ?rhs.sort(),
                "codegen_partial_ord_cmp: unsupported sort combination"
            );
            // Part of #3211: Track constraint drop in demotion pipeline.
            self.ctx.unsupported_with_fallback(
                "partial_ord_cmp_unsupported_sorts",
                "unsupported sort combination",
            );
            return None;
        };

        self.bind_ssa_result(destination, cmp_result);

        target
    }

    pub(super) fn codegen_ord_minmax(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        is_min: bool,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        let (lhs, rhs) = match self.ord_operand_values(&args[..2], destination) {
            Ok(mut values) => {
                let rhs = values.pop()?;
                (values.pop()?, rhs)
            }
            Err(Some(())) => return target,
            Err(None) => return None,
        };
        let raw_pointer = self.operand_is_raw_pointer_like(&args[0])
            || self.operand_is_raw_pointer_like(&args[1]);
        let select_lhs = self.codegen_total_order_relation_expr(
            lhs.clone(),
            rhs.clone(),
            &args[0],
            raw_pointer,
            if is_min { "le" } else { "ge" },
        )?;
        let result = Expr::ite(select_lhs, lhs, rhs);
        self.bind_ssa_result(destination, result);
        target
    }

    pub(super) fn codegen_ord_clamp(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 3 {
            return None;
        }

        let (value, min_value, max_value) = match self.ord_operand_values(&args[..3], destination) {
            Ok(mut values) => {
                let max_value = values.pop()?;
                let min_value = values.pop()?;
                (values.pop()?, min_value, max_value)
            }
            Err(Some(())) => return target,
            Err(None) => return None,
        };
        let raw_pointer = self.operand_is_raw_pointer_like(&args[0])
            || self.operand_is_raw_pointer_like(&args[1])
            || self.operand_is_raw_pointer_like(&args[2]);
        let below_min = self.codegen_total_order_relation_expr(
            value.clone(),
            min_value.clone(),
            &args[0],
            raw_pointer,
            "lt",
        )?;
        let above_max = self.codegen_total_order_relation_expr(
            value.clone(),
            max_value.clone(),
            &args[0],
            raw_pointer,
            "gt",
        )?;
        let result = Expr::ite(below_min, min_value, Expr::ite(above_max, max_value, value));
        self.bind_ssa_result(destination, result);
        target
    }
}
