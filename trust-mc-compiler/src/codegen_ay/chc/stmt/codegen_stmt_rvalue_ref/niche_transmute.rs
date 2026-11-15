// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A transmute of plain bits or a raw pointer into a niche-encoded pointer
//! enum (`Option<&T>`, `Option<NonNull<T>>`, `Option<Box<T>>`).
//!
//! Such a value is `None` exactly when the bits are zero, and otherwise the
//! pointer variant holding those bits. The transmute's sort coercion does not
//! decode the niche: `transmute::<*const u16, Option<&u16>>(&x)` unwrapped to
//! `None`, and the panic was certified Genuine on main (review of
//! fix/chc-lost-writes, lostwrite round 1, finding 4's neighbours). A fresh
//! value of the target sort fixed that, but also lost the cases the coercion
//! got right: `ptr::null()` to `None`, `Box::into_raw` back to `Option<Box>`
//! (lostwrite track round 1, finding 2).
//!
//! The decode is exact where the payload is the pointer itself (a `Box`, a
//! `NonNull`, a raw pointer): `ite(bits == 0, None, Some(bits))`. A reference
//! payload is modelled by VALUE (`Option<&T>` is `Option<T>`,
//! `deref_ref_ty_sized_only`), and a transmute cannot produce the pointee's
//! value without reading memory the reference does not keep current, so the
//! non-null arm is `Some` of a fresh payload: `ite(bits == 0, None,
//! Some(fresh))`. The fresh payload admits the real one, so a proof over it is
//! a proof, and the variant is exact (a non-null reference is `Some`; round 1
//! used a fresh value of the whole sort, which could be `None`, so
//! `r.is_some() == c` failed on a program Kani proves). The payload is recorded
//! as the approximation's freed variable, so a counterexample that reads it is
//! not certified. One that reads only the variant is: an unwrap panic on a
//! symbolic null arm is certified Genuine, where the whole-sort fresh value of
//! round 1 left it OverApproximation (measured on lostwrite round 2; the round 2
//! review, finding 6, noted the round 1 comment claimed this without a
//! measurement, and it was not true then).
//!
//! The constructors are named, not positioned: an Option-like sort lists them in
//! VARIANT order (`option_like_constructors`), so the empty and the payload
//! variant of a payload-first enum (`enum Rev { Has(Box<u16>), Empty }`) are
//! its `None_*` and `Some_*` by name wherever they sit (round 2, finding 1).
//! An integer source makes its pointer as the integer-to-pointer lane does
//! (`int_to_ptr_value_of_operand`, `invalidate_int_to_ptr_object`).

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::debug;

use crate::codegen_ay::chc::stub_codegen::stubs_option_helpers::{
    option_empty_variant_name, option_payload_variant_name,
};
use crate::codegen_ay::shared::mono_ty;
use crate::codegen_ay::types::POINTER_WIDTH;

use super::super::codegen_types::CodegenTypes;
use super::super::codegen_ctx::Havoc;
use super::super::{ChcCtx, chc_fresh_name};

/// Is `ty` plain bits with no provenance (an integer or a float)?
fn ty_is_integer_bits(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_)))
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// The value of a transmute of `bits` (the translated `operand`, of type
    /// `src_ty`) into the niche pointer enum `target_ty`, whose sort is
    /// `target_sort` (see the module documentation).
    pub(in crate::codegen_ay::chc) fn translate_niche_pointer_enum_transmute(
        &mut self,
        operand: &Operand,
        bits: Expr,
        src_ty: Ty,
        target_ty: Ty,
        target_sort: &Sort,
    ) -> Expr {
        if let Some(decoded) =
            self.decode_option_pointer_niche(operand, bits, src_ty, target_ty, target_sort)
        {
            return decoded;
        }
        debug!(%target_sort, "CHC: niche pointer enum target is not Option-shaped");
        debug!(?src_ty, ?target_ty, "CHC: transmute into a niche pointer enum; fresh value");
        let booked = self.record_sound_fallback_reason("transmute_layout_fallback");
        Havoc::booked(booked, chc_fresh_name("__transmute_niche_enum_nondet"), target_sort.clone())
    }

    /// The exact decode of an Option-like target (one empty variant, one
    /// single-field variant), or `None` when the target is not one or its
    /// sort does not have that shape.
    fn decode_option_pointer_niche(
        &mut self,
        operand: &Operand,
        bits: Expr,
        src_ty: Ty,
        target_ty: Ty,
        target_sort: &Sort,
    ) -> Option<Expr> {
        if bits.sort().bitvec_width() != Some(POINTER_WIDTH) {
            return None;
        }
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = target_ty.kind() else { return None };
        let variants = def.variants();
        if variants.len() != 2 {
            return None;
        }
        let some_idx = match (variants[0].fields().len(), variants[1].fields().len()) {
            (0, 1) => 1,
            (1, 0) => 0,
            _ => return None,
        };
        let field_ty = mono_ty::field_ty(variants[some_idx].fields().first()?, &args)?;
        let (payload_ty, payload_by_value) = Self::deref_ref_ty_sized_only(field_ty);

        let dt = target_sort.datatype_sort()?;
        let dt_name = dt.name.clone();
        let none_name = option_empty_variant_name(target_sort)?.to_owned();
        let some_name = option_payload_variant_name(target_sort)?.to_owned();
        let payload_sort =
            dt.constructors.iter().find(|c| c.name == some_name)?.fields.first()?.sort.clone();

        let is_null = bits.clone().eq(Expr::bitvec_const(0u64, POINTER_WIDTH));
        let none = Expr::datatype_constructor(&*dt_name, &*none_name, vec![], target_sort.clone());
        // Bits that fold (`ptr::null()`, a literal) decide the variant here, so
        // a constant null makes no fresh value at all.
        let null_known = match trust_mc_core::chc_const_prop::eval::try_eval_to_const(&is_null)
            .as_ref()
            .map(Expr::value)
        {
            Some(ay_bindings::ExprValue::BoolConst(b)) => Some(*b),
            _ => None,
        };
        if null_known == Some(true) {
            debug!(?src_ty, ?target_ty, "CHC: transmute of null bits decodes to the empty variant");
            return Some(none);
        }
        let some = if payload_by_value {
            let name = chc_fresh_name("__transmute_niche_ref_nondet");
            let booked = self
                .record_sound_fallback_reason_identified("transmute_layout_fallback", Some(&name));
            let payload = Havoc::booked(booked, name, payload_sort.clone());
            Expr::datatype_constructor(&*dt_name, &*some_name, vec![payload], target_sort.clone())
        } else {
            let pointer = if ty_is_integer_bits(src_ty) {
                let pointer = self.int_to_ptr_value_of_operand(bits);
                if !self.int_lift
                    && let Some((obj_id, _offset)) = self.split_pointer(&pointer)
                {
                    self.invalidate_int_to_ptr_object(obj_id, Some(operand));
                }
                pointer
            } else {
                bits
            };
            let payload =
                self.coerce_option_payload_expr(pointer, &payload_sort, payload_ty, &dt_name);
            Expr::datatype_constructor(&*dt_name, &*some_name, vec![payload], target_sort.clone())
        };
        debug!(?src_ty, ?target_ty, payload_by_value, "CHC: transmute decodes a pointer niche");
        if null_known == Some(false) {
            return Some(some);
        }
        Some(Expr::ite(is_null, none, some))
    }
}
