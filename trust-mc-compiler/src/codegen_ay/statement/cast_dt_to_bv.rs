// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! DT→BV (Datatype-to-bitvector) cast handler.
//!
//! Handles enum discriminant extraction, single-field struct unwrapping,
//! fat-pointer data extraction, and TypeId transmute recovery.
//!
//! Extracted from `cast.rs` — Part of #4206.

use ay_bindings::{Expr, Sort, SortInner};
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::warn;

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::ptr_repr::PtrRepr;
use crate::codegen_ay::types::POINTER_WIDTH;

pub(super) struct EnumDiscrInfo {
    pub(super) values: Vec<u128>,
    pub(super) repr_width: u32,
    pub(super) is_signed: bool,
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    pub(super) fn codegen_dt_to_bv(
        &mut self,
        expr: &Expr,
        operand: &Operand,
        dt: &ay_bindings::DatatypeSort,
        dst_width: u32,
        enum_discrs: Option<EnumDiscrInfo>,
        src_widen_signed: bool,
    ) -> Option<Expr> {
        // Keep inferred Sort alive so we can borrow &DatatypeSort from it,
        // avoiding a deep clone of DatatypeSort (String + Vec<Constructor>).
        let inferred_sort: Option<Sort> = if dt.constructors.is_empty() {
            operand
                .ty(self.body.locals())
                .into_option()
                .and_then(|ty| {
                    if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
                        Self::infer_adt_sort(def, args)
                    } else {
                        None
                    }
                })
                .filter(ay_bindings::Sort::is_datatype)
        } else {
            None
        };

        let eff_dt: &ay_bindings::DatatypeSort =
            inferred_sort.as_ref().and_then(|s| s.datatype_sort()).unwrap_or(dt);

        if eff_dt.constructors.len() == 1
            && let Some(c) = eff_dt.constructors.first()
            && c.fields.len() == 1
            && let Some(f) = c.fields.first()
        {
            // field_select accepts impl Into<String> — pass &str to avoid String clones
            let fe = expr.clone().field_select(&*eff_dt.name, &*f.name, f.sort.clone());
            if let SortInner::BitVec(sb) = f.sort.inner() {
                if sb.width == dst_width {
                    return Some(fe);
                } else if sb.width < dst_width {
                    return Some(if src_widen_signed {
                        fe.sign_extend(dst_width - sb.width)
                    } else {
                        fe.zero_extend(dst_width - sb.width)
                    });
                }
                return Some(fe.extract(dst_width - 1, 0));
            }
        }

        // Fat-pointer datatype → the DATA ADDRESS. `dt_fat_pointer_repr` reads the
        // two field roles off the declaration and hands back a `PtrRepr`, so what
        // is selected here is a `Loc` by construction — not "field 0, because it
        // happened to be bv64".
        if let Some(repr) = Self::dt_fat_pointer_repr(expr, eff_dt) {
            let ptr_expr = repr.into_data().into_expr();
            if POINTER_WIDTH == dst_width {
                return Some(ptr_expr);
            } else if POINTER_WIDTH < dst_width {
                return Some(ptr_expr.zero_extend(dst_width - POINTER_WIDTH));
            }
            return Some(ptr_expr.extract(dst_width - 1, 0));
        }

        if dt.constructors.len() > 1 || (dt.constructors.len() == 1 && enum_discrs.is_some()) {
            let mkbv = |v: u128, i: Option<&EnumDiscrInfo>| -> Expr {
                if let Some(i) = i
                    && i.repr_width < dst_width
                {
                    let n = Expr::bitvec_const(v, i.repr_width);
                    if i.is_signed {
                        n.sign_extend(dst_width - i.repr_width)
                    } else {
                        n.zero_extend(dst_width - i.repr_width)
                    }
                } else {
                    Expr::bitvec_const(v, dst_width)
                }
            };
            // When enum_discrs is None, we fall back to positional discriminants
            // (variant 0 → 0, variant 1 → 1, etc.). This is correct for C-like enums
            // without explicit #[repr] discriminant values, but wrong for enums with
            // non-default discriminants (e.g., #[repr(u8)] enum Foo { A = 5 }).
            // The fallback fires when MIR type info is unavailable (src_ty is None).
            if enum_discrs.is_none() {
                warn!(
                    dt_name = %dt.name,
                    num_constructors = dt.constructors.len(),
                    "codegen_dt_to_bv: enum discriminant info unavailable, \
                     using positional fallback (unsound for #[repr] enums with non-default values)"
                );
                self.ctx.unsupported_with_fallback(
                    "Enum discriminant cast",
                    format!(
                        "DT '{}' discriminant info unavailable; positional fallback may be \
                         wrong for #[repr] enums with non-default discriminant values",
                        dt.name
                    ),
                );
                // Fail-closed: inject unconditional violation so the solver
                // reports CTREX instead of false PROOF when positional
                // discriminant mapping is wrong. Part of #3017.
                self.record_violation_guarded(
                    Expr::bool_const(true),
                    "unsound_enum_discriminant_positional_fallback",
                );
            }
            if dt.constructors.len() == 1 {
                return Some(mkbv(
                    enum_discrs.as_ref().and_then(|d| d.values.first().copied()).unwrap_or(0),
                    enum_discrs.as_ref(),
                ));
            }
            let mut r = mkbv(
                enum_discrs.as_ref().and_then(|d| d.values.first().copied()).unwrap_or(0),
                enum_discrs.as_ref(),
            );
            for (i, c) in dt.constructors.iter().enumerate().rev() {
                let ic = expr.clone().is_constructor(&*dt.name, &*c.name);
                r = Expr::ite(
                    ic,
                    mkbv(
                        enum_discrs
                            .as_ref()
                            .and_then(|d| d.values.get(i).copied())
                            .unwrap_or(i as u128),
                        enum_discrs.as_ref(),
                    ),
                    r,
                );
            }
            return Some(r);
        }
        // Part of #3635: TypeId is modeled as opaque bv128 (sort_inference_adt.rs:62).
        // When a TypeId Datatype expression reaches DT→BV (e.g., from a Transmute
        // cast where sort inference short-circuited past Datatype construction),
        // the single-field extraction above fails because the DT has empty
        // constructors. Return the operand re-translated as bv128 via the scalar
        // path in operand_scalar.rs, which handles TypeId with provenance-aware
        // raw-byte extraction.
        if (dt.name == "TypeId" || dt.name.ends_with("::TypeId")) && dst_width == 128 {
            if let Some(ty) = operand.ty(self.body.locals()).into_option()
                && let TyKind::RigidTy(RigidTy::Adt(..)) = ty.kind()
            {
                // Try re-translating the operand through the normal path which
                // includes the TypeId special case in operand_scalar.rs.
                if let Some(scalar) = self.codegen_operand(operand)
                    && scalar.sort().bitvec_width() == Some(128)
                {
                    return Some(scalar);
                }
            }
        }

        // Unsupported: DT→BV fallback. None of the known patterns matched
        // (single-field extraction, fat-pointer, enum discriminant).
        // Returning None lets the caller handle this as an untranslatable cast
        // rather than silently producing an unconstrained variable (false-proof risk).
        // Part of #2423.
        warn!(
            src = %dt.name, dst_width,
            "unsupported DT→BV cast: no known encoding pattern matched"
        );
        self.ctx.unsupported("Cast", format!("DT→BV fallback: {} → bv{}", dt.name, dst_width));
        None
    }

    /// Reads the `(data, metadata)` field roles off a fat-pointer datatype.
    ///
    /// Nothing is inferred here — both role sources are **declarations**:
    ///
    /// * field NAMES. A field literally called `fld_ptr` / `data` is the address
    ///   and one called `fld_len` / `fld_vtable` is the metadata. The declaration
    ///   states the roles; this function only reports them, which is why the
    ///   `Loc` and `Val` minted below are genuine producers and not guesses.
    /// * the datatype NAME. `Slice_*` / `Dyn_*` datatypes carry the positional
    ///   convention "field 0 is data, field 1 is metadata". This half is
    ///   `docs/addr-vs-value-conversion-queue.md` §4 item 7: the declaration
    ///   carries **no** field roles, so a naming convention is standing in for
    ///   one and no type can check it. Closing it needs the per-datatype
    ///   field-role table — the same keystone as the slot-layout authority — not
    ///   this refactor. It is left exactly as narrow as it was: the convention is
    ///   not extended to any other datatype, and no predicate here is widened.
    ///
    /// The `POINTER_WIDTH` tests are retained on purpose. They are no longer
    /// deciding address-vs-value (the declared names did that); they check that
    /// the declared roles are actually pointer-shaped before the roles are
    /// trusted, which is a narrowing and not a guess.
    pub(super) fn dt_fat_pointer_repr(
        expr: &Expr,
        sdt: &ay_bindings::DatatypeSort,
    ) -> Option<PtrRepr> {
        if sdt.constructors.len() != 1 {
            return None;
        }
        let c = sdt.constructors.first()?;
        if c.fields.len() < 2 {
            return None;
        }

        let named_ptr = c
            .fields
            .iter()
            .find(|x| matches!(x.name.as_str(), "ptr" | "fld_ptr" | "data" | "fld_data"));
        let named_meta = c.fields.iter().find(|x| {
            matches!(
                x.name.as_str(),
                "len" | "fld_len" | "meta" | "fld_meta" | "vtable" | "fld_vtable"
            )
        });
        let (ptr_field, meta_field) = match (named_ptr, named_meta) {
            (Some(ptr_field), Some(meta_field)) => (ptr_field, meta_field),
            _ if sdt.name.starts_with("Slice_") || sdt.name.starts_with("Dyn_") => {
                (&c.fields[0], &c.fields[1])
            }
            _ => return None,
        };

        let (SortInner::BitVec(pb), SortInner::BitVec(mb)) =
            (ptr_field.sort.inner(), meta_field.sort.inner())
        else {
            return None;
        };
        if pb.width != POINTER_WIDTH || mb.width != POINTER_WIDTH {
            return None;
        }

        let data = Loc::of_address(expr.clone().field_select(
            &*sdt.name,
            &*ptr_field.name,
            ptr_field.sort.clone(),
        ));
        let meta = Val::of_value(expr.clone().field_select(
            &*sdt.name,
            &*meta_field.name,
            meta_field.sort.clone(),
        ));
        Some(PtrRepr::from_declared_roles(data, meta))
    }
}
