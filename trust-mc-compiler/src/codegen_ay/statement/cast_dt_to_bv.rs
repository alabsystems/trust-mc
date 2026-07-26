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

        let sdt = eff_dt;
        if sdt.constructors.len() == 1
            && let Some(c) = sdt.constructors.first()
            && c.fields.len() >= 2
        {
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
            let ptr_and_meta = if let (Some(ptr_field), Some(meta_field)) = (named_ptr, named_meta)
            {
                Some((ptr_field, meta_field))
            } else if (sdt.name.starts_with("Slice_") || sdt.name.starts_with("Dyn_"))
                && c.fields.len() >= 2
            {
                Some((&c.fields[0], &c.fields[1]))
            } else {
                None
            };

            if let Some((ptr_field, meta_field)) = ptr_and_meta
                && let SortInner::BitVec(pb) = ptr_field.sort.inner()
                && let SortInner::BitVec(mb) = meta_field.sort.inner()
                && pb.width == POINTER_WIDTH
                && mb.width == POINTER_WIDTH
            {
                let ptr_expr =
                    expr.clone().field_select(&*sdt.name, &*ptr_field.name, ptr_field.sort.clone());
                if pb.width == dst_width {
                    return Some(ptr_expr);
                } else if pb.width < dst_width {
                    return Some(ptr_expr.zero_extend(dst_width - pb.width));
                }
                return Some(ptr_expr.extract(dst_width - 1, 0));
            }
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
}
