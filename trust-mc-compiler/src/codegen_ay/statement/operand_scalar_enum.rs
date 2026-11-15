// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Enum and float scalar extraction from MIR allocations.
//!
//! Extracted from `operand_scalar.rs` — Part of #4206.

use super::{Expr, LayoutOf, StatementCodegen};
use crate::codegen_ay::chc::expr::codegen_expr_constant_payload::{
    decode_non_unit_enum_variant_index, fieldless_enum_const_bits, ty_is_fieldless_enum,
};
use crate::codegen_ay::shared::const_pointer::{self, ConstRead};
use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use tracing::debug;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Extract a unit enum constant from an allocation.
    ///
    /// Part of #3543: Sign-extend signed discriminants (CHC parity for #3536).
    /// Uses `sign_extend_discr_val` instead of the previous Ordering-only special case.
    pub(super) fn codegen_unit_enum_from_alloc(
        &self,
        alloc: &dyn ConstRead,
        adt_def: rustc_public::ty::AdtDef,
        variants: &[rustc_public::ty::VariantDef],
    ) -> Option<Expr> {
        // All unit enums use 32-bit bitvecs to match sort_inference.rs.
        let num_variants = variants.len();
        let bits: u32 = if num_variants <= 65536 { 32 } else { 64 };

        // The discriminant, sign-extended as the aggregate path does, decoded
        // from the tag's own width: sign-extending the raw tag from the
        // DISCRIMINANT type's width left a default-repr `enum G { N = -1 }`
        // (discriminant type `isize`, one-byte tag) at `0xFF`.
        let discriminant_val = fieldless_enum_const_bits(adt_def.ty(), alloc, 0, bits)?;
        Some(Expr::bitvec_const(discriminant_val, bits))
    }

    /// Extract an Option-like enum from an allocation (#407).
    /// Option-like: 2 variants, one empty + one with 1 field.
    pub(super) fn codegen_option_like_from_alloc(
        &self,
        alloc: &dyn ConstRead,
        option_ty: rustc_public::ty::Ty,
        adt_def: rustc_public::ty::AdtDef,
        args: rustc_public::ty::GenericArgs,
        variants: &[rustc_public::ty::VariantDef],
    ) -> Option<Expr> {
        let (some_idx, some_variant) =
            variants.iter().enumerate().find(|(_, v)| v.fields().len() == 1)?;
        let concrete_ty = mono_ty::field_ty(&some_variant.fields()[0], &args)?;
        let dt_name = Self::adt_sort_name(adt_def, &args);
        let dt_sort = Self::infer_adt_sort(adt_def, args)?;

        // The active variant, from the layout's own tag: its tag field's
        // offset and width, direct or niche (`Option<char>` keeps `None` at
        // 0x110000, `Option<Ordering>` at 2, `Option<&T>` at null). A guessed
        // tag (`size_of(Option<T>) - size_of(T)` bytes at 0, uninitialized
        // padding read as 0) read `Some('a')` as `None`, and the BMC lane
        // proved `assert!(!(o == Some('a')))` for a joined `o`
        // (tools/soundness-duals/negative/review_r11a_other_payloads.rs).
        let is_some =
            decode_non_unit_enum_variant_index(alloc, option_ty, variants.len())? == some_idx;
        if !is_some {
            let none_variant = variants.iter().find(|v| v.fields().is_empty())?;
            let none_ctor =
                crate::codegen_ay::names::scope_option_ctor(&none_variant.name(), &dt_name);
            return Some(Expr::datatype_constructor(&dt_name, &none_ctor, vec![], dt_sort));
        }

        // The payload at its own offset in the Some variant's layout.
        let payload_offset = LayoutOf::new(option_ty).variant_field_offset(some_idx, 0)?;
        let inner_sort = Self::infer_sort_from_ty(concrete_ty)?;
        // Check for Option<&T> promotion to Option<T>
        if let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Ref(_, pointee_ty, _)) =
            concrete_ty.kind()
        {
            if let Some(result) =
                self.codegen_option_ref_promotion(alloc, payload_offset, pointee_ty, &dt_name)
            {
                return Some(result);
            }
        }
        // A bitvector payload (a fieldless enum's discriminant, an integer,
        // or a pointer slot's value) read under the slot clause.
        if inner_sort.bitvec_width().is_some() {
            let payload_size = LayoutOf::new(concrete_ty).size_of()?;
            if !ty_is_fieldless_enum(concrete_ty)
                && inner_sort.bitvec_width() != u32::try_from(payload_size * 8).ok()
            {
                return None;
            }
            let value =
                self.read_field_from_alloc(alloc, concrete_ty, &inner_sort, payload_offset)?;
            let some_ctor =
                crate::codegen_ay::names::scope_option_ctor(&some_variant.name(), &dt_name);
            return Some(Expr::datatype_constructor(&dt_name, &some_ctor, vec![value], dt_sort));
        }
        None
    }

    /// Promote Option<&T> to Option<T> by reading the pointee (#3133): the
    /// window the payload's pointer names in a FIXED target, at the offset
    /// the pointer carries (`const_pointer::fixed_pointee`), never the
    /// target from byte 0.
    pub(super) fn codegen_option_ref_promotion(
        &self,
        alloc: &dyn ConstRead,
        payload_offset: usize,
        pointee_ty: rustc_public::ty::Ty,
        dt_name: &str,
    ) -> Option<Expr> {
        let pointee_sort = Self::infer_sort_from_ty(pointee_ty)?;
        // Create Option<T> sort with pointee value sort
        let val_option_sort = self.make_option_sort(pointee_sort.clone());
        // Part of #2267: borrow instead of .to_string() — option_some_constructor_name takes &str.
        let val_dt_name = val_option_sort.datatype_name().unwrap_or(dt_name);
        let val_some = crate::codegen_ay::names::option_some_constructor_name(val_dt_name);

        let (_, window) =
            const_pointer::fixed_pointee(self.ctx.tcx, alloc, payload_offset, pointee_ty)?;
        let pointee_expr = self.codegen_scalar_from_bytes(&window, pointee_ty)?;
        debug!("#3133: promoted Option<&T> → Option<T> with value sort {:?}", pointee_sort);
        Some(Expr::datatype_constructor(
            val_dt_name,
            &val_some,
            vec![pointee_expr],
            val_option_sort.clone(),
        ))
    }

    /// Extract a single-variant enum/struct with data fields from an allocation (#3094).
    ///
    /// Phase 1a of operand-translation-completeness: supports multi-field structs
    /// with >1 non-ZST field by extracting each field from the allocation bytes
    /// at its layout offset. Handles BV, Bool, ZST, nested Datatype, and Array
    /// field sorts.
    pub(super) fn codegen_single_variant_enum_from_alloc(
        &self,
        alloc: &dyn ConstRead,
        ty: rustc_public::ty::Ty,
        adt_def: rustc_public::ty::AdtDef,
        args: rustc_public::ty::GenericArgs,
        variants: &[rustc_public::ty::VariantDef],
    ) -> Option<Expr> {
        let variant = &variants[0];
        let layout = LayoutOf::new(ty);
        let mut field_exprs = Vec::new();
        let mut all_fields_ok = true;

        for (idx, field) in variant.fields().iter().enumerate() {
            let Some(concrete_ty) = mono_ty::field_ty(field, &args) else {
                all_fields_ok = false;
                break;
            };

            // Check if field is ZST (zero-sized type): produce canonical bool_const(true).
            let field_size_bytes =
                concrete_ty.layout().ok().map(|l| l.shape().size.bytes()).unwrap_or(usize::MAX);
            if field_size_bytes == 0 {
                field_exprs.push(Expr::bool_const(true));
                continue;
            }

            let Some(field_sort) = Self::infer_sort_from_ty(concrete_ty) else {
                all_fields_ok = false;
                break;
            };
            let Some(offset) = layout.field_offset(idx) else {
                all_fields_ok = false;
                break;
            };

            // A bitvector field whose type is not exactly the sort's width
            // (other than a fieldless enum, decoded from its own tag bytes)
            // drops the constant instead of inventing bytes. Reading the
            // sort's four bytes from `S { a: Ordering::Greater, b: 2 }` (a
            // one-byte field) found none and produced `a == 0`, and a joined
            // `o` was proved unequal to the constant it equals
            // (tools/soundness-duals/negative/joined_enum_constant_payloads.rs).
            let width_ok = match field_sort.bitvec_width() {
                Some(width) => {
                    ty_is_fieldless_enum(concrete_ty)
                        || u32::try_from(field_size_bytes * 8).ok() == Some(width)
                }
                None => true,
            };
            let field_expr = if width_ok {
                self.read_field_from_alloc(alloc, concrete_ty, &field_sort, offset)
            } else {
                None
            };

            match field_expr {
                Some(expr) => field_exprs.push(expr),
                None => {
                    all_fields_ok = false;
                    break;
                }
            }
        }

        if all_fields_ok && field_exprs.len() == variant.fields().len() {
            let dt_name = Self::adt_sort_name(adt_def, &args);
            if let Some(dt_sort) = Self::infer_adt_sort(adt_def, args) {
                let variant_name = variant.name();
                // A single-variant STRUCT (e.g. a const `RangeInclusive<u8>`, 0x80..=0x9f)
                // declares its sole constructor as `{dt_name}_mk` via Sort::struct_type, so
                // scope_option_ctor's `{variant}_{dt_name}` would DOUBLE-NAME it
                // (`RangeInclusive_RangeInclusive_u8`) and never match the declared
                // `RangeInclusive_u8_mk` → an undeclared "unknown constant" in the .smt2.
                // For structs, take the constructor name from the declared sort; keep
                // scope_option_ctor for genuine (single-variant) enums.
                let constructor_name = if adt_def.kind() == rustc_public::ty::AdtKind::Struct {
                    crate::codegen_ay::names::resolve_ctor_name(&dt_sort, &dt_name)
                } else {
                    crate::codegen_ay::names::scope_option_ctor(&variant_name, &dt_name)
                };
                debug!(
                    "codegen_scalar_from_alloc: single-variant enum {} -> {}({} fields)",
                    dt_name,
                    constructor_name,
                    field_exprs.len()
                );
                return Some(Expr::datatype_constructor(
                    &dt_name,
                    &constructor_name,
                    field_exprs,
                    dt_sort,
                ));
            }
        }

        None
    }

    /// Read a float constant from an allocation as an IEEE 754 bitvector.
    ///
    /// Part of #3094: F32 → BV32, F64 → BV64, matching sort_inference.rs.
    #[must_use]
    pub(super) fn float_scalar_to_expr(
        bytes: &dyn ConstRead,
        float_ty: rustc_public::ty::FloatTy,
    ) -> Option<Expr> {
        let width = crate::codegen_ay::types::float_ty_to_bitvec_width(float_ty);
        let value = bytes.read_uint_at(0, (width / 8) as usize)?;
        debug!("float_scalar_to_expr: width={} value={:#x}", width, value);
        Some(Expr::bitvec_const(value, width))
    }
}
