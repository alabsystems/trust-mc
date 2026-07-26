// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Enum and float scalar extraction from MIR allocations.
//!
//! Extracted from `operand_scalar.rs` — Part of #4206.

use super::{Allocation, Expr, GlobalAlloc, IntoOption, LayoutOf, SortInner, StatementCodegen};
use crate::codegen_ay::chc::codegen_stmt_aggregate_adt::sign_extend_discr_val;
use crate::codegen_ay::types::POINTER_WIDTH;
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_public::rustc_internal;
use tracing::debug;

fn read_alloc_uint_le(alloc: &Allocation, offset: usize, byte_count: usize) -> Option<u128> {
    let bytes = alloc.bytes.get(offset..offset.checked_add(byte_count)?)?;
    let mut value = 0u128;
    for (i, byte) in bytes.iter().enumerate() {
        if let Some(b) = byte {
            value |= (*b as u128) << (i * 8);
        }
    }
    Some(value)
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Extract a unit enum constant from an allocation.
    ///
    /// Part of #3543: Sign-extend signed discriminants (CHC parity for #3536).
    /// Uses `sign_extend_discr_val` instead of the previous Ordering-only special case.
    pub(super) fn codegen_unit_enum_from_alloc(
        &self,
        alloc: &Allocation,
        adt_def: rustc_public::ty::AdtDef,
        variants: &[rustc_public::ty::VariantDef],
    ) -> Option<Expr> {
        // All unit enums use 32-bit bitvecs to match sort_inference.rs.
        let num_variants = variants.len();
        let bits: u32 = if num_variants <= 65536 { 32 } else { 64 };

        // Read raw unsigned bytes from the allocation.
        let value = alloc.read_uint().into_option()?;
        let value_u128 = if bits >= 128 { value } else { value & ((1u128 << bits) - 1) };

        // Get the discriminant type from variant 0 (type is the same for all variants).
        let internal_def = rustc_internal::internal(self.ctx.tcx, adt_def);
        let discr =
            internal_def.discriminant_for_variant(self.ctx.tcx, InternalVariantIdx::from_usize(0));

        // Sign-extend if the discriminant type is signed (e.g., Ordering repr(i8)).
        let discriminant_val = sign_extend_discr_val(value_u128, discr.ty, self.ctx.tcx, bits);
        Some(Expr::bitvec_const(discriminant_val, bits))
    }

    /// Extract an Option-like enum from an allocation (#407).
    /// Option-like: 2 variants, one empty + one with 1 field.
    pub(super) fn codegen_option_like_from_alloc(
        &self,
        alloc: &Allocation,
        option_ty: rustc_public::ty::Ty,
        adt_def: rustc_public::ty::AdtDef,
        args: rustc_public::ty::GenericArgs,
        variants: &[rustc_public::ty::VariantDef],
    ) -> Option<Expr> {
        let (some_idx, some_variant) =
            variants.iter().enumerate().find(|(_, v)| v.fields().len() == 1)?;
        let field_ty = some_variant.fields()[0].ty();
        let concrete_ty = Self::resolve_generic_ty(field_ty, &args)?;
        let dt_name = Self::adt_sort_name(adt_def, &args);
        let dt_sort = Self::infer_adt_sort(adt_def, args)?;

        // Check discriminant to determine Some vs None
        let option_layout = LayoutOf::new(option_ty);
        let payload_layout = LayoutOf::new(concrete_ty);
        let payload_size = payload_layout.size_of().unwrap_or(0);
        let option_size = option_layout.size_of().unwrap_or(alloc.bytes.len());
        let explicit_tag_bytes = option_size.saturating_sub(payload_size);
        let payload_offset =
            if explicit_tag_bytes > 0 { explicit_tag_bytes.min(alloc.bytes.len()) } else { 0 };
        let discrim_val = if explicit_tag_bytes > 0 {
            read_alloc_uint_le(alloc, 0, explicit_tag_bytes).unwrap_or(0)
        } else {
            alloc.read_uint().into_option().unwrap_or(0)
        };
        let is_some = discrim_val == some_idx as u128;

        if is_some {
            // Try to extract the inner value
            if let Some(inner_sort) = Self::infer_sort_from_ty(concrete_ty) {
                // Check for Option<&T> promotion to Option<T>
                if let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Ref(
                    _,
                    pointee_ty,
                    _,
                )) = concrete_ty.kind()
                {
                    if let Some(result) =
                        self.codegen_option_ref_promotion(alloc, pointee_ty, &dt_name)
                    {
                        return Some(result);
                    }
                }

                // Extract value from allocation bytes
                if let Some(bv_width) = inner_sort.bitvec_width() {
                    let byte_count = (bv_width / 8) as usize;
                    let value = read_alloc_uint_le(alloc, payload_offset, byte_count)?;
                    let some_ctor =
                        crate::codegen_ay::names::scope_option_ctor(&some_variant.name(), &dt_name);
                    return Some(Expr::datatype_constructor(
                        &dt_name,
                        &some_ctor,
                        vec![Expr::bitvec_const(value, bv_width)],
                        dt_sort,
                    ));
                }
            }
        } else {
            // None variant
            let none_variant = variants.iter().find(|v| v.fields().is_empty())?;
            let none_ctor =
                crate::codegen_ay::names::scope_option_ctor(&none_variant.name(), &dt_name);
            return Some(Expr::datatype_constructor(&dt_name, &none_ctor, vec![], dt_sort));
        }

        None
    }

    /// Promote Option<&T> to Option<T> by following provenance (#3133).
    pub(super) fn codegen_option_ref_promotion(
        &self,
        alloc: &Allocation,
        pointee_ty: rustc_public::ty::Ty,
        dt_name: &str,
    ) -> Option<Expr> {
        let pointee_sort = Self::infer_sort_from_ty(pointee_ty)?;
        // Create Option<T> sort with pointee value sort
        let val_option_sort = self.make_option_sort(pointee_sort.clone());
        // Part of #2267: borrow instead of .to_string() — option_some_constructor_name takes &str.
        let val_dt_name = val_option_sort.datatype_name().unwrap_or(dt_name);
        let val_some = crate::codegen_ay::names::option_some_constructor_name(val_dt_name);

        // Follow provenance to extract pointee value
        if !alloc.provenance.ptrs.is_empty() {
            let (_, prov) = &alloc.provenance.ptrs[0];
            let alloc_id = prov.0;
            if let GlobalAlloc::Memory(target_alloc) = GlobalAlloc::from(alloc_id) {
                if let Some(pointee_expr) =
                    self.codegen_scalar_from_alloc(&target_alloc, pointee_ty)
                {
                    debug!(
                        "#3133: promoted Option<&T> → Option<T> with value sort {:?}",
                        pointee_sort
                    );
                    return Some(Expr::datatype_constructor(
                        val_dt_name,
                        &val_some,
                        vec![pointee_expr],
                        val_option_sort.clone(),
                    ));
                }
            }
        }
        None
    }

    /// Extract a single-variant enum/struct with data fields from an allocation (#3094).
    ///
    /// Phase 1a of operand-translation-completeness: supports multi-field structs
    /// with >1 non-ZST field by extracting each field from the allocation bytes
    /// at its layout offset. Handles BV, Bool, ZST, nested Datatype, and Array
    /// field sorts.
    pub(super) fn codegen_single_variant_enum_from_alloc(
        &self,
        alloc: &Allocation,
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
            let field_ty = field.ty();
            let Some(concrete_ty) = Self::resolve_generic_ty(field_ty, &args) else {
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
            let offset = layout.field_offset(idx).unwrap_or(0);

            // Try to extract the field value based on its sort type.
            let field_expr = if let Some(field_width) = field_sort.bitvec_width() {
                // BV fields: read bytes at offset (original path).
                let field_byte_count = (field_width as usize) / 8;
                let mut value: u128 = 0;
                if let Some(bytes) = alloc.bytes.get(offset..offset + field_byte_count) {
                    for (i, byte) in bytes.iter().enumerate() {
                        if let Some(b) = byte {
                            value |= (*b as u128) << (i * 8);
                        }
                    }
                }
                Some(Expr::bitvec_const(value, field_width))
            } else if field_sort.is_bool() {
                // Bool fields: read 1 byte.
                let byte_val = alloc.bytes.get(offset).and_then(|b| *b).unwrap_or(0);
                Some(Expr::bool_const(byte_val != 0))
            } else if let SortInner::Datatype(_) = field_sort.inner() {
                // Nested Datatype fields: recursively extract from allocation bytes.
                Self::extract_datatype_field_from_alloc(alloc, offset, concrete_ty, &field_sort)
            } else if field_sort.is_array() {
                // Array fields: extract element-wise from allocation bytes.
                self.extract_array_field_from_alloc(alloc, offset, concrete_ty)
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

    /// Extract a nested Datatype field value from allocation bytes at a given offset.
    ///
    /// Used by `codegen_single_variant_enum_from_alloc` for struct fields that are
    /// themselves structs/tuples (Datatype sort). Reads sub-field values from the
    /// allocation bytes using the field layout offsets relative to `base_offset`.
    fn extract_datatype_field_from_alloc(
        alloc: &Allocation,
        base_offset: usize,
        field_ty: rustc_public::ty::Ty,
        field_sort: &ay_bindings::Sort,
    ) -> Option<Expr> {
        let SortInner::Datatype(dt) = field_sort.inner() else {
            return None;
        };
        let ctor = dt.constructors.first()?;

        // Try to get the field layout for offset computation.
        let field_layout = field_ty.layout().ok()?;
        let field_shape = field_layout.shape();

        let mut sub_field_exprs = Vec::with_capacity(ctor.fields.len());
        for (sub_idx, sub_field_info) in ctor.fields.iter().enumerate() {
            // Compute sub-field offset within the nested struct.
            let sub_offset = if let rustc_public::abi::FieldsShape::Arbitrary { ref offsets } =
                field_shape.fields
            {
                offsets.get(sub_idx).map(|off| off.bytes()).unwrap_or(0)
            } else {
                0
            };
            let abs_offset = base_offset + sub_offset;

            let sub_expr = if sub_field_info.sort.is_bool() {
                let byte_val = alloc.bytes.get(abs_offset).and_then(|b| *b).unwrap_or(0);
                Expr::bool_const(byte_val != 0)
            } else if let Some(bits) = sub_field_info.sort.bitvec_width() {
                let bw = (bits as usize / 8).max(1);
                let mut value: u128 = 0;
                if let Some(bytes) = alloc.bytes.get(abs_offset..abs_offset + bw) {
                    for (i, byte) in bytes.iter().enumerate() {
                        if let Some(b) = byte {
                            value |= (*b as u128) << (i * 8);
                        }
                    }
                }
                Expr::bitvec_const(value, bits)
            } else {
                // Unsupported sub-field sort (deeply nested DT, array, etc.).
                // Bail on the entire nested field.
                return None;
            };
            sub_field_exprs.push(sub_expr);
        }

        Some(Expr::datatype_constructor(&dt.name, &ctor.name, sub_field_exprs, field_sort.clone()))
    }

    /// Extract an Array-sorted field value from allocation bytes at a given offset.
    ///
    /// Used by `codegen_single_variant_enum_from_alloc` for struct fields that are
    /// arrays (e.g., `[u32; 4]`). Reads element values from the allocation bytes
    /// starting at `base_offset`.
    fn extract_array_field_from_alloc(
        &self,
        alloc: &Allocation,
        base_offset: usize,
        field_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        // Match the field type to get element type and length.
        let (elem_ty, len) = match field_ty.kind() {
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Array(
                elem_ty,
                len_const,
            )) => {
                let len = len_const.eval_target_usize().into_option()? as usize;
                (elem_ty, len)
            }
            _ => return None,
        };

        let elem_sort = Self::infer_sort_from_ty(elem_ty)?;
        let elem_width = elem_sort.bitvec_width()?;
        let elem_bytes = (elem_width as usize) / 8;

        // Verify allocation has enough bytes.
        if alloc.bytes.len() < base_offset + len * elem_bytes {
            return None;
        }

        // Build const_array base and store each element.
        let zero_elem = Expr::bitvec_const(0u128, elem_width);
        let mut result = Expr::const_array(crate::codegen_ay::types::ptr_sort(), zero_elem);

        for i in 0..len {
            let abs_offset = base_offset + i * elem_bytes;
            let mut value: u128 = 0;
            if let Some(bytes) = alloc.bytes.get(abs_offset..abs_offset + elem_bytes) {
                for (j, byte) in bytes.iter().enumerate() {
                    if let Some(b) = byte {
                        value |= (*b as u128) << (j * 8);
                    }
                }
            }
            let idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
            let elem = Expr::bitvec_const(value, elem_width);
            result = result.store(idx, elem);
        }

        debug!(
            "extract_array_field_from_alloc: {} elements of width {} at offset {}",
            len, elem_width, base_offset
        );
        Some(result)
    }

    /// Read a float constant from an allocation as an IEEE 754 bitvector.
    ///
    /// Part of #3094: F32 → BV32, F64 → BV64, matching sort_inference.rs.
    #[must_use]
    pub(super) fn float_scalar_to_expr(
        alloc: &Allocation,
        float_ty: rustc_public::ty::FloatTy,
    ) -> Option<Expr> {
        let width = crate::codegen_ay::types::float_ty_to_bitvec_width(float_ty);
        let byte_count = (width / 8) as usize;
        if alloc.bytes.len() >= byte_count {
            let mut value: u128 = 0;
            for (i, byte) in alloc.bytes.iter().take(byte_count).enumerate() {
                if let Some(b) = byte {
                    value |= (*b as u128) << (i * 8);
                }
            }
            debug!("float_scalar_to_expr: width={} value={:#x}", width, value);
            Some(Expr::bitvec_const(value, width))
        } else {
            None
        }
    }
}
