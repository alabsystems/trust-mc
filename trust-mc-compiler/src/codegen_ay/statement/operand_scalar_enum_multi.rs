// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Multi-variant enum constant extraction from MIR allocations.
//!
//! Phase 1b of operand-translation-completeness (Part of #4244, #2463).
//! Handles direct-tagged multi-variant enums with data fields by:
//! 1. Decoding the active variant via `decode_non_unit_enum_variant_index`
//! 2. Extracting variant field values at variant-specific layout offsets
//! 3. Constructing the Datatype expression with the correct constructor
//!
//! Niche-encoded enums are also handled (via the shared decoder).

use super::{Allocation, Expr, StatementCodegen};
use crate::codegen_ay::chc::expr::codegen_expr_constant_payload::decode_non_unit_enum_variant_index;
use tracing::debug;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Extract a multi-variant enum with data fields from an allocation.
    ///
    /// Handles enums like `Result<T, E>`, `MyEnum { A(u32), B(bool, u64) }` where
    /// at least one variant has fields and the enum has 2+ variants (not option-like).
    pub(super) fn codegen_multi_variant_enum_from_alloc(
        &self,
        alloc: &Allocation,
        ty: rustc_public::ty::Ty,
        adt_def: rustc_public::ty::AdtDef,
        args: rustc_public::ty::GenericArgs,
        variants: &[rustc_public::ty::VariantDef],
    ) -> Option<Expr> {
        let variant_count = variants.len();
        let active_idx = decode_non_unit_enum_variant_index(alloc, ty, variant_count)?;
        if active_idx >= variant_count {
            return None;
        }

        let active_variant = &variants[active_idx];
        let dt_name = Self::adt_sort_name(adt_def, &args);
        let dt_sort = Self::infer_adt_sort(adt_def, args.clone())?;

        let variant_name = active_variant.name();
        let constructor_name = crate::codegen_ay::names::scope_option_ctor(&variant_name, &dt_name);

        let field_exprs = if active_variant.fields().is_empty() {
            vec![]
        } else {
            self.extract_variant_fields(alloc, ty, &args, active_variant, active_idx)?
        };
        // A zero-sized field is extracted as the Bool sentinel `true`, but the
        // constructor may declare it as the `Unit` datatype (`ExtData::None(())`
        // inside every `Context::from_waker`): emitting `(None_ExtData true)`
        // against a `Unit` field makes the solver discard the whole command and
        // the harness comes back reason-unknown. Hand a `Unit`-declared field
        // its sole inhabitant instead — exact, a ZST carries no information.
        let declared: Vec<ay_bindings::Sort> = dt_sort
            .datatype_sort()
            .and_then(|dt| dt.constructors.iter().find(|c| c.name == constructor_name))
            .map(|c| c.fields.iter().map(|f| f.sort.clone()).collect())
            .unwrap_or_default();
        let field_exprs: Vec<Expr> = field_exprs
            .into_iter()
            .enumerate()
            .map(|(i, expr)| match declared.get(i) {
                Some(want)
                    if expr.sort() != want
                        && expr.sort().is_bool()
                        && want.datatype_name() == Some("Unit") =>
                {
                    Expr::datatype_constructor("Unit", "Unit_mk", vec![], want.clone())
                }
                _ => expr,
            })
            .collect();

        debug!(
            "codegen_multi_variant_enum_from_alloc: {} variant={} ctor={} fields={}",
            dt_name,
            variant_name,
            constructor_name,
            field_exprs.len()
        );

        Some(Expr::datatype_constructor(&dt_name, &constructor_name, field_exprs, dt_sort))
    }

    /// Extract field values for the active variant of a multi-variant enum.
    ///
    /// Uses variant-specific field offsets from `VariantsShape::Multiple` layout.
    fn extract_variant_fields(
        &self,
        alloc: &Allocation,
        ty: rustc_public::ty::Ty,
        args: &rustc_public::ty::GenericArgs,
        variant: &rustc_public::ty::VariantDef,
        variant_idx: usize,
    ) -> Option<Vec<Expr>> {
        let layout = ty.layout().ok()?;
        let shape = layout.shape();

        let variant_offsets = match &shape.variants {
            rustc_public::abi::VariantsShape::Multiple { variants, .. } => {
                let variant_layout = variants.get(variant_idx)?;
                if let rustc_public::abi::FieldsShape::Arbitrary { offsets } =
                    &variant_layout.fields
                {
                    offsets.iter().map(|off| off.bytes()).collect::<Vec<_>>()
                } else {
                    return None;
                }
            }
            _ => return None,
        };

        let mut field_exprs = Vec::with_capacity(variant.fields().len());

        for (idx, field) in variant.fields().iter().enumerate() {
            let field_ty = field.ty();
            let concrete_ty = Self::resolve_generic_ty(field_ty, args)?;

            let field_size_bytes =
                concrete_ty.layout().ok().map(|l| l.shape().size.bytes()).unwrap_or(usize::MAX);
            if field_size_bytes == 0 {
                field_exprs.push(Expr::bool_const(true));
                continue;
            }

            let field_sort = Self::infer_sort_from_ty(concrete_ty)?;
            let offset = *variant_offsets.get(idx)?;

            let field_expr = self.read_field_from_alloc(alloc, concrete_ty, &field_sort, offset)?;
            field_exprs.push(field_expr);
        }

        Some(field_exprs)
    }
}
