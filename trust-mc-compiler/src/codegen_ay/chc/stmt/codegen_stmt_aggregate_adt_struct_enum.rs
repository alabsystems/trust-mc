// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Struct and general enum aggregate construction for CHC encoding.
//!
//! Extracted from codegen_stmt_aggregate_adt.rs per #4130 (500 LOC threshold).
//! Contains:
//! - `translate_struct_aggregate`: regular struct (Range, String, user-defined structs)
//! - `translate_general_enum_aggregate`: multi-variant enums (Result, ControlFlow, user-defined)

use std::collections::HashSet;
use std::sync::atomic::Ordering;

use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;
use rustc_public::ty::{AdtDef, GenericArgs, VariantDef};
use tracing::{debug, warn};

use crate::codegen_ay::chc::call::canonical_zst_expr_for_sort;
use crate::codegen_ay::chc::call::codegen_call_kani_model_dst::is_zst_ty;
use crate::codegen_ay::names::{self, enum_sort, struct_sort};
use crate::codegen_ay::types::{
    SignExtension, coerce_bitvec_width_safe, coerce_bool_to_unit_datatype,
    coerce_datatype_structural, unflatten_bitvec_to_datatype,
};

use super::codegen_expr_signedness::ty_signedness;
use super::codegen_types::CodegenTypes;
use super::codegen_types_adt_sort::CodegenTypesAdtSort;
use super::{ChcCtx, UNDEF_COUNTER, declare_pending_var};
use crate::codegen_ay::chc::decl::codegen_types_adt::CodegenTypesAdt;
use crate::codegen_ay::shared::signedness_fallback_for_cast_or_coerce;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Translate a regular struct ADT aggregate construction.
    ///
    /// Handles structs like Range<T>, String, user-defined structs. Translates
    /// each field operand and constructs a Datatype constructor expression.
    /// Returns `None` if any field translation fails (triggers caller self-loop).
    pub(in crate::codegen_ay::chc) fn translate_struct_aggregate(
        &mut self,
        def: AdtDef,
        args: &GenericArgs,
        operands: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let variants = def.variants();
        if variants.is_empty() {
            return None;
        }
        let variant = &variants[0];
        let adt_name = Self::adt_sort_name(def, args);
        let mut field_exprs = Vec::new();
        let mut fields = Vec::new();

        // Part of #3984: Compute parent ADT sort for correctly monomorphized field sorts.
        // resolve_generic_ty is shallow -- it does not substitute Params inside nested
        // ADT type args. The parent sort (from translate_adt_ty) uses the IntoIter handler
        // which correctly monomorphizes. Fall back to per-field translate_ty when unavailable.
        let parent_field_sorts: Vec<Sort> = Self::translate_adt_ty(def, args.clone())
            .and_then(|s: Sort| {
                let dt = s.datatype_sort()?;
                let c = dt.constructors.first()?;
                Some(c.fields.iter().map(|f| f.sort.clone()).collect())
            })
            .unwrap_or_default();

        for (idx, field) in variant.fields().iter().enumerate() {
            let field_ty = field.ty();
            let concrete_ty = Self::resolve_generic_ty(field_ty, args)?;
            let sort = if idx < parent_field_sorts.len() {
                parent_field_sorts[idx].clone()
            } else {
                Self::translate_ty(concrete_ty)?
            };
            fields.push((names::adt_struct_field_name(&field.name), sort.clone()));

            // Translate the corresponding operand
            if idx < operands.len() {
                let Some(expr) =
                    self.translate_operand_with_modified(&operands[idx], modified_locals)
                else {
                    warn!(idx, operand = ?operands[idx], "translate_adt_aggregate: failed to translate operand");
                    // Part of #3369: Reclassified SOUND_APPROXIMATION -> DEMOTED.
                    // Returning None triggers caller's self-loop (identity).
                    self.record_fallback();
                    return None;
                };
                let expr = self.coerce_struct_field_expr(expr, &sort, concrete_ty, &adt_name, idx);
                field_exprs.push(expr);
            } else {
                warn!(
                    idx,
                    num_operands = operands.len(),
                    "translate_adt_aggregate: missing operand for field"
                );
                // Part of #3447: record encoding gap so CTREX classification
                // reports OverApproximation instead of Genuine.
                self.record_aggregate_gap("adt_struct_missing_operand");
                return None;
            }
        }

        let struct_sort = struct_sort(&*adt_name, fields);
        // Part of #2980: Ensure the struct Datatype sort is declared
        // in the CHC preamble when constructed via MIR Aggregate.
        self.declare_datatype_sort_if_needed(&struct_sort);
        debug!(
            adt_name = %adt_name,
            num_fields = field_exprs.len(),
            "translate_adt_aggregate: constructed struct"
        );
        let cons_name = names::resolve_ctor_name(&struct_sort, &adt_name);
        Some(Expr::datatype_constructor(adt_name, cons_name, field_exprs, struct_sort))
    }

    /// Coerce a struct field expression to match the expected sort.
    ///
    /// Handles BV width coercion, Bool->unit datatype, BV->DT unflattening,
    /// DT->DT structural coercion, and ZST array construction.
    fn coerce_struct_field_expr(
        &mut self,
        expr: Expr,
        sort: &Sort,
        concrete_ty: rustc_public::ty::Ty,
        adt_name: &str,
        idx: usize,
    ) -> Expr {
        if expr.sort() == sort {
            return expr;
        }
        let signed = ty_signedness(concrete_ty)
            .unwrap_or_else(|| signedness_fallback_for_cast_or_coerce("struct_field_coerce"));
        if let Some(target_w) = sort.bitvec_width() {
            return coerce_bitvec_width_safe(expr, target_w, SignExtension::for_signedness(signed));
        }
        if expr.sort().is_bool()
            && sort.is_array()
            && is_zst_ty(concrete_ty)
            && let Some(zst_array) = canonical_zst_expr_for_sort(concrete_ty, sort)
        {
            return zst_array;
        }
        if let Some(unit_expr) = coerce_bool_to_unit_datatype(&expr, sort) {
            return unit_expr;
        }
        if expr.sort().is_bitvec() && sort.is_datatype() {
            if let Some(dt_expr) = unflatten_bitvec_to_datatype(&expr, sort) {
                return dt_expr;
            }
            warn!(
                adt_name = %adt_name,
                idx,
                expected = ?sort,
                actual = ?expr.sort(),
                "struct aggregate field sort mismatch; using fresh symbolic"
            );
            self.record_aggregate_gap("adt_struct_field_bv_to_dt_unflatten_failed");
            let undef_id = UNDEF_COUNTER.fetch_add(1, Ordering::Relaxed);
            let name = crate::codegen_ay::names::undef_sym_name(adt_name, undef_id);
            return declare_pending_var(name, sort.clone());
        }
        if expr.sort().is_datatype()
            && sort.is_datatype()
            && let Some(src_dt) = expr.sort().datatype_sort()
            && let Some(tgt_dt) = sort.datatype_sort()
            && let Some(coerced) = coerce_datatype_structural(
                expr.clone(),
                src_dt,
                tgt_dt,
                sort.clone(),
                SignExtension::for_signedness(signed),
            )
        {
            // Part of #3955: DT->DT structural coercion for
            // lifetime-parameterized type name divergence.
            return coerced;
        }
        warn!(
            adt_name = %adt_name,
            idx,
            expected = ?sort,
            actual = ?expr.sort(),
            "struct aggregate field sort mismatch; using fresh symbolic"
        );
        self.record_aggregate_gap("adt_struct_field_sort_mismatch");
        let undef_id = UNDEF_COUNTER.fetch_add(1, Ordering::Relaxed);
        let name = crate::codegen_ay::names::undef_sym_name(adt_name, undef_id);
        declare_pending_var(name, sort.clone())
    }

    /// Translate a general enum ADT aggregate construction (multi-variant enums).
    ///
    /// Handles enums with multiple constructors including Result<T, E>,
    /// ControlFlow, and user-defined enums. Translates field operands for the
    /// active variant and builds the full enum sort with all constructors.
    pub(in crate::codegen_ay::chc) fn translate_general_enum_aggregate(
        &mut self,
        def: AdtDef,
        variant_index: usize,
        args: &GenericArgs,
        operands: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let variants = def.variants();
        let variant = &variants[variant_index];
        let adt_name = Self::adt_sort_name(def, args);
        // Cache variant name: CrateDef::name() returns String, so each call allocates.
        // Part of #2267.
        let variant_name = variant.name();
        debug!(
            adt_name = %adt_name,
            variant_name = %variant_name,
            variant_index,
            num_operands = operands.len(),
            "translate_adt_aggregate: general enum path"
        );
        let mut field_exprs = Vec::new();
        let mut fields = Vec::new();

        for (idx, field) in variant.fields().iter().enumerate() {
            let field_ty = field.ty();
            let concrete_ty = Self::resolve_generic_ty(field_ty, args)?;
            // Apply deref_ref_ty for &[T; N] fields to produce Array sort,
            // matching the Option-like path. Without this, Result<&[T; N], E>
            // uses BV64 for the field but the inline walker provides Array values.
            // Sized-only: &str / &[T] stay BV128 fat pointers.
            let (deref_ty, _is_ref) = Self::deref_ref_ty_sized_only(concrete_ty);
            let use_deref = deref_ty != concrete_ty
                && matches!(
                    deref_ty.kind(),
                    rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Array(..))
                );
            let sort_ty = if use_deref { deref_ty } else { concrete_ty };
            let sort = Self::translate_ty(sort_ty)?;
            // Prefix field name with variant to avoid SMT-LIB accessor name collision (#776)
            fields.push((names::variant_field_name(&variant_name, idx), sort.clone()));

            if idx < operands.len() {
                let expr = self.translate_operand_with_modified(&operands[idx], modified_locals)?;
                let expr =
                    self.coerce_enum_field_expr(expr, &sort, concrete_ty, &variant_name, idx);
                field_exprs.push(expr);
            } else {
                // Part of #3447: record encoding gap for missing enum operand
                // so CTREX classification reports OverApproximation.
                self.record_aggregate_gap("adt_enum_missing_operand");
                return None;
            }
        }

        // Build the enum sort (all constructors)
        let all_constructors = Self::build_enum_constructors(&variants, &adt_name, args);

        let enum_sort = enum_sort(&*adt_name, all_constructors);
        // Part of #2980: Ensure the enum Datatype sort is declared
        // in the CHC preamble when constructed via MIR Aggregate.
        self.declare_datatype_sort_if_needed(&enum_sort);
        // Scope variant name to match datatype declaration (#1739)
        let scoped_variant_name = names::scope_option_ctor(&variant_name, &adt_name);
        Some(Expr::datatype_constructor(adt_name, scoped_variant_name, field_exprs, enum_sort))
    }

    /// Coerce an enum field expression to match the expected sort.
    ///
    /// Part of #3094: handles ZST operands, Bool<->BV, and BV width mismatches.
    fn coerce_enum_field_expr(
        &mut self,
        expr: Expr,
        sort: &Sort,
        concrete_ty: rustc_public::ty::Ty,
        variant_name: &str,
        idx: usize,
    ) -> Expr {
        if expr.sort() == sort {
            return expr;
        }
        if let Some(coerced) =
            Self::coerce_assignment_rhs_to_sort(expr.clone(), sort, ty_signedness(concrete_ty))
        {
            return coerced;
        }
        if let Some(target_w) = sort.bitvec_width() {
            // Bool->BV or BV->BV coercion
            let signed = ty_signedness(concrete_ty)
                .unwrap_or_else(|| signedness_fallback_for_cast_or_coerce("enum_field_coerce"));
            return coerce_bitvec_width_safe(expr, target_w, SignExtension::for_signedness(signed));
        }
        if expr.sort().is_bool()
            && sort.is_array()
            && is_zst_ty(concrete_ty)
            && let Some(zst_array) = canonical_zst_expr_for_sort(concrete_ty, sort)
        {
            return zst_array;
        }
        if let Some(unit_expr) = coerce_bool_to_unit_datatype(&expr, sort) {
            debug!("  Coercing field {} Bool -> Unit datatype", idx);
            return unit_expr;
        }
        // Target is not bitvec, not unit datatype. Use fresh symbolic.
        warn!(
            variant_name = %variant_name,
            idx,
            expected = ?sort,
            actual = ?expr.sort(),
            "enum aggregate field sort mismatch; using fresh symbolic"
        );
        self.record_aggregate_gap("adt_enum_field_sort_mismatch");
        let undef_id = UNDEF_COUNTER.fetch_add(1, Ordering::Relaxed);
        let name = crate::codegen_ay::names::undef_sym_name(variant_name, undef_id);
        declare_pending_var(name, sort.clone())
    }

    /// Build all constructors for an enum sort from its variant definitions.
    ///
    /// Used by `translate_general_enum_aggregate` to construct the full enum
    /// Datatype sort with all variant constructors, not just the active one.
    fn build_enum_constructors(
        variants: &[VariantDef],
        adt_name: &str,
        args: &GenericArgs,
    ) -> Vec<(String, Vec<(String, Sort)>)> {
        let mut all_constructors = Vec::new();
        for v in variants {
            // Cache per-variant: avoids N+1 String allocations per variant
            // (N field iterations + 1 for constructor name). Part of #2267.
            let v_name = v.name();
            let mut v_fields = Vec::new();
            for (i, f) in v.fields().iter().enumerate() {
                let f_ty = f.ty();
                if let Some(concrete) = Self::resolve_generic_ty(f_ty, args) {
                    // Apply deref_ref_ty for &[T; N] fields: match Option-like path.
                    // Sized-only: &str / &[T] stay BV128 fat pointers.
                    let (deref_ty, _is_ref) = Self::deref_ref_ty_sized_only(concrete);
                    let use_deref = deref_ty != concrete
                        && matches!(
                            deref_ty.kind(),
                            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Array(..))
                        );
                    let sort_ty = if use_deref { deref_ty } else { concrete };
                    if let Some(s) = Self::translate_ty(sort_ty) {
                        // Prefix field name with variant to avoid SMT-LIB accessor name collision (#776)
                        v_fields.push((names::variant_field_name(&v_name, i), s));
                    }
                }
            }
            // Scope constructor name to match datatype declaration (#1739)
            all_constructors.push((names::scope_option_ctor(&v_name, adt_name), v_fields));
        }
        all_constructors
    }
}
