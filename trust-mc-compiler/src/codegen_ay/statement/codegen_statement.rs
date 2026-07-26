// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Statement codegen entry point (converted from include!() per #2595).

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::chc::codegen_stmt_aggregate_adt::sign_extend_discr_val;
use crate::codegen_ay::types::{
    SignExtension, coerce_bitvec_width_safe, coerce_bool_to_unit_datatype,
};
use ay_bindings::{Expr, Sort};
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_public::mir::{
    CopyNonOverlapping, NonDivergingIntrinsic, ProjectionElem, Statement, StatementKind,
};
use rustc_public::rustc_internal;
use rustc_public::ty::{AdtKind, RigidTy, TyKind};
use rustc_public_bridge::IndexedVal;
use tracing::{debug, warn};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Translate a MIR Statement into AY constraints.
    ///
    /// In SSA form, assignments become equality constraints between
    /// the new version of a variable and the computed rvalue.
    ///
    /// REQUIRES: stmt is a valid MIR statement from self.body
    /// ENSURES: Adds AY constraints encoding stmt semantics to self.ctx
    /// ENSURES: Updates SSA environment for assigned places
    pub(in crate::codegen_ay) fn codegen_statement(&mut self, stmt: &Statement) {
        debug!(?stmt, kind=?stmt.kind, "AY codegen_statement");
        // Track source span for property locations (#1164).
        self.current_span = Some(stmt.span);

        match &stmt.kind {
            StatementKind::Assign(lhs, rhs) => {
                // Assignment semantics live in codegen_assign.rs.
                self.codegen_assign(lhs, rhs);
                // SwitchInt→variant bridge (#3017): a store to this place may retag its
                // enum — drop any variant fact on that storage (over-kill on doubt).
                self.kill_variant_facts_for_place(lhs);
            }
            StatementKind::SetDiscriminant { place, variant_index } => {
                // SwitchInt→variant bridge (#3017): a discriminant write retags the enum
                // — drop any variant fact on that storage before re-encoding it.
                self.kill_variant_facts_for_place(place);
                // For unit enums, SetDiscriminant assigns the discriminant value to the enum.
                // Get the place type to check if it's a unit enum.
                let ty = place.ty(self.body.locals()).into_option();
                if let Some(ty) = ty
                    && matches!(ty.kind(), TyKind::RigidTy(RigidTy::Coroutine(..)))
                {
                    let base_name = if place.projection.len() == 1
                        && matches!(place.projection[0], ProjectionElem::Deref)
                    {
                        let ref_base = crate::codegen_ay::names::local_name(
                            self.ctx.current_fn_name(),
                            place.local,
                        );
                        self.ref_pointees
                            .get(ref_base.as_str())
                            .map(|name| name.to_string())
                            .unwrap_or_else(|| self.ssa_base_name(place))
                    } else {
                        self.ssa_base_name(place)
                    };
                    let location = format!("{:?}", stmt.span);
                    let Some(root_expr) = self.env_lookup(&base_name).cloned() else {
                        self.ctx.unsupported_with_fallback("SetDiscriminant", location);
                        return;
                    };
                    let discr_width =
                        crate::codegen_ay::types::coroutine_discriminant_select(root_expr.clone())
                            .and_then(|expr| expr.sort().bitvec_width())
                            .unwrap_or(32);
                    let internal_ty = rustc_internal::internal(self.ctx.tcx, ty);
                    let variant_idx_internal =
                        rustc_internal::internal(self.ctx.tcx, *variant_index);
                    let Some(discr) =
                        internal_ty.discriminant_for_variant(self.ctx.tcx, variant_idx_internal)
                    else {
                        self.ctx.unsupported_with_fallback("SetDiscriminant", location);
                        return;
                    };
                    let rhs_expr = Expr::bitvec_const(
                        sign_extend_discr_val(discr.val, discr.ty, self.ctx.tcx, discr_width),
                        discr_width,
                    );
                    let Some(updated) = crate::codegen_ay::types::coroutine_discriminant_update(
                        &root_expr, rhs_expr,
                    ) else {
                        self.ctx.unsupported_with_fallback("SetDiscriminant", location);
                        return;
                    };
                    let lhs_name = self.ssa_name_from_base(&base_name, true);
                    let lhs_expr = self.ctx.declare_var(&lhs_name, updated.sort().clone());
                    self.assert_ssa_def(lhs_expr.clone(), updated, &base_name);
                    self.env_update(base_name, lhs_expr);
                    return;
                }
                if let Some(ty) = ty
                    && let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind()
                {
                    let variants = def.variants();
                    let is_unit_enum = variants.iter().all(|v| v.fields().is_empty());

                    if is_unit_enum {
                        // For unit enums, assign the actual discriminant value (not variant index).
                        // Bug fix (#1393): Enums with explicit discriminants like `A = -500` need
                        // the actual value, not the variant index.
                        let internal_def = rustc_internal::internal(self.ctx.tcx, def);
                        let variant_idx_internal =
                            InternalVariantIdx::from_usize(variant_index.to_index());
                        let discr = internal_def
                            .discriminant_for_variant(self.ctx.tcx, variant_idx_internal);

                        // Use fixed bit width to match sort_inference.rs.
                        let num_variants = variants.len();
                        let bits = if num_variants <= 65536 { 32 } else { 64 };
                        // Part of #3543: Sign-extend signed discriminants (CHC parity for #3536).
                        let discriminant_val =
                            sign_extend_discr_val(discr.val, discr.ty, self.ctx.tcx, bits);

                        let base_name = self.ssa_base_name(place);
                        let lhs_name = self.ssa_name(place, true);
                        let lhs_expr = self.ctx.declare_var(&lhs_name, Sort::bitvec(bits));
                        let rhs_expr = Expr::bitvec_const(discriminant_val, bits);

                        // SSA def with ite semantics (#2081)
                        self.assert_ssa_def(lhs_expr.clone(), rhs_expr, &base_name);
                        self.env_update(base_name, lhs_expr);
                        return;
                    }
                }
                // Non-unit ADTs: construct SMT datatype from previously written fields.
                // Part of #1229: Handle piecewise enum construction pattern in MIR.
                // MIR pattern: (_place as Variant).field = value; set_discriminant(_place, variant)
                if let Some(ty) = ty
                    && let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind()
                {
                    let variants = def.variants();
                    let variant_idx_val = variant_index.to_index();
                    let variant = &variants[variant_idx_val];
                    let adt_name = Self::adt_sort_name(def, &args);

                    // Clone args: infer_adt_sort takes ownership but we need args for field sort resolution.
                    if let Some(sort) = Self::infer_adt_sort(def, args.clone())
                        && sort.is_datatype()
                    {
                        let place_base = self.ssa_base_name(place);
                        let num_fields = variant.fields().len();
                        let variant_fields = variant.fields();
                        // Part of #2549: Scope Option constructor names — but ONLY for
                        // genuine multi-variant enums. A single-variant STRUCT (e.g.
                        // `RangeInclusive<u8>`) declares its sole constructor as
                        // `{adt_name}_mk` via Sort::struct_type, so scope_option_ctor's
                        // `{variant}_{adt_name}` would DOUBLE-NAME it
                        // (`RangeInclusive_RangeInclusive_u8`) and never match the declared
                        // `RangeInclusive_u8_mk` → an undeclared "unknown constant" in the
                        // .smt2. For structs, take the constructor name from the declared
                        // sort (its default ctor `{adt_name}_mk`).
                        let variant_name = if def.kind() == AdtKind::Struct {
                            crate::codegen_ay::names::resolve_ctor_name(&sort, &adt_name)
                        } else {
                            crate::codegen_ay::names::scope_option_ctor(variant.name(), &adt_name)
                        };

                        // Collect field values from the environment.
                        // Fields were written as: {place_base}_variant_{V}_field_{F}
                        let mut field_exprs = Vec::with_capacity(num_fields);
                        let mut all_found = true;
                        for field_idx in 0..num_fields {
                            let field_key = {
                                use std::fmt::Write;
                                let mut s = String::with_capacity(
                                    place_base.len() + "_variant__field_".len() + 20,
                                );
                                s.push_str(&place_base);
                                s.push_str("_variant_");
                                let _ = write!(&mut s, "{variant_idx_val}");
                                s.push_str("_field_");
                                let _ = write!(&mut s, "{field_idx}");
                                s
                            };
                            if let Some(expr) = self.env_lookup(&field_key) {
                                // Part of #3094: Coerce field sort to match declared datatype field.
                                // ZST fields (e.g., unit enum `Unit`) translate to Bool but the
                                // datatype constructor expects BitVec(32).
                                let coerced = if let Some(field_def) = variant_fields.get(field_idx)
                                {
                                    let field_ty = field_def.ty();
                                    let expected_sort = Self::resolve_generic_ty(field_ty, &args)
                                        .and_then(Self::infer_sort_from_ty);
                                    if let Some(ref target_sort) = expected_sort {
                                        if expr.sort() != target_sort {
                                            if let Some(tw) = target_sort.bitvec_width() {
                                                debug!(
                                                    "SetDiscriminant: coercing field {} sort {:?} → BV({})",
                                                    field_idx,
                                                    expr.sort(),
                                                    tw
                                                );
                                                coerce_bitvec_width_safe(
                                                    expr.clone(),
                                                    tw,
                                                    SignExtension::ZeroExtend,
                                                )
                                            } else if let Some(unit_expr) =
                                                coerce_bool_to_unit_datatype(&expr, target_sort)
                                            {
                                                debug!(
                                                    "SetDiscriminant: coercing field {} Bool → Unit datatype",
                                                    field_idx
                                                );
                                                unit_expr
                                            } else {
                                                warn!(
                                                    "SetDiscriminant: sort mismatch field {} of '{}::{}': {:?} vs {:?}",
                                                    field_idx,
                                                    adt_name,
                                                    variant_name,
                                                    expr.sort(),
                                                    target_sort
                                                );
                                                expr.clone()
                                            }
                                        } else {
                                            expr.clone()
                                        }
                                    } else {
                                        expr.clone()
                                    }
                                } else {
                                    expr.clone()
                                };
                                field_exprs.push(coerced);
                            } else {
                                debug!(
                                    "SetDiscriminant: field {} not found in env for {} variant {}",
                                    field_idx, adt_name, variant_name
                                );
                                all_found = false;
                                break;
                            }
                        }

                        if all_found {
                            // Construct the datatype value.
                            let dt_expr = Expr::datatype_constructor(
                                adt_name,
                                variant_name,
                                field_exprs,
                                sort,
                            );

                            let lhs_name = self.ssa_name(place, true);
                            let lhs_expr = self.ctx.declare_var(&lhs_name, dt_expr.sort().clone());
                            // SSA def with ite semantics (#2081)
                            self.assert_ssa_def(lhs_expr.clone(), dt_expr, &place_base);
                            self.env_update(place_base, lhs_expr);
                            return;
                        }

                        // If no fields (None-like variant), construct directly.
                        if num_fields == 0 {
                            let dt_expr =
                                Expr::datatype_constructor(adt_name, variant_name, vec![], sort);
                            let lhs_name = self.ssa_name(place, true);
                            let lhs_expr = self.ctx.declare_var(&lhs_name, dt_expr.sort().clone());
                            // SSA def with ite semantics (#2081)
                            self.assert_ssa_def(lhs_expr.clone(), dt_expr, &place_base);
                            self.env_update(place_base, lhs_expr);
                            return;
                        }
                    }
                }

                // Fallback: unsupported
                let location = format!("{:?}", stmt.span);
                self.ctx.unsupported_with_fallback("SetDiscriminant", location);
            }
            StatementKind::StorageLive(_var_id) => {
                // In AY, we don't need explicit storage markers
                // Variables are declared when first assigned
            }
            StatementKind::StorageDead(var_id) => {
                // Track that this local has gone out of scope.
                // This enables dead object detection for raw pointer dereferences. (#313)
                let local_idx: usize = *var_id;
                self.dead_locals.insert(local_idx);
                debug!("StorageDead: marked local_{} as dead", local_idx);
            }
            StatementKind::Intrinsic(intrinsic) => {
                match intrinsic {
                    NonDivergingIntrinsic::Assume(op) => {
                        // Assume the operand is true. Add to path constraints.
                        // This is like `std::hint::assume` - UB if condition is false.
                        if let Some(cond) = self.codegen_operand(op) {
                            // Convert to boolean if needed (e.g., if it's a bitvec)
                            let bool_cond = if cond.sort().is_bool() {
                                cond
                            } else if let Some(width) = cond.sort().bitvec_width() {
                                // Non-zero bitvec is true
                                let zero = Expr::bitvec_const(0i32, width);
                                cond.ne(zero)
                            } else {
                                // For other sorts, just use the condition directly
                                // (will fail if not Bool, but that's a type error)
                                cond
                            };
                            // Add as SMT assertion (assume = assert in SMT-LIB)
                            self.ctx.program.assert(bool_cond);
                            debug!("AY codegen: added assume constraint for {:?}", op);
                        }
                    }
                    NonDivergingIntrinsic::CopyNonOverlapping(CopyNonOverlapping {
                        src,
                        dst,
                        count,
                    }) => {
                        // CopyNonOverlapping copies `count` elements from src to dst.
                        // Part of #1478: Implement copy/copy_nonoverlapping intrinsics.
                        //
                        // Memory model semantics:
                        // - For constant counts: unroll and copy byte-by-byte
                        // - For symbolic counts: use guarded memcpy model
                        //
                        // Soundness: Non-overlapping is assumed by the intrinsic contract.
                        self.codegen_copy_nonoverlapping(src, dst, count, stmt.span);
                    }
                }
            }
            StatementKind::Coverage(..) => {
                let condition =
                    self.current_path_condition.clone().unwrap_or_else(|| Expr::bool_const(true));
                let location = self.current_source_location();
                self.ctx.record_coverage_property_with_location(condition, location);
            }
            StatementKind::FakeRead(..)
            | StatementKind::PlaceMention(..)
            | StatementKind::AscribeUserType { .. }
            | StatementKind::Nop
            | StatementKind::ConstEvalCounter
            | StatementKind::Retag(..) => {
                // These are no-ops for verification
            }
        }
    }
}
