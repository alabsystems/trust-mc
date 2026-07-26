// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Datatype field selection and updates for MIR place projections.

use std::sync::Arc;

use super::datatype_deref_write::ArrayIndexPrefix;
use super::{
    Expr, IndexedVal, IntoOption, Operand, Place, ProjectionElem, Rvalue, StatementCodegen,
};
use tracing::debug;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    pub(super) fn try_codegen_datatype_field_assign(&mut self, lhs: &Place, rhs: &Rvalue) -> bool {
        if lhs.projection.is_empty() {
            return false;
        }

        let Some(rhs_expr) = self.codegen_rvalue(rhs) else {
            let location = format!("{:?}", lhs);
            self.ctx.unconstrained_assignment("Datatype field assign rvalue codegen", location);
            return true;
        };

        // Check if first projection is Deref - handle (*ref).field = value pattern (#357)
        let (projections_to_check, root_base_name, is_deref_path): (
            &[ProjectionElem],
            Arc<str>,
            bool,
        ) = if let Some(ProjectionElem::Deref) = lhs.projection.first() {
            // For Deref, get the pointee via ref_pointees and use remaining projections
            let ref_base = self.root_ssa_base_name(lhs);
            if let Some(pointee_base) = self.ref_pointees.get(ref_base.as_str()).cloned() {
                debug!(
                    "try_codegen_datatype_field_assign: Deref path, ref={}, pointee={}",
                    ref_base, pointee_base
                );
                // Skip the Deref, use remaining projections
                (&lhs.projection[1..], pointee_base, true)
            } else {
                // No tracked pointee - fall through to normal handling
                debug!(
                    "try_codegen_datatype_field_assign: Deref but no tracked pointee for {}",
                    ref_base
                );
                return false;
            }
        } else {
            // No Deref - use all projections with root local
            (&lhs.projection[..], self.root_ssa_base_name(lhs).into(), false)
        };

        // #1262: Handle array element + field pattern: arr[i].field = value
        // When first projection is Index/ConstantIndex, we need to:
        // 1. Select the element from the array
        // 2. Update the field in that element
        // 3. Store the updated element back into the array
        let (array_index_info, remaining_projections) =
            match self.extract_array_index_prefix(projections_to_check, root_base_name.as_ref()) {
                ArrayIndexPrefix::None(remaining) => (None, remaining),
                ArrayIndexPrefix::Some(info, remaining) => (Some(info), remaining),
                ArrayIndexPrefix::Unsupported => {
                    self.ctx.unconstrained_assignment(
                        "Datatype field assign array index unsupported",
                        format!("{:?}", lhs),
                    );
                    return true;
                }
            };

        // Extract field indices and constructor indices from projections (#419)
        // Track Downcast projections to select correct constructor for enum variants
        let mut field_projections: Vec<(usize, Option<usize>)> =
            Vec::with_capacity(remaining_projections.len());
        let mut active_variant: Option<usize> = None;
        for proj in remaining_projections {
            match proj {
                ProjectionElem::Downcast(variant_idx) => {
                    // Track the variant index for subsequent Field projection
                    active_variant = Some(variant_idx.to_index());
                }
                ProjectionElem::Field(field, _ty) => {
                    // Store field index with current active variant
                    field_projections.push((*field, active_variant));
                    // Reset variant after use (each Field uses its preceding Downcast)
                    active_variant = None;
                }
                _ => return false, // external enum: ProjectionElem
            }
        }

        // No Field projections found - can't do field assignment (#419 audit)
        if field_projections.is_empty() {
            return false;
        }

        debug!(
            "try_codegen_datatype_field_assign: field_projections={:?}, is_deref={}, array_index={:?}",
            field_projections,
            is_deref_path,
            array_index_info.as_ref().map(|(_, idx)| idx)
        );
        let Some(base_expr) = self.env_lookup(root_base_name.as_ref()).cloned() else {
            // Root not in env - this happens when tuples are stored field-by-field
            // (e.g., CheckedBinaryOp). Let the normal assignment path handle it.
            return false;
        };

        // #1262: For array element access, select the element first
        let root_expr = if let Some((arr_base, idx_expr)) = &array_index_info {
            // base_expr should be the array
            if !base_expr.sort().is_array() {
                debug!(
                    "try_codegen_datatype_field_assign: expected array for {}, got {:?}",
                    arr_base,
                    base_expr.sort()
                );
                return false;
            }
            // Select element at index
            let element = base_expr.clone().select(idx_expr.clone());
            debug!(
                "try_codegen_datatype_field_assign: selected array element, sort={:?}",
                element.sort()
            );
            element
        } else {
            base_expr.clone()
        };

        if !root_expr.sort().is_datatype() {
            debug!(
                "try_codegen_datatype_field_assign: element is not a datatype, sort={:?}",
                root_expr.sort()
            );
            return false;
        }

        let mut path: Vec<(Expr, usize, Option<usize>)> =
            Vec::with_capacity(field_projections.len());
        let mut current = root_expr.clone();
        for (i, (field_idx, cons_idx)) in field_projections.iter().enumerate() {
            path.push((current.clone(), *field_idx, *cons_idx));
            if i + 1 < field_projections.len() {
                let Some(next) =
                    Self::datatype_field_select(&current, *field_idx, *cons_idx, lhs, self.ctx)
                else {
                    self.ctx.unconstrained_assignment(
                        "Datatype field select failed in assignment",
                        format!("{:?}", lhs),
                    );
                    return true;
                };
                current = next;
            }
        }

        let mut updated = rhs_expr;
        for (container, field_idx, cons_idx) in path.into_iter().rev() {
            let Some(new_container) = Self::datatype_field_update(
                &container, field_idx, cons_idx, updated, lhs, self.ctx,
            ) else {
                self.ctx.unconstrained_assignment(
                    "Datatype field update failed in assignment",
                    format!("{:?}", lhs),
                );
                return true;
            };
            updated = new_container;
        }

        // #1262: For array element access, store the updated element back into the array
        if let Some((arr_base, idx_expr)) = &array_index_info {
            // Part of #2970: Vec/String coercion (this site previously had none).
            if let Some(coerced) = crate::codegen_ay::store_coercion::coerce_vec_string_store_value(
                base_expr.sort(),
                &updated,
            ) {
                debug!("datatype field assign: Vec/String coercion (Part of #2970)");
                updated = coerced;
            }
            // Part of #2970: BMC sort coercion beyond Vec/String.
            // Part of #3407: derive signedness from MIR type (was hardcoded false).
            let signed = lhs
                .ty(self.body.locals())
                .into_option()
                .and_then(crate::codegen_ay::shared::ty_signedness_shallow)
                .unwrap_or(false);
            if let Some(coerced) = crate::codegen_ay::store_coercion::coerce_store_value_bmc(
                base_expr.sort(),
                &updated,
                signed,
            ) {
                debug!("datatype field assign: BMC-coerced value (Part of #2970)");
                updated = coerced;
            }
            // Part of #2970: Last-resort fresh symbolic if sorts still mismatch.
            if base_expr.sort().array_sort().is_some_and(|a| *updated.sort() != a.element_sort) {
                let sym_name = crate::codegen_ay::store_coercion::bmc_store_fallback_name();
                if let Some(arr) = base_expr.sort().array_sort() {
                    debug!(
                        store_sort = ?updated.sort(),
                        elem_sort = ?arr.element_sort,
                        "datatype field assign: fresh symbolic for array store sort mismatch (Part of #2970)"
                    );
                    updated = self.ctx.declare_var(&sym_name, arr.element_sort.clone());
                }
            }
            let new_array = base_expr.store(idx_expr.clone(), updated);
            let arr_ssa = self.ssa_name_from_base(arr_base, true);
            let arr_var = self.ctx.declare_var(&arr_ssa, new_array.sort().clone());
            // SSA def with ite semantics (#2081)
            self.assert_ssa_def(arr_var.clone(), new_array, arr_base);
            self.env_update(*arr_base, arr_var);
            debug!(
                "try_codegen_datatype_field_assign: stored updated element into array {}",
                arr_ssa
            );
        } else {
            let root_ssa = self.ssa_name_from_base(root_base_name.as_ref(), true);
            let root_var = self.ctx.declare_var(&root_ssa, root_expr.sort().clone());
            // SSA def with ite semantics (#2081, #2096)
            // Datatype field updates preserve the container sort, so root_var and
            // updated should have matching sorts. assert_ssa_def handles sort
            // reconciliation internally if they differ.
            self.assert_ssa_def(root_var.clone(), updated, root_base_name.as_ref());
            self.env_update(root_base_name.clone(), root_var.clone());

            // Part of #3041: Propagate deref writes back to parent enum containers.
            // When mutating through a reference into an enum variant (e.g.,
            // `(*ref_to_some_payload).field = value`), the extracted variant field
            // is updated but the parent enum variable is stale. Reconstruct the
            // parent with the updated field value.
            if is_deref_path {
                self.try_propagate_deref_write_to_parent_datatype(&root_base_name, &root_var, lhs);
            }
        }

        // Track ref_pointees for field assignments containing references (#431).
        // When assigning a reference to a field, propagate the pointee mapping.
        match rhs {
            Rvalue::Ref(_, _, pointee_place) | Rvalue::AddressOf(_, pointee_place) => {
                let field_base = self.ssa_base_name(lhs);
                let pointee_base = self.ssa_base_name(pointee_place);
                debug!(
                    "datatype field assign: ref {} -> {} (pointee={})",
                    field_base, pointee_base, pointee_base
                );
                self.ref_pointees
                    .insert(std::sync::Arc::from(field_base), std::sync::Arc::from(pointee_base));
            }
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) => {
                let src_base = self.ssa_base_name(src);
                if let Some(pointee) = self.ref_pointees.get(src_base.as_str()).cloned() {
                    let field_base = self.ssa_base_name(lhs);
                    debug!(
                        "datatype field assign: propagating ref {} -> {} (pointee={})",
                        src_base, field_base, pointee
                    );
                    self.ref_pointees.insert(std::sync::Arc::from(field_base), pointee);
                }
            }
            _ => {} // external enum: Rvalue
        }

        true
    }

    /// Store into an array that is a (possibly nested) FIELD of a datatype —
    /// e.g. `self.buf[self.len] = v`, whose LHS projection is
    /// `[Deref?, Field(buf), …, Index(idx)]`. This is the inlined element-store
    /// shape (NOT an `index_mut` call). Without this, the generic path drops the
    /// store (it rebuilds the struct with the array field UNCHANGED) and records
    /// an `unsupported_construct_fallback`, demoting the proof. Encode it EXACTLY
    /// as `store(field_array, idx, v)` then `datatype_field_update` back up to the
    /// owning struct and `env_update` the struct base — sound now that ay's array
    /// store/select axioms are fixed (#5148), and path-guarded by
    /// `assert_ssa_def`'s ite semantics so a conditional store stays conditional.
    ///
    /// FAILS CLOSED: once the shape is recognised as ours, any unresolved
    /// base/index/value or element-sort mismatch records a demoting
    /// `unconstrained_assignment` — NEVER a fresh symbolic (which would lose the
    /// written value) and NEVER a silent drop (the audited false-proof hazard).
    pub(super) fn try_codegen_assign_datatype_field_index(
        &mut self,
        lhs: &Place,
        rhs: &Rvalue,
    ) -> bool {
        // Resolve the base, stripping a leading Deref via ref_pointees (the
        // `(*self).buf[..]` shape), mirroring try_codegen_datatype_field_assign.
        let (projs, base_name, is_deref): (&[ProjectionElem], std::sync::Arc<str>, bool) =
            if let Some(ProjectionElem::Deref) = lhs.projection.first() {
                let ref_base = self.root_ssa_base_name(lhs);
                let Some(pointee) = self.ref_pointees.get(ref_base.as_str()).cloned() else {
                    return false;
                };
                (&lhs.projection[1..], pointee, true)
            } else {
                (&lhs.projection[..], std::sync::Arc::from(self.root_ssa_base_name(lhs)), false)
            };

        // This handler's signature: a trailing Index preceded by >= 1 Field.
        let Some((ProjectionElem::Index(idx_local), lead)) = projs.split_last() else {
            return false;
        };
        let idx_local = *idx_local;
        let mut field_path: Vec<(usize, Option<usize>)> = Vec::with_capacity(lead.len());
        let mut active_variant: Option<usize> = None;
        for p in lead {
            match p {
                ProjectionElem::Downcast(v) => active_variant = Some(v.to_index()),
                ProjectionElem::Field(f, _) => {
                    field_path.push((*f, active_variant));
                    active_variant = None;
                }
                _ => return false, // external enum: ProjectionElem — not our shape
            }
        }
        if field_path.is_empty() {
            // Top-level `arr[i]` — handled by try_codegen_assign_array_index.
            return false;
        }

        let Some(base_expr) = self.env_lookup(base_name.as_ref()).cloned() else {
            return false;
        };

        // Navigate to the array field, recording each container for write-back.
        let mut containers: Vec<(Expr, usize, Option<usize>)> =
            Vec::with_capacity(field_path.len());
        let mut current = base_expr;
        for (fi, ci) in &field_path {
            containers.push((current.clone(), *fi, *ci));
            let Some(next) = Self::datatype_field_select(&current, *fi, *ci, lhs, self.ctx) else {
                return false;
            };
            current = next;
        }
        if !current.sort().is_array() {
            // The field chain does not end in an array — not our shape.
            return false;
        }
        let arr_expr = current;

        // From here the shape is ours; any failure FAILS CLOSED (demote).
        let idx_name = crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), idx_local);
        let idx_expr_opt = self.env_lookup(&idx_name).cloned().or_else(|| {
            let idx_ssa = self.ssa_name_from_base(&idx_name, false);
            self.ctx.lookup_var(&idx_ssa).cloned()
        });
        let Some(idx_expr) = idx_expr_opt else {
            self.ctx.unconstrained_assignment(
                "datatype field-index store: index unresolved",
                format!("{lhs:?}"),
            );
            return true;
        };
        let pw = crate::codegen_ay::types::POINTER_WIDTH;
        let idx_coerced = match idx_expr.sort().bitvec_width() {
            Some(w) if w == pw => idx_expr,
            Some(w) if w < pw => idx_expr.zero_extend(pw - w),
            Some(w) if w > pw => idx_expr.extract(pw - 1, 0),
            _ => {
                self.ctx.unconstrained_assignment(
                    "datatype field-index store: non-bitvec index",
                    format!("{lhs:?}"),
                );
                return true;
            }
        };

        let Some(mut val_expr) = self.codegen_rvalue(rhs) else {
            self.ctx.unconstrained_assignment(
                "datatype field-index store: rvalue None",
                format!("{lhs:?}"),
            );
            return true;
        };
        // Coerce the value to the element sort; FAIL CLOSED on residual mismatch
        // (do NOT substitute a fresh symbolic — that would lose the written value).
        let signed = lhs
            .ty(self.body.locals())
            .into_option()
            .and_then(crate::codegen_ay::shared::ty_signedness_shallow)
            .unwrap_or(false);
        if let Some(c) = crate::codegen_ay::store_coercion::coerce_vec_string_store_value(
            arr_expr.sort(),
            &val_expr,
        ) {
            val_expr = c;
        }
        if let Some(c) = crate::codegen_ay::store_coercion::coerce_store_value_bmc(
            arr_expr.sort(),
            &val_expr,
            signed,
        ) {
            val_expr = c;
        }
        if let Some(arr) = arr_expr.sort().array_sort()
            && *val_expr.sort() != arr.element_sort
        {
            self.ctx.unconstrained_assignment(
                "datatype field-index store: element sort mismatch",
                format!("{lhs:?}"),
            );
            return true;
        }

        // store + rebuild the owning datatype up the field path.
        let mut updated = arr_expr.store(idx_coerced, val_expr);
        for (container, fi, ci) in containers.into_iter().rev() {
            let Some(new_container) =
                Self::datatype_field_update(&container, fi, ci, updated, lhs, self.ctx)
            else {
                self.ctx.unconstrained_assignment(
                    "datatype field-index store: field update failed",
                    format!("{lhs:?}"),
                );
                return true;
            };
            updated = new_container;
        }

        let base_ssa = self.ssa_name_from_base(base_name.as_ref(), true);
        let base_var = self.ctx.declare_var(&base_ssa, updated.sort().clone());
        // ite semantics (#2081) path-guard the store to the current PC.
        self.assert_ssa_def(base_var.clone(), updated, base_name.as_ref());
        self.env_update(base_name.clone(), base_var.clone());
        if is_deref {
            self.try_propagate_deref_write_to_parent_datatype(&base_name, &base_var, lhs);
        }
        debug!("datatype field-index store: stored into array field of {base_name}");
        true
    }

    // try_propagate_deref_write_to_parent_datatype, datatype_field_select,
    // datatype_field_update, extract_array_index_prefix moved to
    // datatype_deref_write.rs per #4206.
}
