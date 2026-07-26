// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Deref resolution and Box field access for place translation.
//!
//! Extracted from place.rs as part of #2039 decomposition.
//! Functions for Box<T> deref patterns and raw pointer safety checks.

use super::{
    CrateDef, Expr, IntoOption, LayoutOf, Place, ProjectionElem, RigidTy, StatementCodegen, TyKind,
};
use crate::codegen_ay::types::{CtorFieldExt, POINTER_WIDTH};
use ay_bindings::SortInner;
use tracing::debug;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Try to codegen Box<T> field access with Deref in non-first position.
    ///
    /// For Box<T>, MIR generates places like `(*((b.0).0)).field` where:
    /// - `b` is the Box local
    /// - `.0.0` extracts the raw pointer through Unique and NonNull wrappers
    /// - `*` dereferences to get T
    /// - `.field` accesses the struct field
    ///
    /// Projection chain: [Field(0), Field(0), Deref, Field(?), ...]
    ///
    /// When Box::new(value) stores to heap, we track the value in heap_pointees
    /// keyed by the Box local. This function looks up that value and applies
    /// remaining field projections.
    ///
    /// Part of #1210: Fix Box<struct> field access in CHC codegen.
    pub(super) fn try_codegen_box_field_access(&mut self, place: &Place) -> Option<Expr> {
        // Check if we have at least Field, Field, Deref pattern
        if place.projection.len() < 3 {
            return None;
        }

        // Find Deref position - for Box it should be at position 2
        let deref_idx = place.projection.iter().position(|p| matches!(p, ProjectionElem::Deref))?;

        // For Box, Deref should be at position 2 (after two Field(0) projections)
        if deref_idx < 2 {
            return None;
        }

        // Check that all projections before Deref are Field(0) - the Box unwrapping
        for proj in place.projection.iter().take(deref_idx) {
            match proj {
                ProjectionElem::Field(0, _) => continue,
                _ => return None, // external enum: ProjectionElem — not a Box unwrap pattern
            }
        }

        // Check if the BASE LOCAL's type is Box (not place.ty() which is after projections).
        // For `(*(b.0).0)` where b: Box<i32>, place.ty() returns i32 but we need Box<i32>.
        // Construct minimal Place instead of cloning full projection Vec.
        let base_place = Place { local: place.local, projection: vec![] };
        let base_ty = base_place.ty(self.body.locals()).into_option()?;
        if !Self::is_box_type(base_ty) {
            return None;
        }

        // Look up the stored value in heap_pointees using root local
        let heap_key = self.root_ssa_base_name(place);
        let heap_value = if let Some(v) = self.heap_pointees.get(heap_key.as_str()).cloned() {
            // Part of #3748 D2: If the heap value is a BV64 pointer (nested Box
            // pattern like Box<Box<T>>), follow ptr_source_map to find the inner
            // Box's actual non-bitvec content. Without this, nested Box deref
            // returns the inner pointer instead of the inner Box's content.
            if v.sort().is_bitvec() && v.sort().bitvec_width() == Some(POINTER_WIDTH) {
                let mut resolved = v;
                let mut chain_key = heap_key.as_str();
                for _ in 0..4 {
                    if let Some(inner_key) = self.ptr_source_map.get(chain_key) {
                        if let Some(inner_val) = self.heap_pointees.get(inner_key.as_ref()).cloned()
                        {
                            if !inner_val.sort().is_bitvec() {
                                debug!(
                                    "Part of #3748: nested Box resolved [{}] -> [{}] (sort={:?})",
                                    heap_key,
                                    inner_key,
                                    inner_val.sort()
                                );
                                resolved = inner_val;
                                break;
                            }
                            chain_key = inner_key.as_ref();
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }
                resolved
            } else {
                v
            }
        } else {
            // #1112: Fallback for symbolic/uninitialized Box contents.
            // When PartialEq explores enum variant paths with Box<T> fields that
            // were never populated (e.g., Expr::A vs Expr::A where Expr has
            // B(Box<Expr>) variants), we need to generate symbolic values.
            let pointee_ty = Self::box_pointee_ty(base_ty)?;
            let sort = Self::infer_sort_from_ty(pointee_ty)?;
            let name = self.ctx.fresh_name("box_symbolic");
            debug!(
                "try_codegen_box_field_access: created symbolic value for heap_pointees[{}] (sort={:?})",
                heap_key, sort
            );
            let symbolic_value = self.ctx.declare_var(&name, sort);

            // Store for consistency - repeated derefs get the same symbolic value
            self.heap_pointees.insert(std::sync::Arc::from(heap_key), symbolic_value.clone());
            symbolic_value
        };

        // If there are projections after Deref, apply them (struct field access)
        let projections_after_deref = &place.projection[deref_idx + 1..];
        if projections_after_deref.is_empty() {
            return Some(heap_value);
        }

        // Apply remaining Field projections to the heap value
        let mut expr = heap_value;
        for proj in projections_after_deref {
            if let ProjectionElem::Field(field_idx, _ty) = proj {
                if Self::is_marker_bv32_sort(expr.sort()) {
                    debug!(
                        "try_codegen_box_field_access: Field {} on bv32 (ZST/marker) - returning unchanged",
                        field_idx
                    );
                    continue;
                }
                if let Some(selected) =
                    crate::codegen_ay::types::datatype_field_select(expr.clone(), 0, *field_idx)
                {
                    expr = selected;
                    continue;
                }
                // Field projection failed
                debug!(
                    "try_codegen_box_field_access: field projection failed, sort={:?}, field={}",
                    expr.sort(),
                    field_idx
                );
                return None;
            }
            // external enum: ProjectionElem
            debug!("try_codegen_box_field_access: unsupported projection after Deref: {:?}", proj);
            return None;
        }

        Some(expr)
    }

    /// Check if a type is Box<T>.
    pub(super) fn is_box_type(ty: rustc_public::ty::Ty) -> bool {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                def.name().ends_with("::Box") || def.name() == "Box"
            }
            _ => false, // external enum: TyKind
        }
    }

    /// Emit null pointer and alignment checks for raw pointer dereferences.
    ///
    /// When a place contains a Deref projection on a raw pointer (*const T or *mut T),
    /// this function emits:
    /// 1. A null pointer check (violation if ptr == 0)
    /// 2. An alignment check (violation if ptr % align != 0, when alignment > 1)
    /// 3. A heap-allocation validity check (violation if `heap_is_allocated(ptr, size)` is false)
    ///
    /// Regular references (&T, &mut T) are not checked as Rust guarantees their validity.
    ///
    /// REQUIRES: place.projection contains at least one Deref to be effective
    /// ENSURES: For each RawPtr Deref in place.projection, adds null_pointer_check violation
    /// ENSURES: For each RawPtr Deref with align > 1, adds alignment_check violation
    /// ENSURES: For each RawPtr Deref, adds use_after_free_check violation
    /// ENSURES: For each RawPtr Deref through dead local, adds dead_object violation
    pub(super) fn emit_raw_ptr_deref_checks(&mut self, place: &Place) {
        for (deref_idx, proj) in place.projection.iter().enumerate() {
            if !matches!(proj, ProjectionElem::Deref) {
                continue;
            }

            // Construct minimal Place with projections up to deref_idx
            // instead of cloning the full projection Vec and truncating.
            let ptr_place =
                Place { local: place.local, projection: place.projection[..deref_idx].to_vec() };
            let Some(ptr_ty) = ptr_place.ty(self.body.locals()).into_option() else {
                continue;
            };
            let TyKind::RigidTy(RigidTy::RawPtr(pointee_ty, _)) = ptr_ty.kind() else {
                continue;
            };

            debug!("emit_raw_ptr_deref_checks: raw pointer deref at {:?}", place);

            // Get pointer expression. Note: ptr_place has no Deref projection (we truncated it),
            // so the recursive call to codegen_place will return early from emit_raw_ptr_deref_checks.
            let Some(ptr_expr) = self.codegen_place(&ptr_place) else {
                continue;
            };
            // Part of #3159: extract fld_ptr from Dyn_Trait sorts for pointer checks.
            let ptr_expr = extract_ptr_from_dyn_sort(ptr_expr);
            let Some(ptr_width) = ptr_expr.sort().bitvec_width() else {
                self.ctx
                    .unsupported("Raw pointer deref", "non-bitvector pointer sort for deref check");
                continue;
            };
            let zero = Expr::bitvec_const(0, ptr_width);

            // Record null pointer dereference violation if pointer is zero.
            debug!("  emitting null_pointer_check for ptr width={}", ptr_width);
            self.record_violation_guarded(ptr_expr.clone().eq(zero.clone()), "null_pointer_check");

            if ptr_width == POINTER_WIDTH {
                let access_size = LayoutOf::new(pointee_ty)
                    .size_of()
                    .map(|size| Expr::bitvec_const(size as u128, POINTER_WIDTH));
                let is_allocated = self.ctx.heap_is_allocated(ptr_expr.clone(), access_size);
                self.record_violation_guarded(is_allocated.not(), "use_after_free_check");
            }

            // Record alignment violation when the pointee alignment is known.
            let Some(align) = LayoutOf::new(pointee_ty).align_of() else {
                continue;
            };
            if align > 1 {
                debug!("  emitting alignment_check for align={}", align);
                let align_expr = Expr::bitvec_const(align as u128, ptr_width);
                let rem = ptr_expr.bvurem(align_expr);
                self.record_violation_guarded(rem.eq(zero).not(), "alignment_check");
            }

            // Dead object check: detect dereference of pointer to out-of-scope local. (#313)
            // If the pointer was created from &local as *const T, and local has gone
            // out of scope (StorageDead), emit a dead_object violation.
            //
            // Gated on current_path_condition.is_some() because dead_locals is
            // accumulated globally across blocks during traversal. In bb0 (entry
            // block, path_condition=None), StorageDead of reference temporaries
            // causes false positives. Assert terminators now propagate non-None
            // path conditions to their target blocks (#762), enabling detection in
            // post-Assert blocks where dead_object violations actually occur.
            let ptr_base = self.ssa_base_name(&ptr_place);
            if let Some(pointee_base) = self.ref_pointees.get(ptr_base.as_str()).cloned() {
                let target_local_idx =
                    Self::resolve_ref_chain_target(&self.ref_pointees, &pointee_base);
                if self.dead_locals.contains(&target_local_idx)
                    && self.current_path_condition.is_some()
                {
                    debug!(
                        "  emitting dead_object violation: ptr {} -> pointee {} (local_{})",
                        ptr_base, pointee_base, target_local_idx
                    );
                    self.record_violation_guarded(Expr::bool_const(true), "dead_object");
                }
            }
            // NOTE: pointer_invalid check (unknown provenance) also disabled because it
            // causes false positives for legitimate raw pointer casts. Tracking in #762.
        }
    }

    /// Resolve the ultimate target local index from a ref_pointees chain.
    ///
    /// Given a `pointee_base` name (format: `"fn::local_N"` or `"fn::local_N_field_M"`),
    /// extracts the local index N and chases one level through `ref_pointees` to find
    /// the actual source local whose liveness determines the dead_object check.
    ///
    /// Returns `usize::MAX` as a sentinel when the pointee name cannot be parsed
    /// (will not match any realistic `dead_locals` entry).
    ///
    /// Part of #2271: extracted from inline logic for testability.
    pub(super) fn resolve_ref_chain_target(
        ref_pointees: &std::collections::BTreeMap<std::sync::Arc<str>, std::sync::Arc<str>>,
        pointee_base: &str,
    ) -> usize {
        let Some(local_str) = pointee_base.split("::local_").nth(1) else {
            return usize::MAX;
        };
        // Handle cases like "local_5_field_0" -> extract just "5"
        let local_num_str = local_str.split('_').next().unwrap_or(local_str);
        let Ok(imm_idx) = local_num_str.parse::<usize>() else {
            return usize::MAX;
        };
        // Chase one level through ref_pointees to find the ultimate source local.
        // Pattern: ptr -> ref_temp_deref -> source_local.
        let fn_prefix = pointee_base.split("::local_").next().unwrap_or("");
        let imm_key = crate::codegen_ay::names::local_name(fn_prefix, imm_idx);
        if let Some(inner_pointee) = ref_pointees.get(imm_key.as_str()) {
            inner_pointee
                .split("::local_")
                .nth(1)
                .and_then(|s| s.split('_').next())
                .and_then(|s| s.parse::<usize>().ok())
                .unwrap_or(imm_idx)
        } else {
            imm_idx
        }
    }
}

/// Extract the `fld_ptr` field from a Dyn_Trait-like Datatype sort.
///
/// If the expression has a Datatype sort with a `fld_ptr` field, extracts it
/// as a BV64 pointer. Otherwise returns the expression unchanged.
///
/// Part of #3159: enables pointer deref checks on dyn Trait fat pointers.
fn extract_ptr_from_dyn_sort(expr: Expr) -> Expr {
    // Extract sort info before consuming expr to avoid borrow-after-move.
    let extraction = if let SortInner::Datatype(dt) = expr.sort().inner() {
        if let Some(cons) = dt.constructors.first() {
            cons.field("fld_ptr").map(|field| (dt.name.clone(), field.sort.clone()))
        } else {
            None
        }
    } else {
        None
    };
    if let Some((dt_name, field_sort)) = extraction {
        return expr.field_select(&dt_name, "fld_ptr", field_sort);
    }
    expr
}
