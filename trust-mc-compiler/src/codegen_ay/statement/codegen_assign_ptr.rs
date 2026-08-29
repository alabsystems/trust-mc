// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Raw pointer and Box assignment (converted from include!() per #2595).
// Extracted from codegen_assign.rs (#2246): raw pointer deref, Box unwrap,
// and array index assignment handlers.

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::kani_middle::abi::LayoutOf;
use ay_bindings::Expr;
use rustc_public::mir::{Operand, Place, ProjectionElem, Rvalue};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, trace, warn};

/// Bound on the `&x` -> `&raw mut (*_)` pointee-chain walk. Two steps is the
/// observed shape; the cap makes a malformed table terminate rather than spin.
const MAX_POINTEE_CHAIN: usize = 8;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Handle raw pointer deref assignment: `*ptr = value` stores to memory.
    ///
    /// Covers both simple deref (`*ptr = value`) and field-projected deref
    /// (`(*ptr).field = value`). Returns `true` if handled.
    pub(super) fn try_codegen_assign_raw_ptr_deref(&mut self, lhs: &Place, rhs: &Rvalue) -> bool {
        let Some(ProjectionElem::Deref) = lhs.projection.first() else {
            return false;
        };
        // Part of #2267: construct Place directly instead of clone + clear.
        let ptr_place = Place { local: lhs.local, projection: vec![] };
        let Some(ptr_ty) = ptr_place.ty(self.body.locals()).into_option() else {
            return false;
        };
        let TyKind::RigidTy(RigidTy::RawPtr(pointee_ty, _)) = ptr_ty.kind() else {
            return false;
        };

        // Emit pointer validity checks for raw pointer dereference (#430, #508).
        self.emit_raw_ptr_deref_checks(lhs);

        // FC-06 (BMC): a raw-pointer store (including `static mut` writes)
        // inside a modifies frame with an empty declared footprint is an
        // assigns violation (see `statement::modifies_frame`).
        self.bmc_modifies_check_raw_store(lhs);

        // Handle projections after Deref (e.g., (*ptr).field = value)
        if lhs.projection.len() > 1 {
            return self.try_codegen_raw_ptr_field_store(lhs, rhs, &ptr_place, pointee_ty);
        }

        // Simple deref: *ptr = value
        self.codegen_raw_ptr_simple_store(rhs, &ptr_place);
        true
    }

    /// Handle `(*ptr).field = value` — raw pointer with field projections after Deref.
    fn try_codegen_raw_ptr_field_store(
        &mut self,
        lhs: &Place,
        rhs: &Rvalue,
        ptr_place: &Place,
        pointee_ty: rustc_public::ty::Ty,
    ) -> bool {
        let mut total_offset: usize = 0;
        let mut current_ty = pointee_ty;
        let mut all_fields = true;
        let mut field_indices: Vec<usize> = vec![];

        for proj in lhs.projection.iter().skip(1) {
            if let ProjectionElem::Field(field_idx, field_ty) = proj {
                let layout = LayoutOf::new(current_ty);
                if let Some(offset) = layout.field_offset(*field_idx) {
                    total_offset += offset;
                    current_ty = *field_ty;
                    field_indices.push(*field_idx);
                } else {
                    debug!("codegen_assign: cannot compute field offset for field {}", *field_idx);
                    all_fields = false;
                    break;
                }
            } else {
                // external enum: ProjectionElem
                debug!("codegen_assign: unsupported projection after Deref: {:?}", proj);
                all_fields = false;
                break;
            }
        }

        if !all_fields {
            return false;
        }

        let Some(ptr_expr) = self.codegen_place(ptr_place) else {
            return false;
        };
        let Some(value_expr) = self.codegen_rvalue(rhs) else {
            return false;
        };

        // Add offset to pointer if non-zero
        let addr = if total_offset > 0 {
            ptr_expr.bvadd(Expr::bitvec_const(total_offset as i64, POINTER_WIDTH))
        } else {
            ptr_expr
        };
        debug!("codegen_assign: raw ptr deref + field, offset={}, storing to memory", total_offset);
        self.ctx.store_memory_bytes(addr, value_expr.clone());

        // #1039: Update heap_pointees for struct field mutations through Box.
        let ptr_base = self.root_ssa_base_name(ptr_place);
        warn!(
            "#1039: field mutation path, ptr_base={}, field_indices={:?}",
            ptr_base, field_indices
        );
        if let Some(source_box) = self.ptr_source_map.get(ptr_base.as_str()).cloned() {
            warn!("#1039: found source_box={} in ptr_source_map", source_box);
            if let Some(old_struct) = self.heap_pointees.get(source_box.as_ref()).cloned() {
                warn!("#1039: found old_struct in heap_pointees, sort={:?}", old_struct.sort());
                if let Some(new_struct) =
                    self.update_struct_field(&old_struct, &field_indices, value_expr)
                {
                    warn!(
                        "#1039: struct field mutation SUCCESS, updating heap_pointees[{}] and [{}]",
                        source_box, ptr_base
                    );
                    self.heap_pointees.insert(source_box, new_struct.clone());
                    self.heap_pointees.insert(std::sync::Arc::from(ptr_base), new_struct);
                } else {
                    warn!("#1039: update_struct_field returned None");
                }
            } else {
                warn!("#1039: source_box {} NOT found in heap_pointees", source_box);
            }
        } else {
            warn!("#1039: ptr_base {} NOT found in ptr_source_map", ptr_base);
        }
        true
    }

    /// Handle simple `*ptr = value` — raw pointer deref without field projections.
    fn codegen_raw_ptr_simple_store(&mut self, rhs: &Rvalue, ptr_place: &Place) {
        if let Some(ptr_expr) = self.codegen_place(ptr_place)
            && let Some(value_expr) = self.codegen_rvalue(rhs)
        {
            debug!("codegen_assign: raw ptr deref, storing to memory, ptr_place={:?}", ptr_place);
            self.ctx.store_memory_bytes(ptr_expr, value_expr.clone());

            // #1210: Track heap value for symbolic deref resolution.
            let ptr_base: std::sync::Arc<str> =
                std::sync::Arc::from(self.root_ssa_base_name(ptr_place));
            debug!("codegen_assign: heap_pointees[{}] = <expr> (raw ptr)", ptr_base);
            self.heap_pointees.insert(std::sync::Arc::clone(&ptr_base), value_expr.clone());

            // #1039: Propagate mutation back to source Box.
            if let Some(source_box) = self.ptr_source_map.get(ptr_base.as_ref()).cloned() {
                debug!("codegen_assign: propagating mutation to source box={}", source_box);
                self.heap_pointees.insert(source_box, value_expr.clone());
            }

            // Propagate the mutation back to a STACK-LOCAL pointee.
            //
            // Without this, a write through a raw pointer never reached the
            // thing pointed at. The byte-level store above and the
            // `heap_pointees` entry are both keyed by the POINTER, and the only
            // write-back was the Box case immediately above, so
            //
            //     let mut x: u8 = 3;
            //     let p: *mut u8 = &mut x;
            //     unsafe { *p = 9; }
            //     assert!(x == 3);
            //
            // reported SUCCESSFUL with PROOF_QUALIFIERS:clean — a FALSE PROOF
            // of a statement native Rust panics on — because reads of `x` still
            // resolved to its pre-store SSA value. `ref_pointees` is where the
            // pointer-to-local relationship lives, and nothing consulted it.
            self.write_back_to_stack_pointee(&ptr_base, &value_expr);
        }
    }

    /// Update a stack local's SSA value after a store through a pointer to it.
    ///
    /// Sort-guarded on purpose: a pointer produced by a CAST can address a
    /// local of a different width, and overwriting that local with a
    /// differently-sorted value would trade one wrong answer for another. When
    /// the sorts disagree the byte-level memory store still stands, so this
    /// only declines to ALSO update the scalar view.
    fn write_back_to_stack_pointee(
        &mut self,
        ptr_base: &std::sync::Arc<str>,
        value_expr: &Expr,
    ) {
        let Some(mut pointee_base) = self.ref_pointees.get(ptr_base.as_ref()).cloned() else {
            return;
        };
        // Follow the chain to the REAL local. `let p: *mut u8 = &mut x` lowers
        // to two steps — `_3 = &mut x` then `_2 = &raw mut (*_3)` — and records
        //
        //     ref_pointees[local_3] = local_1          (x itself)
        //     ref_pointees[local_2] = local_3_deref    (a synthetic)
        //
        // so one lookup from the raw pointer lands on `local_3_deref`, which no
        // read of `x` resolves to. Strip the `_deref` marker and look through
        // again until it settles on a base the environment actually holds.
        for _ in 0..MAX_POINTEE_CHAIN {
            let Some(stem) = pointee_base.as_ref().strip_suffix("_deref") else {
                break;
            };
            let Some(next) = self.ref_pointees.get(stem).cloned() else {
                break;
            };
            pointee_base = next;
        }
        // An element-qualified pointee (`<array>_idx_by_<local>`, written by
        // the as_ptr/offset provenance) names ONE SLOT of an array, not a
        // scalar local. Overwriting the whole local with a single element's
        // value would be a fresh wrong answer, so hand it to the helper that
        // already knows how to store into an array at an index — the same one
        // the `&mut a[i]` path uses.
        if pointee_base.contains("_idx_by_") {
            let fn_name = self.ctx.current_fn_name().to_string();
            debug!("codegen_assign: raw ptr store -> indexed array write {}", pointee_base);
            self.try_propagate_indexed_ref_write_to_array(
                &fn_name,
                pointee_base.as_ref(),
                value_expr.clone(),
            );
            return;
        }
        // The pointee resolves to a whole ARRAY while the value is one ELEMENT:
        // this is `a.as_mut_ptr()` with no offset, which addresses element 0.
        // Overwriting the array with a scalar would be nonsense, and declining
        // (what the sort guard below would do) leaves the store dropped and the
        // old value provable. Store at index 0 instead.
        if let Some(current) = self.env_lookup(pointee_base.as_ref()).cloned()
            && let Some(arr) = current.sort().array_sort()
            && arr.element_sort == *value_expr.sort()
        {
            debug!("codegen_assign: raw ptr store -> array element 0 of {}", pointee_base);
            let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);
            let stored = current.store(zero, value_expr.clone());
            let new_name = self.ssa_name_from_base(pointee_base.as_ref(), true);
            let new_var = self.ctx.declare_var(&new_name, stored.sort().clone());
            self.assert_ssa_def(new_var.clone(), stored, pointee_base.as_ref());
            self.env_update(std::sync::Arc::clone(&pointee_base), new_var);
            return;
        }
        if let Some(current) = self.env_lookup(pointee_base.as_ref())
            && current.sort() != value_expr.sort()
        {
            debug!(
                "codegen_assign: raw ptr store to {} skipped — sort {:?} != {:?}",
                pointee_base,
                current.sort(),
                value_expr.sort()
            );
            return;
        }
        debug!("codegen_assign: raw ptr store writes back to stack local {}", pointee_base);
        let pointee_name = self.ssa_name_from_base(pointee_base.as_ref(), true);
        let pointee_var = self.ctx.declare_var(&pointee_name, value_expr.sort().clone());
        self.assert_ssa_def(pointee_var.clone(), value_expr.clone(), pointee_base.as_ref());
        self.env_update(std::sync::Arc::clone(&pointee_base), pointee_var);
    }

    /// Handle Box unwrap assignment patterns (#1039).
    ///
    /// For `Box<T>`, MIR generates projections like `[Field(0), Field(0), Deref]`
    /// where `Field(0)` unwraps through `Unique` and `NonNull` wrappers.
    /// Returns `true` if handled.
    pub(super) fn try_codegen_assign_box_unwrap(&mut self, lhs: &Place, rhs: &Rvalue) -> bool {
        let Some(deref_idx) =
            lhs.projection.iter().position(|p| matches!(p, ProjectionElem::Deref))
        else {
            return false;
        };
        if deref_idx < 1 {
            return false;
        }
        let all_field_0_before_deref =
            lhs.projection.iter().take(deref_idx).all(|p| matches!(p, ProjectionElem::Field(0, _)));
        if !all_field_0_before_deref {
            return false;
        }

        // Part of #2267: construct Place directly instead of clone + clear.
        let box_place = Place { local: lhs.local, projection: vec![] };
        let Some(box_ty) = box_place.ty(self.body.locals()).into_option() else {
            return false;
        };
        if Self::box_pointee_ty(box_ty).is_none() {
            return false;
        }

        // Case 1: Deref is last projection — whole-value Box assignment
        if deref_idx == lhs.projection.len() - 1 {
            if let Some(value_expr) = self.codegen_rvalue(rhs) {
                let box_base = self.root_ssa_base_name(&box_place);
                debug!(
                    "codegen_assign: Box unwrap pattern [Field(0)^{}, Deref], \
                         heap_pointees[{}] = {:?}",
                    deref_idx,
                    box_base,
                    value_expr.sort()
                );
                self.heap_pointees.insert(std::sync::Arc::from(box_base.as_str()), value_expr);

                // Part of #3748 D2: For nested Box patterns (Box<Box<T>>), record
                // ptr_source_map from the outer Box local to the inner Box's local.
                // This enables deref chains to find the inner Box's heap_pointees
                // content when resolving multi-level Box dereferences.
                if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rhs {
                    let src_root = self.root_ssa_base_name(src);
                    if src_root != box_base && self.heap_pointees.contains_key(src_root.as_str()) {
                        debug!(
                            "Part of #3748: nested Box ptr_source_map[{}] = {}",
                            box_base, src_root
                        );
                        self.ptr_source_map.insert(
                            std::sync::Arc::from(box_base.as_str()),
                            std::sync::Arc::from(src_root.as_str()),
                        );
                    }
                }

                return true;
            }
            return false;
        }

        // Case 2: Field projections after Deref — Box field mutation
        self.try_codegen_box_field_mutation(lhs, rhs, &box_place, deref_idx)
    }

    /// Handle `(*(box.0).0).field = value` — Box field mutation (#1039).
    fn try_codegen_box_field_mutation(
        &mut self,
        lhs: &Place,
        rhs: &Rvalue,
        box_place: &Place,
        deref_idx: usize,
    ) -> bool {
        let projections_after_deref = &lhs.projection[deref_idx + 1..];
        let field_indices: Vec<usize> = projections_after_deref
            .iter()
            .filter_map(|p| match p {
                ProjectionElem::Field(idx, _) => Some(*idx),
                _ => None, // external enum: ProjectionElem
            })
            .collect();

        if field_indices.len() != projections_after_deref.len() || field_indices.is_empty() {
            return false;
        }

        let box_base = self.root_ssa_base_name(box_place);
        warn!(
            "#1039: Box field mutation pattern detected, box_base={}, field_indices={:?}",
            box_base, field_indices
        );

        let box_base: std::sync::Arc<str> = std::sync::Arc::from(box_base);
        let Some(old_struct) = self.heap_pointees.get(box_base.as_ref()).cloned() else {
            warn!("#1039: box_base {} NOT found in heap_pointees", box_base);
            return false;
        };
        let Some(value_expr) = self.codegen_rvalue(rhs) else {
            return false;
        };
        if let Some(new_struct) = self.update_struct_field(&old_struct, &field_indices, value_expr)
        {
            warn!("#1039: Box field mutation SUCCESS, updating heap_pointees[{}]", box_base);
            self.heap_pointees.insert(box_base, new_struct);
            true
        } else {
            warn!("#1039: update_struct_field returned None");
            false
        }
    }

    /// Handle array index assignment: `arr[i] = value` uses SMT store.
    ///
    /// Only handles simple cases where `Index` is the ONLY projection.
    /// Multi-dimensional arrays and struct field arrays fall through to the generic path.
    /// Returns `true` if handled.
    pub(super) fn try_codegen_assign_array_index(&mut self, lhs: &Place, rhs: &Rvalue) -> bool {
        if lhs.projection.len() != 1 {
            return false;
        }
        let Some(ProjectionElem::Index(idx_local)) = lhs.projection.first() else {
            return false;
        };

        debug!("Array index assign detected: lhs={:?}, idx_local={}", lhs, idx_local);
        // Part of #2267: construct Place directly instead of clone + clear.
        let base_place = Place { local: lhs.local, projection: vec![] };

        let Some(arr_expr) = self.codegen_place(&base_place) else {
            debug!("Array index assign: SMT store not applicable, using generic path");
            return false;
        };
        if !arr_expr.sort().is_array() {
            debug!("Array index assign: SMT store not applicable, using generic path");
            return false;
        }

        let idx_name = crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), *idx_local);
        let idx_expr_opt = self.env_lookup(&idx_name).cloned().or_else(|| {
            let idx_ssa = self.ssa_name_from_base(&idx_name, false);
            self.ctx.lookup_var(&idx_ssa).cloned()
        });

        let Some(idx_expr) = idx_expr_opt else {
            debug!("Array index assign: SMT store not applicable, using generic path");
            return false;
        };

        // Convert index to pointer width
        let idx_coerced = match idx_expr.sort().bitvec_width() {
            Some(w) if w == POINTER_WIDTH => idx_expr,
            Some(w) if w < POINTER_WIDTH => idx_expr.zero_extend(POINTER_WIDTH - w),
            Some(w) if w > POINTER_WIDTH => idx_expr.extract(POINTER_WIDTH - 1, 0),
            _ => {
                // non-enum: Option<u32> from bitvec_width()
                let location = format!("{:?}", lhs);
                self.ctx.unsupported("Array index assign - non-bitvec index", location);
                return true; // Handled (as unsupported)
            }
        };

        let Some(mut val_expr) = self.codegen_rvalue(rhs) else {
            debug!("Array index assign: SMT store not applicable, using generic path");
            return false;
        };

        // Part of #2894: Vec/String coercion via shared helper (was inline #1341).
        if let Some(coerced) = crate::codegen_ay::store_coercion::coerce_vec_string_store_value(
            arr_expr.sort(),
            &val_expr,
        ) {
            trace!("Array index assign: coerced value for Vec/String element");
            val_expr = coerced;
        }

        // Part of #2970: BMC sort coercion beyond Vec/String (BV width, Bool↔BV, etc.).
        // Part of #3034: derive signedness from LHS element type.
        let signed = lhs
            .ty(self.body.locals())
            .into_option()
            .and_then(crate::codegen_ay::shared::ty_signedness_shallow)
            .unwrap_or(false);
        if let Some(coerced) = crate::codegen_ay::store_coercion::coerce_store_value_bmc(
            arr_expr.sort(),
            &val_expr,
            signed,
        ) {
            debug!("Array index assign: BMC-coerced value (Part of #2970)");
            val_expr = coerced;
        }

        // Part of #2970: Last-resort fresh symbolic if sorts still mismatch.
        if let Some(arr) = arr_expr.sort().array_sort() {
            if *val_expr.sort() != arr.element_sort {
                let sym_name = crate::codegen_ay::store_coercion::bmc_store_fallback_name();
                debug!(
                    store_sort = ?val_expr.sort(),
                    elem_sort = ?arr.element_sort,
                    "Array index assign: fresh symbolic for sort mismatch (Part of #2970)"
                );
                val_expr = self.ctx.declare_var(&sym_name, arr.element_sort.clone());
            }
        }

        let new_arr = arr_expr.store(idx_coerced, val_expr);
        let new_arr_name = self.ssa_name(&base_place, true);
        let new_arr_var = self.ctx.declare_var(&new_arr_name, new_arr.sort().clone());

        let base_name = self.ssa_base_name(&base_place);
        self.assert_ssa_def(new_arr_var.clone(), new_arr, &base_name);
        self.env_update(base_name, new_arr_var);
        let base_name = self.ssa_base_name(&base_place);
        self.repeat_array_values.remove(base_name.as_str());
        debug!("Array index assignment: {} = store(arr, idx, val)", new_arr_name);
        true
    }
}
