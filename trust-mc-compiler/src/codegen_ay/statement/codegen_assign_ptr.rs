// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Raw pointer and Box assignment (converted from include!() per #2595).
// Extracted from codegen_assign.rs (#2246): raw pointer deref, Box unwrap,
// and array index assignment handlers.

use super::{IndexedVal, IntoOption, StatementCodegen};
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};
use crate::kani_middle::abi::LayoutOf;
use ay_bindings::{Expr, Sort};
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
        self.store_memory_bytes_on_path(addr, value_expr.clone(), "raw pointer field store");

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
                    self.update_struct_field(&old_struct, &field_indices, value_expr.clone())
                {
                    warn!(
                        "#1039: struct field mutation SUCCESS, updating heap_pointees[{}] and [{}]",
                        source_box, ptr_base
                    );
                    self.heap_pointees.insert(source_box, new_struct.clone());
                    self.heap_pointees.insert(std::sync::Arc::from(ptr_base.as_str()), new_struct);
                } else {
                    warn!("#1039: update_struct_field returned None");
                }
            } else {
                warn!("#1039: source_box {} NOT found in heap_pointees", source_box);
            }
        } else {
            warn!("#1039: ptr_base {} NOT found in ptr_source_map", ptr_base);
        }
        // The byte store above and the `heap_pointees` / `ptr_source_map`
        // write-backs both key on the POINTER. A raw pointer taken of a STACK
        // place reaches none of them, so `let p: *mut S = &mut a[0];
        // (*p).y = 9; assert!(a[0].y == 0)` was VERIFICATION:- SUCCESSFUL with
        // `[AY:PROOF_QUALIFIERS:clean]` — the store landed nowhere a read of
        // `a` resolves to (fourth adversarial review of m3/soundness-fixes-2,
        // 2026-09-14, defect M1/D2; pre-existing on main). The `&mut` deref
        // path writes the field back through the projection walk; this one now
        // does the same, or fails closed.
        self.write_back_field_to_stack_pointee(&ptr_base, &field_indices, &value_expr, lhs);
        true
    }

    /// Write `(*ptr).f0.f1… = value` back into the STACK place `ptr` addresses.
    ///
    /// The field's derived name (`{pointee}_field_{f0}_field_{f1}`) is the name
    /// the projection walk owns, so updating that register and handing it to
    /// `try_propagate_deref_write_to_parent_datatype` undoes the fields — and,
    /// for a pointer of an array ELEMENT's field, the element too. Anything this
    /// cannot place exactly records a fail-closed reason: a silently dropped
    /// field store is the false proof this exists to close.
    fn write_back_field_to_stack_pointee(
        &mut self,
        ptr_base: &str,
        field_indices: &[usize],
        value_expr: &Expr,
        lhs: &Place,
    ) {
        let Some(pointee_base) = self.resolved_stack_pointee_base(ptr_base) else {
            // No stack pointee is recorded: the pointer addresses memory the
            // byte store above already covers (a heap object, a parameter).
            return;
        };
        if field_indices.is_empty() {
            return;
        }
        let mut derived = pointee_base.to_string();
        for idx in field_indices {
            derived.push_str(&format!("_field_{idx}"));
        }
        // The field register must be able to HOLD the stored value. A mismatch
        // (a flattened payload word, a narrower view) is not a write-back this
        // path can make exactly.
        if let Some(current) = self.env_lookup(&derived).cloned()
            && current.sort() != value_expr.sort()
        {
            self.ctx.unsupported_with_fallback(
                "raw_ptr_field_store_pointee_sort_mismatch",
                format!("{derived}: {:?} != {:?}", current.sort(), value_expr.sort()),
            );
            return;
        }
        debug!("codegen_assign: raw ptr field store writes back to {derived}");
        let field_name = self.ssa_name_from_base(&derived, true);
        let field_var = self.ctx.declare_var(&field_name, value_expr.sort().clone());
        self.assert_ssa_def(field_var.clone(), value_expr.clone(), &derived);
        self.env_update(derived.clone(), field_var.clone());
        self.try_propagate_deref_write_to_parent_datatype(&derived, &field_var, lhs);
    }

    /// Handle simple `*ptr = value` — raw pointer deref without field projections.
    fn codegen_raw_ptr_simple_store(&mut self, rhs: &Rvalue, ptr_place: &Place) {
        if let Some(ptr_expr) = self.codegen_place(ptr_place)
            && let Some(value_expr) = self.codegen_rvalue(rhs)
        {
            debug!("codegen_assign: raw ptr deref, storing to memory, ptr_place={:?}", ptr_place);
            // A store on one path keeps main's path-guarded lane; a store on every
            // path of a known pointee type replaces only its object's bytes.
            match ptr_place.ty(self.body.locals()).into_option().map(|t| t.kind()) {
                Some(TyKind::RigidTy(RigidTy::RawPtr(pointee, _)))
                    if self.store_path_condition().is_none() =>
                {
                    self.store_typed_value_to_memory(ptr_expr, value_expr.clone(), pointee)
                }
                _ => self.store_memory_bytes_on_path(
                    ptr_expr,
                    value_expr.clone(),
                    "raw pointer store",
                ),
            }

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
            self.write_back_to_stack_pointee(&ptr_base, &value_expr, ptr_place, rhs);
        }
    }

    /// Update a stack local's SSA value after a store through a pointer to it.
    ///
    /// Sort-guarded on purpose: a pointer produced by a CAST can address a
    /// local of a different width, and overwriting that local with a
    /// differently-sorted value would trade one wrong answer for another. When
    /// the sorts disagree the byte-level memory store still stands, so this
    /// only declines to ALSO update the scalar view.
    /// The storage a pointer's `ref_pointees` entry finally names.
    ///
    /// Follow the chain to the REAL local. `let p: *mut u8 = &mut x` lowers
    /// to two steps — `_3 = &mut x` then `_2 = &raw mut (*_3)` — and records
    ///
    ///     ref_pointees[local_3] = local_1          (x itself)
    ///     ref_pointees[local_2] = local_3_deref    (a synthetic)
    ///
    /// so one lookup from the raw pointer lands on `local_3_deref`, which no
    /// read of `x` resolves to. Strip the `_deref` marker and look through
    /// again until it settles on a base the environment actually holds.
    pub(super) fn resolved_stack_pointee_base(
        &self,
        ptr_base: &str,
    ) -> Option<std::sync::Arc<str>> {
        let mut pointee_base = self.ref_pointees.get(ptr_base).cloned()?;
        for _ in 0..MAX_POINTEE_CHAIN {
            let Some(stem) = pointee_base.as_ref().strip_suffix("_deref") else {
                break;
            };
            let Some(next) = self.ref_pointees.get(stem).cloned() else {
                break;
            };
            pointee_base = next;
        }
        Some(pointee_base)
    }

    /// Move an element-qualified pointee's OWN register to the stored value.
    ///
    /// `a_idx_by_L`, `a_idx_by_L_field_0` and friends are names the READ side
    /// resolves directly (`codegen_place` tries the full projected name first),
    /// so a store through a raw pointer of such a slot has to update that
    /// register as well as the array the walk writes back into. A sort the
    /// register cannot hold is not a write-back this path can make exactly: the
    /// register is havocked and a fail-closed reason recorded, never left at
    /// the pre-store value.
    fn place_element_slot_register(&mut self, pointee_base: &str, value_expr: &Expr) {
        let current_sort = self.env_lookup(pointee_base).map(|e| e.sort().clone());
        match current_sort {
            Some(sort) if sort != *value_expr.sort() => {
                self.ctx.unsupported_with_fallback(
                    "raw_ptr_store_element_slot_sort_mismatch",
                    format!("{pointee_base}: {:?} != {:?}", sort, value_expr.sort()),
                );
                let fresh_name = self.ssa_name_from_base(pointee_base, true);
                let fresh = self.ctx.declare_var(&fresh_name, sort);
                self.env_update(pointee_base.to_owned(), fresh);
            }
            _ => {
                let slot_name = self.ssa_name_from_base(pointee_base, true);
                let slot_var = self.ctx.declare_var(&slot_name, value_expr.sort().clone());
                self.assert_ssa_def(slot_var.clone(), value_expr.clone(), pointee_base);
                self.env_update(pointee_base.to_owned(), slot_var);
            }
        }
    }

    pub(super) fn write_back_to_stack_pointee(
        &mut self,
        ptr_base: &std::sync::Arc<str>,
        value_expr: &Expr,
        ptr_place: &Place,
        rhs: &Rvalue,
    ) {
        let Some(pointee_base) = self.resolved_stack_pointee_base(ptr_base.as_ref()) else {
            return;
        };
        // An element-qualified pointee (`<array>_idx_by_<local>`, written by
        // the as_ptr/offset provenance) names ONE SLOT of an array, not a
        // scalar local. Overwriting the whole local with a single element's
        // value would be a fresh wrong answer, so hand it to the helper that
        // already knows how to store into an array at an index — the same one
        // the `&mut a[i]` path uses.
        if pointee_base.contains("_idx_by_") {
            let fn_name = self.ctx.current_fn_name().to_string();
            debug!("codegen_assign: raw ptr store -> indexed array write {}", pointee_base);
            // The pointee's OWN register is a name a READ resolves: `codegen_place`
            // looks the full projected name (`a_idx_by_L_field_0`) up in the
            // environment BEFORE it walks the array, and `&raw mut a[i].x`
            // recorded the pre-store value under exactly that name. Every other
            // branch of this function updates that register first; this one did
            // not, so the array was updated exactly and the read still answered
            // with the value the borrow was taken at:
            // `let p: *mut u8 = &raw mut a[i].x; *p = 9; assert!(a[i].x == 0)`
            // was VERIFICATION:- SUCCESSFUL with [AY:PROOF_QUALIFIERS:clean] and
            // its safe twin FAILED [AY:CTREX_CAT:Genuine] (fifth adversarial
            // review of m3/soundness-fixes-2, 2026-09-14, defect R1 — a
            // regression of the D1 commit, which stopped
            // `try_propagate_indexed_ref_write_to_array` from recording the
            // coercion fallback that used to demote this shape). The element
            // slot is placed under the array by the walk below; here the slot's
            // own register moves with it, or the store fails closed.
            self.place_element_slot_register(&pointee_base, value_expr);
            self.try_propagate_indexed_ref_write_to_array(
                &fn_name,
                pointee_base.as_ref(),
                value_expr.clone(),
            );
            // The projection walk owns every derived name (`_idx_by_`,
            // `_cidx_`, `_field_`) and undoes them innermost first; the call
            // above is now only the stub-pointee fallback.
            self.try_propagate_deref_write_to_parent_datatype(
                pointee_base.as_ref(),
                value_expr,
                ptr_place,
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
            self.env_update(std::sync::Arc::clone(&pointee_base), new_var.clone());
            self.try_propagate_deref_write_to_parent_datatype(
                pointee_base.as_ref(),
                &new_var,
                ptr_place,
            );
            return;
        }
        if let Some(current) = self.env_lookup(pointee_base.as_ref()).cloned()
            && current.sort() != value_expr.sort()
        {
            // The local holds the pointee in another representation (a flattened
            // payload word against a datatype value, a narrower cast view). The
            // store still happened: leaving the local at its old value made the
            // old value provable. It is left unconstrained instead, with its
            // flattened components, and the harness is marked.
            debug!(
                "codegen_assign: raw ptr store to {} — sort {:?} != {:?}, pointee havocked",
                pointee_base,
                current.sort(),
                value_expr.sort()
            );
            self.ctx.unsupported_with_fallback(
                "raw_ptr_store_pointee_sort_mismatch",
                format!("{pointee_base}: {:?} != {:?}", current.sort(), value_expr.sort()),
            );
            let fresh_name = self.ssa_name_from_base(pointee_base.as_ref(), true);
            let fresh = self.ctx.declare_var(&fresh_name, current.sort().clone());
            self.env_update(std::sync::Arc::clone(&pointee_base), fresh.clone());
            self.store_flattened_components(pointee_base.as_ref(), Vec::new());
            // The havocked field reaches its enclosing datatype register too, as
            // every exact write-back below does: otherwise the next `&(*r).N`
            // re-derives the field from the stale parent.
            self.try_propagate_deref_write_to_parent_datatype(
                pointee_base.as_ref(),
                &fresh,
                ptr_place,
            );
            return;
        }
        debug!("codegen_assign: raw ptr store writes back to stack local {}", pointee_base);
        let pointee_name = self.ssa_name_from_base(pointee_base.as_ref(), true);
        let pointee_var = self.ctx.declare_var(&pointee_name, value_expr.sort().clone());
        self.assert_ssa_def(pointee_var.clone(), value_expr.clone(), pointee_base.as_ref());
        let bindings_before = self.ref_pointees.generation();
        self.env_update(std::sync::Arc::clone(&pointee_base), pointee_var.clone());
        // The stored value's flattened components travel with it.
        self.store_flattened_components_through_ref(pointee_base.as_ref(), rhs);
        // The local now holds a value written through a raw pointer; bindings
        // recorded for its previous value are stale (see the `&mut` deref store).
        self.ref_pointees.poison_stale_since(&pointee_base, bindings_before);
        // Keep the enclosing datatype register in step with a FIELD write,
        // exactly as the `&mut` deref-store path does
        // (`try_codegen_assign_ref_deref`). Without it the flattened field
        // register (`<obj>_field_N`) holds the new value while `<obj>` still
        // holds the old one, and the next borrow of that field
        // (`&(*r).N`, which re-derives `<obj>_field_N` from `<obj>`) silently
        // restores the pre-store value. `dual_uc_ensures.rs::harness_for_modify`
        // (`*im.x.get() += 2` under `requires x < 100`, `ensures x < 101`) read
        // the stale value in its postcondition and verified SUCCESSFUL.
        self.try_propagate_deref_write_to_parent_datatype(
            pointee_base.as_ref(),
            &pointee_var,
            ptr_place,
        );
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
                if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) = rhs {
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

    /// `g[i][j] = v`, `g[K][j] = v`, `a[i].buf[k] = v`: a store into a place on a
    /// LOCAL that nests an element index inside another index or a field, which
    /// neither `try_codegen_assign_array_index` (one `Index`) nor the datatype
    /// field handlers (fields after one index, one trailing index under fields)
    /// cover. The generic path bound a register named for the projection while
    /// the local never changed: `let mut g = [[0u8; 2]; 2]; g[1][0] = 9;
    /// assert!(g[1][0] == 0)` verified SUCCESSFUL and the safe twin FAILED with a
    /// Genuine counterexample (main 31793ccc3). The local's value is rebuilt from
    /// the leaf outwards (`update_projected_value`); anything that cannot be
    /// rebuilt records `unsupported_with_fallback` and fails closed. Returns
    /// `true` when the store was handled (exactly or fail-closed).
    pub(super) fn try_codegen_assign_nested_place(&mut self, lhs: &Place, rhs: &Rvalue) -> bool {
        if lhs.projection.len() < 2
            || lhs.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
        {
            return false;
        }
        let indexes = lhs
            .projection
            .iter()
            .filter(|p| {
                matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. })
            })
            .count();
        if indexes == 0 {
            return false;
        }
        let location = || format!("{lhs:?}");
        let base_place = Place { local: lhs.local, projection: vec![] };
        let Some(root) = self.codegen_place(&base_place) else {
            self.ctx
                .unsupported_with_fallback("nested place store: local has no value", location());
            return true;
        };
        let Some(rhs_expr) = self.codegen_rvalue(rhs) else {
            self.ctx
                .unsupported_with_fallback("nested place store: value did not codegen", location());
            return true;
        };
        let signed = lhs
            .ty(self.body.locals())
            .into_option()
            .and_then(crate::codegen_ay::shared::ty_signedness_shallow)
            .unwrap_or(false);
        let Some(new_root) =
            self.update_projected_value(&root, &lhs.projection, &rhs_expr, lhs, signed)
        else {
            self.ctx.unsupported_with_fallback("nested place store: place not rebuilt", location());
            return true;
        };
        let base_name = self.ssa_base_name(&base_place);
        // A materialized byte image of the local (its address was taken) would be
        // stale after this store; nothing may rest on it.
        if self.addr_symbols.contains_key(base_name.as_str()) {
            self.ctx.unsupported_with_fallback(
                "nested place store: address-taken local not mirrored",
                location(),
            );
        }
        let new_name = self.ssa_name(&base_place, true);
        let new_var = self.ctx.declare_var(&new_name, new_root.sort().clone());
        self.assert_ssa_def(new_var.clone(), new_root, &base_name);
        self.env_update(base_name.clone(), new_var);
        self.repeat_array_values.remove(base_name.as_str());
        debug!("nested place store: {} rebuilt from the leaf", new_name);
        true
    }

    /// `value` with the sub-place `projs` denotes replaced by `leaf`: an `Index` /
    /// `ConstantIndex` becomes `store(array, i, ..)` (over the element array of a
    /// slice / Vec datatype when `value` is one), a `Field` (after an optional
    /// `Downcast`) a rebuilt constructor. The leaf is coerced to the slot's sort
    /// with the BMC store coercions. `None` when a projection does not fit the
    /// value's sort, an index has no value, or the leaf cannot be coerced — the
    /// caller fails closed, never stores a fresh symbol.
    pub(in crate::codegen_ay::statement) fn update_projected_value(
        &mut self,
        value: &Expr,
        projs: &[ProjectionElem],
        leaf: &Expr,
        lhs: &Place,
        leaf_signed: bool,
    ) -> Option<Expr> {
        let mut variant: Option<usize> = None;
        let mut at = 0;
        while let Some(ProjectionElem::Downcast(v)) = projs.get(at) {
            variant = Some(v.to_index());
            at += 1;
        }
        let Some(proj) = projs.get(at) else {
            return self.coerce_leaf_to_slot(value.sort(), leaf, leaf_signed);
        };
        match proj {
            ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => {
                // The element storage: the value itself, or `fld_data` / `fld_buf`
                // of a slice / Vec datatype.
                let data_field = if value.sort().is_array() {
                    None
                } else {
                    let dt = value.sort().datatype_sort()?;
                    if dt.constructors.len() != 1 {
                        return None;
                    }
                    let (field_idx, field) =
                        dt.constructors[0].fields.iter().enumerate().find(|(_, f)| {
                            matches!(&*f.name, "fld_data" | "fld_buf") && f.sort.is_array()
                        })?;
                    Some((
                        dt.name.to_string(),
                        field_idx,
                        field.name.to_string(),
                        field.sort.clone(),
                    ))
                };
                let array = match &data_field {
                    None => value.clone(),
                    Some((dt_name, _, field_name, field_sort)) => {
                        value.clone().field_select(dt_name, field_name, field_sort.clone())
                    }
                };
                let arr_sort = array.sort().array_sort()?;
                let index_width = arr_sort.index_sort.bitvec_width().unwrap_or(POINTER_WIDTH);
                let idx = self.projection_index_value(proj, index_width)?;
                let elem = array.clone().select(idx.clone());
                let new_elem =
                    self.update_projected_value(&elem, &projs[at + 1..], leaf, lhs, leaf_signed)?;
                let new_array = array.store(idx, new_elem);
                match data_field {
                    None => Some(new_array),
                    Some((_, field_idx, _, _)) => Self::datatype_field_update(
                        value, field_idx, None, new_array, lhs, self.ctx,
                    ),
                }
            }
            ProjectionElem::Field(field_idx, _) => {
                let sort = value.sort().clone();
                let dt = sort.datatype_sort()?;
                let cons_idx = if dt.constructors.len() > 1 { variant? } else { 0 };
                let cons = dt.constructors.get(cons_idx)?;
                // `datatype_field_update` maps field 0 of the `Some` arm of an
                // option-like struct onto its second field; read the same slot.
                let is_option_like_struct = dt.constructors.len() == 1
                    && cons.fields.len() == 2
                    && cons.fields[0].name == "is_some";
                let slot = if is_option_like_struct && variant == Some(1) && *field_idx == 0 {
                    1
                } else {
                    *field_idx
                };
                let field = cons.fields.get(slot)?;
                let current =
                    value.clone().field_select(&*dt.name, &*field.name, field.sort.clone());
                let new_field = self.update_projected_value(
                    &current,
                    &projs[at + 1..],
                    leaf,
                    lhs,
                    leaf_signed,
                )?;
                Self::datatype_field_update(value, *field_idx, variant, new_field, lhs, self.ctx)
            }
            _ => None, // external enum: ProjectionElem (Deref, Subslice, OpaqueCast, ...)
        }
    }

    /// The index of an `Index` / `ConstantIndex` projection as a bitvector of
    /// `width` bits: the index local's value, or the constant offset. `None` for an
    /// index counted from the end (a runtime length this layer has no value for)
    /// or an index local with no value.
    pub(super) fn projection_index_value(
        &mut self,
        proj: &ProjectionElem,
        width: u32,
    ) -> Option<Expr> {
        let idx = match proj {
            ProjectionElem::Index(idx_local) => {
                let idx_name =
                    crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), *idx_local);
                self.env_lookup(&idx_name).cloned().or_else(|| {
                    let idx_ssa = self.ssa_name_from_base(&idx_name, false);
                    self.ctx.lookup_var(&idx_ssa).cloned()
                })?
            }
            ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                let offset = super::constant_index_offset(*offset, *min_length, *from_end)?;
                Expr::bitvec_const(offset as u128, width)
            }
            _ => return None, // external enum: ProjectionElem
        };
        match idx.sort().bitvec_width() {
            Some(w) if w == width => Some(idx),
            Some(w) if w < width => Some(idx.zero_extend(width - w)),
            Some(_) => Some(idx.extract(width - 1, 0)),
            None => None,
        }
    }

    /// `leaf` coerced to `slot_sort` with the BMC store coercions (Vec / String
    /// element images, bitvector widths, `Bool` <-> `BV1`); `None` when the sorts
    /// still differ.
    fn coerce_leaf_to_slot(&self, slot_sort: &Sort, leaf: &Expr, signed: bool) -> Option<Expr> {
        if leaf.sort() == slot_sort {
            return Some(leaf.clone());
        }
        let slot_array = Sort::array(ptr_sort(), slot_sort.clone());
        let coerced =
            crate::codegen_ay::store_coercion::coerce_vec_string_store_value(&slot_array, leaf)
                .or_else(|| {
                    crate::codegen_ay::store_coercion::coerce_store_value_bmc(
                        &slot_array,
                        leaf,
                        signed,
                    )
                })?;
        (coerced.sort() == slot_sort).then_some(coerced)
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
