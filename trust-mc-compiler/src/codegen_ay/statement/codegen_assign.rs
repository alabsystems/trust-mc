// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Assignment dispatch (converted from include!() per #2595).
// Core assignment dispatch — pointer/ref/tracking helpers extracted to:
//   codegen_assign_ptr.rs  (raw ptr deref, Box unwrap, array index)
//   codegen_assign_ref.rs  (ref/pointee tracking, cast propagation)

use super::{DiscrScrutinee, IntoOption, StatementCodegen};
use rustc_public::mir::{AggregateKind, Operand, Place, ProjectionElem, Rvalue};
use rustc_public::ty::{AdtKind, RigidTy, TyKind};
use std::sync::Arc;
use tracing::{debug, warn};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Translate an assignment statement.
    ///
    /// In SSA form: `lhs_new = rvalue`, guarded by current path condition.
    /// Also updates the current environment so phi merges can select the right value.
    ///
    /// REQUIRES: lhs is a valid place in self.body, rhs is a valid rvalue
    /// ENSURES: Creates fresh SSA variable for lhs, constrains to rhs evaluation
    /// ENSURES: Updates environment mapping for lhs
    /// ENSURES: Handles pointer derefs, checked ops, and aggregates
    pub(super) fn codegen_assign(&mut self, lhs: &Place, rhs: &Rvalue) {
        // #408: Skip ZST assignments — ZSTs have no runtime representation.
        if let Some(lhs_ty) = lhs.ty(self.body.locals()).into_option()
            && Self::is_zst_type(lhs_ty)
        {
            debug!("codegen_assign: skipping ZST assignment to {:?}", lhs);
            return;
        }

        // SwitchInt→variant bridge (Effort 2, #3017): maintain the discriminant-scrutinee
        // side table for bare-local destinations. ANY write to the local first
        // invalidates a prior record (so a reused temp never carries a stale scrutinee);
        // a `Discriminant(P)` of a multi-variant datatype enum then re-records it so the
        // following SwitchInt can pin the active variant. Pure metadata — does not alter
        // codegen. (A match's discriminant read and switch live in one basic block, and
        // the table is also cleared at every block entry — see initialize_block_entry_env.)
        if lhs.projection.is_empty() {
            self.discr_of_local.remove(&lhs.local);
            if let Rvalue::Discriminant(scrutinee) = rhs {
                self.try_record_discr_scrutinee(lhs, scrutinee);
            }
        }

        // Handle raw pointer deref on LHS: *ptr = value stores to memory (#24).
        if self.try_codegen_assign_raw_ptr_deref(lhs, rhs) {
            return;
        }

        // Handle reference deref assignment: *ref = value for mutable references (#484).
        if self.try_codegen_assign_ref_deref(lhs, rhs) {
            return;
        }

        // Handle Box unwrap pattern: (*(box.0).0) = value (#1039).
        if self.try_codegen_assign_box_unwrap(lhs, rhs) {
            return;
        }

        // Handle array index assignment: arr[i] = value uses SMT store.
        if self.try_codegen_assign_array_index(lhs, rhs) {
            return;
        }

        // Handle special rvalue patterns with early returns.
        match rhs {
            Rvalue::CheckedBinaryOp(op, l, r) => {
                self.codegen_assign_checked_binary_op(lhs, *op, l, r);
                return;
            }
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) => {
                if self.try_codegen_tuple_copy(lhs, src) {
                    return;
                }
                // #1039: Track ptr_source_map for raw pointer copies from Box internals.
                if let Some(lhs_ty) = lhs.ty(self.body.locals()).into_option()
                    && matches!(lhs_ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(..)))
                {
                    self.try_track_box_ptr_source(lhs, src);
                }
            }
            // Flattened tuple aggregate
            Rvalue::Aggregate(AggregateKind::Tuple, operands) => {
                if self.try_codegen_flattened_tuple_aggregate(lhs, operands) {
                    return;
                }
            }
            // Part of #2076: Flatten Option-like enum aggregates
            Rvalue::Aggregate(
                AggregateKind::Adt(def, variant_idx, args, _user_ty_annot, _active_field),
                operands,
            ) => {
                if self.try_codegen_flattened_option_aggregate(
                    lhs,
                    def,
                    variant_idx,
                    args,
                    operands,
                ) {
                    return;
                }
                // #3159: Propagate heap_pointees through Box construction chain.
                // After MIR inlining, Box::new decomposes into:
                //   raw_ptr → NonNull<T>(raw_ptr) → Unique<T>(nonnull) → Box<T>(unique)
                // Each step is an ADT Aggregate. Propagate heap_pointees from any
                // operand to the resulting ADT so deref can trace back to the heap value.
                self.try_propagate_heap_through_adt_aggregate(lhs, operands);
            }
            // Part of #2970: AY workaround — select-only array aggregate encoding.
            // AY has broken store/select axioms (ay#5148): select(store(a,i,v),i)!=v.
            // Intercept array aggregates and encode with select-equality assertions.
            Rvalue::Aggregate(AggregateKind::Array(elem_ty), operands) => {
                if self.try_codegen_array_aggregate_with_select_workaround(lhs, *elem_ty, operands)
                {
                    return;
                }
                // Fall through to generic path if workaround fails
            }
            // #1210: ShallowInitBox heap_pointees propagation.
            Rvalue::ShallowInitBox(Operand::Copy(src_place) | Operand::Move(src_place), _ty) => {
                let src_base = self.root_ssa_base_name(src_place);
                let dst_base = self.root_ssa_base_name(lhs);
                if let Some(heap_value) = self.heap_pointees.get(src_base.as_str()).cloned() {
                    debug!(
                        "#1210: ShallowInitBox: propagating heap_pointees [{}] -> [{}]",
                        src_base, dst_base
                    );
                    self.heap_pointees.insert(std::sync::Arc::from(dst_base), heap_value);
                }
                // Fall through to generic codegen
            }
            _other => {} // external enum: Rvalue
        }

        if self.try_codegen_datatype_field_assign(lhs, rhs) {
            return;
        }

        // Store into an array that is a FIELD of a datatype: `self.buf[self.len]=v`
        // (LHS = [Deref?, Field(buf), …, Index(idx)]). The generic path drops this
        // store; encode it as store(field_array, idx, v) + datatype_field_update.
        if self.try_codegen_assign_datatype_field_index(lhs, rhs) {
            return;
        }

        // Handle slice coercion Cast: &[T; N] -> &[T] (#1140)
        if let Rvalue::Cast(_kind, operand, target_ty) = rhs
            && Self::is_slice_pointer_ty(*target_ty)
            && let Some(slice_expr) =
                self.try_construct_slice_datatype_from_cast(operand, *target_ty)
        {
            let lhs_name = self.ssa_name(lhs, true);
            let lhs_expr = self.ctx.declare_var(&lhs_name, slice_expr.sort().clone());
            let base_name = self.ssa_base_name(lhs);
            self.assert_ssa_def(lhs_expr.clone(), slice_expr, &base_name);
            self.env_update(base_name.clone(), lhs_expr);

            if matches!(target_ty.kind(), TyKind::RigidTy(RigidTy::Ref(..)))
                && let Operand::Copy(src) | Operand::Move(src) = operand
            {
                let src_base = self.ssa_base_name(src);
                if let Some(pointee) = self.ref_pointees.get(src_base.as_str()).cloned() {
                    debug!(
                        "codegen_assign slice Cast: propagating ref {} -> {} (pointee={})",
                        src_base, base_name, pointee
                    );
                    self.ref_pointees.insert(std::sync::Arc::from(base_name), pointee);
                }
            }
            return;
        }

        // --- Generic assignment path ---
        let lhs_name = self.ssa_name(lhs, true);

        // Generate rvalue expression to get actual sort
        let rhs_expr = self.codegen_rvalue(rhs);

        // Determine sort: prefer actual expression sort > place type > rvalue inference
        let sort = if let Some(ref rhs_expr) = rhs_expr {
            rhs_expr.sort().clone()
        } else {
            self.infer_sort_from_place(lhs).unwrap_or_else(|| self.infer_sort_from_rvalue(rhs))
        };

        let lhs_expr = self.ctx.declare_var(&lhs_name, sort);
        let base_name = self.ssa_base_name(lhs);

        // Assert SSA definition with ite semantics (#2081)
        if let Some(rhs_expr) = rhs_expr {
            self.assert_ssa_def(lhs_expr.clone(), rhs_expr, &base_name);
        } else {
            // Part of #3192: Track unconstrained assignment with distinct counter.
            // When codegen_rvalue returns None, the LHS variable is declared but
            // unconstrained (the solver can pick any value). This is a potential
            // false-proof vector: the solver might pick a value that satisfies
            // downstream assertions when the real value would violate them.
            // Uses the dedicated unconstrained_assignment counter (distinct from
            // unsupported_construct_fallback) so the driver can report the specific
            // class of encoding gap in demotion diagnostics.
            warn!(
                lhs = %lhs_name,
                rvalue = ?rhs,
                "codegen_assign: rvalue returned None, LHS is unconstrained"
            );
            self.ctx.unconstrained_assignment(
                "Assignment rvalue codegen returned None",
                format!("{:?}", lhs),
            );
        }

        self.env_update(base_name.clone(), lhs_expr);
        self.track_repeat_array_value(&base_name, rhs);

        // --- Post-assignment tracking ---

        // Track aggregate field ref_pointees
        self.track_rvalue_aggregate_refs(&base_name, lhs, rhs);

        // Track cast-related propagation
        self.track_cast_propagation(lhs, &lhs_name, rhs);

        // Track reference pointees for Ref/AddressOf rvalues
        self.track_ref_pointees(lhs, rhs);

        // Track Copy/Move reference propagation
        self.track_copy_move_ref_pointees(lhs, rhs);

        // Track constant reference pointees
        self.track_const_ref_pointees(lhs, rhs);

        // #3133: Propagate heap_pointees through Copy/Move chains.
        // Fallback for cases where ref_pointees propagation doesn't cover
        // the full chain (e.g., ShallowInitBox, Box unwrap patterns).
        if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rhs {
            // Part of #4112 follow-up: whole-value copies of flattened Option-like
            // enums (#2076) must carry the piecewise `{src}.0` discriminant and
            // `{src}_variant_V_field_F` payload entries to the new base. Otherwise
            // `discriminant(lhs)` degrades to an unconstrained symbolic and the
            // Downcast payload read loses the stored value (EncodingGap).
            let src_base = self.ssa_base_name(src);
            let flattened_entries =
                Self::collect_flattened_value_entries(&self.current_env, &src_base);
            if !flattened_entries.is_empty() {
                self.apply_flattened_value_entries(&base_name, flattened_entries);
            }

            let src_root = self.root_ssa_base_name(src);
            if let Some(heap_val) = self.heap_pointees.get(src_root.as_str()).cloned() {
                let dst_base: std::sync::Arc<str> = std::sync::Arc::from(base_name.as_str());
                debug!("#3133: Copy/Move heap propagation: [{}] -> [{}]", src_root, dst_base);
                self.heap_pointees.insert(dst_base.clone(), heap_val);

                // Part of #3748 D2: Also propagate ptr_source_map for nested Box
                // deref chains. When an outer Box's content pointer is moved to a
                // new local, the ptr_source_map link to the inner Box must follow.
                if let Some(src_map) = self.ptr_source_map.get(src_root.as_str()).cloned() {
                    self.ptr_source_map.insert(dst_base, src_map);
                }
            }
        }
    }

    /// SwitchInt→variant bridge (#3017): record `discr_of_local[lhs.local]` when
    /// `rhs = Discriminant(scrutinee)` for a bare local `lhs` and `scrutinee` resolves
    /// to a MULTI-VARIANT DATATYPE enum. Excludes unit enums (bitvec-sorted) and any
    /// scrutinee whose storage cannot be canonicalized — those keep no fact, so the
    /// downstream field read stays fail-closed.
    fn try_record_discr_scrutinee(&mut self, lhs: &Place, scrutinee: &Place) {
        if !lhs.projection.is_empty() {
            return;
        }
        let Some(place_key) = self.variant_fact_place_key(scrutinee) else {
            return;
        };
        let Some(ty) = scrutinee.ty(self.body.locals()).into_option() else {
            return;
        };
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
            return;
        };
        if def.kind() != AdtKind::Enum {
            return;
        }
        // Datatype sort with >1 constructor ⇒ the datatype-tester discriminant path is
        // used (build_discriminant_ite_chain), NOT the symbolic/bitvec/unit fallbacks.
        let Some(sort) = Self::infer_adt_sort(def, args) else {
            return;
        };
        let Some(dt) = sort.datatype_sort() else {
            return;
        };
        if dt.constructors.len() <= 1 {
            return;
        }
        // Bridge soundness gate (discr-mapping false-PROOF, adversarial finding): the
        // fact guard is built in declaration-index space (build_discriminant_ite_chain)
        // but SwitchInt case_vals are discriminant values; they agree ONLY for the
        // identity permutation. For explicit-#[repr]/permuted/signed discriminants,
        // record NO scrutinee → no facts → the #3017 fail-close stands (sound).
        if !self.enum_has_identity_discriminants(def, dt.constructors.len()) {
            return;
        }
        let dt_name: Arc<str> = Arc::from(dt.name.as_str());
        let ctor_names: Vec<Arc<str>> =
            dt.constructors.iter().map(|c| Arc::from(c.name.as_str())).collect();
        self.discr_of_local
            .insert(lhs.local, DiscrScrutinee { place_key, dt_name, ctor_names, adt_def: def });
    }

    fn track_repeat_array_value(&mut self, base_name: &str, rhs: &Rvalue) {
        let Rvalue::Repeat(operand, len_const) = rhs else {
            self.repeat_array_values.remove(base_name);
            return;
        };
        let Some(len) = len_const.eval_target_usize().into_option() else {
            self.repeat_array_values.remove(base_name);
            return;
        };
        let Some(elem_expr) = self.codegen_operand(operand) else {
            self.repeat_array_values.remove(base_name);
            return;
        };
        let elem_expr = self.resolve_concrete_expr(&elem_expr);
        if elem_expr.sort().is_datatype() {
            self.repeat_array_values.insert(std::sync::Arc::from(base_name), (elem_expr, len));
        } else {
            self.repeat_array_values.remove(base_name);
        }
    }

    /// Part of #2970: Array aggregate assignment with AY select-only workaround.
    ///
    /// AY has broken array store/select axiom, congruence, and non-monotonic
    /// behavior when combining store chains with select assertions (ay#5148).
    ///
    /// Workaround: instead of `lhs = store(store(base, 0, v0), 1, v1)`, declare
    /// `lhs` as a fresh array variable and constrain it via select equalities:
    ///   `(= (select lhs 0) v0)`, `(= (select lhs 1) v1)`.
    /// This avoids store chains entirely, which AY cannot reason about.
    fn try_codegen_array_aggregate_with_select_workaround(
        &mut self,
        lhs: &Place,
        elem_ty: rustc_public::ty::Ty,
        operands: &[Operand],
    ) -> bool {
        use ay_bindings::{Expr, Sort};

        let elem_sort = Self::infer_sort_from_ty(elem_ty).unwrap_or_else(|| Sort::bitvec(32));
        let array_sort =
            Sort::array(Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH), elem_sort.clone());

        // Declare the LHS SSA variable directly — no store chain.
        let lhs_name = self.ssa_name(lhs, true);
        let lhs_expr = self.ctx.declare_var(&lhs_name, array_sort);
        let base_name = self.ssa_base_name(lhs);

        // Emit select-equality assertions: `(= (select lhs i) val_i)` for each element.
        // This is the only definition of the array — no store chains involved.
        let mut constrained = 0u32;
        for (i, op) in operands.iter().enumerate() {
            if let Some(mut val) = self.codegen_operand(op) {
                // Apply the same coercion cascade as codegen_array_aggregate.
                let arr_sort_for_coerce = Sort::array(
                    Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH),
                    elem_sort.clone(),
                );
                if let Some(coerced) =
                    crate::codegen_ay::store_coercion::coerce_vec_string_store_value(
                        &arr_sort_for_coerce,
                        &val,
                    )
                {
                    val = coerced;
                }
                // Part of #3034: derive signedness from MIR element type.
                let signed =
                    crate::codegen_ay::shared::ty_signedness_shallow(elem_ty).unwrap_or(false);
                if let Some(coerced) = crate::codegen_ay::store_coercion::coerce_store_value_bmc(
                    &arr_sort_for_coerce,
                    &val,
                    signed,
                ) {
                    val = coerced;
                }
                if *val.sort() != elem_sort {
                    // Sort mismatch after coercion — element remains unconstrained.
                    // Part of #3192: track this as an unconstrained assignment.
                    debug!(
                        i,
                        store_sort = ?val.sort(),
                        elem_sort = ?elem_sort,
                        "Array aggregate select workaround: sort mismatch, element unconstrained (Part of #2970)"
                    );
                    self.ctx.unconstrained_assignment(
                        "Array aggregate element sort mismatch",
                        format!("element {i}"),
                    );
                    continue;
                }
                let idx = Expr::bitvec_const(i as u128, crate::codegen_ay::types::POINTER_WIDTH);
                self.ctx.assert(lhs_expr.clone().select(idx).eq(val));
                constrained += 1;
            } else {
                // Part of #3192: operand codegen returned None, element is unconstrained.
                self.ctx.unconstrained_assignment(
                    "Array aggregate operand codegen returned None",
                    format!("element {i}"),
                );
            }
        }

        self.env_update(base_name, lhs_expr);
        debug!(
            "codegen_assign: array aggregate select-only workaround ({}/{} elements constrained, Part of #2970)",
            constrained,
            operands.len()
        );
        true
    }

    /// Track ptr_source_map for raw pointer copies from Box internals (#1039).
    fn try_track_box_ptr_source(&mut self, lhs: &Place, src: &Place) {
        if src.projection.len() < 2 {
            return;
        }
        let last_two_field_0 =
            src.projection.iter().rev().take(2).all(|p| matches!(p, ProjectionElem::Field(0, _)));
        if !last_two_field_0 {
            return;
        }
        // Part of #2267: construct Place directly instead of clone + clear.
        let base_place = Place { local: src.local, projection: vec![] };
        if let Some(base_ty) = base_place.ty(self.body.locals()).into_option()
            && Self::box_pointee_ty(base_ty).is_some()
        {
            let ptr_base = self.root_ssa_base_name(lhs);
            let box_base = self.root_ssa_base_name(&base_place);
            warn!("#1039: raw ptr copy from Box, ptr_source_map[{}] = {}", ptr_base, box_base);
            self.ptr_source_map
                .insert(std::sync::Arc::from(ptr_base), std::sync::Arc::from(box_base));
        }
    }

    /// #3159: Propagate heap_pointees through ADT Aggregate construction.
    ///
    /// After MIR inlining, Box::new decomposes into a chain of ADT Aggregates:
    ///   raw_ptr → NonNull<T>(raw_ptr) → Unique<T>(nonnull) → Box<T>(unique)
    /// Each step wraps the previous. The heap_pointees entry lives on the raw
    /// pointer (set by codegen_raw_ptr_simple_store). This method propagates
    /// it forward through the wrapper chain so that Box locals also carry the
    /// heap value, enabling deref resolution.
    fn try_propagate_heap_through_adt_aggregate(&mut self, lhs: &Place, operands: &[Operand]) {
        let dst_base = self.root_ssa_base_name(lhs);
        // Check each operand: if a Move/Copy operand's root local has heap_pointees,
        // propagate to the destination. Also follow ptr_source_map transitively.
        for op in operands {
            let (Operand::Copy(src) | Operand::Move(src)) = op else {
                continue;
            };
            let src_root = self.root_ssa_base_name(src);
            // Direct check.
            if let Some(heap_val) = self.heap_pointees.get(src_root.as_str()).cloned() {
                debug!("#3159: ADT Aggregate heap propagation: [{}] -> [{}]", src_root, dst_base);
                self.heap_pointees.insert(std::sync::Arc::from(dst_base.as_str()), heap_val);
                self.ptr_source_map.insert(
                    std::sync::Arc::from(dst_base.as_str()),
                    std::sync::Arc::from(src_root.as_str()),
                );
                return;
            }
            // Follow ptr_source_map chain.
            let mut chain = src_root.clone();
            for _ in 0..8 {
                if let Some(next) = self.ptr_source_map.get(chain.as_str()) {
                    if let Some(heap_val) = self.heap_pointees.get(next.as_ref()).cloned() {
                        debug!(
                            "#3159: ADT Aggregate heap propagation (chain): [{}] -> [{}] (via {})",
                            next, dst_base, chain
                        );
                        self.heap_pointees
                            .insert(std::sync::Arc::from(dst_base.as_str()), heap_val);
                        self.ptr_source_map.insert(
                            std::sync::Arc::from(dst_base.as_str()),
                            std::sync::Arc::clone(next),
                        );
                        return;
                    }
                    chain = next.to_string();
                } else {
                    break;
                }
            }
        }
    }
}
