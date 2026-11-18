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
        let indexed_borrow = self.normalize_indexed_reference_borrow(rhs);
        let rhs = indexed_borrow.as_ref().unwrap_or(rhs);
        self.guard_box_pointer_store(lhs);
        // ABI AddressOf can also produce a typed reference in ordinary drop
        // glue. Refuse only an actual raw-pointer destination here.
        if let Rvalue::AddressOf(_, source) = rhs
            && lhs
                .ty(self.body.locals())
                .ok()
                .is_some_and(|ty| matches!(ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(..))))
            && source.ty(self.body.locals()).ok().is_some_and(|ty| {
                crate::codegen_ay::shared::string_identity::type_contains_native_string(
                    self.ctx.tcx,
                    ty,
                )
            })
        {
            self.ctx.unsupported_with_fallback(
                "native_string_header_physical_custody_unqualified",
                "raw native String header address",
            );
        }

        // A store to the storage itself (no deref) replaces its value: a pointee
        // entry the handler does not re-insert describes the previous value, so
        // it is poisoned rather than silently reused (`ref_pointee_table`).
        let reassigned = (!lhs.projection.iter().any(|p| matches!(p, ProjectionElem::Deref)))
            .then(|| self.ssa_base_name(lhs));
        let generation = self.ref_pointees.generation();
        let check = lhs
            .projection
            .is_empty()
            .then(|| self.bmc_box_pointer_check_casts.get(&lhs.local).copied())
            .flatten();
        let previous = std::mem::replace(&mut self.bmc_box_pointer_check_alignment, check);
        self.codegen_assign_inner(lhs, rhs);
        self.bmc_box_pointer_check_alignment = previous;
        if let Some(key) = reassigned {
            self.ref_pointees.poison_stale_since(&key, generation);
        }
        self.poison_pointer_rebound_through_deref(lhs, generation);
        self.refresh_address_taken_image(lhs);
    }

    /// A POINTER VALUE stored THROUGH a dereference into a sub-place rebinds
    /// what that slot points at, and the `ref_pointees` entries this lane keeps
    /// were recorded from the BORROWS in the body: `let r = &mut h;
    /// (*r).p = &mut y; *h.p = 9; assert!(y == 2)` verified SUCCESSFUL with
    /// `[AY:PROOF_QUALIFIERS:clean]` because `*h.p` still resolved through the
    /// pointer the field held BEFORE the store (fourth adversarial review of
    /// m3/soundness-fixes-2, 2026-09-14, defect M3/D4 — the BMC half).
    ///
    /// The handlers that DO record the new binding (`h.p = &mut y` with no
    /// dereference, an aggregate built from a reference) run first and leave the
    /// table's generation moved, so this only fires where nothing was recorded.
    /// Anything it cannot re-bind exactly is poisoned AND records a fail-closed
    /// reason: a kept entry names the pre-store referent.
    fn poison_pointer_rebound_through_deref(&mut self, lhs: &Place, generation: u64) {
        if lhs.projection.len() < 2
            || !matches!(lhs.projection.first(), Some(ProjectionElem::Deref))
        {
            return;
        }
        let carries_pointer =
            lhs.ty(self.body.locals()).into_option().is_some_and(Self::ty_carries_a_pointer_value);
        if !carries_pointer {
            return;
        }
        if self.ref_pointees.generation() != generation {
            // A handler recorded the new binding while encoding this store.
            return;
        }
        let root_place = Place { local: lhs.local, projection: vec![] };
        let ptr_base = self.ssa_base_name(&root_place);
        let Some(pointee_base) = self.resolved_stack_pointee_base(&ptr_base) else {
            return;
        };
        warn!(
            ?lhs,
            %pointee_base,
            "BMC: a pointer stored through a dereference rebinds its target — fail closed"
        );
        let now = self.ref_pointees.generation();
        self.ref_pointees.poison_stale_since(&pointee_base, now);
        self.ctx.unsupported_with_fallback(
            "pointer_stored_through_deref_rebinds_target",
            format!("{pointee_base}: a pointer value was stored into a slot of it"),
        );
    }

    /// Keep the BYTE IMAGE of an address-taken local in step with a store into
    /// one of its sub-places.
    ///
    /// `get_or_create_address_symbol` materializes a local into byte memory
    /// when its address is taken (#1246), and every raw-pointer read loads from
    /// that image. A store into a FIELD or an ELEMENT updates only the local's
    /// register, so the image kept the old bytes: `let mut s = S { x: 0, y: 0 };
    /// let p: *mut u8 = &mut s.x; s.x = 9; assert!(unsafe { *p } == 0)`
    /// verified SUCCESSFUL in BMC and the safe twin was FAILED
    /// [AY:CTREX_CAT:Genuine] (adversarial review of m3/soundness-fixes-2,
    /// 2026-09-14; red on main too — and the same for an array element).
    /// The whole-local store path has its own write-backs; a store THROUGH a
    /// dereference writes memory itself, so neither is re-done here.
    ///
    /// Re-storing the local's new value is EXACT, so this costs no proof. When
    /// the value cannot be read back the image is left stale, and that fails
    /// closed rather than silently disagreeing with the register lane.
    fn refresh_address_taken_image(&mut self, lhs: &Place) {
        if lhs.projection.is_empty()
            || lhs.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
        {
            return;
        }
        let root_place = Place { local: lhs.local, projection: vec![] };
        let base = self.ssa_base_name(&root_place);
        let leaf_base = self.ssa_base_name(lhs);
        let addr = self.addr_symbols.get(base.as_str()).cloned();
        // The sub-place's OWN name is what a reference to it points at
        // (`ref_pointees[p] = ..._field_0`), and a read through that reference
        // resolves THAT name — not the root the store updated.
        let leaf_tracked = self.env_lookup(leaf_base.as_str()).is_some();
        if addr.is_none() && !leaf_tracked {
            return;
        }
        if let Some(addr) = addr {
            let Some(value) = self.codegen_place(&root_place) else {
                self.ctx.unsupported_with_fallback(
                    "address-taken local image not refreshed",
                    format!("{base}: the local has no value after a store into it"),
                );
                return;
            };
            let ty = root_place.ty(self.body.locals()).into_option();
            let materialized =
                ty.is_some_and(|ty| self.try_materialize_array_to_memory(&addr, &value, ty));
            if !materialized {
                self.store_memory_bytes_on_path(addr, value, "address-taken local image refresh");
            }
            debug!("refreshed the byte image of address-taken local {base}");
        }
        if leaf_tracked {
            let Some(leaf_value) = self.codegen_place(lhs) else {
                self.ctx.unsupported_with_fallback(
                    "referenced sub-place not refreshed",
                    format!("{leaf_base}: no value after a store into it"),
                );
                return;
            };
            let ssa = self.ssa_name_from_base(&leaf_base, true);
            let var = self.ctx.declare_var(&ssa, leaf_value.sort().clone());
            self.assert_ssa_def(var.clone(), leaf_value, &leaf_base);
            self.env_update(leaf_base.clone(), var);
            debug!("refreshed the referenced sub-place {leaf_base}");
        }
    }

    fn codegen_assign_inner(&mut self, lhs: &Place, rhs: &Rvalue) {
        // #408: Skip ZST assignments — ZSTs have no runtime representation.
        if let Some(lhs_ty) = lhs.ty(self.body.locals()).into_option()
            && Self::is_zst_type(lhs_ty)
        {
            debug!("codegen_assign: skipping ZST assignment to {:?}", lhs);
            return;
        }

        // FC-06 (BMC): classify a store through a deref against the innermost
        // modifies frame BEFORE dispatch, so every store shape below is
        // attributed (accused, certified, frame-local, or failed closed) no
        // matter which handler encodes it. See `statement::modifies_frame`.
        self.bmc_modifies_check_deref_store(lhs);

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

        // A store through a pointer with no tracked pointee cannot reach the
        // stack local it may address (`mark_untracked_deref_store`).
        self.mark_untracked_deref_store(lhs);

        // Handle raw pointer deref on LHS: *ptr = value stores to memory (#24).
        if self.try_codegen_assign_raw_ptr_deref(lhs, rhs) {
            return;
        }

        // Handle reference deref assignment: *ref = value for mutable references (#484).
        if self.try_codegen_assign_ref_deref(lhs, rhs) {
            return;
        }

        if self.try_codegen_assign_ref_deref_index(lhs, rhs) {
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

        if self.try_codegen_shared_scalar_slice_element_borrow(lhs, rhs) {
            return;
        }

        // Handle special rvalue patterns with early returns.
        match rhs {
            Rvalue::CheckedBinaryOp(op, l, r) => {
                self.codegen_assign_checked_binary_op(lhs, *op, l, r);
                return;
            }
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) => {
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
            #[cfg(not(trust_toolchain))]
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

        // A store into a place that nests an element index inside another index
        // or a field on a LOCAL (`g[i][j] = v`, `a[i].buf[k] = v`): rebuild the
        // local from the leaf outwards.
        if self.try_codegen_assign_nested_place(lhs, rhs) {
            return;
        }

        // A store under a dereference or an index that no handler above consumed
        // would bind a register named for the projection while the storage it
        // denotes never changes: `let r: &mut [[u8; 2]; 2] = &mut g; r[i][1] = 9;
        // assert!(g[i][1] == 0)` and `g[1][0] = 9; assert!(g[1][0] == 0)` verified
        // SUCCESSFUL and the safe twins FAILED with a Genuine counterexample
        // (main 31793ccc3). The generic path below is only exact for a local and
        // the flattened fields of a local, so any other place fails closed here.
        if lhs.projection.iter().any(|p| {
            matches!(
                p,
                ProjectionElem::Deref
                    | ProjectionElem::Index(_)
                    | ProjectionElem::ConstantIndex { .. }
                    | ProjectionElem::Subslice { .. }
            )
        }) {
            self.ctx.unsupported_with_fallback(
                "generic store to a place under a dereference or an index",
                format!("{lhs:?}"),
            );
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

        self.env_update(base_name.clone(), lhs_expr.clone());
        self.mirror_untracked_ref_deref_store(lhs, &lhs_expr);
        self.track_repeat_array_value(&base_name, rhs);

        // --- Post-assignment tracking ---

        // Track aggregate field ref_pointees
        self.track_rvalue_aggregate_refs(&base_name, lhs, rhs);

        // Track cast-related propagation
        self.track_cast_propagation(lhs, &lhs_name, rhs);

        // A sub-slice view with a nonzero start keeps that fact through copies
        // and reborrows, so the consumer guard can see it at the call site.
        self.propagate_shifted_subslice_view(&base_name, rhs);

        // Track reference pointees for Ref/AddressOf rvalues
        self.track_ref_pointees(lhs, rhs);

        // Track Copy/Move reference propagation
        self.track_copy_move_ref_pointees(lhs, rhs);

        // Track constant reference pointees
        self.track_const_ref_pointees(lhs, rhs);

        // #3133: Propagate heap_pointees through Copy/Move chains.
        // Fallback for cases where ref_pointees propagation doesn't cover
        // the full chain (e.g., ShallowInitBox, Box unwrap patterns).
        if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) = rhs {
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
        let elem_expr = self.repeat_element_value(operand, &elem_expr);
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
