// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Statement encoding helpers: failed rvalue handling, safety checks,
//! alloc-id propagation, and promoted-const seeding.
//!
//! Extracted from `codegen_stmt/mod.rs` — Part of #4206.

use std::collections::{HashMap, HashSet};

use ay_bindings::Expr;
use rustc_public::mir::{BinOp, Operand, Place, ProjectionElem, Rvalue, UnOp};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use crate::args::ChcTrackLevel;
use crate::codegen_ay::shared::signedness_fallback_for_arithmetic;

use super::super::ChcCtx;
use super::super::codegen_expr_signedness::ExprSignedness;
use super::StmtAccumulator;
use super::codegen_stmt_safety_checks::{
    division_by_zero_condition, signed_div_overflow_condition, signed_neg_overflow_condition,
    unchecked_shift_distance_condition,
};

fn try_extract_data_obj_id(expr: &Expr) -> Option<u32> {
    // obj_id 0 is the null/invalid sentinel — see clusters_ref_resolution.rs
    // comments and ay_compiler heap conventions: allocations use obj_id >= 2,
    // promoted-const region uses obj_id == 1, and obj_id == 0 means NULL.
    // Propagating obj_id 0 into `known_alloc_ids` / `alloc_result_locals` would
    // (a) make null-deref checks vacuously skipped (#null-fix), and
    // (b) cause store/load codegen to address the null region.
    ChcCtx::try_extract_obj_id(expr)
        .or_else(|| {
            let width = expr.sort().bitvec_width()?;
            let ptr_width = crate::codegen_ay::types::POINTER_WIDTH;
            (width == 2 * ptr_width).then(|| {
                let data_ptr = expr.clone().extract(ptr_width - 1, 0);
                ChcCtx::try_extract_obj_id(&data_ptr)
            })?
        })
        .filter(|&obj_id| obj_id != 0)
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// D3: Handle failed rvalue translation — self-loop emission, deref-load
    /// detection, ref-to-flattened recovery, vtable discriminant recovery,
    /// and collection ghost state propagation.
    ///
    /// Called when `translate_rvalue_with_modified` returns `None`. All paths
    /// produce a placeholder constraint (self-loop or tautological `true`).
    pub(in crate::codegen_ay::chc) fn handle_failed_rvalue_translation(
        &mut self,
        lhs: &Place,
        rhs: &Rvalue,
        local_idx: usize,
        bb_idx: usize,
        modified: &mut HashSet<usize>,
        constraints: &mut Vec<Expr>,
        last_constraint_for_local: &mut HashMap<usize, usize>,
    ) {
        // Part of #3038: constraint-or-unchanged invariant.
        // When rvalue translation fails, emit a self-loop constraint
        // (output_var = input_var) instead of leaving the output unconstrained.
        Self::mark_modified_for_unsupported_rvalue(lhs, modified);
        self.encode.local_expr_env.remove(&local_idx);
        self.encode.local_signedness.remove(&local_idx);
        let has_projection = !lhs.projection.is_empty();
        // Part of #3138: Detect deref-load BEFORE self-loop emission.
        // Deref-loads should NOT get a self-loop (out = in) because that
        // identity-copies the prior value — unsound for locals reassigned
        // across blocks. Instead, leave output universally quantified.
        let is_deref_load = matches!(
            rhs,
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                if place.projection.first()
                    == Some(&ProjectionElem::Deref)
        );
        {
            let mut acc = StmtAccumulator::new(modified, constraints, last_constraint_for_local);
            if is_deref_load {
                // Part of #3138: Deref-loads must NOT get a self-loop
                // (out = in) because that identity-copies the prior value —
                // unsound for locals reassigned across blocks. Emit a
                // tautological `true` constraint instead. This keeps the
                // local in last_constraint_for_local (preventing
                // enforce_modified_constraint_invariant from reverting to
                // identity-copy) while leaving the output variable genuinely
                // unconstrained (universally quantified by PDR).
                acc.replace_constraint(local_idx, Expr::bool_const(true));
            } else if !self.emit_self_loop_constraint(local_idx, &mut acc) {
                // Part of #3052: When self-loop emission fails (corrupted
                // state mapping or missing output slot), emit a BoolConst(true)
                // placeholder to maintain the #3038 invariant.
                acc.replace_constraint(local_idx, Expr::bool_const(true));
            }
        }
        // Part of #112: Ref/AddressOf to a flattened local (Range, Option,
        // tuple) is a sound over-approximation. The reference variable gets
        // an unconstrained pointer address, but call stubs operate directly
        // on the flattened fields — the reference is never dereferenced
        // through memory in the CHC encoding.
        let is_ref_to_flattened = matches!(
            rhs,
            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)
                if self.flatten.flattened_tuple_locals.contains(&place.local)
        );
        // Part of #4030: projected Ref/AddressOf at Reg level can return
        // `None` solely to request Mem promotion. The full `mir_to_chc`
        // pipeline reruns translation at Mem level when `needs_mem_promote`
        // is set, so counting the discarded Reg pass as a DEMOTED fallback
        // is misleading. Keep the placeholder constraint for this pass,
        // but leave `fallback_count` unchanged.
        let ref_or_addressof_waiting_for_mem_promote =
            self.needs_mem_promote && matches!(rhs, Rvalue::Ref(..) | Rvalue::AddressOf(..));
        // Part of #3973: When int_lift is active, ref-to-flattened
        // is doubly sound — stubs operate on flattened fields and
        // the reference is never dereferenced. Don't count as a
        // translation drop since the encoding is precise at field level.
        // Skip both the sound_fallback_reason AND the demoted fallback.
        let ref_to_flattened_is_int_lifted = is_ref_to_flattened && self.int_lift;
        if ref_to_flattened_is_int_lifted || ref_or_addressof_waiting_for_mem_promote {
            // Intentionally no fallback recording — encoding is
            // precise at field level via Pattern 4 field-by-field copy,
            // or the current pass is being discarded in favor of Mem.
        } else if is_deref_load || is_ref_to_flattened {
            if is_deref_load
                && self.track_level >= ChcTrackLevel::Ptr
                && let Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) = rhs
                && matches!(place.projection.first(), Some(ProjectionElem::Deref))
                && matches!(
                    self.body.locals()[place.local].ty.kind(),
                    TyKind::RigidTy(RigidTy::RawPtr(_, _))
                )
            {
                self.emit_ptr_obj_valid_check(place.local, modified);
                // Fail closed: an unresolved raw-pointer deref at Ptr level
                // cannot soundly prove safety from a tautological/fallback
                // validity check, because the loaded value is unconstrained.
                self.heap_state.pending_checks.push(Expr::bool_const(false));
                self.mark_heap_metadata_read();
                self.record_sound_fallback_reason("raw_ptr_deref_unresolved_fail_closed");
            }
            warn!(
                "CHC: bb{} Assign _{} {} rvalue unresolved (sound over-approx, rhs={:?})",
                bb_idx,
                local_idx,
                if is_deref_load { "deref-load" } else { "ref-to-flattened" },
                rhs
            );
            // Task #78: the destination local `local_idx` is left universally
            // quantified (havoced) here — plumb its SMT-var identity so the
            // driver can dependency-check the violated `error_p{N}`. The freed
            // value is the local's output state var (or `None`/dead).
            let deref_reason = if is_deref_load {
                "rvalue_deref_load_unresolved"
            } else {
                "rvalue_ref_to_flattened"
            };
            let deref_freed = self.freed_dest_output_var(local_idx);
            self.record_sound_fallback_reason_identified(deref_reason, deref_freed.as_deref());
            // Part of #3608: Recover vtable discriminant for deref-loaded
            // wrapper-dyn values (e.g., Box<dyn Trait> loaded from heap).
            // The local's output is universally quantified (sound, #3138),
            // but we still need the vtable side-channel so downstream
            // virtual dispatch can devirtualize.
            if is_deref_load {
                let local_ty = self.body.locals()[local_idx].ty;
                if let Some(vtable_id) = self.resolve_unique_wrapped_dyn_vtable_id(local_ty) {
                    let vtable_expr = Expr::bitvec_const(
                        vtable_id as u128,
                        crate::codegen_ay::types::POINTER_WIDTH,
                    );
                    if let Some(vc) = self.capture_known_vtable_discriminant(local_idx, vtable_expr)
                    {
                        constraints.push(vc);
                    }
                }
            }
        } else {
            warn!(
                "CHC: bb{} Assign _{} rvalue translation failed (self-loop fallback, rhs={:?}) — recording fallback",
                bb_idx, local_idx, rhs
            );
            self.record_fallback();
        }
        debug!(
            local_idx,
            has_projection,
            is_deref_load,
            "CHC: unsupported rvalue, using self-loop fallback (#3038)"
        );
        // Part of #3284: Even when rvalue translation fails (e.g.,
        // Ref with Deref+Field projections), propagate collection
        // ghost state through ref_targets if available. Without this,
        // `_23 = &((*_ref).0)` leaves vec_len_23 unconstrained.
        if self.collections.len_state.get_len_var(local_idx).is_some() {
            if let Some(rt) = self.ref_resolution.ref_targets.get(&local_idx).cloned() {
                let field_idx = rt.projections.iter().find_map(|p| {
                    if let ProjectionElem::Field(idx, _) = p { Some(*idx) } else { None }
                });
                if let Some(field_idx) = field_idx {
                    // Use a dummy rhs_expr (ghost propagation uses
                    // flattened field lookup, not the rhs expression).
                    let dummy_rhs = Expr::bool_const(true);
                    self.propagate_collection_ghost_through_projection(
                        local_idx,
                        &dummy_rhs,
                        rt.local,
                        field_idx,
                        modified,
                        constraints,
                    );
                }
            }
        }
    }

    /// D4: Emit UB safety checks for arithmetic operations.
    ///
    /// Covers unchecked overflow (Add/Sub/Mul), shift distance, division by zero,
    /// signed division overflow, negation overflow, pointer offset overflow, and
    /// the NaN-generation obligation for symbolic float binops (Kani --nan-check
    /// parity).
    pub(in crate::codegen_ay::chc) fn emit_assignment_safety_checks(
        &mut self,
        rhs: &'body Rvalue,
        rhs_expr: &Expr,
        bb_idx: usize,
        modified: &HashSet<usize>,
        safety_checks: &mut Vec<Expr>,
    ) {
        // Emit UB safety checks for arithmetic ops (#3299, #3363).
        // Mirrors BMC path (statement/rvalue.rs:106-141).
        if let Rvalue::BinaryOp(op, lhs_op, rhs_op) = rhs {
            if let (Some(le), Some(re)) = (
                self.translate_operand_with_modified(lhs_op, modified),
                self.translate_operand_with_modified(rhs_op, modified),
            ) {
                let is_float = matches!(
                    lhs_op.ty(self.body.locals()).map(|ty| ty.kind()),
                    Ok(TyKind::RigidTy(RigidTy::Float(_)))
                );
                if is_float {
                    // NaN-generation obligation for float value binops,
                    // gated on `--nan-check` (see codegen_stmt_safety_checks.rs).
                    //
                    // OFF by default, matching Kani. Producing a NaN is DEFINED
                    // behaviour in Rust, not UB, so this is a lint and not a
                    // safety property. It used to be pushed unconditionally,
                    // which made EVERY harness containing symbolic float
                    // arithmetic report a false FAILURE: the obligation ranges
                    // over an unconstrained select from the uninterpreted
                    // `float_binop_tbl_*`, and the only discharges are literal
                    // constant operands or a dominating is_finite assume. The
                    // integer div/rem and overflow checks below must NOT run
                    // for floats — float division by zero is DEFINED in Rust
                    // (±inf/NaN results), and the divisor-bits != 0 check
                    // would spuriously fail legal float divisions now that
                    // symbolic float binops translate successfully.
                    if self.nan_checks
                        && let Some(c) = self.float_nan_check_condition(
                            *op, lhs_op, rhs_op, &le, &re, rhs_expr, bb_idx,
                        )
                    {
                        debug!(?op, "CHC: float NaN-generation check (Kani --nan-check parity)");
                        safety_checks.push(c);
                    }
                } else if le.sort().is_bitvec() && re.sort().is_bitvec() {
                    let signed = || {
                        self.is_signed_integer_op(lhs_op, rhs_op)
                            .unwrap_or_else(|| signedness_fallback_for_arithmetic("chc_safety"))
                    };
                    match op {
                        BinOp::AddUnchecked | BinOp::SubUnchecked | BinOp::MulUnchecked => {
                            if self.overflow_checks
                                && let Some(c) =
                                    Self::unchecked_overflow_condition(*op, &le, &re, signed())
                            {
                                debug!(?op, "CHC: overflow check (#3299)");
                                safety_checks.push(c);
                            }
                        }
                        BinOp::ShlUnchecked | BinOp::ShrUnchecked => {
                            if self.overflow_checks {
                                let d_signed = self.operand_signedness(rhs_op).unwrap_or(false);
                                if let Some(c) =
                                    unchecked_shift_distance_condition(&le, &re, d_signed)
                                {
                                    debug!(?op, "CHC: shift distance check (#3363)");
                                    safety_checks.push(c);
                                }
                            }
                        }
                        BinOp::Div | BinOp::Rem => {
                            if let Some(c) = division_by_zero_condition(&re) {
                                debug!(?op, "CHC: div-by-zero check (#3363)");
                                safety_checks.push(c);
                            }
                            if self.overflow_checks && signed() {
                                if let Some(c) = signed_div_overflow_condition(&le, &re) {
                                    debug!(?op, "CHC: signed div overflow (#3363)");
                                    safety_checks.push(c);
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }

        // Part of #3300: Emit pointer overflow safety checks for BinOp::Offset.
        // The call path (codegen_call_ptr.rs) handles ptr::offset/add/sub
        // intrinsics, but the rvalue path was missing these checks, producing
        // false PROOF verdicts.
        //
        // Kani parity: default-on under memory_safety_checks. The earlier
        // static-discharge blocker (guards referencing block-relation state
        // vars that don't const-fold) is resolved: the constant fast-paths in
        // pointer_step.rs and ptr_offset_alloc_bound_check fold fully-concrete
        // harnesses to literal bools (trivially-true checks are skipped at
        // emission), and the state-array-referencing obj_valid provenance
        // select stays gated behind extra_pointer_checks inside
        // ptr_offset_overflow_conditions.
        if self.memory_safety_checks
            && let Rvalue::BinaryOp(BinOp::Offset, lhs_op, rhs_op)
            | Rvalue::CheckedBinaryOp(BinOp::Offset, lhs_op, rhs_op) = rhs
        {
            let offset_checks = self.ptr_offset_overflow_conditions(lhs_op, rhs_op, modified);
            safety_checks.extend(offset_checks);
        }

        // Part of #3363 Phase 2+: Emit negation overflow check for UnOp::Neg.
        // Signed negation of INT_MIN overflows (e.g., -(-128i8) wraps to -128).
        // Mirrors BMC path (statement/rvalue.rs:250-251, arithmetic_checks.rs:261-264).
        if self.overflow_checks
            && let Rvalue::UnaryOp(UnOp::Neg, operand) = rhs
        {
            if self.operand_signedness(operand) == Some(true) {
                if let Some(op_e) = self.translate_operand_with_modified(operand, modified) {
                    if let Some(c) = signed_neg_overflow_condition(&op_e) {
                        debug!("CHC: neg overflow check (#3363)");
                        safety_checks.push(c);
                    }
                }
            }
        }
    }

    /// D5: Propagate known_alloc_ids through pointer-identity operations.
    ///
    /// Tracks allocation identity through deref loads, ShallowInitBox, casts,
    /// aggregate construction, and Ref-to-Deref patterns for store-to-load
    /// forwarding in inlined Rc::new/deref chains.
    pub(in crate::codegen_ay::chc) fn propagate_alloc_ids_for_assign(
        &mut self,
        lhs: &Place,
        rhs: &Rvalue,
        local_idx: usize,
        rhs_expr: &Expr,
    ) {
        // Part of #3608, #3589: Propagate known_alloc_ids through pointer-identity
        // operations. Without this, inlined Rc::new/deref chains lose allocation
        // identity at intermediate MIR assignments (NonNull wrapping, field extraction,
        // casts), preventing store-to-load forwarding on the Deref load side.
        if !lhs.projection.is_empty() {
            return;
        }

        // Field-0 data-pointer provenance forward (Box<dyn>/drop-glue lane).
        // A drop reads the container's data-pointer field through `&mut self`:
        //   `_dst = Copy((*_ref).0)`   (proj = [Deref, Field(0)])
        // The reference names the container's STACK slot (obj_C), so the bare
        // fallback below would make `_dst` inherit obj_C — the container's own
        // 16-byte fat-ptr slot — and the later dealloc then sees a stack object
        // of the wrong size (false "dealloc of stack local" / size-mismatch).
        // The field-0 lane instead resolves `_dst` to the heap DATA allocation
        // (obj_H) that the field points into, recorded at construction under the
        // single-assignment provenance gate. See `try_field0_provenance_forward`.
        if let Some(obj_h) = self.try_field0_provenance_forward(rhs) {
            self.known_alloc_ids.insert(local_idx, obj_h);
            self.ref_resolution.alloc_result_locals.insert(local_idx);
            return;
        }

        let loaded_alloc_id = match rhs {
            // Part of #3871: `move (*_ptr)` loads the pointee value. The
            // destination must track the loaded object's alloc_id, not the
            // source pointer local's alloc_id (which still names the outer
            // allocation). Reusing `p.local` here makes nested Box/Rc deref
            // chains follow the wrong object on the next load.
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                if matches!(p.projection.first(), Some(ProjectionElem::Deref)) =>
            {
                try_extract_data_obj_id(rhs_expr)
            }
            Rvalue::CopyForDeref(_) => try_extract_data_obj_id(rhs_expr),
            _ => None,
        };

        if let Some(obj_id) = loaded_alloc_id {
            self.known_alloc_ids.insert(local_idx, obj_id);
            self.ref_resolution.alloc_result_locals.insert(local_idx);
        } else {
            // Completes the #3871 rule stated above: a deref load through a
            // pointer that provably holds `&_L` yields _L's VALUE, so _L's own
            // slot alloc_id must NOT reach the destination. Without this the
            // generic `Rvalue::Use` arm below re-derives it from the source
            // pointer local and a later deref of the destination reads _L's
            // slot as though it were the pointee — an ADDRESS used as a VALUE,
            // landing on a memory cell no rule writes at that type. This also
            // gives the `known_alloc_ids.remove` branch at the bottom of this
            // function, written for exactly this shape, a path to run: the
            // generic arm used to capture the shape first, leaving it dead.
            // `deref_load_referent_local` matches only that exact shape, so
            // Box/Rc/NonNull deref chains keep their inheritance.
            if let Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) = rhs
                && matches!(p.projection.first(), Some(ProjectionElem::Deref))
                && let Some(referent) = self.deref_load_referent_local(p.local)
            {
                let forwarded = self.known_alloc_ids.get(&referent).copied();
                debug!(
                    local_idx,
                    ptr_local = p.local,
                    referent,
                    ?forwarded,
                    "CHC: deref load through a pointer to a local's own slot — \
                     forwarding the referent's alloc_id, not the slot's"
                );
                match forwarded {
                    Some(obj_id) => {
                        self.known_alloc_ids.insert(local_idx, obj_id);
                        self.ref_resolution.alloc_result_locals.insert(local_idx);
                    }
                    None => {
                        self.known_alloc_ids.remove(&local_idx);
                    }
                }
                return;
            }
            let src_local_for_alloc = match rhs {
                Rvalue::ShallowInitBox(Operand::Copy(p) | Operand::Move(p), _)
                | Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                // Cast preserves pointer identity (ptr casts, unsized coercions).
                | Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _) => {
                    Some(p.local)
                }
                Rvalue::ShallowInitBox(..) | Rvalue::Use(..) | Rvalue::Cast(..) => {
                    None
                }
                // Aggregate construction wrapping a pointer (NonNull, Rc, Box):
                // find the first operand that carries an alloc_id.
                Rvalue::Aggregate(_, operands) => {
                    operands.iter().find_map(|op| match op {
                        Operand::Copy(p) | Operand::Move(p) => {
                            if self.known_alloc_ids.contains_key(&p.local) {
                                Some(p.local)
                            } else {
                                None
                            }
                        }
                        _ => None,
                    })
                }
                // Ref to a Deref place: _20 = &mut (*_28) — the reference
                // points into the same allocation as the deref base.
                // Part of #3589: Without this, Rc::new stores through a
                // reference whose address is symbolic, preventing store-to-load
                // forwarding when the load uses alloc_id-based constant addresses.
                // Only handle leading Deref: Ref(_, _, (*_base).fields)
                Rvalue::Ref(_, _, p)
                    if matches!(p.projection.first(), Some(ProjectionElem::Deref)) =>
                {
                    Some(p.local)
                }
                Rvalue::Ref(_, _, _) | Rvalue::CopyForDeref(_) => None,
                _ => None,
            };
            let rhs_alloc_id = match rhs {
                Rvalue::ShallowInitBox(..)
                | Rvalue::Use(..)
                | Rvalue::Cast(..)
                | Rvalue::Aggregate(..)
                | Rvalue::Ref(..) => try_extract_data_obj_id(rhs_expr),
                Rvalue::CopyForDeref(_) => None,
                _ => None,
            };
            if let Some(src) = src_local_for_alloc {
                if let Some(obj_id) = self
                    .known_alloc_ids
                    .get(&src)
                    .copied()
                    .or_else(|| self.trace_deref_store_alloc_id(src))
                    .or(rhs_alloc_id)
                {
                    self.known_alloc_ids.insert(local_idx, obj_id);
                    self.ref_resolution.alloc_result_locals.insert(local_idx);
                    // WRITER (field-0 provenance): the value copied into
                    // `local_idx` carries heap alloc `obj_id`; record that its
                    // data-pointer field (field 0) points into that allocation,
                    // so a later drop-glue read of the field resolves obj_H.
                    self.maybe_record_field0_provenance(local_idx, obj_id, src);
                }
            } else if let Some(obj_id) = rhs_alloc_id {
                self.known_alloc_ids.insert(local_idx, obj_id);
                self.ref_resolution.alloc_result_locals.insert(local_idx);
            } else if matches!(
                rhs,
                Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                    if matches!(p.projection.first(), Some(ProjectionElem::Deref))
            ) || matches!(rhs, Rvalue::CopyForDeref(_))
            {
                self.known_alloc_ids.remove(&local_idx);
            }
        }
    }

    /// WRITER for the field-0 data-pointer provenance map
    /// (`known_pointer_to_alloc`). Records `(container_local, 0) -> obj_id`
    /// when `container_local` provably holds a pointer wrapper whose data field
    /// points into the fresh heap allocation `obj_id`, under a single-assignment
    /// gate that makes the later field read sound.
    ///
    /// Gate (each condition load-bearing; a wrong record is a false-Safe
    /// factory that could mask a UAF/double-free at the drop dealloc):
    /// - `obj_id` names a GENUINE heap allocation with a concrete recorded size
    ///   (never a stack slot / symbolic alloc);
    /// - the value's source local is SINGLE-ASSIGNMENT (`single_assign_locals`),
    ///   so `obj_id` is path-independent (no branch-merged provenance);
    /// - the container is written EXACTLY ONCE directly
    ///   (`raw_single_assign_locals`: no reassignment / branch-merge of the
    ///   container itself), and
    /// - the container is NEVER stored-through
    ///   (`deref_store_target_locals`): its data field cannot have been
    ///   overwritten via a pointer after construction.
    /// On any failure the map is left untouched (fail-closed): under-recording
    /// only forgoes the parity gain, whereas over-recording is unsound.
    fn maybe_record_field0_provenance(&mut self, container_local: usize, obj_id: u32, src: usize) {
        if self.heap_state.heap_alloc_size(obj_id).is_none() {
            return; // not a concrete heap allocation
        }
        if !self.encode.single_assign_locals.contains(&src) {
            return; // path-dependent provenance
        }
        if !self.encode.raw_single_assign_locals.contains(&container_local)
            || self.encode.deref_store_target_locals.contains(&container_local)
        {
            return; // container reassigned / branch-merged / stored-through
        }
        self.known_pointer_to_alloc.insert((container_local, 0), obj_id);
    }

    /// READER for the field-0 data-pointer provenance map. Given the rvalue of
    /// an assignment `_dst = <rhs>`, returns the heap allocation obj_id that the
    /// read data-pointer field points into, or `None` to fall back to the bare
    /// alloc-id propagation.
    ///
    /// Handles the drop-glue shape `_dst = Copy((*_ref).0)` (proj
    /// `[Deref, Field(0)]`): the reference `_ref` names the container's stack
    /// slot (obj_C); resolving obj_C back to the container local and consulting
    /// the writer-populated map yields the heap DATA allocation (obj_H). The
    /// deref source `_ref` must itself be single-assignment so it unambiguously
    /// names one container.
    fn try_field0_provenance_forward(&self, rhs: &Rvalue) -> Option<u32> {
        use rustc_public::mir::CastKind;
        let p = match rhs {
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) | Rvalue::CopyForDeref(p) => p,
            // Value-preserving pointer casts keep provenance identity.
            Rvalue::Cast(kind, Operand::Copy(p) | Operand::Move(p), _)
                if matches!(
                    kind,
                    CastKind::PtrToPtr
                        | CastKind::Transmute
                        | CastKind::PointerCoercion(_)
                        | CastKind::PointerExposeAddress
                        | CastKind::PointerWithExposedProvenance
                        | CastKind::Subtype
                ) =>
            {
                p
            }
            _ => return None,
        };
        // Only the `(*ref).field` read shape: the reference names the
        // container's stack slot; map obj_C back to the container local.
        let [ProjectionElem::Deref, ProjectionElem::Field(field_idx, _)] = p.projection.as_slice()
        else {
            return None;
        };
        if !self.encode.single_assign_locals.contains(&p.local) {
            return None; // deref source must name exactly one container
        }
        let obj_c = self.known_alloc_ids.get(&p.local).copied()?;
        let container_local = self.heap_state.local_idx_for_obj_id(obj_c)?;
        self.known_pointer_to_alloc.get(&(container_local, *field_idx)).copied()
    }

    pub(in crate::codegen_ay::chc) fn seed_promoted_const_store_chains_for_bb0(
        &mut self,
        bb_idx: usize,
    ) {
        // The entry rule constrains select(mem_in, addr) = value, but PDR does
        // not reliably carry those SELECT facts across block relations. Replaying
        // the same writes into bb0 store chains preserves them for Ptr+ tracks.
        if bb_idx != 0
            || self.track_level < ChcTrackLevel::Ptr
            || self.ref_resolution.const_ref_memory_inits.is_empty()
        {
            return;
        }

        let inits = std::mem::take(&mut self.ref_resolution.const_ref_memory_inits);
        for (type_key, _elem_sort, value, promoted_obj_id, byte_offset) in inits {
            let Some((arr_name, declared_elem_sort)) =
                self.heap_state.type_arrays.get(&type_key).cloned()
            else {
                warn!(
                    type_key = %type_key,
                    "bb0 promoted-const replay skipped: array not predeclared"
                );
                continue;
            };

            let arr_sort = ay_bindings::Sort::array(
                crate::codegen_ay::types::ptr_sort(),
                declared_elem_sort.clone(),
            );
            let arr_out_name = crate::codegen_ay::names::out_name(&arr_name);
            let promoted_addr = self.heap_state.promoted_const_address_for(promoted_obj_id);
            let addr = if byte_offset == 0 {
                promoted_addr
            } else {
                promoted_addr
                    .bvadd(Expr::bitvec_const(byte_offset, crate::codegen_ay::types::POINTER_WIDTH))
            };
            let arr_base = Expr::var(&*arr_name, arr_sort);
            let value = Self::coerce_store_value(&arr_base.sort(), value, false, &self.diagnostics);
            let store_expr = arr_base.store(addr, value);
            self.heap_state.accumulate_store(&type_key, arr_out_name, store_expr);
            self.heap_state.mark_array_modified(&type_key);
            debug!(
                type_key = %type_key,
                promoted_obj_id,
                byte_offset,
                "bb0: seeded promoted constant into store chain"
            );
        }
    }
}
