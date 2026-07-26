// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Vec lifecycle/query operation helpers: VecClear, VecClone, VecLen, VecExtendFromSlice.
//!
//! Range extension (VecExtendRange) extracted to `codegen_call_vec_ops_extend_range.rs`
//! per design: designs/2026-03-17-vec-ops-len-misnamed-module-decomposition.md
//!
//! Originally extracted from `codegen_call_vec_ops.rs` per design:
//! designs/2026-02-24-codegen-call-vec-ops-rs-decomposition.md
//!
//! Part of #2304 cleanup decomposition. Part of #3928 decomposition.

use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use ay_bindings::Expr;
use rustc_public::mir::{Operand, ProjectionElem};
use std::collections::HashSet;
use tracing::debug;

use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};

use super::ChcCtx;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_call_vec::ChcVecFields;
use super::codegen_call_vec_ops::ProjectedVecState;
use super::codegen_ctx::globals::declare_pending_var;
use super::codegen_ctx::types::CollectionProjectionKind;

/// Maximum number of source bytes unrolled into `store` constraints by
/// `extend_from_slice`/`extend` when the source is a concrete byte slice.
/// Beyond this, the data array is left unconstrained (sound). Part of Fix 4.
const MAX_APPEND_MOVE_ELEMS: usize = 16;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// VecClear: len = 0.
    pub(in crate::codegen_ay::chc) fn vec_op_clear(
        &mut self,
        collection_local: Option<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        if let Some(coll_local) = collection_local
            && let Some(len_var_name) = self.collections.len_state.get_len_var(coll_local).cloned()
        {
            self.collection_len_set(&len_var_name, Expr::bitvec_const(0u64, POINTER_WIDTH), acc);
        }
    }

    /// VecSetLen: len = new_len. Preserves ptr, cap, and data.
    ///
    /// `unsafe fn set_len(&mut self, new_len: usize)` — the caller is
    /// responsible for ensuring `new_len <= capacity()` and that elements
    /// in `[0..new_len)` are initialized. The CHC model updates only the
    /// tracked length; data contents remain unchanged.
    ///
    /// Part of #3895: required for `copy_nonoverlapping_append` harness.
    pub(in crate::codegen_ay::chc) fn vec_op_set_len(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        collection_local: Option<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        // args[0] = &mut self, args[1] = new_len: usize
        let new_len =
            args.get(1).and_then(|a| self.translate_operand_with_modified(a, modified_locals));

        let Some(new_len) = new_len else {
            debug!(
                fn_name = %self.fn_name,
                "VecSetLen: could not translate new_len argument"
            );
            self.record_sound_fallback_reason("vec_set_len_no_new_len");
            return;
        };

        // Sidecar len tracking
        if let Some(coll_local) = collection_local
            && let Some(len_var_name) = self.collections.len_state.get_len_var(coll_local).cloned()
        {
            self.collection_len_set(&len_var_name, new_len.clone(), acc);
        }

        // Projected path: preserve ptr, cap, data; replace only len.
        if let Some(coll_local) = collection_local
            && self.collections.projection_locals.get(&coll_local).copied()
                == Some(CollectionProjectionKind::Vec)
        {
            if let Some((ptr, _old_len, cap, data)) =
                self.extract_projected_vec_fields(coll_local, modified_locals)
            {
                Self::emit_cap_ge_len(cap.clone(), new_len.clone(), acc.constraints);
                if !self.constrain_projected_vec_fields_for_call(
                    coll_local,
                    ProjectedVecState { ptr, len: new_len, cap, data },
                    acc.constraints,
                    acc.dests,
                ) {
                    self.record_sound_fallback_reason("vec_field_constraint_not_emitted");
                }
                return;
            }
        }

        // Datatype path: reconstruct Vec with new len.
        if let Some(coll_local) = collection_local {
            let vec_idx = self
                .ref_resolution
                .ref_arg_pointee_idx
                .get(&coll_local)
                .copied()
                .or_else(|| self.state_var_mgr.local_to_state_idx.get(&coll_local).copied());
            if let Some(idx) = vec_idx {
                let src_info = if modified_locals.contains(&coll_local) {
                    self.state_var_mgr.output_state_vars.get(idx)
                } else {
                    self.state_var_mgr.state_vars.get(idx)
                }
                .cloned();
                if let Some((name, sort)) = src_info
                    && sort.datatype_name().is_some()
                {
                    let vec_in = Expr::var(&*name, sort);
                    if let Some(fields) = ChcVecFields::extract(vec_in) {
                        let ChcVecFields { vec_sort, ptr, len: _, cap, data } = fields;
                        Self::emit_cap_ge_len(cap.clone(), new_len.clone(), acc.constraints);
                        if let Some((out_name, out_sort)) =
                            self.state_var_mgr.output_state_vars.get(idx).cloned()
                        {
                            let dt_name = vec_sort.datatype_name().expect(
                                "invariant: ChcVecFields::extract ensures datatype Vec sort",
                            );
                            acc.constraints.push(Self::build_vec_datatype_eq(
                                dt_name,
                                vec![ptr, new_len, cap, data],
                                &out_name,
                                &out_sort,
                            ));
                            acc.dests.push(idx);
                        }
                    }
                }
            }
        }
    }

    /// VecClone: propagate data array + len + cap from source to dest.
    ///
    /// Part of #3348: previously only copied sidecar len, leaving dest data
    /// unconstrained. Now propagates the full Vec structure (ptr fresh, data
    /// and len/cap copied) so that `clone().len()` and element equality work.
    pub(in crate::codegen_ay::chc) fn vec_op_clone(
        &mut self,
        collection_local: Option<usize>,
        dest_local: usize,
        modified_locals: &HashSet<usize>,
        dest_vec_idx: usize,
        acc: &mut CallAccumulator<'_>,
    ) {
        // Sidecar len + cap tracking (existing len path + new cap path).
        if let Some(coll_local) = collection_local
            && let Some(src_len_var) = self.collections.len_state.get_len_var(coll_local).cloned()
        {
            let src_len = self.collection_current_len(&src_len_var);
            if let Some(dst_len_var) = self.collections.len_state.get_len_var(dest_local).cloned() {
                self.collection_len_set(&dst_len_var, src_len, acc);
            }
            if let Some(src_cap_var) = self.collections.len_state.get_cap_var(coll_local).cloned() {
                let src_cap = self.collection_current_cap(&src_cap_var);
                if let Some(dst_cap_var) =
                    self.collections.len_state.get_cap_var(dest_local).cloned()
                {
                    self.collection_cap_set(&dst_cap_var, src_cap, acc);
                }
            }
        }

        // Projected path: copy all 4 fields (fresh ptr, same len/cap/data).
        if let Some(coll_local) = collection_local
            && self.collections.projection_locals.get(&coll_local).copied()
                == Some(CollectionProjectionKind::Vec)
            && self.collections.projection_locals.get(&dest_local).copied()
                == Some(CollectionProjectionKind::Vec)
        {
            if let Some((_src_ptr, src_len, src_cap, src_data)) =
                self.extract_projected_vec_fields(coll_local, modified_locals)
            {
                let clone_ptr =
                    declare_pending_var(format!("vec_clone_ptr_{dest_local}"), ptr_sort());
                Self::emit_cap_ge_len(src_cap.clone(), src_len.clone(), acc.constraints);
                if !self.constrain_projected_vec_fields_for_call(
                    dest_local,
                    ProjectedVecState {
                        ptr: clone_ptr,
                        len: src_len,
                        cap: src_cap,
                        data: src_data,
                    },
                    acc.constraints,
                    acc.dests,
                ) {
                    self.record_sound_fallback_reason("vec_field_constraint_not_emitted");
                }
                return;
            }
        }

        // Datatype path: extract source fields, build dest Vec with same data.
        if let Some(coll_local) = collection_local {
            let src_vec_idx = self
                .ref_resolution
                .ref_arg_pointee_idx
                .get(&coll_local)
                .copied()
                .or_else(|| self.state_var_mgr.local_to_state_idx.get(&coll_local).copied());
            if let Some(src_idx) = src_vec_idx {
                let src_info = if modified_locals.contains(&coll_local) {
                    self.state_var_mgr.output_state_vars.get(src_idx)
                } else {
                    self.state_var_mgr.state_vars.get(src_idx)
                }
                .cloned();
                if let Some((name, sort)) = src_info
                    && sort.datatype_name().is_some()
                {
                    let vec_in = Expr::var(&*name, sort);
                    if let Some(fields) = ChcVecFields::extract(vec_in) {
                        let ChcVecFields { vec_sort, ptr: _, len, cap, data } = fields;
                        if let Some((out_name, out_sort)) =
                            self.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
                        {
                            let dt_name = vec_sort.datatype_name().expect(
                                "invariant: ChcVecFields::extract ensures datatype Vec sort",
                            );
                            let clone_ptr = declare_pending_var(
                                format!("vec_clone_ptr_{dest_local}"),
                                ptr_sort(),
                            );
                            Self::emit_cap_ge_len(cap.clone(), len.clone(), acc.constraints);
                            acc.constraints.push(Self::build_vec_datatype_eq(
                                dt_name,
                                vec![clone_ptr, len, cap, data],
                                &out_name,
                                &out_sort,
                            ));
                            // Task #69 (dests index-space fix): `dest_vec_idx`
                            // is a STATE-VAR index, but `acc.dests` entries are
                            // read as MIR locals by `build_output_args` (see
                            // the contract in codegen_call_coerce.rs). Pushing
                            // it there left the constrained `__out` var out of
                            // the rule head, so the clone destination's Vec
                            // state var stayed stale. Route through
                            // `mark_state_var_modified` — the documented
                            // channel for raw state-vector slots.
                            self.mark_state_var_modified(dest_vec_idx);
                            return;
                        }
                    }
                }
            }
        }

        // Fallback: dest unconstrained (sound over-approximation).
        //
        // Task #69 SoundHavoc AUDIT (basis for the allowlist entry in
        // codegen_ctx/mod.rs::fallback_soundness):
        // - The dest state var (and all its flattened fields) reaches the rule
        //   head as a fresh `__out` var via `extra_dests` with NO equality
        //   constraining it in this rule — a universally quantified havoc that
        //   only ADDS behaviors (monotone; can never remove an error edge).
        // - The only accompanying constraints on this path are the sidecar
        //   pins emitted above: dst_len := src_len (exact real Vec::clone
        //   semantics) and dst_cap := src_cap (the uniform VecClone stub
        //   semantics, identical to the fully-modeled projected/datatype
        //   paths; satisfies cap >= len). Neither ties the havocked dest var
        //   to stale input.
        // - Both partially-attempted paths above bail out BEFORE pushing any
        //   constraint (projected: emit_cap_ge_len + constrain happen only on
        //   extract success and return; datatype: constraints pushed only in
        //   the innermost success branch which returns) — no partial residue
        //   accompanies the havoc.
        // - dest's adapter_source_data is invalidated at dispatch
        //   (vec_stub_overwrites_dest_adapter_source_data includes VecClone),
        //   so no stale concrete-element forwarding bypasses the havoc.
        self.record_sound_fallback_reason("vec_clone_dest_unconstrained");
        acc.dests.push(dest_local);
    }

    /// VecLen: dest = tracked length.
    ///
    /// Three resolution paths:
    /// 1. Sidecar len_var — collection_local has tracked length (most common)
    /// 2. Struct-embedded C1/C2 — collection_local is a struct, field_projections
    ///    describe the path to the Vec field (Part of #3348)
    /// 3. Fallback — dest unconstrained (sound over-approximation)
    pub(in crate::codegen_ay::chc) fn vec_op_len(
        &mut self,
        collection_local: Option<usize>,
        dest_local: usize,
        field_projections: &[ProjectionElem],
        modified_locals: &HashSet<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        // Path 1: Sidecar len_var.
        // Part of #3084: Skip sidecar when field_projections is non-empty.
        // The sidecar belongs to the struct local (or a sibling Vec), not the
        // specific Vec field being queried. The struct-embedded path (Path 2)
        // navigates the Datatype to the correct Vec's fld_len.
        if field_projections.is_empty()
            && let Some(coll_local) = collection_local
            && let Some(len_var_name) = self.collections.len_state.get_len_var(coll_local).cloned()
        {
            let len_expr = self.collection_current_len(&len_var_name);
            if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                if let Some(eq) = self.make_coerced_eq_constraint(
                    &dest_var,
                    len_expr,
                    dest_var.sort(),
                    dest_local,
                    "codegen_call_vec_core::VecLen",
                ) {
                    acc.constraints.push(eq);
                }
                acc.dests.push(dest_local);
            }
            return;
        }

        // Path 1.5: Ref-chase through field projections (Part of #3924).
        // When collection_local is a struct (e.g., closure environment) and
        // field_projections point to a reference field (e.g., &Vec captured by
        // a closure), the struct-embedded path fails because the field is a
        // pointer, not a Vec datatype. Instead, find a tracked Vec local whose
        // ref_target resolves through (collection_local, field_projections).
        if !field_projections.is_empty()
            && let Some(coll_local) = collection_local
        {
            let mut len_via_ref = None;
            let mut matched_vec_local = None;
            for (&tracked_local, len_var) in &self.collections.len_state.len_var_names {
                let Some(rt) = self.ref_resolution.ref_targets.get(&tracked_local) else {
                    continue;
                };
                if rt.local != coll_local || rt.projections.len() != field_projections.len() {
                    continue;
                }

                let projs_match =
                    rt.projections.iter().zip(field_projections.iter()).all(|(a, b)| {
                        match (a, b) {
                            (ProjectionElem::Field(idx_a, _), ProjectionElem::Field(idx_b, _)) => {
                                idx_a == idx_b
                            }
                            _ => false,
                        }
                    });
                if !projs_match {
                    continue;
                }

                // Bucket A (#4046): only preserve the #3924 ref-chase
                // short-circuit when the traced local is actually Vec-shaped.
                // Part of #4057: also accept when the field projection type is
                // &Vec<T> (closure-captured Vec reference). The tracked_local is
                // a BV64 pointer, not a Vec DT, but it correctly tracks the
                // referenced Vec's length.
                if !self.local_is_vec_shaped(tracked_local, modified_locals) {
                    let field_ty_is_vec_ref = rt.projections.last().map_or(false, |proj| {
                        if let ProjectionElem::Field(_, ty) = proj {
                            Self::is_vec_or_ref_to_vec(*ty)
                        } else {
                            false
                        }
                    });
                    if !field_ty_is_vec_ref {
                        debug!(
                            fn_name = %self.fn_name,
                            coll_local,
                            tracked_local,
                            "VecLen: ref-chase matched non-Vec local; falling through to struct-embedded path (#4046)"
                        );
                        continue;
                    }
                }

                matched_vec_local = Some(tracked_local);
                len_via_ref = Some(len_var.clone());
                break;
            }
            if let Some((len_var_name, matched_vec_local)) = len_via_ref.zip(matched_vec_local) {
                // Part of #4057: When the matched tracked local's ref_target
                // field type is &Vec<T> (closure-captured reference), the
                // tracked len_var (e.g., vec_main_len_40) may be uninitialized
                // because no transition rule sets it. Resolve to the source
                // Vec's len_var instead by following the ref chain.
                let effective_len_var =
                    self.resolve_source_vec_len_var(matched_vec_local, &len_var_name);
                debug!(
                    fn_name = %self.fn_name,
                    coll_local,
                    dest_local,
                    ?matched_vec_local,
                    %len_var_name,
                    %effective_len_var,
                    "VecLen: ref-chase through Vec-shaped field projections (#3924, #4046, #4057)"
                );
                let len_expr = self.collection_current_len(&effective_len_var);
                if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                    if let Some(eq) = self.make_coerced_eq_constraint(
                        &dest_var,
                        len_expr,
                        dest_var.sort(),
                        dest_local,
                        "codegen_call_vec_core::VecLen_ref_chase",
                    ) {
                        acc.constraints.push(eq);
                    }
                    acc.dests.push(dest_local);
                }
                return;
            }
        }

        // Path 2: Struct-embedded Vec len (Part of #3348).
        // When collection_local is a struct (no sidecar len_var) and
        // field_projections describe the path from struct to Vec, extract
        // the Vec's fld_len value from the struct's state var.
        if !field_projections.is_empty()
            && let Some(coll_local) = collection_local
        {
            debug!(
                fn_name = %self.fn_name,
                coll_local,
                dest_local,
                proj_count = field_projections.len(),
                "VecLen: entering struct-embedded path (#3348)"
            );
            self.vec_len_struct_embedded(
                coll_local,
                dest_local,
                field_projections,
                modified_locals,
                acc,
            );
            return;
        }

        // Path 3: Fallback — dest unconstrained.
        debug!(
            fn_name = %self.fn_name,
            ?collection_local,
            proj_count = field_projections.len(),
            "VecLen: fallback — no sidecar, no field_projections (#3348)"
        );
        self.record_sound_fallback_reason("vec_len_no_sidecar");
        acc.dests.push(dest_local);
    }

    /// VecExtendFromSlice: new_len = old_len + source_slice_len.
    ///
    /// `extend_from_slice(&mut self, other: &[T])` appends all elements of the
    /// source slice to the Vec. The CHC model updates the tracked length to
    /// `old_len + source_len`. Data contents are left unconstrained (sound
    /// over-approximation — a PROOF under this model is valid for all concrete
    /// element values).
    ///
    /// Source slice length resolution:
    /// 1. Trace args[1] through ref_targets to find the source collection local
    /// 2. Check slice_to_vec_local for Vec-backed slices
    /// 3. Fallback: source length is unconstrained (still updates self.len)
    ///
    /// Part of #3348: enables bv_concat_width_sum PROOF by modeling the length
    /// change from `bits.extend_from_slice(&self.0)` in Bits::concat.
    pub(in crate::codegen_ay::chc) fn vec_op_extend_from_slice(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        collection_local: Option<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        let Some(coll_local) = collection_local else {
            return;
        };
        let Some(len_var_name) = self.collections.len_state.get_len_var(coll_local).cloned() else {
            return;
        };
        let old_len = self.collection_current_len(&len_var_name);

        // Fix 4: resolve the source as a concrete constant byte slice (only for
        // byte-element destination Vecs). Gives the exact moved element values.
        let concrete_bytes =
            self.resolve_extend_from_slice_byte_values(args, coll_local, modified_locals);

        // Resolve source slice length from args[1]. Fall back to the concrete
        // byte count when the slice is a raw const with no tracked length (e.g.
        // `my_vec.extend(b"Hi")`), so length AND data both track.
        let source_len = self.resolve_slice_arg_length(args, 1, modified_locals).or_else(|| {
            concrete_bytes.as_ref().map(|vals| Expr::bitvec_const(vals.len() as u64, POINTER_WIDTH))
        });

        let new_len = if let Some(src_len) = source_len {
            tracing::debug!(coll_local, "VecExtendFromSlice: old_len + source_len");
            let sum = old_len.clone().bvadd(src_len);
            // Part of #3409: guard against unsigned overflow on old_len+src_len.
            acc.constraints.push(sum.clone().bvuge(old_len.clone()));
            sum
        } else {
            // Source length unknown — leave dest len unconstrained.
            // This is a sound over-approximation: the solver will consider
            // all possible lengths, which includes the correct one.
            tracing::debug!(coll_local, "VecExtendFromSlice: source length unresolved");
            return;
        };

        self.collection_len_set(&len_var_name, new_len.clone(), acc);

        // Capacity growth: cap = max(cap, new_len).
        if let Some(cap_var_name) = self.collections.len_state.get_cap_var(coll_local).cloned() {
            let old_cap = self.collection_current_cap(&cap_var_name);
            let grow_needed = old_cap.clone().bvult(new_len.clone());
            let new_cap = Expr::ite(grow_needed, new_len.clone(), old_cap);
            self.collection_cap_set(&cap_var_name, new_cap.clone(), acc);
            Self::emit_cap_ge_len(new_cap, new_len, acc.constraints);
        }

        // Fix 4: store the copied element VALUES into the data array so reads of
        // the appended slots return the real bytes instead of the construction
        // fill. Adds only genuine facts; anything unresolved above is skipped
        // (unconstrained over-approximation, sound).
        if let Some(values) = concrete_bytes
            && (1..=MAX_APPEND_MOVE_ELEMS).contains(&values.len())
        {
            self.vec_store_appended_elements(coll_local, &old_len, &values, modified_locals, acc);
        }
    }

    /// Resolve a constant `&[u8]` source slice (for `extend_from_slice`/`extend`)
    /// into its concrete byte element values, as `Fix 4` moved-element data.
    /// Gated on:
    /// - the destination `data` array having an 8-bit element sort (else the
    ///   per-byte interpretation of the source would be wrong), and
    /// - the source resolving to a concrete byte slice of a small count.
    ///
    /// Returns `None` (leaving the data array unconstrained — sound) in every
    /// other case. This is the `extend_from_slice` analogue of `vec_op_append`'s
    /// moved-element tracking; source values come from the const-slice literal.
    fn resolve_extend_from_slice_byte_values(
        &mut self,
        args: &[Operand],
        coll_local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Vec<Expr>> {
        let dst_data = self.vec_current_data_expr(coll_local, modified_locals)?;
        let is_byte_elem =
            dst_data.sort().array_sort().and_then(|arr| arr.element_sort.bitvec_width()) == Some(8);
        if !is_byte_elem {
            return None;
        }
        if args.len() < 2 {
            return None;
        }
        // Resolve the source bytes. `extend`/`extend_from_slice` passes the
        // source slice either as a tracked Copy/Move operand (handled by
        // `try_resolve_concrete_byte_slice_arg`) or — for a byte-string literal
        // like `b"Hi"` — directly as a `Constant` fat-pointer `&[u8]` operand,
        // which the tracked path does not handle. Try both.
        let bytes: Vec<u8> = if let Some(slice) =
            self.try_resolve_concrete_byte_slice_arg(&args[1..], modified_locals)
        {
            slice.bytes
        } else {
            Self::const_byte_slice_operand_bytes(&args[1])?
        };
        let count = bytes.len();
        if count == 0 || count > MAX_APPEND_MOVE_ELEMS {
            return None;
        }
        Some(bytes.iter().map(|&b| Expr::bitvec_const(u64::from(b), 8)).collect())
    }

    /// Read the concrete data bytes of a `Constant` fat-pointer `&[u8]` operand
    /// (e.g. a `b"..."` byte-string literal). The constant's own allocation
    /// holds the fat pointer `(data_ptr, len)`; the actual bytes live in the
    /// allocation named by its provenance. Returns `None` for any operand that
    /// is not such a constant (sound — the caller then stores nothing).
    fn const_byte_slice_operand_bytes(arg: &Operand) -> Option<Vec<u8>> {
        use rustc_public::mir::alloc::GlobalAlloc;
        use rustc_public::ty::{ConstantKind, TyConstKind};

        let Operand::Constant(const_op) = arg else {
            return None;
        };
        let alloc = match const_op.const_.kind() {
            ConstantKind::Allocated(alloc) => alloc,
            ConstantKind::Ty(ty_const) => match ty_const.kind() {
                TyConstKind::Value(_ty, alloc) => alloc,
                _ => return None,
            },
            _ => return None,
        };
        // Follow provenance to the data allocation.
        let alloc_id = alloc.provenance.ptrs.first()?.1.0;
        let GlobalAlloc::Memory(inner) = GlobalAlloc::from(alloc_id) else {
            return None;
        };
        // Length from the fat-pointer metadata (little-endian usize at offset
        // `ptr_bytes`), falling back to the inner allocation size.
        let ptr_bytes = (POINTER_WIDTH / 8) as usize;
        let len = if alloc.bytes.len() >= 2 * ptr_bytes {
            let mut v: u64 = 0;
            for i in 0..ptr_bytes.min(8) {
                v |= u64::from(alloc.bytes[ptr_bytes + i].unwrap_or(0)) << (8 * i);
            }
            usize::try_from(v).ok()?
        } else {
            inner.bytes.len()
        };
        if len == 0 || len > inner.bytes.len() {
            return None;
        }
        Some(inner.bytes.iter().take(len).map(|opt| opt.unwrap_or(0)).collect())
    }
}
