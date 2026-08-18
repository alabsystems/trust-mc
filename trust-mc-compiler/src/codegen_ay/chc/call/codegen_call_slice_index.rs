// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC scalar slice-index codegen extracted from codegen_call_slice.rs.
//! Covers SliceIndexIndex/IndexIndex element lowering, ZST handling, and
//! pointer-backed fallback paths.

use ay_bindings::{Expr, Sort};
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use crate::args::ChcTrackLevel;
use crate::codegen_ay::names::{struct_sort, vec_layout};
use crate::codegen_ay::provenance::{
    Loc, Val, is_value_widened_into_address, mir_ty_denotes_address,
};
use crate::codegen_ay::ptr_repr::PtrSlot;
use crate::codegen_ay::types::POINTER_WIDTH;
use trust_mc_core::chc::{Rule, RuleBody};
use trust_mc_core::violation::PropertyKind;

use super::chc_call_context::ChcCallContext;
use super::codegen_call_coerce::{
    CallCoerce, emit_sound_fallback_goto, emit_sound_fallback_goto_prebuilt,
};
use super::codegen_call_misc::CallMisc;
use super::codegen_rules::CodegenRules;
use super::{ChcCtx, RelationApp};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle `SliceIndexIndex` / `IndexIndex` — parity with statement backend.
    ///
    /// Replaces the prior unconstrained over-approximation with:
    /// 1. ZST element detection -> Unit constructor
    /// 2. Operand resolution -> array select
    /// 3. Bounds guard emission
    /// 4. Constrained symbolic fallback only for unresolvable sources
    ///
    /// Note: `build_output_args` is called AFTER element expression computation
    /// (not inherited from the caller) because `slice_index_via_memory_model` may
    /// create late state variables via `push_late_state_var_pair`. Capturing output
    /// args before that would produce a stale vector with wrong arity.
    /// Part of #2970.
    pub(super) fn codegen_call_slice_index_impl(
        &mut self,
        cx: &ChcCallContext<'_>,
        dest_local: usize,
    ) {
        let args = cx.args;
        let target = cx.target;
        let from_app = cx.from_app;
        let stmt_constraints = cx.stmt_constraints;
        let modified_locals = cx.modified_locals;
        // Need at least 2 args: (slice_or_self, index)
        if args.len() < 2 {
            debug!(fn_name = %self.fn_name, "CHC slice index: insufficient args; fallback");
            emit_sound_fallback_goto(
                self,
                from_app,
                target,
                modified_locals,
                &[dest_local],
                stmt_constraints,
            );
            return;
        }

        // Identify slice and index operands.
        let (slice_arg, index_arg) = self.split_chc_slice_index_args(args);

        // Check for ZST element type — if ZST, the result is a Unit constructor
        // regardless of index value (parity with statement/slice.rs:180-183).
        if let Some(elem_ty) = self.chc_slice_elem_ty(slice_arg)
            && Self::is_zst_type_for_slice(elem_ty)
        {
            debug!(
                fn_name = %self.fn_name,
                "CHC slice index: ZST element; emitting Unit constructor"
            );
            let output_args = self.build_output_args(modified_locals, &[dest_local]);
            return self.emit_slice_index_zst(
                dest_local,
                target,
                from_app,
                stmt_constraints,
                &output_args,
            );
        }

        // Part of #3327, #3551: Detect Range/RangeInclusive slice indexing.
        // Range<usize> / RangeInclusive<usize> args produce a subslice, not a scalar element.
        if let Some(idx_op) = index_arg
            && Self::is_range_type_operand(idx_op, self.body.locals())
        {
            let inclusive = Self::is_range_inclusive_operand(idx_op, self.body.locals());
            debug!(fn_name = %self.fn_name, inclusive, "CHC slice index: Range index detected; subslice path");
            return self
                .codegen_call_slice_range_index(cx, dest_local, slice_arg, idx_op, inclusive);
        }

        // Part of #3495: RangeFull indexing (`&slice[..]`) is identity.
        if let Some(idx_op) = index_arg
            && Self::is_range_full_operand(idx_op, self.body.locals())
        {
            return self.codegen_call_slice_range_full_identity(cx, dest_local, slice_arg);
        }

        if let Some(idx_op) = index_arg
            && Self::is_range_to_operand(idx_op, self.body.locals())
        {
            let inclusive = Self::is_range_to_inclusive_operand(idx_op, self.body.locals());
            return self
                .codegen_call_slice_range_to_index(cx, dest_local, slice_arg, idx_op, inclusive);
        }

        // Part of #3495: RangeFrom indexing (`&slice[start..]`) is a subslice from start to end.
        if let Some(idx_op) = index_arg
            && Self::is_range_from_operand(idx_op, self.body.locals())
        {
            return self.codegen_call_slice_range_from_index(cx, dest_local, slice_arg, idx_op);
        }

        // Try to resolve the index operand to a BV expression.
        let idx_expr = index_arg
            .and_then(|arg| self.translate_operand_with_modified(arg, modified_locals))
            .and_then(|expr| self.coerce_to_pointer_width(expr));

        // Prefer concrete byte backing before generic referent resolution.
        let slice_backing = self.resolve_slice_backing(slice_arg, modified_locals);
        let slice_backing_len = slice_backing.as_ref().map(|backing| backing.len.as_expr().clone());
        let slice_backing_offset =
            slice_backing.as_ref().map(|backing| backing.offset.as_expr().clone());

        // Try to resolve the slice/array value.
        // Part of #3606: Try struct-embedded Vec data array FIRST. When `s.data`
        // is a Vec field in a flattened struct, `resolve_ref_or_const_referent`
        // returns Some(BV64_pointer) via Tier 5 (translate_operand), which falls
        // through to `slice_index_via_memory_model` and returns None. By trying
        // the direct fld_data Array lookup first, we get an Array-sort expression
        // that hits the efficient array-select path instead.
        //
        // Provenance of the four lanes: the first three all hand back element
        // STORAGE (`ResolvedSliceBacking::data` is a `Val`, and the two
        // `*_vec_data_array` helpers select an `fld_data` array). Only
        // `resolve_ref_or_const_referent` can stop at a pointer instead of
        // dereferencing it — so that is the ONE lane whose result may be an
        // address, and `storage_lane` below carries that fact forward instead
        // of leaving the pointer arm of the `match` to re-derive it from a
        // width comparison.
        let storage_value = slice_backing
            .as_ref()
            .map(|backing| backing.data.as_expr().clone())
            .or_else(|| self.try_resolve_struct_vec_data_array(slice_arg))
            .or_else(|| self.try_resolve_projected_vec_data_array(slice_arg));
        let mut storage_lane = storage_value.is_some();
        let slice_value = storage_value
            .or_else(|| self.resolve_ref_or_const_referent(slice_arg, modified_locals));

        // Part of #4003: follow closure-captured Vec pointers back to data arrays.
        //
        // Four producers feed `slice_value` above and only the last of them can
        // stop at a pointer, so what this asks is "did resolution land in a
        // pointer-shaped SLOT rather than on array data?" — a question about the
        // declared sort, which is what `PtrSlot` names. The predicate is the one
        // it replaces (`PtrSlot::Thin` is exactly `width == POINTER_WIDTH`); it
        // is written this way so it is not mistaken for a provenance test, which
        // a width comparison can never be.
        let slice_value = if slice_value
            .as_ref()
            .is_some_and(|sv| PtrSlot::of_sort(sv.sort()) == Some(PtrSlot::Thin))
        {
            match self.try_resolve_closure_captured_vec_data(slice_arg, modified_locals) {
                // This lane hands back the capture's `fld_data` array: storage.
                Some(data) => {
                    storage_lane = true;
                    Some(data)
                }
                None => slice_value,
            }
        } else {
            slice_value
        };

        // The pointer lane's address, established once, here, at the producer.
        // `None` means "nothing available says this term is an address", and
        // the `match` below then takes the constrained-symbolic fallback rather
        // than dereferencing whatever landed in the slot.
        let slice_ptr = if storage_lane {
            None
        } else {
            slice_value.clone().and_then(|sv| self.slice_referent_as_address(slice_arg, sv))
        };

        // Emit bounds guard if we can determine array length.
        let mut bounds_guard_emitted = false;
        if let (Some(idx), Some(sv)) = (&idx_expr, &slice_value)
            && let Some(len_expr) = slice_backing_len.clone().or_else(|| Self::chc_array_length(sv))
        {
            let len_coerced = match len_expr.sort().bitvec_width() {
                Some(w) if w == POINTER_WIDTH => len_expr,
                Some(w) if w < POINTER_WIDTH => len_expr.zero_extend(POINTER_WIDTH - w),
                Some(_) => len_expr.extract(POINTER_WIDTH - 1, 0),
                None => {
                    debug!(fn_name = %self.fn_name, "CHC slice index: non-BV length sort; skipping bounds guard");
                    Expr::bitvec_const(0, POINTER_WIDTH)
                }
            };
            // The width re-test that used to guard this block is deleted: every
            // arm of the `match` above yields a `POINTER_WIDTH` bitvector (two
            // coerce to it, one is already it, the `None` arm builds a constant
            // at it), so the guard was vacuously true and decided nothing. A
            // length is a VALUE, and re-measuring a value's width is exactly the
            // kind of test this refactor exists to remove.
            let oob = idx.clone().bvuge(len_coerced);
            debug!(fn_name = %self.fn_name, "CHC slice index: emitting bounds_check error rule");
            let error_app = RelationApp::new("error", Vec::new());
            let body =
                RuleBody::from_base_and_extra(Some(from_app.clone()), stmt_constraints, [oob]);
            self.vc.add_rule(Rule::new(body, error_app));
            bounds_guard_emitted = true;
        }

        // Part of #3495: Check for subslice offset from range-based indexing.
        // When the source slice was produced by `&source[start..end]`, the source
        // backing array is in const_ref_values and the start offset is in
        // subslice_offset. Apply the offset to the index: `source.select(idx + offset)`.
        //
        // The offset is registered under the Range call destination (e.g., _3).
        // But when MIR reborrows the subslice (`_4 = &(*_3)`), the scalar index
        // call sees _4 as slice_arg. Follow ref_targets one level to find the
        // original subslice local if the direct lookup misses.
        let slice_local_for_offset = match slice_arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        };
        let subslice_offset = slice_backing_offset.or_else(|| {
            slice_local_for_offset.and_then(|l| {
                self.ref_resolution.subslice_offset.get(&l).cloned().or_else(|| {
                    // Follow ref_targets: if _4 = &(*_3), look up _3's offset.
                    let referent = self.ref_resolution.ref_targets.get(&l)?;
                    if referent.projections.is_empty() {
                        self.ref_resolution.subslice_offset.get(&referent.local).cloned()
                    } else {
                        None
                    }
                })
            })
        });

        // Attempt to compute element expression via array select.
        let elem_expr = match (&idx_expr, &slice_value, &slice_ptr) {
            (Some(idx), Some(sv), _) if sv.sort().is_array() => {
                // Direct array select — parity with statement/slice.rs:185-186.
                // Part of #3495: Apply subslice offset if present.
                let effective_idx = if let Some(ref offset) = subslice_offset {
                    idx.clone().bvadd(offset.clone())
                } else {
                    idx.clone()
                };
                debug!(
                    fn_name = %self.fn_name,
                    has_offset = subslice_offset.is_some(),
                    "CHC slice index: array select"
                );
                Some(sv.clone().select(effective_idx))
            }
            (Some(idx), Some(sv), _) if sv.sort().datatype_name().is_some() => {
                // Datatype: check for fld_data (Vec/Slice backing array).
                // Parity with statement/slice.rs:187-192.
                let dt_name =
                    sv.sort().datatype_name().expect("invariant: match guard checked is_some");
                if let Some(data_sort) = Self::get_dt_field_sort(sv, "fld_data") {
                    let data = sv.clone().field_select(dt_name, "fld_data", data_sort);
                    let elem = data.select(idx.clone());
                    debug!(fn_name = %self.fn_name, "CHC slice index: fld_data array select");
                    Some(elem)
                } else {
                    // No fld_data — constrained symbolic fallback.
                    debug!(fn_name = %self.fn_name, "CHC slice index: datatype without fld_data; constrained symbolic");
                    None
                }
            }
            (Some(idx), Some(_), Some(ptr)) => {
                // Pointer-to-slice: dereference through memory model. Part of #2915.
                //
                // The width fallback that used to select this arm is retired.
                // It was the only arm not matched structurally, so every
                // pointer-width scalar that reached the slice slot — a
                // dematerialized `usize`, an opaque `ptr_sort()` ADT, a
                // zero-extended narrow datum — became a base address that this
                // path then offsets by `idx * sizeof(elem)` and LOADS from.
                // `slice_ptr` is `Some` only when a producer established the
                // address; see `slice_referent_as_address`.
                self.slice_index_via_memory_model(slice_arg, ptr, idx)
            }
            _ => {
                // non-enum: (Option, Option) tuple exhaustion
                debug!(fn_name = %self.fn_name, "CHC slice index: cannot resolve slice/index; constrained symbolic");
                None
            }
        };

        // Register element for deref-bypass via const_ref_values (#3024).
        // Same pattern as VecAsSlice (codegen_call_vec_ops_views.rs:146).
        if let Some(ref elem) = elem_expr {
            self.ref_resolution.const_ref_values.insert(dest_local, elem.clone());
        }

        // Flush pending_checks from load_from_memory (bypasses encode_block_statements). #3359.
        let pending_checks: Vec<_> = self.heap_state.pending_checks.drain(..).collect();
        for check in pending_checks {
            self.emit_error_rule_for_condition(from_app, check, stmt_constraints, target);
        }

        // Task #69: bounds-guard completeness against the CURRENT length.
        //
        // The primary guard above uses the backing length (subslice_len /
        // static [T; N] / cast-traced construction length / datatype fld_len).
        // For a Vec that was SHRUNK at runtime (truncate / resize-smaller,
        // which update the sidecar length), a static construction-time hint is
        // STALE: a shrink-then-index real OOB passes `idx < old_len` and
        // proves Safe. Additions, all fail-closed:
        //
        // 1. When the operand views the WHOLE collection (no registered
        //    subslice view, zero/absent offset) and a COHERENT current length
        //    resolves (sidecar seeded by collection stubs and never bypassed
        //    by a fn-inline &mut call), emit `idx < current_len` through the
        //    registered per-property error channel (BSEM-18) — never a bare
        //    aggregate error rule. Incoherent lengths (free/stale sidecar
        //    vars) must NOT be guarded: a guard on a free variable produces
        //    arbitrary counterexamples misclassified as Genuine.
        // 2. When the element read is Vec-backed but only an incoherent
        //    length was available, the primary static guard is stale-able —
        //    record the fail-closed `slice_index_unguarded` marker.
        // 3. When a concrete element read was computed but NO length guard at
        //    all could be emitted, record the same fail-closed marker.
        let has_subslice_len_view = slice_local_for_offset.is_some_and(|l| {
            self.ref_resolution.subslice_len.contains_key(&l)
                || self.ref_resolution.ref_targets.get(&l).is_some_and(|rt| {
                    rt.projections.is_empty()
                        && self.ref_resolution.subslice_len.contains_key(&rt.local)
                })
        });
        let whole_collection_view = !has_subslice_len_view
            && subslice_offset.as_ref().is_none_or(Self::is_zero_pointer_width_bitvec);
        // A registered subslice view has a FIXED length (safe Rust cannot
        // shrink the parent while the view is borrowed), so a primary guard
        // that used it is exact.
        let view_exactly_guarded = bounds_guard_emitted && has_subslice_len_view;
        let resolved_len = self.resolve_current_slice_view_len(args, slice_arg, modified_locals);
        let mut current_len_guarded = false;
        if let Some(idx) = &idx_expr
            && whole_collection_view
            && let Some((cur_len, true)) = resolved_len.clone()
            && let Some(cur_len) = self.coerce_to_pointer_width(cur_len)
        {
            debug!(fn_name = %self.fn_name, "CHC slice index: current-length bounds guard (#69)");
            self.emit_error_rule_for_condition_with_kind(
                from_app,
                idx.clone().bvult(cur_len),
                stmt_constraints,
                target,
                PropertyKind::OutOfBounds,
                Some("index out of bounds: index must be less than the current length".to_string()),
            );
            current_len_guarded = true;
        }
        if elem_expr.is_some() && !current_len_guarded && !view_exactly_guarded {
            match &resolved_len {
                Some((cur_len, true)) if !bounds_guard_emitted => {
                    // Coherent length but a non-whole view without any primary
                    // guard: guard the BACKING access (select index =
                    // idx + offset). This catches backing overruns but NOT
                    // subslice-view violations, so the marker still applies.
                    if let Some(idx) = &idx_expr
                        && let Some(cur_len) = self.coerce_to_pointer_width(cur_len.clone())
                    {
                        let eff_idx = if let Some(ref off) = subslice_offset {
                            idx.clone().bvadd(off.clone())
                        } else {
                            idx.clone()
                        };
                        self.emit_error_rule_for_condition_with_kind(
                            from_app,
                            eff_idx.bvult(cur_len),
                            stmt_constraints,
                            target,
                            PropertyKind::OutOfBounds,
                            Some(
                                "index out of bounds: backing access must be within length"
                                    .to_string(),
                            ),
                        );
                    }
                    warn!(fn_name = %self.fn_name, "CHC slice index: subslice view without exact guard (#69)");
                    self.record_sound_fallback_reason("slice_index_unguarded");
                }
                Some(_) => {
                    // Vec-backed read whose current length is incoherent (or a
                    // coherent length shadowed by a static-only primary
                    // guard on a non-whole view): the emitted guard, if any,
                    // is stale-able — fail-close.
                    warn!(fn_name = %self.fn_name, "CHC slice index: Vec-backed read without coherent length guard (#69)");
                    self.record_sound_fallback_reason("slice_index_unguarded");
                }
                None if !bounds_guard_emitted => {
                    // No length source at all for a concrete element read.
                    warn!(fn_name = %self.fn_name, "CHC slice index: concrete element read without a bounds guard (#69)");
                    self.record_sound_fallback_reason("slice_index_unguarded");
                }
                None => {
                    // Static backing guard emitted and the read is not
                    // Vec-backed (fixed [T; N] / const backing): the static
                    // length is exact and permanent — fully guarded.
                }
            }
        }

        // Part of #3528/#3495: Mem-level bridge — mirror element into typed memory
        // so subsequent Deref reads via load_from_memory return the correct value.
        let mut mem_constraints: Vec<Expr> = Vec::new();
        if self.track_level >= ChcTrackLevel::Mem {
            if let Some(ref elem) = elem_expr {
                let local_place = Place { local: dest_local, projection: vec![] };
                if let Some(addr_expr) =
                    self.translate_ref_to_address(&local_place, modified_locals)
                {
                    let local_ty = self.body.locals()[dest_local].ty;
                    if let Some(sc) = self.build_memory_store(addr_expr, elem.clone(), local_ty) {
                        mem_constraints.push(sc);
                    }
                    mem_constraints.append(&mut self.heap_state.pending_updates);
                    mem_constraints
                        .append(&mut self.heap_state.drain_store_chains(&self.diagnostics));
                }
            }
        }

        // Build output args AFTER element computation — late state vars from
        // slice_index_via_memory_model must be captured here. Part of #2970, #3528.
        let new_output_args = self.build_output_args(modified_locals, &[dest_local]);

        // Part of #3528: Filter superseded store chain constraints.
        let filtered_stmts = super::heap_store_chains::filter_superseded_store_chains(
            stmt_constraints,
            &mem_constraints,
        );
        let effective_stmts: &[Expr] = filtered_stmts.as_deref().unwrap_or(stmt_constraints);

        // Constrain destination to computed element value (#3182: flattened dest).
        if let Some(elem) = elem_expr {
            if let Some(mut fc) =
                self.build_flattened_destination_constraints(dest_local, elem.clone())
            {
                fc.extend(mem_constraints);
                self.emit_goto_rule_extra(from_app, target, &new_output_args, effective_stmts, fc);
                return;
            } else if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                let eq = self.make_coerced_eq_constraint(
                    &dest_var,
                    elem,
                    dest_var.sort(),
                    dest_local,
                    "codegen_call_slice::SliceIndex",
                );
                if eq.is_some() {
                    let extra: Vec<Expr> = eq.into_iter().chain(mem_constraints).collect();
                    self.emit_goto_rule_extra(
                        from_app,
                        target,
                        &new_output_args,
                        effective_stmts,
                        extra,
                    );
                    return;
                }
            }

            if matches!(
                self.body.locals()[dest_local].ty.kind(),
                TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))
            ) {
                debug!(
                    fn_name = %self.fn_name,
                    dest_local,
                    "CHC slice index: using side-table/memory bridge for reference destination"
                );
                self.emit_goto_rule_extra(
                    from_app,
                    target,
                    &new_output_args,
                    effective_stmts,
                    mem_constraints,
                );
                return;
            }
        }

        // Constrained symbolic fallback — bounds guards emitted above. Record fallback.
        warn!(fn_name = %self.fn_name, "CHC slice index: constrained symbolic fallback");
        emit_sound_fallback_goto_prebuilt(
            self,
            from_app,
            target,
            &new_output_args,
            effective_stmts,
        );
    }

    /// Task #69: resolve the CURRENT length of the collection a slice-index
    /// operand views, with a COHERENCE verdict. Unlike the static backing
    /// hints used by the primary bounds guard (subslice_len / `[T; N]` /
    /// cast-traced construction length), these sources track runtime shrinks
    /// (truncate/resize update the sidecar length and — after the #69 dests
    /// fix — the datatype and flat len slots).
    ///
    /// Returns `(len_expr, coherent)`. `coherent == true` means the length is
    /// trustworthy for a bounds guard: its sidecar var was seeded by a
    /// collection stub in this function AND the owning collection was never
    /// bypassed by a fn-inline `&mut` call. An INCOHERENT length (free or
    /// stale variable) must not be guarded — but its presence still tells the
    /// caller the read is Vec-backed (shrinkable), so a static-only guard is
    /// stale-able and must fail-close.
    ///
    /// Strategy order:
    /// 1. `resolve_slice_arg_length` — the shared sidecar chain (direct
    ///    sidecar, ref_targets trace, slice_to_vec_local, iter tracking,
    ///    datatype fld_len).
    /// 2. Projected-Vec len slot (mirrors `try_resolve_projected_vec_data_array`).
    /// 3. Struct-embedded Vec len slot (mirrors `try_resolve_struct_vec_data_array`).
    fn resolve_current_slice_view_len(
        &self,
        args: &[Operand],
        slice_arg: &Operand,
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<(Expr, bool)> {
        use super::codegen_ctx::types::CollectionProjectionKind;
        use ay_bindings::ExprValue;
        use rustc_public::mir::ProjectionElem;

        let len_state = &self.collections.len_state;

        // Strategy 1: sidecar candidates in the same order the shared
        // `resolve_slice_arg_length` chain visits locals (direct, ref_targets
        // trace, slice_to_vec_local, iter_to_collection_local) — but instead
        // of stopping at the FIRST len var (which for `&v` temporaries is the
        // temp's own never-seeded var), prefer the first COHERENT candidate
        // and fall back to the first found (incoherent) for Vec-backed
        // detection.
        let arg_local = match slice_arg {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
            _ => None,
        };
        if let Some(arg_local) = arg_local {
            let resolved_local = self
                .ref_resolution
                .ref_targets
                .get(&arg_local)
                .map(|rt| rt.local)
                .unwrap_or(arg_local);
            let mut candidates: Vec<usize> = vec![arg_local];
            let push_unique = |v: &mut Vec<usize>, l: usize| {
                if !v.contains(&l) {
                    v.push(l);
                }
            };
            push_unique(&mut candidates, resolved_local);
            for key in [arg_local, resolved_local] {
                if let Some(&vec_local) = self.ref_resolution.slice_to_vec_local.get(&key) {
                    push_unique(&mut candidates, vec_local);
                }
                if let Some(&coll_local) = self.ref_resolution.iter_to_collection_local.get(&key) {
                    push_unique(&mut candidates, coll_local);
                }
            }
            let mut first_found: Option<(Expr, bool)> = None;
            for cand in candidates {
                let Some(name) = len_state.get_len_var(cand).cloned() else { continue };
                let coherent =
                    len_state.is_len_seeded(&name) && !len_state.is_sidecar_untrusted(cand);
                let len = self.collection_current_len(&name);
                if coherent {
                    return Some((len, true));
                }
                if first_found.is_none() {
                    first_found = Some((len, false));
                }
            }
            if first_found.is_some() {
                return first_found;
            }
            // Strategy 1b: shared chain as a last sidecar resort (covers its
            // Strategy-5 fld_len read for param Vecs) — conservatively
            // incoherent unless it names a seeded, trusted sidecar var.
            if let Some(arg_idx) = args.iter().position(|a| std::ptr::eq(a, slice_arg))
                && let Some(len) = self.resolve_slice_arg_length(args, arg_idx, modified_locals)
            {
                let coherent = match len.value() {
                    ExprValue::Var { name } => {
                        len_state.is_len_seeded(name)
                            && len_state
                                .local_for_len_var(name)
                                .is_none_or(|owner| !len_state.is_sidecar_untrusted(owner))
                    }
                    _ => false,
                };
                return Some((len, coherent));
            }
        }

        let local = arg_local?;
        let ref_target = self.ref_resolution.ref_targets.get(&local)?;

        // Strategy 2: projected-Vec len slot (base + IDX_LEN).
        if ref_target.projections.is_empty()
            && self.collections.projection_locals.get(&ref_target.local).copied()
                == Some(CollectionProjectionKind::Vec)
            && let Some(len) = self.flattened_local_field_expr(
                ref_target.local,
                vec_layout::IDX_LEN,
                modified_locals,
            )
        {
            let owner = ref_target.local;
            let coherent = !len_state.is_sidecar_untrusted(owner)
                && len_state.get_len_var(owner).is_none_or(|name| len_state.is_len_seeded(name));
            return Some((len, coherent));
        }

        // Strategy 3: struct-embedded Vec len slot (data slot - IDX_DATA + IDX_LEN).
        if ref_target.projections.len() == 1
            && let ProjectionElem::Field(field_idx, _) = &ref_target.projections[0]
            && let Some(data_idx) = self.compute_vec_data_flat_offset(ref_target.local, *field_idx)
        {
            let len_idx = data_idx - vec_layout::IDX_DATA + vec_layout::IDX_LEN;
            if let Some((name, sort)) = self.state_var_mgr.state_vars.get(len_idx)
                && sort.bitvec_width() == Some(POINTER_WIDTH)
            {
                let owner = ref_target.local;
                let coherent = !len_state.is_sidecar_untrusted(owner)
                    && len_state.get_len_var(owner).is_none_or(|n| len_state.is_len_seeded(n));
                return Some((Expr::var(&**name, sort.clone()), coherent));
            }
        }

        None
    }

    /// Try to resolve a struct-embedded Vec's data array from a reference operand.
    ///
    /// When `resolve_ref_or_const_referent` fails for `&s.data` because Vec Datatype
    /// reconstruction from flattened state vars fails, this fallback directly looks up
    /// the `fld_data` Array state variable from the flattened struct encoding.
    ///
    /// Part of #3606: struct-embedded Vec Index fallback.
    fn try_resolve_struct_vec_data_array(&self, slice_arg: &Operand) -> Option<Expr> {
        use rustc_public::mir::ProjectionElem;

        let local = match slice_arg {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
            _ => return None,
        };
        let ref_target = self.ref_resolution.ref_targets.get(&local)?;
        // Must have exactly one Field projection pointing to a Vec field.
        if ref_target.projections.len() != 1 {
            return None;
        }
        let field_idx = match &ref_target.projections[0] {
            ProjectionElem::Field(idx, _) => *idx,
            _ => return None,
        };
        let state_idx = self.compute_vec_data_flat_offset(ref_target.local, field_idx)?;
        let (name, sort) = self.state_var_mgr.state_vars.get(state_idx)?;
        sort.array_sort()?;
        debug!(
            struct_local = ref_target.local,
            field_idx, state_idx, "slice index: struct-embedded Vec data array fallback (#3606)"
        );
        Some(Expr::var(&**name, sort.clone()))
    }

    /// Try to resolve a bare projected Vec's data array from a reference operand.
    ///
    /// When a bare Vec local (not embedded in a struct) is projected into 4 state
    /// vars (ptr, len, cap, data), `try_resolve_struct_vec_data_array` returns None
    /// because there's no Field projection. This fallback directly looks up the
    /// data Array (offset +3) from the projected Vec's state variables.
    ///
    /// Part of #1739: projected Vec store/load domain mismatch recovery.
    fn try_resolve_projected_vec_data_array(&self, slice_arg: &Operand) -> Option<Expr> {
        use super::codegen_ctx::types::CollectionProjectionKind;

        let local = match slice_arg {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
            _ => return None,
        };
        // Check if the ref target points directly to a projected Vec local
        // (no Field projection — this is the bare Vec case).
        let ref_target = self.ref_resolution.ref_targets.get(&local)?;
        if !ref_target.projections.is_empty() {
            return None; // Has projections — handled by try_resolve_struct_vec_data_array
        }
        let coll_local = ref_target.local;
        if self.collections.projection_locals.get(&coll_local).copied()
            != Some(CollectionProjectionKind::Vec)
        {
            return None;
        }
        // Projected Vec: base_state_idx + 3 = data field (Array<BV64, elem_sort>)
        let base_idx = self.try_state_idx_for_local(coll_local)?;
        let data_idx = base_idx + 3;
        let (name, sort) = self.state_var_mgr.state_vars.get(data_idx)?;
        sort.array_sort()?;
        debug!(coll_local, data_idx, "slice index: projected Vec data array fallback");
        Some(Expr::var(&**name, sort.clone()))
    }

    /// Emit a canonical ZST value for ZST slice index results.
    ///
    /// Part of #4113: When the destination is BV-sorted (e.g., BV128 fat pointer
    /// for `&()`), the Unit datatype constructor causes a sort mismatch. Detect
    /// the destination sort first and emit a matching canonical value:
    /// - BV destination → `bv_const(0, width)` (ZST has no meaningful bits)
    /// - Bool destination → `true` (canonical unit value)
    /// - Datatype/other → Unit constructor (original behavior)
    pub(in crate::codegen_ay::chc) fn emit_slice_index_zst(
        &mut self,
        dest_local: usize,
        target: BasicBlockIdx,
        from_app: &RelationApp,
        stmt_constraints: &[Expr],
        new_output_args: &[Expr],
    ) {
        if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
            // Choose canonical ZST expression matching the destination sort.
            let zst_expr = if let Some(width) = dest_var.sort().bitvec_width() {
                Expr::bitvec_const(0u64, width)
            } else if dest_var.sort().is_bool() {
                Expr::bool_const(true)
            } else {
                let unit_sort = struct_sort("Unit", Vec::<(&str, Sort)>::new());
                Expr::datatype_constructor("Unit", "Unit_mk", vec![], unit_sort)
            };
            let eq = self.make_coerced_eq_constraint(
                &dest_var,
                zst_expr,
                dest_var.sort(),
                dest_local,
                "codegen_call_slice::SliceIndex_ZST",
            );
            if eq.is_some() {
                self.emit_goto_rule_extra(from_app, target, new_output_args, stmt_constraints, eq);
                return;
            }
        }

        // If we couldn't constrain (no destination resolved), leave unconstrained.
        warn!(fn_name = %self.fn_name, "CHC: ZST slice index sort mismatch — recording fallback");
        emit_sound_fallback_goto_prebuilt(
            self,
            from_app,
            target,
            new_output_args,
            stmt_constraints,
        );
    }

    /// The address the slice's elements live at, when the referent resolver
    /// stopped at the pointer instead of dereferencing it.
    ///
    /// # What establishes the tag
    ///
    /// Two facts, neither of them a width:
    ///
    /// 1. The resolver did **not** hand back element storage. An `Array`- or
    ///    `Datatype`-sorted term is the backing itself and has no address lane,
    ///    so those shapes answer `None` and take their own `match` arm.
    /// 2. The MIR type of the operand denotes a pointer
    ///    ([`mir_ty_denotes_address`]). This is the fact the retired width test
    ///    stood in for, and it is the one the operand's Rust type states
    ///    outright — `&[T]`, `&Vec<T>`, `*const T`, a `NonNull` field reached
    ///    through a projection chain. A `usize` slot, or one of the ADTs
    ///    `translate_adt_ty` collapses to an opaque `ptr_sort()`, answers `no`.
    ///
    /// The widened-value refusal runs on the UNCOERCED term, before any
    /// pointer-width coercion could make a narrow datum look addressable.
    fn slice_referent_as_address(&self, slice_arg: &Operand, referent: Expr) -> Option<Loc> {
        if referent.sort().is_array() || referent.sort().datatype_name().is_some() {
            return None;
        }
        if is_value_widened_into_address(&referent) {
            debug!(
                fn_name = %self.fn_name,
                "CHC slice index: refusing widened value-as-address for pointer lane"
            );
            return None;
        }
        if PtrSlot::of_sort(referent.sort()) != Some(PtrSlot::Thin) {
            return None;
        }
        let arg_ty = self.resolve_body_ty(slice_arg.ty(self.body.locals()).ok()?);
        if !mir_ty_denotes_address(arg_ty) {
            debug!(
                fn_name = %self.fn_name,
                ?arg_ty,
                "CHC slice index: pointer-width slice slot whose MIR type is not a pointer; \
                 refusing the memory-model deref"
            );
            return None;
        }
        Some(Loc::of_address(referent))
    }

    /// When `resolve_ref_or_const_referent` returns a raw pointer (bv64) instead of
    /// Array/Datatype — because ref_targets can't track through complex projection
    /// chains (e.g., PolymorphicIter field access) — compute `ptr + idx * sizeof(elem)`
    /// and load from the memory array. Part of #2915.
    fn slice_index_via_memory_model(
        &mut self,
        slice_arg: &Operand,
        ptr: &Loc,
        idx: &Expr,
    ) -> Option<Expr> {
        let elem_ty = self.chc_slice_elem_ty(slice_arg)?;
        // #2931: defaults to 1 if type size unknown (correct for u8/bool only).
        let elem_size = self.get_type_size(elem_ty).unwrap_or(1) as u64;
        // Split-add keeps the obj_id lane intact for symbolic indices (#3921):
        // whole-width bvadd smears the index across the id bits and the load's
        // heap bounds check gets dropped for non-foldable obj_ids.
        let byte_offset = if elem_size <= 1 {
            idx.clone()
        } else {
            idx.clone().bvmul(Expr::bitvec_const(elem_size as i128, POINTER_WIDTH))
        };
        // Byte-offset arithmetic on an address is still an address (wave 11's
        // `Loc` producer rule), so the `Loc` the caller established is inherited
        // here rather than re-minted — which lets the load go through the typed
        // `load_from_memory` instead of the deprecated untyped shim.
        let elem_addr = Loc::of_address(
            crate::codegen_ay::chc::pointer_step::step_split_pointer(
                ptr.as_expr().clone(),
                byte_offset,
            )
            .result,
        );
        debug!(fn_name = %self.fn_name, ?elem_size, "CHC slice index: pointer deref via memory model");
        self.load_from_memory(elem_addr, elem_ty).map(Val::into_expr)
    }
}
