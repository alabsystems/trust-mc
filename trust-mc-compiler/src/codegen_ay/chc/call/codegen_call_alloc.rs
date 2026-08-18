// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Heap allocation call handling.
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.

use ay_bindings::{Expr, ExprValue};

use super::chc_call_context::ChcCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_rules::CodegenRules;
use super::{ChcCtx, RelationApp, chc_debug_enabled, codegen_expr_heap};
use crate::codegen_ay::stubs::StubKind;
use rustc_public::mir::{CastKind, Operand, PointerCoercion, Rvalue, StatementKind};
use tracing::{debug, warn};

/// Extension trait for heap allocation call handling on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallAlloc {
    fn codegen_call_alloc(&mut self, bb_idx: usize, cx: &ChcCallContext<'_>);
}

impl<'tcx, 'body> CallAlloc for ChcCtx<'tcx, 'body> {
    /// Handle heap allocation intrinsic calls (Part of #1100).
    fn codegen_call_alloc(&mut self, bb_idx: usize, cx: &ChcCallContext<'_>) {
        let stub = cx.stub;
        let args = cx.args;
        let destination = cx.destination;
        let target = cx.target;
        let from_app = cx.from_app;
        let stmt_constraints = cx.stmt_constraints;
        let modified_locals = cx.modified_locals;
        if chc_debug_enabled() {
            debug!("alloc_stub stub={:?} has_target=true dest={}", stub, destination.local);
        }
        let mut extra_constraints: Vec<Expr> = Vec::new();
        let mut extra_dests: Vec<usize> = Vec::new();

        if let Some(result) = self.translate_alloc_call(stub, args, modified_locals) {
            let super::AllocCallResult {
                result,
                heap_constraints,
                safety_checks,
                alloc_obj_id,
                transition_branches,
            } = result;
            // Emit error rules for allocation/deallocation precondition checks.
            if self.memory_safety_checks {
                for check in safety_checks {
                    self.emit_error_rule_for_condition(from_app, check, stmt_constraints, bb_idx);
                }
            }
            let dest_local: usize = destination.local;
            if transition_branches.is_empty() {
                self.emit_alloc_single_rule(
                    bb_idx,
                    stub,
                    args,
                    result,
                    heap_constraints,
                    alloc_obj_id,
                    dest_local,
                    modified_locals,
                    from_app,
                    stmt_constraints,
                    target,
                    &mut extra_constraints,
                    &mut extra_dests,
                );
            } else {
                // MEMUB-24/25/27: shadow effect shared by every branch.
                let mut heap_constraints = heap_constraints;
                self.append_alloc_shadow_constraints(stub, alloc_obj_id, &mut heap_constraints);
                self.emit_alloc_branched_rules(
                    result,
                    heap_constraints,
                    alloc_obj_id,
                    transition_branches,
                    dest_local,
                    modified_locals,
                    from_app,
                    stmt_constraints,
                    target,
                    &mut extra_dests,
                );
            }
        } else {
            self.codegen_call_alloc_fallback(bb_idx, cx);
        }
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Emit a single alloc/realloc transition rule (no branching).
    #[allow(clippy::too_many_arguments)]
    fn emit_alloc_single_rule(
        &mut self,
        bb_idx: usize,
        stub: StubKind,
        args: &[rustc_public::mir::Operand],
        result: Option<Expr>,
        heap_constraints: Vec<Expr>,
        alloc_obj_id: Option<u32>,
        dest_local: usize,
        modified_locals: &std::collections::HashSet<usize>,
        from_app: &RelationApp,
        stmt_constraints: &[Expr],
        target: usize,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) {
        if let Some(result_expr) = result.as_ref() {
            self.cache_layout_stub_constant_result(stub, dest_local, result_expr);
        }

        if let Some(ptr_expr) = result
            && let Some((_, dest_var)) = self.resolve_destination(dest_local)
        {
            if stub == StubKind::BoxNew {
                self.emit_boxnew_heap_stores(
                    bb_idx,
                    args,
                    &ptr_expr,
                    modified_locals,
                    extra_constraints,
                );
            }
            if let Some(eq) = self.make_coerced_eq_constraint(
                &dest_var,
                ptr_expr,
                dest_var.sort(),
                dest_local,
                "codegen_call_alloc",
            ) {
                extra_constraints.push(eq);
            }
            extra_dests.push(dest_local);
            self.record_alloc_dest(dest_local, alloc_obj_id);
        }
        extra_constraints.extend(heap_constraints);
        // MEMUB-24/25/27: apply the alloc family's memory-init shadow effect.
        self.append_alloc_shadow_constraints(stub, alloc_obj_id, extra_constraints);
        self.emit_alloc_pending_checks(from_app, stmt_constraints, target);
        let new_output_args = self.build_output_args(modified_locals, extra_dests);
        self.emit_goto_rule_extra(
            from_app,
            target,
            &new_output_args,
            stmt_constraints,
            std::mem::take(extra_constraints),
        );
    }

    fn cache_layout_stub_constant_result(
        &mut self,
        stub: StubKind,
        dest_local: usize,
        result_expr: &Expr,
    ) {
        if !matches!(
            stub,
            StubKind::LayoutSize
                | StubKind::LayoutAlign
                | StubKind::LayoutPaddingNeededFor
                | StubKind::LayoutIsSizeAlignValid
        ) || !self.encode.single_assign_locals.contains(&dest_local)
        {
            return;
        }

        let cached = match result_expr.value() {
            ExprValue::BitVecConst { .. } | ExprValue::BoolConst(_) => Some(result_expr.clone()),
            _ if result_expr.sort().is_bitvec() => {
                result_expr.sort().bitvec_width().and_then(|width| {
                    Self::try_extract_concrete_usize(result_expr)
                        .map(|value| Expr::bitvec_const(value as i128, width))
                })
            }
            _ => None,
        };

        if let Some(expr) = cached {
            self.encode.const_folded_call_results.insert(dest_local, expr);
        }
    }

    /// Emit branched alloc transition rules (moved/in-place paths).
    #[allow(clippy::too_many_arguments)]
    fn emit_alloc_branched_rules(
        &mut self,
        result: Option<Expr>,
        heap_constraints: Vec<Expr>,
        alloc_obj_id: Option<u32>,
        transition_branches: Vec<super::codegen_ctx::types::AllocTransitionBranch>,
        dest_local: usize,
        modified_locals: &std::collections::HashSet<usize>,
        from_app: &RelationApp,
        stmt_constraints: &[Expr],
        target: usize,
        extra_dests: &mut Vec<usize>,
    ) {
        if result.is_some() || transition_branches.iter().any(|branch| branch.result.is_some()) {
            extra_dests.push(dest_local);
            self.record_alloc_dest(dest_local, alloc_obj_id);
        }
        self.emit_alloc_pending_checks(from_app, stmt_constraints, target);
        let new_output_args = self.build_output_args(modified_locals, extra_dests);
        for branch in transition_branches {
            let mut branch_constraints = heap_constraints.clone();
            let branch_result = branch.result.or_else(|| result.clone());
            if let Some(ptr_expr) = branch_result
                && let Some((_, dest_var)) = self.resolve_destination(dest_local)
                && let Some(eq) = self.make_coerced_eq_constraint(
                    &dest_var,
                    ptr_expr,
                    dest_var.sort(),
                    dest_local,
                    "codegen_call_alloc",
                )
            {
                branch_constraints.push(eq);
            }
            branch_constraints.extend(branch.constraints);
            self.emit_goto_rule_extra(
                from_app,
                target,
                &new_output_args,
                stmt_constraints,
                branch_constraints,
            );
        }
    }

    /// Part of #3159, #3589: Store BoxNew payload at the heap address, then
    /// drain accumulated store chains so heap stores reach the CHC rule.
    fn emit_boxnew_heap_stores(
        &mut self,
        bb_idx: usize,
        args: &[rustc_public::mir::Operand],
        ptr_expr: &Expr,
        modified_locals: &std::collections::HashSet<usize>,
        extra_constraints: &mut Vec<Expr>,
    ) {
        let prev_suppress = self.suppress_heap_store_checks;
        self.suppress_heap_store_checks = true;
        self.emit_boxnew_value_stores(bb_idx, args, ptr_expr, modified_locals, extra_constraints);
        self.suppress_heap_store_checks = prev_suppress;
        extra_constraints.append(&mut self.heap_state.drain_store_chains(&self.diagnostics));
    }

    /// Emit any call-terminator heap checks accumulated during alloc handling.
    pub(in crate::codegen_ay::chc) fn emit_alloc_pending_checks(
        &mut self,
        from_app: &RelationApp,
        stmt_constraints: &[Expr],
        target: usize,
    ) {
        for check in self.heap_state.pending_checks.drain(..).collect::<Vec<_>>() {
            self.emit_error_rule_for_condition(from_app, check, stmt_constraints, target);
        }
    }

    /// Fallback when `translate_alloc_call` returns `None` (Part of #3123).
    ///
    /// For `RustRealloc`, applies targeted nondeterministic invalidation of
    /// the old pointer's `obj_valid` entry (#3636). Without this, the old
    /// pointer stays "valid" after realloc → false PROOF (soundness bug).
    fn codegen_call_alloc_fallback(&mut self, _bb_idx: usize, cx: &ChcCallContext<'_>) {
        self.record_sound_fallback_reason("alloc_dispatch_fallback");
        // Raw-alloc route: under `-Z uninit-checks` an UNTRACKED `__rust_alloc`
        // is the exact shape the former blanket `body_has_direct_alloc_call`
        // demotion guarded (fresh UNINIT bytes with no shadow marking, then
        // blessed fail-open below). Keep that net here, at the only path where
        // the stub failed to register the object — a tracked allocation gets
        // the faithful shadow effect in `translate_rust_alloc` instead.
        if self.uninit_checks && cx.stub == StubKind::RustAlloc {
            warn!(
                fn_name = %self.fn_name,
                "uninit-checks: untracked raw alloc (dispatch fallback) — chc_fallback"
            );
            self.record_fallback();
        }
        // MEMUB-24/25/27: the allocation is untracked here — bless the shadow
        // state (fail-open) so later init checks cannot false-fail.
        let mut shadow_constraints: Vec<Expr> = Vec::new();
        self.append_alloc_shadow_constraints(cx.stub, None, &mut shadow_constraints);
        if cx.stub == StubKind::RustRealloc {
            self.mark_heap_metadata_modified();
            // Try to resolve old_ptr → obj_id for targeted invalidation.
            let old_ptr_expr = cx
                .args
                .first()
                .and_then(|arg| self.translate_operand_with_modified(arg, cx.modified_locals));
            if let Some(ref ptr) = old_ptr_expr
                && let Some((old_obj_id_expr, _)) = self.split_pointer(ptr)
            {
                // Part of #3677: Store-chain encoding for obj_valid invalidation.
                // The previous pointwise SELECT encoding (#3728) missed pre-existing
                // allocations not in known_alloc_ids. Store-chain provides an
                // implicit frame for ALL indices.
                self.record_aggregate_gap("alloc_dealloc_obj_valid_store_chain");
                let obj_valid_out = codegen_expr_heap::obj_valid_out();
                let obj_valid_in = codegen_expr_heap::obj_valid_in();

                let new_output_args =
                    self.build_output_args(cx.modified_locals, &[cx.destination.local]);

                let obj_valid_updated =
                    obj_valid_in.store(old_obj_id_expr, Expr::bool_const(false));
                let mut constraints = vec![obj_valid_out.eq(obj_valid_updated)];
                constraints.append(&mut shadow_constraints);
                self.emit_goto_rule_extra(
                    cx.from_app,
                    cx.target,
                    &new_output_args,
                    cx.stmt_constraints,
                    constraints,
                );

                debug!("CHC: RustRealloc fallback - always-moved invalidation (#3728)");
                return;
            }
            // old_ptr resolution or split_pointer failed — metadata stays fully
            // unconstrained (UNKNOWN verdict). Log for diagnostics (#3636).
            warn!(
                "CHC: RustRealloc fallback - could not resolve old_ptr for targeted \
                 invalidation; obj_valid_out/obj_size_out fully unconstrained"
            );
        }
        let new_output_args = self.build_output_args(cx.modified_locals, &[cx.destination.local]);
        self.emit_goto_rule_extra(
            cx.from_app,
            cx.target,
            &new_output_args,
            cx.stmt_constraints,
            shadow_constraints,
        );
    }

    /// Record allocation tracking for a destination local (#3012, #3273).
    pub(in crate::codegen_ay::chc) fn record_alloc_dest(
        &mut self,
        dest_local: usize,
        alloc_obj_id: Option<u32>,
    ) {
        self.ref_resolution.alloc_result_locals.insert(dest_local);
        if let Some(obj_id) = alloc_obj_id {
            self.known_alloc_ids.insert(dest_local, obj_id);
        }
    }

    /// Store boxed value's fields at heap address. Falls back to MIR Aggregate
    /// scan when struct decomposition fails. (Part of #3159, #3589)
    ///
    /// Part of #4274 (TL15): For `PointerCoercion::Unsize` defining rvalues,
    /// emit stores under BOTH the post-cast `Dyn_Trait` view AND the source
    /// concrete payload view. The post-cast view is consumed by `mem_Dyn_Trait`
    /// loads (e.g. `Box<dyn Trait>::deref`), while the concrete view is the key
    /// the virtual-call inline walker uses when loading `(*self).field` inside
    /// the devirtualized impl body. Without the dual store, the PDR
    /// invariant sees `mem_<Concrete>[addr]` as unconstrained and the
    /// assertion on the field value is a false counterexample.
    fn emit_boxnew_value_stores(
        &mut self,
        bb_idx: usize,
        args: &[rustc_public::mir::Operand],
        ptr_expr: &Expr,
        modified_locals: &std::collections::HashSet<usize>,
        extra_constraints: &mut Vec<Expr>,
    ) {
        let Some(arg0) = args.first() else {
            return;
        };
        // Prefer defining rvalue for richer payload structure.
        let value_expr = self
            .translate_boxnew_source_rvalue(bb_idx, arg0, modified_locals)
            .or_else(|| self.translate_operand_with_modified(arg0, modified_locals));
        // Shape B (boxnew payload store drop): positively track whether the
        // primary path emitted an EXACT whole-value store for the payload.
        // Previously the aggregate-scan fallback below ran unconditionally,
        // so operands with no defining Assign statement (call results such
        // as `Box::new(kani::any())`, moved arguments) recorded a spurious
        // `boxnew_payload_store_drop` even though the whole payload had just
        // been stored verbatim through the ordinary reader-consistent lanes.
        // The drop is recorded IFF no exact whole-value store was emitted —
        // never skipped on a partial store (see
        // `boxnew_whole_value_store_is_exact` for the fail-closed criteria).
        let mut payload_fully_stored = false;
        if let Some(value_expr) = value_expr
            && let Ok(arg_ty) = arg0.ty(self.body.locals())
        {
            let store_ty = self.resolve_boxnew_store_ty(bb_idx, arg0, arg_ty);
            // Watermark BEFORE emitting: any degradation the store helpers
            // record (dropped store, fresh-symbolic value substitution,
            // skipped field, …) disqualifies exactness below (fail-closed).
            let degradation_watermark = self.boxnew_store_degradation_watermark();
            self.mirror_array_elements_to_flat_memory(
                &value_expr,
                store_ty,
                ptr_expr,
                extra_constraints,
            );
            // Part of #4059: Always emit both per-field AND whole-struct
            // stores. Per-field stores enable field-level loads (e.g.,
            // `mem_bool[addr]` for `self.fancy` via virtual dispatch).
            // Whole-struct stores enable struct-level loads (e.g.,
            // `mem_Table[addr]`). Previously, decomposition success skipped
            // the whole-struct store, matching the inline walker bug fixed
            // in #4014. Mirrors the Rc::new fix in codegen_rc_arc_new.
            self.try_decompose_struct_store(ptr_expr, &value_expr, store_ty, extra_constraints);
            if let Some(store_constraint) =
                self.build_memory_store_untyped(ptr_expr.clone(), value_expr.clone(), store_ty)
            {
                extra_constraints.push(store_constraint);
            }
            // Part of #4274 (TL15): If store_ty is a post-Unsize dyn view, also
            // emit stores under the concrete source-payload view so virtual
            // dispatch loads (`mem_<Concrete>[addr]`) inside the inlined impl
            // body match the same address the Dyn view was stored at.
            let mut dual_view_emitted = false;
            if let Some(concrete_ty) = self.resolve_boxnew_concrete_payload_ty(bb_idx, arg0)
                && concrete_ty != store_ty
            {
                dual_view_emitted = true;
                self.emit_boxnew_concrete_payload_alias_store(
                    bb_idx,
                    arg0,
                    ptr_expr,
                    concrete_ty,
                    &value_expr,
                    modified_locals,
                    extra_constraints,
                );
            }
            // Exact iff: the whole-value shape is positively recognized as
            // stored verbatim, no dual (dyn/concrete) view was in play, and
            // no store helper recorded a degradation while emitting. Dyn
            // dual-view payloads are conservatively NOT claimed exact: their
            // coercion lanes are audited separately and keep the SoundHavoc
            // drop marker exactly as before this change.
            payload_fully_stored = !dual_view_emitted
                && self.boxnew_whole_value_store_is_exact(ptr_expr, &value_expr, store_ty)
                && self.boxnew_store_degradation_watermark() == degradation_watermark;
        }
        // Part of #3589: Aggregate scan fallback.
        let src_local = match arg0 {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
            _ => {
                // Constant or projected operands have no aggregate-scan
                // fallback. Previously this returned silently even when the
                // primary path failed (a fail-open marker hole: silent havoc
                // with no accounting). Record the audited SoundHavoc drop
                // unless the payload was positively stored in full.
                if !payload_fully_stored {
                    warn!(
                        fn_name = %self.fn_name,
                        ?arg0,
                        "BoxNew: emit_boxnew_value_stores: non-plain-local operand \
                         payload not fully stored"
                    );
                    self.record_sound_fallback_reason("boxnew_payload_store_drop");
                }
                return;
            }
        };
        // Search current block first, then all blocks for the aggregate definition.
        // Coroutine aggregates are often defined in a predecessor block (e.g., async
        // block created in BB0, Box::new in BB1). Cross-block search is sound because
        // the aggregate construction is deterministic and happens exactly once.
        let aggregate_rvalue = self
            .body
            .blocks
            .get(bb_idx)
            .and_then(|bb_data| {
                bb_data.statements.iter().find_map(|stmt| {
                    if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                        && lhs.local == src_local
                        && matches!(rhs, Rvalue::Aggregate(..))
                    {
                        Some(rhs.clone())
                    } else {
                        None
                    }
                })
            })
            .or_else(|| {
                self.body.blocks.iter().enumerate().find_map(|(other_bb, bb_data)| {
                    if other_bb == bb_idx {
                        return None;
                    }
                    bb_data.statements.iter().find_map(|stmt| {
                        if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                            && lhs.local == src_local
                            && matches!(rhs, Rvalue::Aggregate(..))
                        {
                            Some(rhs.clone())
                        } else {
                            None
                        }
                    })
                })
            });
        if let Some(ref rhs) = aggregate_rvalue
            && let Ok(agg_ty) = arg0.ty(self.body.locals())
        {
            let store_ty = self.resolve_boxnew_store_ty(bb_idx, arg0, agg_ty);
            debug!(
                src_local,
                bb_idx,
                "BoxNew: emit_boxnew_value_stores: using Aggregate fallback to mirror fields to heap"
            );
            self.mirror_aggregate_field_stores_to_memory(
                rhs,
                store_ty,
                modified_locals,
                ptr_expr.clone(),
                extra_constraints,
            );
        } else if let Some(callable_expr) = self.translate_boxnew_callable_operand(arg0)
            && let Ok(arg_ty) = arg0.ty(self.body.locals())
        {
            // Part of #3980: Promoted &fn-item payload store for dyn dispatch.
            let store_ty = self.resolve_boxnew_store_ty(bb_idx, arg0, arg_ty);
            if let Some(store) =
                self.build_memory_store_untyped(ptr_expr.clone(), callable_expr, store_ty)
            {
                extra_constraints.push(store);
            }
        } else if payload_fully_stored {
            // Shape B: the primary path stored the WHOLE payload verbatim
            // through the same lanes ordinary stores use (region array +
            // type-indexed array + array element mirror), so there is no
            // havoc in play and no drop to record. Typical shape: the
            // payload local is a call result (`Box::new(kani::any())`) or a
            // moved argument — no defining Assign statement exists, so the
            // aggregate scan finds nothing, but the operand itself
            // translated to an exact value above.
            debug!(
                fn_name = %self.fn_name,
                src_local,
                "BoxNew: emit_boxnew_value_stores: whole-value payload stored exactly; \
                 no drop recorded"
            );
        } else {
            warn!(
                fn_name = %self.fn_name,
                src_local,
                "BoxNew: emit_boxnew_value_stores: translate_operand failed and no Aggregate found"
            );
            // No store is emitted: the boxed payload stays an unconstrained heap
            // cell (a sound over-approximation that ADDS behaviors). Record it so
            // downstream counterexample-quality accounting never tags the harness
            // Clean/Genuine while a real havoc is in play (silent-havoc bug,
            // observed on Box<Box<dyn T>> in UnsizedCoercion/double_coercion.rs).
            self.record_sound_fallback_reason("boxnew_payload_store_drop");
        }
    }

    /// Shape B: snapshot of the degradation counters bumped by the heap-store
    /// helpers whenever a store is dropped, its value is substituted with a
    /// fresh symbolic (`coerce_store_value`), a struct field store is skipped
    /// (`store_adt_field_offset_unknown`), or any other encoding gap is
    /// recorded mid-store. Taken before/after the primary BoxNew payload
    /// store path: any movement means the emitted stores are NOT exact and
    /// the audited `boxnew_payload_store_drop` SoundHavoc must still be
    /// recorded (fail-closed).
    fn boxnew_store_degradation_watermark(&self) -> [usize; 5] {
        [
            self.diagnostics.store_dropped_transition.get(),
            self.diagnostics.aggregate_encoding_gap.get(),
            self.diagnostics.place_translation_drop.get(),
            self.diagnostics.sound_havoc_drop.get(),
            self.fallback_count,
        ]
    }

    /// Shape B: positively recognize payload shapes whose whole-value store
    /// through `build_memory_store` is EXACT — i.e. the boxed heap cell is
    /// fully constrained to the translated payload value, with no coercion
    /// loss and no fresh-symbolic substitution, so no silent havoc is in play.
    ///
    /// Fail-closed: anything not positively recognized returns `false` and
    /// the caller keeps recording the audited SoundHavoc drop. A PARTIAL
    /// store (e.g. struct decomposition storing only some fields, or a lossy
    /// datatype→bitvec truncation) must never reach `true`: exactness is
    /// claimed only for
    /// (a) ZST payloads — no bytes, the skipped store loses nothing;
    /// (b) plain `[T; N]` arrays fully decomposed per-element by the #4099
    ///     path with the value's element sort equal to the memory element
    ///     sort (verbatim element stores at every index `0..N`); and
    /// (c) whole values whose sort equals the memory array's element sort
    ///     (`coerce_store_value` is then an identity — verbatim store).
    /// Callers must pair this with `boxnew_store_degradation_watermark` so a
    /// pre-existing type array declared at a DIFFERENT element sort (which
    /// routes the store through a fresh symbolic and records an aggregate
    /// gap) also disqualifies exactness.
    fn boxnew_whole_value_store_is_exact(
        &self,
        ptr_expr: &Expr,
        value_expr: &Expr,
        store_ty: rustc_public::ty::Ty,
    ) -> bool {
        // build_memory_store's address gate: Int addresses are int2bv-coerced;
        // anything else that is not a bitvec drops the store silently.
        let addr_sort = ptr_expr.sort();
        if !addr_sort.is_bitvec() && !addr_sort.is_int() {
            return false;
        }
        let store_ty = self.resolve_body_ty(store_ty);
        // (a) ZST payloads carry no bytes.
        if super::codegen_call_kani_model_dst::is_zst_ty(store_ty) {
            return true;
        }
        let elem_sort = self.elem_sort_for_memory_array(store_ty);
        let value_sort = value_expr.sort();
        let is_plain_array = matches!(
            store_ty.kind(),
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Array(..))
        );
        // (b) Mirror of build_memory_store's #4099 decomposition gate: when
        // it takes over, every element is stored individually at its byte
        // offset; exact iff the value's element sort equals the memory
        // element sort (verbatim element stores, no substitution).
        if is_plain_array && value_sort.is_array() && !elem_sort.is_array() {
            let Some(array_sort) = value_sort.array_sort() else {
                return false;
            };
            let Some(array_len) = self.get_array_length(store_ty) else {
                return false;
            };
            let Some(elem_size) =
                self.get_array_element_ty(store_ty).and_then(|et| self.get_type_size(et))
            else {
                return false;
            };
            return array_len > 0
                && array_len <= 64
                && elem_size > 0
                && array_sort.element_sort == elem_sort;
        }
        // (c) Whole-value lane: the store is verbatim iff the value sort
        // already equals the declared element sort. Datatype payloads (which
        // build_memory_store coerces via flatten/truncate lanes) and any
        // other mismatch stay fail-closed.
        *value_sort == elem_sort
    }

    fn translate_boxnew_source_rvalue(
        &mut self,
        bb_idx: usize,
        operand: &Operand,
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<Expr> {
        let src_local = match operand {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        }?;
        let rhs = self
            .find_local_defining_rvalue_in_block(bb_idx, src_local)
            .or_else(|| self.find_unique_local_defining_rvalue_outside_block(bb_idx, src_local))?;
        debug!(bb_idx, src_local, ?rhs, "BoxNew: rebuilding payload from defining MIR rvalue");
        // Part of #3871: Unsize casts need rvalue-first (synthesizes vtable metadata).
        if let Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), source_operand, _) =
            &rhs
        {
            return self
                .translate_rvalue_with_modified(&rhs, modified_locals, Some(src_local))
                .or_else(|| {
                    self.translate_boxnew_payload_operand(source_operand, modified_locals)
                });
        }
        if let Some(expr) = match &rhs {
            Rvalue::Cast(_, source_operand, _)
            | Rvalue::Use(source_operand)
            | Rvalue::ShallowInitBox(source_operand, _) => {
                self.translate_boxnew_payload_operand(source_operand, modified_locals)
            }
            _ => None,
        } {
            return Some(expr);
        }
        self.translate_rvalue_with_modified(&rhs, modified_locals, Some(src_local))
    }

    fn find_local_defining_rvalue_in_block(
        &self,
        bb_idx: usize,
        target_local: usize,
    ) -> Option<Rvalue> {
        let bb_data = self.body.blocks.get(bb_idx)?;
        bb_data.statements.iter().rev().find_map(|stmt| {
            if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                && lhs.local == target_local
                && lhs.projection.is_empty()
            {
                Some(rhs.clone())
            } else {
                None
            }
        })
    }

    fn find_unique_local_defining_rvalue_outside_block(
        &self,
        bb_idx: usize,
        target_local: usize,
    ) -> Option<Rvalue> {
        let mut found = None;
        for (other_bb, bb_data) in self.body.blocks.iter().enumerate() {
            if other_bb == bb_idx {
                continue;
            }
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                    && lhs.local == target_local
                    && lhs.projection.is_empty()
                {
                    if found.is_some() {
                        return None;
                    }
                    found = Some(rhs.clone());
                }
            }
        }
        found
    }

    fn translate_boxnew_payload_operand(
        &mut self,
        operand: &Operand,
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<Expr> {
        // Part of #3980: callable ID first (fn-item constants are ZST).
        if self.boxnew_operand_is_callable(operand) {
            return self
                .translate_boxnew_callable_operand(operand)
                .or_else(|| self.translate_operand_with_modified(operand, modified_locals));
        }
        self.translate_operand_with_modified(operand, modified_locals).or_else(|| {
            self.translate_boxnew_callable_operand(operand).or_else(|| match operand {
                Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                    self.known_alloc_ids.get(&place.local).map(|obj_id| {
                        Expr::bitvec_const(*obj_id as i128, 32)
                            .concat(Expr::bitvec_const(0i128, 32))
                    })
                }
                _ => None,
            })
        })
    }

    fn resolve_boxnew_store_ty(
        &self,
        bb_idx: usize,
        operand: &Operand,
        ty: rustc_public::ty::Ty,
    ) -> rustc_public::ty::Ty {
        // Part of #3871: For Unsize casts, use post-cast type (Dyn_Trait value) to
        // match the store/load type key. For other casts, prefer the source operand type.
        let source_rvalue_ty = match operand {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                self.find_local_defining_rvalue_in_block(bb_idx, place.local).and_then(|rhs| {
                    if matches!(
                        rhs,
                        Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), _, _)
                    ) {
                        return Some(ty);
                    }
                    super::super::dyn_coercion::find_dyn_trait_tail_ty(self, ty)?;
                    match rhs {
                        Rvalue::Cast(_, source_operand, _) | Rvalue::Use(source_operand) => {
                            source_operand.ty(self.body.locals()).ok()
                        }
                        _ => None,
                    }
                })
            }
            _ => None,
        };
        if let Some(source_ty) = source_rvalue_ty {
            return source_ty;
        }
        // Part of #3975: route fallback through the shared normalization helper
        // instead of reimplementing the two-step resolve+replace sequence locally.
        super::super::dyn_coercion::normalize_unique_dyn_tail_ty(self, ty)
    }

    /// Part of #4274 (TL15): Recover the pre-Unsize concrete payload type for a
    /// Box::new arg0 whose defining rvalue is a `PointerCoercion::Unsize`. The
    /// inline virtual-call walker loads `(*self).field` under the concrete-self
    /// type key; we use this type to emit a companion store so that key is
    /// populated.
    ///
    /// Returns `None` when the defining rvalue is not an Unsize cast or the
    /// source operand type is unavailable.
    fn resolve_boxnew_concrete_payload_ty(
        &self,
        bb_idx: usize,
        operand: &Operand,
    ) -> Option<rustc_public::ty::Ty> {
        let src_local = match operand {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => return None,
        };
        let rhs = self.find_local_defining_rvalue_in_block(bb_idx, src_local)?;
        let Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), source_operand, _) =
            &rhs
        else {
            return None;
        };
        source_operand.ty(self.body.locals()).ok()
    }

    /// Part of #4274 (TL15): Emit companion heap stores under the concrete
    /// payload type key so later virtual-call body loads (`mem_<Concrete>[addr]`)
    /// see the stored field values. Mirrors the per-field + whole-struct store
    /// pattern used by the primary (dyn-view) store above.
    fn emit_boxnew_concrete_payload_alias_store(
        &mut self,
        bb_idx: usize,
        arg0: &Operand,
        ptr_expr: &Expr,
        concrete_ty: rustc_public::ty::Ty,
        dyn_value_expr: &Expr,
        modified_locals: &std::collections::HashSet<usize>,
        extra_constraints: &mut Vec<Expr>,
    ) {
        // Prefer to re-translate the pre-Unsize source operand so the value
        // shape matches `concrete_ty`. The `dyn_value_expr` holds the fat-ptr
        // dyn view and is the wrong shape for a concrete-payload store.
        let concrete_value = self
            .translate_boxnew_concrete_source(bb_idx, arg0, modified_locals)
            .unwrap_or_else(|| dyn_value_expr.clone());
        self.mirror_array_elements_to_flat_memory(
            &concrete_value,
            concrete_ty,
            ptr_expr,
            extra_constraints,
        );
        self.try_decompose_struct_store(ptr_expr, &concrete_value, concrete_ty, extra_constraints);
        if let Some(store_constraint) =
            self.build_memory_store_untyped(ptr_expr.clone(), concrete_value, concrete_ty)
        {
            extra_constraints.push(store_constraint);
        }
        debug!(
            bb_idx,
            "BoxNew: emit_boxnew_concrete_payload_alias_store — dual-view store under concrete key"
        );
    }

    /// Part of #4274 (TL15): Translate the source operand of the Unsize cast
    /// that defines `arg0`. Used to recover the concrete-payload value shape
    /// for the dual-view store.
    fn translate_boxnew_concrete_source(
        &mut self,
        bb_idx: usize,
        arg0: &Operand,
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<Expr> {
        let src_local = match arg0 {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => return None,
        };
        let rhs = self.find_local_defining_rvalue_in_block(bb_idx, src_local)?;
        let Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), source_operand, _) =
            rhs
        else {
            return None;
        };
        self.translate_operand_with_modified(&source_operand, modified_locals)
    }
}
