// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pointer/memory operation stubs: ptr.add, ptr.read, ptr.write, ptr.cast,
//! copy_nonoverlapping, mem::size_of/align_of, pointer utilities.
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.

use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::Operand;
use std::collections::HashMap;

use crate::codegen_ay::stubs::StubKind;

use super::ChcCtx;
use super::chc_call_context::ChcCallContext;
use super::codegen_call_coerce::{
    CallCoerce, emit_sound_fallback_goto, try_emit_precise_call_result,
};
use super::codegen_ctx::types::RefTarget;
use super::codegen_rules::CodegenRules;
use super::stmt_accumulator::StmtAccumulator;
use tracing::{debug, warn};

/// Extension trait for pointer/memory call handling on `ChcCtx`.
/// Pointer identity/passthrough ops extracted to codegen_call_ptr_identity.rs per #3199.
pub(in crate::codegen_ay::chc) trait CallPtr {
    fn codegen_call_ptr_memory(&mut self, cx: &ChcCallContext<'_>);
    fn codegen_call_pointer_utility(&mut self, cx: &ChcCallContext<'_>);
    fn codegen_call_copy_nonoverlapping(
        &mut self,
        bb_idx: usize,
        cx: &ChcCallContext<'_>,
        allow_overlap: bool,
    );
    fn codegen_call_mem_intrinsic(&mut self, func: &Operand, cx: &ChcCallContext<'_>);
}

impl<'tcx, 'body> CallPtr for ChcCtx<'tcx, 'body> {
    /// Handle ptr.add / ptr.write / ptr.read stubs for CHC memory operations.
    ///
    /// Unlike BMC which over-approximates (symbolic read, no-op write), CHC models
    /// real memory semantics via `build_memory_store` / `load_from_memory`.
    /// Part of #1836: Required for test_realloc_grow and test_alloc_array.
    fn codegen_call_ptr_memory(&mut self, cx: &ChcCallContext<'_>) {
        let dest_local: usize = cx.destination.local;
        debug!("ptr_memory_stub stub={:?} dest={}", cx.stub, dest_local);

        match cx.stub {
            StubKind::PtrAdd => {
                // Pointer offset overflow error rules (#3176).
                if self.extra_pointer_checks {
                    self.emit_ptr_offset_overflow_error_rules(
                        cx.from_app,
                        cx.args,
                        cx.modified_locals,
                        cx.stmt_constraints,
                        cx.target,
                    );
                }
                // ptr.add(count) -> *mut T: compute ptr + count * sizeof(T)
                // Part of #3561: consolidated resolve→coerce→emit via helper.
                let definedness = self.ptr_add_definedness_constraints(cx.args, cx.modified_locals);
                let result = self.translate_ptr_add_call(cx.args, cx.modified_locals);
                let result_addr = result.clone();
                let emitted = try_emit_precise_call_result(
                    self,
                    result,
                    dest_local,
                    cx.from_app,
                    cx.target,
                    cx.modified_locals,
                    cx.stmt_constraints,
                    definedness,
                    "codegen_call_ptr_memory::PtrAdd",
                );
                if emitted {
                    if let Some(addr) = result_addr {
                        self.record_known_stack_addr_expr(dest_local, addr, "ptr-add");
                    }
                    self.propagate_ptr_add_result_metadata(dest_local, cx.args, cx.modified_locals);
                } else {
                    self.known_stack_addr_exprs.remove(&dest_local);
                    self.ref_resolution.ref_targets.remove(&dest_local);
                    self.ref_resolution.call_forwarded_raw_ptrs.remove(&dest_local);
                    self.ref_resolution.const_ref_values.remove(&dest_local);
                    self.ref_resolution.subslice_len.remove(&dest_local);
                    self.ref_resolution.subslice_offset.remove(&dest_local);
                }
            }
            // Part of #4156: ptr.sub(count) -> *mut T: compute ptr - count * sizeof(T).
            // Mirror of PtrAdd above but uses translate_ptr_sub_call (bvsub).
            StubKind::PtrSub => {
                if self.extra_pointer_checks {
                    self.emit_ptr_offset_overflow_error_rules(
                        cx.from_app,
                        cx.args,
                        cx.modified_locals,
                        cx.stmt_constraints,
                        cx.target,
                    );
                }
                let result = self.translate_ptr_sub_call(cx.args, cx.modified_locals);
                let emitted = try_emit_precise_call_result(
                    self,
                    result,
                    dest_local,
                    cx.from_app,
                    cx.target,
                    cx.modified_locals,
                    cx.stmt_constraints,
                    [],
                    "codegen_call_ptr_memory::PtrSub",
                );
                if emitted {
                    self.propagate_ptr_sub_result_metadata(dest_local, cx.args, cx.modified_locals);
                } else {
                    self.ref_resolution.ref_targets.remove(&dest_local);
                    self.ref_resolution.call_forwarded_raw_ptrs.remove(&dest_local);
                    self.ref_resolution.const_ref_values.remove(&dest_local);
                    self.ref_resolution.subslice_len.remove(&dest_local);
                    self.ref_resolution.subslice_offset.remove(&dest_local);
                }
            }
            // Part of #3518: wrapping_add/sub use element-sized steps (count * sizeof(T)),
            // NOT byte steps. wrapping_offset also uses element-sized steps (#3510).
            // Consolidated into emit_ptr_wrapping_element_transition.
            StubKind::PtrWrappingAdd | StubKind::PtrWrappingSub | StubKind::PtrWrappingOffset => {
                self.emit_ptr_wrapping_element_transition(cx);
            }
            // Byte-level variants: ptr +/- byte_count (no sizeof(T) scaling).
            StubKind::PtrWrappingByteOffset
            | StubKind::PtrWrappingByteAdd
            | StubKind::PtrWrappingByteSub => {
                self.emit_ptr_wrapping_byte_transition(cx);
            }
            // Part of #3492: with_metadata_of is identity for thin pointers (BV64).
            // Used by map_addr → with_addr → wrapping_byte_offset chain.
            StubKind::PtrWithMetadataOf => {
                let dest_local: usize = cx.destination.local;
                let first_arg = cx
                    .args
                    .first()
                    .and_then(|arg| self.translate_operand_with_modified(arg, cx.modified_locals));
                // Part of #3561: consolidated resolve→coerce→emit via helper.
                try_emit_precise_call_result(
                    self,
                    first_arg,
                    dest_local,
                    cx.from_app,
                    cx.target,
                    cx.modified_locals,
                    cx.stmt_constraints,
                    [],
                    "PtrWithMetadataOf",
                );
            }
            StubKind::PtrWrite => {
                // ptr.write(value): store to memory, destination is () (unit).
                // build_memory_store modifies heap_state type-indexed arrays, so
                // we must rebuild _output_args to propagate store chain state.
                // Using stale _output_args would silently drop the write (#2342).
                let ptr_write_ok = self.translate_ptr_write_call(cx.args, cx.modified_locals);
                if !ptr_write_ok {
                    // Fail-open fallback: keep transition but surface unsoundness
                    // in CHC fallback counters for verdict demotion (#2738).
                    // NOTE: Kept as record_fallback() (DEMOTED) because ptr.write
                    // has heap side effects — partial loss of the write may cause
                    // downstream reads to see stale values.
                    warn!(
                        fn_name = %self.fn_name,
                        "CHC: ptr.write translation failed; emitting fail-open transition with fallback metadata"
                    );
                    self.record_fallback();
                }

                // Part of #3932: Local writeback — if the pointer targets a known
                // stack local, also update the local's state variable so direct
                // reads see the written value instead of the stale pre-write value.
                let mut writeback_locals: Vec<usize> = Vec::new();
                let mut writeback_constraints: Vec<Expr> = Vec::new();
                if ptr_write_ok {
                    if let Some(ptr_local) = cx.args.first().and_then(|a| match a {
                        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
                            Some(p.local)
                        }
                        _ => None,
                    }) {
                        if let Some(target_local) = self.resolve_ptr_write_target_local(ptr_local) {
                            if let Some(value_expr) = self
                                .translate_operand_with_modified(&cx.args[1], cx.modified_locals)
                            {
                                if let Some((_, out_var)) = self.resolve_destination(target_local) {
                                    let out_sort = out_var.sort().clone();
                                    if let Some(eq) = self.make_coerced_eq_constraint(
                                        &out_var,
                                        value_expr.clone(),
                                        &out_sort,
                                        target_local,
                                        "ptr_write_local_writeback",
                                    ) {
                                        writeback_constraints.push(eq);
                                        writeback_locals.push(target_local);
                                        self.encode.local_expr_env.insert(target_local, value_expr);
                                        self.encode.invalidate_local_cache(target_local);
                                        debug!(
                                            target_local,
                                            "CHC: ptr.write local writeback for stack local"
                                        );
                                    }
                                }
                            }
                        }
                    }
                }

                // Call-terminator handlers bypass encode_block_statements, so
                // they must flush heap side effects explicitly. Without this,
                // store chain constraints (arr_out = store(...)) are silently
                // dropped and ptr.write memory stores are unconstrained. (#2905)
                let mut extra_constraints = Vec::new();
                extra_constraints.append(&mut self.heap_state.pending_updates);
                extra_constraints
                    .append(&mut self.heap_state.drain_store_chains(&self.diagnostics));
                extra_constraints.extend(writeback_constraints);
                let pending_checks: Vec<_> = self.heap_state.pending_checks.drain(..).collect();
                for check in pending_checks {
                    self.emit_error_rule_for_condition(
                        cx.from_app,
                        check,
                        cx.stmt_constraints,
                        cx.target, // proxy for bb_idx (diagnostic only)
                    );
                }
                let new_output_args = self.build_output_args(cx.modified_locals, &writeback_locals);
                self.emit_goto_rule_extra(
                    cx.from_app,
                    cx.target,
                    &new_output_args,
                    cx.stmt_constraints,
                    extra_constraints,
                );
            }
            StubKind::PtrRead => {
                // ptr.read() -> T: load from memory
                if let Some(result_expr) = self.translate_ptr_read_call(cx.args, cx.modified_locals)
                {
                    // load_from_memory pushes heap validity/bounds checks into
                    // pending_checks. Call-terminator handlers bypass
                    // encode_block_statements, so flush them here. (#2905)
                    let pending_checks: Vec<_> = self.heap_state.pending_checks.drain(..).collect();
                    for check in pending_checks {
                        self.emit_error_rule_for_condition(
                            cx.from_app,
                            check,
                            cx.stmt_constraints,
                            cx.target, // proxy for bb_idx (diagnostic only)
                        );
                    }

                    // Part of #3182: check for flattened destination first.
                    if let Some(flat_constraints) = self
                        .build_flattened_destination_constraints(dest_local, result_expr.clone())
                    {
                        let new_output_args =
                            self.build_output_args(cx.modified_locals, &[dest_local]);
                        self.emit_goto_rule_extra(
                            cx.from_app,
                            cx.target,
                            &new_output_args,
                            cx.stmt_constraints,
                            flat_constraints,
                        );
                    } else {
                        // Part of #3561: consolidated resolve→coerce→emit via helper.
                        try_emit_precise_call_result(
                            self,
                            Some(result_expr),
                            dest_local,
                            cx.from_app,
                            cx.target,
                            cx.modified_locals,
                            cx.stmt_constraints,
                            [],
                            "codegen_call_ptr_memory::PtrRead",
                        );
                    }
                } else {
                    // Fail-open fallback: couldn't load, destination unconstrained.
                    // Surface in CHC fallback counters for verdict demotion (#2744).
                    warn!(
                        fn_name = %self.fn_name,
                        "CHC: ptr.read translation failed; emitting unconstrained transition with fallback metadata"
                    );
                    emit_sound_fallback_goto(
                        self,
                        cx.from_app,
                        cx.target,
                        cx.modified_locals,
                        &[dest_local],
                        cx.stmt_constraints,
                    );
                }
            }
            // All is_ptr_memory() variants (PtrAdd, PtrSub, PtrWrite, PtrRead) are matched
            // above. Caller pre-filters via stub.is_ptr_memory().
            other => {
                // SOUND AUDIT (#3369): unknown stub effects — reclassified from
                // record_sound_fallback to record_fallback since this catch-all
                // handles operations with unknown side effects (e.g., future
                // PtrWriteVolatile). Defensive DEMOTED classification.
                warn!(?other, "codegen_call_ptr_memory: unexpected stub — update routing");
                self.record_fallback();
                let new_output_args = self.build_output_args(cx.modified_locals, &[]);
                self.emit_goto_rule(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints);
            }
        }
    }

    /// Handle pointer/NonZero utility stubs (#1979).
    fn codegen_call_pointer_utility(&mut self, cx: &ChcCallContext<'_>) {
        let dest_local: usize = cx.destination.local;
        debug!("pointer_utility_stub stub={:?} has_target=true dest={}", cx.stub, dest_local);
        // Part of #9185: inlined std pointer construction can consume the call
        // destination in CHC memory/aggregate lowering in the target block even
        // when MIR StorageDead markers make the local appear dead at block entry.
        // Keep the destination threaded so the generated constraints do not
        // reintroduce it as an unconstrained free variable.
        self.ensure_local_live_at_block(dest_local, cx.target);
        if let Some(result_expr) =
            self.translate_pointer_utility_call(cx.stub, cx.args, cx.modified_locals)
        {
            let forwarded_nonnull = matches!(cx.stub, StubKind::NonNullAsPtr);
            let src_local = cx.args.first().and_then(|arg| match arg {
                Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                    Some(place.local)
                }
                _ => None,
            });
            if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                // NonZeroGet: add nonzero guard before coercion (guard uses original sort)
                let nonzero_guard: Option<Expr> = if cx.stub == StubKind::NonZeroGet
                    && let Some(width) = result_expr.sort().bitvec_width()
                {
                    debug!("pointer_utility_stub NonZeroGet adds nonzero guard width={}", width);
                    Some(result_expr.clone().ne(Expr::bitvec_const(0, width)))
                } else {
                    None
                };
                // Part of #3470: CharFromU32Unchecked encodes the precondition that the
                // input u32 is a valid Unicode scalar value: [0, 0xD7FF] ∪ [0xE000, 0x10FFFF].
                // This replaces the broken kani::assume(RangeBounds::contains) chain where
                // RangeBounds::contains becomes an uninterpreted function.
                let char_validity_guard: Option<Expr> = if cx.stub == StubKind::CharFromU32Unchecked
                {
                    if let Some(width) = result_expr.sort().bitvec_width() {
                        let v = result_expr.clone();
                        let low = v.clone().bvule(Expr::bitvec_const(0xD7FFu64, width));
                        let hi_lo = v.clone().bvuge(Expr::bitvec_const(0xE000u64, width));
                        let hi_hi = v.bvule(Expr::bitvec_const(0x10FFFFu64, width));
                        debug!(
                            "pointer_utility_stub CharFromU32Unchecked validity guard BV{}",
                            width
                        );
                        Some(low.or(hi_lo.and(hi_hi)))
                    } else if result_expr.sort().is_int() {
                        let v = result_expr.clone();
                        let low = v.clone().int_le(Expr::int_const(0xD7FFi64));
                        let hi_lo = v.clone().int_ge(Expr::int_const(0xE000i64));
                        let hi_hi = v.int_le(Expr::int_const(0x10FFFFi64));
                        debug!("pointer_utility_stub CharFromU32Unchecked validity guard Int");
                        Some(low.or(hi_lo.and(hi_hi)))
                    } else {
                        None
                    }
                } else {
                    None
                };
                if let Some(eq) = self.make_coerced_eq_constraint(
                    &dest_var,
                    result_expr.clone(),
                    dest_var.sort(),
                    dest_local,
                    "codegen_call_pointer_utility",
                ) {
                    if forwarded_nonnull {
                        let mut forwarded_ref_target = false;
                        // Part of #4101: Try direct ref_target lookup on src_local.
                        if let Some(src_local) = src_local {
                            if let Some(ref_target) =
                                self.ref_resolution.ref_targets.get(&src_local).cloned()
                            {
                                self.ref_resolution.ref_targets.insert(dest_local, ref_target);
                                forwarded_ref_target = true;
                            }

                            if let Some(obj_id) = self.known_alloc_ids.get(&src_local).copied() {
                                self.known_alloc_ids.insert(dest_local, obj_id);
                            } else {
                                self.known_alloc_ids.remove(&dest_local);
                            }
                        } else {
                            self.known_alloc_ids.remove(&dest_local);
                        }
                        // Part of #4101: Fallback — resolve via obj_id even when
                        // src_local is None (field-projected arg, e.g.,
                        // `container.ptr.as_ptr()` where the NonNull is stored
                        // inside a struct field). The pointer BV value from
                        // translate_operand is correct; only ref_target linkage
                        // was lost at the field boundary.
                        if !forwarded_ref_target {
                            if let Some(obj_id) = ChcCtx::try_extract_obj_id(&result_expr)
                                && let Some(owning_local) =
                                    self.heap_state.local_idx_for_obj_id(obj_id)
                            {
                                self.ref_resolution.ref_targets.insert(
                                    dest_local,
                                    RefTarget::with_projections(owning_local, vec![]),
                                );
                                forwarded_ref_target = true;
                            }
                        }

                        if forwarded_ref_target {
                            self.ref_resolution.call_forwarded_raw_ptrs.insert(dest_local);
                        } else {
                            self.ref_resolution.ref_targets.remove(&dest_local);
                            self.ref_resolution.call_forwarded_raw_ptrs.remove(&dest_local);
                        }

                        if let Some(arg) = cx.args.first() {
                            if let Some(inner_value) =
                                self.resolve_ref_or_const_referent_impl(arg, cx.modified_locals)
                            {
                                self.ref_resolution
                                    .const_ref_values
                                    .insert(dest_local, inner_value);
                            } else {
                                self.ref_resolution.const_ref_values.remove(&dest_local);
                            }
                        }
                    }
                    let new_output_args = self.build_output_args(cx.modified_locals, &[dest_local]);
                    self.emit_goto_rule_extra(
                        cx.from_app,
                        cx.target,
                        &new_output_args,
                        cx.stmt_constraints,
                        nonzero_guard.into_iter().chain(char_validity_guard).chain([eq]),
                    );
                } else {
                    warn!(
                        fn_name = %self.fn_name,
                        "CHC: pointer utility coercion failed; emitting unconstrained transition with fallback metadata"
                    );
                    if forwarded_nonnull {
                        self.ref_resolution.ref_targets.remove(&dest_local);
                        self.ref_resolution.call_forwarded_raw_ptrs.remove(&dest_local);
                        self.ref_resolution.const_ref_values.remove(&dest_local);
                        self.known_alloc_ids.remove(&dest_local);
                    }
                    emit_sound_fallback_goto(
                        self,
                        cx.from_app,
                        cx.target,
                        cx.modified_locals,
                        &[dest_local],
                        cx.stmt_constraints,
                    );
                }
            } else {
                warn!(
                    fn_name = %self.fn_name,
                    "CHC: pointer utility missing destination output state; emitting unconstrained transition with fallback metadata"
                );
                if forwarded_nonnull {
                    self.ref_resolution.ref_targets.remove(&dest_local);
                    self.ref_resolution.call_forwarded_raw_ptrs.remove(&dest_local);
                    self.ref_resolution.const_ref_values.remove(&dest_local);
                    self.known_alloc_ids.remove(&dest_local);
                }
                emit_sound_fallback_goto(
                    self,
                    cx.from_app,
                    cx.target,
                    cx.modified_locals,
                    &[dest_local],
                    cx.stmt_constraints,
                );
            }
        } else {
            // SOUND AUDIT (#3369): sound for most stubs (NonNullAsPtr, NonZeroGet,
            // PtrAddr, PtrIsNull). For PtrNull, translate failure would lose
            // obj_valid invalidation (under-approx), but PtrNull returns a constant
            // zero and cannot fail in practice. Accepted as sound.
            warn!(
                fn_name = %self.fn_name,
                "CHC: pointer utility translation failed; emitting unconstrained transition with fallback metadata"
            );
            if matches!(cx.stub, StubKind::NonNullAsPtr) {
                self.ref_resolution.ref_targets.remove(&dest_local);
                self.ref_resolution.call_forwarded_raw_ptrs.remove(&dest_local);
                self.ref_resolution.const_ref_values.remove(&dest_local);
                self.known_alloc_ids.remove(&dest_local);
            }
            emit_sound_fallback_goto(
                self,
                cx.from_app,
                cx.target,
                cx.modified_locals,
                &[dest_local],
                cx.stmt_constraints,
            );
        }
    }

    /// Handle lowered `std::ptr::copy_nonoverlapping` call terminators.
    ///
    /// Some MIR paths emit this as a call terminator instead of
    /// `StatementKind::Intrinsic(CopyNonOverlapping)`. Reuse the intrinsic
    /// modeling path so destination arrays receive guarded store updates.
    ///
    /// P4-1: `allow_overlap` selects the legal-overlap `copy` (memmove)
    /// variant — it suppresses only the range-disjointness obligation.
    fn codegen_call_copy_nonoverlapping(
        &mut self,
        bb_idx: usize,
        cx: &ChcCallContext<'_>,
        allow_overlap: bool,
    ) {
        if cx.args.len() < 3 {
            warn!(
                fn_name = %self.fn_name,
                arg_count = cx.args.len(),
                "CHC: copy_nonoverlapping call missing args; emitting unconstrained transition with fallback metadata"
            );
            // Part of #3369: Reclassified to DEMOTED — copy_nonoverlapping has
            // memory side effects. Without encoding, destination memory retains its
            // previous value (identity) instead of becoming nondeterministic. This
            // can cause false PROOFs when assertions depend on copied values.
            self.record_fallback();
            let new_output_args = self.build_output_args(cx.modified_locals, &[]);
            self.emit_goto_rule(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints);
            return;
        }

        let copy = rustc_public::mir::CopyNonOverlapping {
            src: cx.args[0].clone(),
            dst: cx.args[1].clone(),
            count: cx.args[2].clone(),
        };

        // Part of #2486: collect extras instead of stmt_constraints.to_vec().
        let mut extra_constraints: Vec<Expr> = Vec::new();
        let mut modified = cx.modified_locals.clone();
        let mut last_constraint_for_local: HashMap<usize, usize> =
            HashMap::with_capacity(self.body.locals().len());

        let handled = {
            let mut acc = StmtAccumulator::new(
                &mut modified,
                &mut extra_constraints,
                &mut last_constraint_for_local,
            );
            self.try_encode_copy_nonoverlapping_intrinsic(&copy, bb_idx, &mut acc, allow_overlap)
        };

        // Call terminators bypass the statement-level pending_checks drain
        // (codegen_stmt/mod.rs) — emit the copy UB obligations (span bounds /
        // alignment / overlap) staged by the encoder here.
        if self.memory_safety_checks {
            for check in self.heap_state.pending_checks.drain(..).collect::<Vec<_>>() {
                // Tag only the precise, provenance-independent span checks
                // (alignment / count-overflow / allocation-bound) as eligible
                // for the offset-provenance discharge — NOT the disjointness
                // obligation (spurious for the legal-overlap `copy` variant).
                let eligible = self.diagnostics.span_check_exprs.contains(&check);
                let id_before = self.vc.properties.len();
                self.emit_error_rule_for_condition(
                    cx.from_app,
                    check,
                    cx.stmt_constraints,
                    cx.target,
                );
                if eligible && self.vc.properties.len() == id_before + 1 {
                    self.diagnostics.intrinsic_span_property_ids.push(id_before as u32);
                }
            }
        } else {
            self.heap_state.pending_checks.clear();
        }

        if handled {
            let new_output_args = self.build_output_args(&modified, &[]);
            self.emit_goto_rule_extra(
                cx.from_app,
                cx.target,
                &new_output_args,
                cx.stmt_constraints,
                extra_constraints,
            );
        } else {
            // Fail-open fallback: unresolved copy_nonoverlapping leaves destination
            // memory unconstrained (over-approximation). Transition still emitted
            // so control flow continues, but memory contents are nondet.
            // Surface in CHC fallback counters for verdict demotion (#2754).
            warn!(
                fn_name = %self.fn_name,
                "CHC: copy_nonoverlapping unresolved; emitting unconstrained transition with fallback metadata"
            );
            // Part of #3369: Reclassified to DEMOTED — copy_nonoverlapping has
            // memory side effects. Destination memory is unchanged (identity)
            // rather than nondeterministic, which can cause false PROOFs.
            self.record_fallback();
            let new_output_args = self.build_output_args(&modified, &[]);
            self.emit_goto_rule(cx.from_app, cx.target, &new_output_args, cx.stmt_constraints);
        }
    }

    /// Handle `mem::size_of::<T>` / `mem::align_of::<T>` intrinsic stubs (Part of #2196).
    fn codegen_call_mem_intrinsic(&mut self, func: &Operand, cx: &ChcCallContext<'_>) {
        let dest_local: usize = cx.destination.local;
        debug!("mem_intrinsic_stub stub={:?} dest={}", cx.stub, dest_local);
        // Part of #3655: For size_of_val_raw on unsized types (str, [T]),
        // compute the dynamic size from fat pointer metadata instead of using
        // the element size. translate_mem_intrinsic_call returns the element
        // size (1 for str, sizeof(T) for [T]) via get_type_size(), which is
        // correct for heap access checks but wrong for dealloc Layout where
        // the total allocation size (elem_size * len) is needed.
        if cx.stub == StubKind::MemSizeOf {
            if let Some(result_expr) =
                Self::try_unsized_size_of_val_raw(self, func, cx.args, cx.modified_locals)
            {
                if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                    if let Some(eq) = self.make_coerced_eq_constraint(
                        &dest_var,
                        result_expr,
                        dest_var.sort(),
                        dest_local,
                        "codegen_call_mem_intrinsic_unsized",
                    ) {
                        let new_output_args =
                            self.build_output_args(cx.modified_locals, &[dest_local]);
                        self.emit_goto_rule_extra(
                            cx.from_app,
                            cx.target,
                            &new_output_args,
                            cx.stmt_constraints,
                            [eq],
                        );
                        return;
                    }
                }
            }
        }
        // Part of #3561: consolidated resolve→coerce→emit via helper.
        let result = self.translate_mem_intrinsic_call(cx.stub, func);
        if let Some(result_expr) = result.as_ref()
            && matches!(result_expr.value(), ExprValue::BitVecConst { .. })
            && self.encode.single_assign_locals.contains(&dest_local)
        {
            self.encode.const_folded_call_results.insert(dest_local, result_expr.clone());
        }
        try_emit_precise_call_result(
            self,
            result,
            dest_local,
            cx.from_app,
            cx.target,
            cx.modified_locals,
            cx.stmt_constraints,
            [],
            "codegen_call_mem_intrinsic",
        );
    }
    // Pointer identity/passthrough ops extracted to codegen_call_ptr_identity.rs per #3199.
}
