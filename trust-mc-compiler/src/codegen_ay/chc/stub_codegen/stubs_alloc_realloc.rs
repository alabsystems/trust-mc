// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC heap reallocation implementation.
//!
//! Extracted from `stubs_alloc_heap_ops.rs` — Part of #4206.

use std::collections::HashSet;

use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::Operand;
use tracing::{debug, warn};

use super::types::POINTER_WIDTH;
use super::{AllocCallResult, ChcCtx, codegen_expr_heap};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Translate `__rust_realloc` to CHC constraints.
    ///
    /// Supports both realloc ABIs:
    /// - `__rust_realloc(ptr, old_size, align, new_size)`
    /// - `std::alloc::realloc(ptr, layout, new_size)`
    ///
    /// Uses nondeterministic model (Part of #2425): a fresh boolean
    /// `realloc_moved` lets the CHC solver explore both in-place growth
    /// and move-to-new-allocation paths.
    pub(in crate::codegen_ay::chc) fn translate_rust_realloc(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<AllocCallResult> {
        // Address-vs-value: which argument is the OLD POINTER is read off the
        // Rust types in MIR (see `allocator_pointer_arg_idx`), never off a width.
        //
        // The retired test asked `bitvec_width() == POINTER_WIDTH` of arg[0] and
        // then of arg[1], with only a `Ref` veto above it. Both questions are
        // unanswerable that way: a `&self` allocator receiver, a `*mut u8` and a
        // `usize` size are all `bv64`. Picking the wrong arm does not merely
        // misname the pointer that realloc's move/free model is built on — it
        // shifts the whole `(old_size, align, new_size)` window with it, so the
        // size-mismatch and alignment obligations are then asserted about the
        // wrong operands as well.
        let Some(ptr_arg_idx) = self.allocator_pointer_arg_idx(args) else {
            warn!(
                "RustRealloc: no pointer-typed argument in MIR; falling back to unconstrained call"
            );
            self.record_sound_fallback_reason("realloc_pointer_arg_unresolved");
            return None;
        };
        let size_start = ptr_arg_idx + 1;
        let old_ptr_expr = args
            .get(ptr_arg_idx)
            .and_then(|arg| self.translate_operand_with_modified(arg, modified_locals));

        let raw_old_size_or_layout_expr = args
            .get(size_start)
            .and_then(|arg| self.resolve_layout_operand_expr(arg, modified_locals));
        let raw_align_or_new_size_expr = args
            .get(size_start + 1)
            .and_then(|arg| self.resolve_layout_operand_expr(arg, modified_locals));
        let raw_new_size_expr = args
            .get(size_start + 2)
            .and_then(|arg| self.resolve_layout_operand_expr(arg, modified_locals));

        let (old_size_expr, align_expr, new_size_expr) = if let Some((layout_size, layout_align)) =
            raw_old_size_or_layout_expr.clone().and_then(Self::extract_layout_size_align)
        {
            // Part of #3841: Same concrete-layout recovery as translate_rust_alloc.
            let (layout_size, layout_align) =
                if !matches!(layout_size.value(), ExprValue::BitVecConst { .. }) {
                    if let Some(layout_arg) = args.get(size_start) {
                        if let Some((s, a)) = self.trace_arg_to_layout_pair(layout_arg) {
                            debug!(
                                size = s,
                                align = a,
                                "translate_rust_realloc: recovered concrete layout from trace"
                            );
                            (
                                Expr::bitvec_const(s as u128, POINTER_WIDTH),
                                Expr::bitvec_const(a as u128, POINTER_WIDTH),
                            )
                        } else {
                            (layout_size, layout_align)
                        }
                    } else {
                        (layout_size, layout_align)
                    }
                } else {
                    (layout_size, layout_align)
                };
            let Some(new_size_expr) = raw_align_or_new_size_expr else {
                warn!(
                    "RustRealloc: failed to resolve new_size argument from layout ABI; falling back to unconstrained call"
                );
                self.record_sound_fallback_reason("realloc_new_size_layout_unresolved");
                return None;
            };
            (layout_size, layout_align, new_size_expr)
        } else {
            let Some(old_size_expr) = raw_old_size_or_layout_expr else {
                warn!(
                    "RustRealloc: failed to resolve old_size argument; falling back to unconstrained call"
                );
                self.record_sound_fallback_reason("realloc_old_size_unresolved");
                return None;
            };
            let Some(align_expr) = raw_align_or_new_size_expr else {
                warn!(
                    "RustRealloc: failed to resolve align argument; falling back to unconstrained call"
                );
                self.record_sound_fallback_reason("realloc_align_unresolved");
                return None;
            };
            let Some(new_size_expr) = raw_new_size_expr else {
                warn!(
                    "RustRealloc: failed to resolve new_size argument; falling back to unconstrained call"
                );
                self.record_sound_fallback_reason("realloc_new_size_unresolved");
                return None;
            };
            (old_size_expr, align_expr, new_size_expr)
        };
        let Some(new_size_32) = self.coerce_to_heap_bv32(new_size_expr.clone()) else {
            warn!(
                sort = ?new_size_expr.sort(),
                "RustRealloc: new_size expression is not a bitvec; falling back to unconstrained call"
            );
            self.record_sound_fallback_reason("realloc_size_bv32_coercion_failed");
            return None;
        };

        // Part of #2425: Nondeterministic realloc model.
        let new_obj_id = self.heap_state.next_heap_alloc_id().or_else(|| {
            warn!("RustRealloc: allocation ID overflow; falling back to unconstrained call");
            self.record_sound_fallback_reason("realloc_id_overflow");
            None
        })?;

        // Fix #2553: Split the raw old pointer once to recover a direct concrete
        // obj_id when available. The moved-branch copy path may later replace the
        // pointer with a canonical heap address after MIR tracing resolves the
        // allocation ID.
        let raw_old_split = old_ptr_expr.as_ref().and_then(|ptr| self.split_pointer(ptr));
        let old_concrete_id =
            raw_old_split.as_ref().and_then(|(obj_id_expr, _)| Self::const_obj_id_u32(obj_id_expr));
        // Part of #3273: When the expression-level extraction fails (symbolic CHC
        // variable), trace the pointer operand through MIR assignments back to the
        // original alloc result local to recover the concrete obj_id.
        let old_id_resolved = old_concrete_id
            .or_else(|| args.get(ptr_arg_idx).and_then(|arg| self.trace_arg_to_alloc_id(arg)));
        if let Some(old_id) = old_id_resolved {
            self.heap_state.alias_region(old_id, new_obj_id);
            // Fix #3677: If the old region was upgraded from bv8 to a typed
            // sort (e.g., bv32 by ptr.write), alias_region only copies the
            // current entry — which might still be bv8 if the upgrade created
            // a new entry for old_id but didn't propagate to the alias.
            // Force the new region to match the old region's current sort so
            // the load path finds the correct typed region variable.
            if let Some((_, _, old_sort)) = self.heap_state.get_region_array(old_id) {
                if old_sort.bitvec_width() != Some(8) {
                    let _ = self.assign_region_array_to_relation(new_obj_id, old_sort);
                }
            }
        } else {
            // Symbolic old pointer: fall back to most-recent heuristic.
            tracing::warn!(
                new_obj_id,
                "realloc: old pointer obj_id is symbolic; falling back to most-recent-region heuristic"
            );
            self.heap_state.alias_most_recent_region(new_obj_id);
        }
        let canonical_old_ptr_expr = old_id_resolved
            .map(|old_id| Expr::bitvec_const(old_id as i128, 32).concat(Expr::bitvec_const(0, 32)));
        let copy_old_ptr_expr = canonical_old_ptr_expr.clone().or(old_ptr_expr.clone());
        // Capture the raw caller-supplied old pointer before it is consumed by
        // `result_old_ptr_expr`, for the unconditional non-null check below.
        let raw_old_ptr_for_null_check = old_ptr_expr.clone();
        let result_old_ptr_expr = old_ptr_expr.or(canonical_old_ptr_expr);
        let old_split = copy_old_ptr_expr.as_ref().and_then(|ptr| self.split_pointer(ptr));

        let obj_valid_in = codegen_expr_heap::obj_valid_in();
        let obj_valid_out = codegen_expr_heap::obj_valid_out();
        let obj_size_in = codegen_expr_heap::obj_size_in();
        let obj_size_out = codegen_expr_heap::obj_size_out();

        let mut heap_constraints = Vec::new();
        let mut safety_checks = Vec::new();

        // Safety checks on arguments.
        safety_checks.extend(self.fits_in_bv32_check(&old_size_expr));
        safety_checks.extend(self.fits_in_bv32_check(&new_size_expr));
        safety_checks.extend(self.nonzero_bv_check(new_size_expr, 64));
        safety_checks.extend(self.power_of_two_bv_check(align_expr.clone(), POINTER_WIDTH));
        safety_checks.extend(self.nonzero_bv_check(align_expr, 64));

        // Kani: "rust_realloc must be called with a non-null pointer". A null
        // old pointer resolves to obj_id 0, whose entry-rule defaults
        // (obj_valid[0]=true, obj_size[0]=0) make every downstream valid/size
        // check vacuously pass, so realloc(null, ..) would be proved SAFE.
        // Emitted unconditionally (not only in the splittable-pointer branch)
        // so a null old_ptr is caught even when it does not split into a
        // tracked obj_id. (realloc/null false proof.)
        if let Some(raw_old_ptr) = raw_old_ptr_for_null_check {
            if let Some(width) = raw_old_ptr.sort().bitvec_width() {
                safety_checks.push(raw_old_ptr.ne(Expr::bitvec_const(0, width)));
            }
        }

        // Build nondeterministic model when we have a splittable old pointer
        if let Some(ref old_ptr) = copy_old_ptr_expr
            && let Some((old_obj_id_expr, offset_expr)) = old_split
        {
            // Check old pointer is valid
            let is_old_valid = obj_valid_in.clone().select(old_obj_id_expr.clone());
            safety_checks.push(is_old_valid);

            // Require base pointer (offset == 0). Preserve the raw offset check
            // when it is available so caller-side interior-pointer misuse still
            // hits the safety path even if the copy source was canonicalized.
            let offset_to_check = raw_old_split
                .as_ref()
                .map(|(_, raw_offset_expr)| raw_offset_expr.clone())
                .unwrap_or(offset_expr);
            safety_checks.push(offset_to_check.eq(Expr::bitvec_const(0, 32)));

            // Part of #2785: Validate caller's old_size matches recorded allocation size,
            // analogous to dealloc size-mismatch check (line 236). Without this, a buggy
            // caller passing wrong old_size to realloc is not flagged as a safety violation.
            if let Some(old_size_32) = self.coerce_to_heap_bv32(old_size_expr.clone()) {
                let size_matches =
                    obj_size_in.clone().select(old_obj_id_expr.clone()).eq(old_size_32);
                safety_checks.push(size_matches);
            }

            // #3728: Always model realloc as "moved" — old allocation invalidated,
            // data copied to a fresh allocation. The in-place branch (old pointer
            // stays valid) is removed because Z3 PDR's invariant synthesis over
            // array-valued disjunctions infers obj_valid = ALL_TRUE, producing a
            // false proof. Always-moved is a sound over-approximation: any program
            // that is safe when realloc always moves is also safe when it sometimes
            // stays in-place. The worst case is false CTREX for code that relies on
            // in-place growth, never false PROOF.
            let new_obj_id_expr = Expr::bitvec_const(new_obj_id as i128, 32);
            let new_ptr =
                Expr::bitvec_const(new_obj_id as i128, 32).concat(Expr::bitvec_const(0, 32));

            // Part of #3677: Store-chain encoding for obj_valid. The previous
            // pointwise SELECT encoding (#3728) iterated known_alloc_ids for
            // frame conditions, but that map only tracks dynamic alloc calls —
            // it misses pre-existing stack/static allocations from the entry
            // rule. The solver exploited the unconstrained gap to set
            // obj_valid_out[pre_existing_id] = false, triggering false CTREX.
            //
            // Store-chain provides an implicit frame for ALL indices:
            //   obj_valid_out = store(store(obj_valid_in, old, false), new, true)
            // The #3728 concern about PDR was about ITE over array-valued
            // disjunctions (in-place vs moved), which the always-moved model
            // already eliminates. A 2-deep store chain is within PDR's
            // lemma generalization capabilities.
            let obj_valid_updated = obj_valid_in
                .store(old_obj_id_expr, Expr::bool_const(false))
                .store(new_obj_id_expr.clone(), Expr::bool_const(true));
            heap_constraints.push(obj_valid_out.eq(obj_valid_updated));

            // obj_size uses store-based encoding (frame implicit in Array
            // store semantics). obj_size doesn't cause false proofs since
            // safety checks use obj_valid for the critical reachability query.
            self.record_known_heap_alloc_size_expr(new_obj_id, &new_size_32);
            let size_moved = obj_size_in.store(new_obj_id_expr, new_size_32);
            heap_constraints.push(obj_size_out.eq(size_moved));

            // Part of #3273: Resolve concrete old_size through MIR tracing.
            let layout_concrete_old_size = args
                .get(size_start)
                .and_then(|arg| {
                    if let Operand::Copy(place) | Operand::Move(place) = arg {
                        self.known_layout_sizes.get(&place.local).map(|(size, _)| *size as usize)
                    } else {
                        None
                    }
                })
                .or_else(|| self.trace_arg_to_layout_size(args.get(size_start)?));
            self.add_always_moved_realloc_copy_constraints(
                old_ptr.clone(),
                new_ptr.clone(),
                old_size_expr,
                layout_concrete_old_size,
                &mut heap_constraints,
            );

            // Mark metadata arrays as modified
            self.mark_heap_metadata_modified();

            debug!(new_obj_id, "CHC: RustRealloc - always-moved model (#3728)");

            Some(AllocCallResult {
                result: Some(new_ptr),
                heap_constraints,
                safety_checks,
                alloc_obj_id: Some(new_obj_id),
                transition_branches: Vec::new(),
            })
        } else {
            debug!("CHC: RustRealloc - old pointer not splittable, in-place fallback");
            // Cannot split old pointer — fall back to returning the best available
            // old-pointer expression
            // with just size update (best effort).
            Some(AllocCallResult {
                result: result_old_ptr_expr,
                heap_constraints,
                safety_checks,
                alloc_obj_id: None,
                transition_branches: Vec::new(),
            })
        }
    }
}
