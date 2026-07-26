// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Vec residual mutation operation leaf handlers.
//!
//! Covers operations that previously fell through to the `other` arm in
//! `codegen_call_vec_core` with a warning + identity fallback. Each handler
//! provides a sound CHC abstraction of the operation's effect on Vec state
//! (length, capacity, data).
//!
//! Semantics summary:
//! - **VecSort/VecReverse/VecSwap**: permutation — preserves len, data unconstrained.
//! - **VecAppend**: `self.len += src.len`, `src.len = 0`.
//! - **VecTruncate**: `len = min(len, new_len)`.
//! - **VecInsert**: `len += 1`.
//! - **VecRemove**: `len -= 1`, returns removed element (unconstrained).
//! - **VecRetain/VecDedup**: `len' <= len` (some elements removed).
//! - **VecDrain**: `len -= drained_count` (range removed).
//! - **VecSplitOff**: `self.len = at`, new vec has `old_len - at`.
//! - **VecSplice**: range replaced; len changes by `(replacement_count - range_len)`.
//! - **VecLast**: returns Option of last element (query, no mutation).
//!
//! Part of #4135: Vec residual extend/sort/append leaf handlers.

use std::collections::HashSet;

use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::Expr;
use rustc_public::mir::Operand;
use tracing::debug;

use super::ChcCtx;

/// Maximum number of moved source elements unrolled into `store` constraints by
/// `vec_op_append` when the source length is a concrete constant. Beyond this,
/// the data array is left as the sound unconstrained over-approximation. Part
/// of Fix 4.
const MAX_APPEND_MOVE_ELEMS: usize = 16;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// VecSort/VecReverse/VecSwap: permutation operations.
    ///
    /// Length and capacity are preserved. Data contents are left unconstrained
    /// (sound over-approximation: the solver considers all possible element
    /// orderings, which includes the correct sorted/reversed/swapped order).
    pub(in crate::codegen_ay::chc) fn vec_op_permutation(
        &mut self,
        collection_local: Option<usize>,
        label: &str,
    ) {
        // Permutation preserves len and cap — no sidecar update needed.
        // Data array is left unconstrained (identity on state vars).
        debug!(
            fn_name = %self.fn_name,
            ?collection_local,
            label,
            "Vec permutation op: len/cap preserved, data unconstrained"
        );
    }

    /// VecAppend: `self.append(&mut other)`.
    ///
    /// Moves all elements from `other` into `self`. After the call:
    /// - `self.len = self.len + other.len`
    /// - `other.len = 0`
    /// - `self.cap >= self.len` (may grow)
    /// - Data contents unconstrained (sound over-approximation).
    pub(in crate::codegen_ay::chc) fn vec_op_append(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        collection_local: Option<usize>,
        // Fix 4: the source Vec's concrete literal element values, captured from
        // `adapter_source_data` BEFORE the append call invalidates it (see
        // `codegen_call_vec.rs`). `Some` only when the source was built from a
        // compile-time-known literal (e.g. `vec![3]`); `None` otherwise.
        src_concrete_elems: Option<&[Expr]>,
        acc: &mut CallAccumulator<'_>,
    ) {
        let Some(self_local) = collection_local else {
            self.record_sound_fallback_reason("vec_append_no_self_local");
            return;
        };
        let Some(self_len_var) = self.collections.len_state.get_len_var(self_local).cloned() else {
            self.record_sound_fallback_reason("vec_append_no_self_len");
            return;
        };
        let self_old_len = self.collection_current_len(&self_len_var);

        // Resolve other's collection local from args[1].
        let other_local = args.get(1).and_then(|op| match op {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        });

        // Try to resolve other's ref target for length lookup.
        let other_resolved = other_local
            .and_then(|l| self.ref_resolution.ref_targets.get(&l).map(|rt| rt.local).or(Some(l)));

        let other_len_var =
            other_resolved.and_then(|l| self.collections.len_state.get_len_var(l).cloned());

        let other_len = other_len_var.as_ref().map(|v| self.collection_current_len(v));

        if let Some(ref src_len) = other_len {
            // self.len = self.len + other.len
            let new_self_len = self_old_len.clone().bvadd(src_len.clone());
            // Guard against unsigned overflow
            acc.constraints.push(new_self_len.clone().bvuge(self_old_len.clone()));
            self.collection_len_set(&self_len_var, new_self_len.clone(), acc);

            // Capacity growth: cap = max(cap, new_len).
            if let Some(cap_var) = self.collections.len_state.get_cap_var(self_local).cloned() {
                let old_cap = self.collection_current_cap(&cap_var);
                let grow_needed = old_cap.clone().bvult(new_self_len.clone());
                let new_cap = Expr::ite(grow_needed, new_self_len.clone(), old_cap);
                self.collection_cap_set(&cap_var, new_cap.clone(), acc);
                Self::emit_cap_ge_len(new_cap, new_self_len, acc.constraints);
            }

            // other.len = 0
            if let Some(ref other_lv) = other_len_var {
                self.collection_len_set(other_lv, Expr::bitvec_const(0u64, POINTER_WIDTH), acc);
            }

            // Fix 4: when the source was built from a compile-time-known literal
            // (its concrete element values were captured before this call
            // invalidated the adapter source data), store the MOVED element
            // VALUES into self's data array so reads of the appended slots
            // (`self[self_old_len + i]`) return the real moved values instead of
            // the construction fill. `append` moves ALL of other's elements, and
            // `src_concrete_elems` are exactly those values in order. This adds
            // only genuine facts, tightening the sound over-approximation.
            // Anything without a concrete literal source keeps the unconstrained
            // data model (do not store) — sound.
            if let Some(elems) = src_concrete_elems
                && (1..=MAX_APPEND_MOVE_ELEMS).contains(&elems.len())
            {
                self.vec_store_appended_elements(
                    self_local,
                    &self_old_len,
                    elems,
                    modified_locals,
                    acc,
                );
            }

            debug!(
                fn_name = %self.fn_name,
                self_local,
                ?other_resolved,
                "VecAppend: self.len += other.len, other.len = 0"
            );
        } else {
            // Cannot resolve other's length — leave self.len unconstrained
            // (sound over-approximation).
            debug!(
                fn_name = %self.fn_name,
                self_local,
                ?other_local,
                "VecAppend: other length unresolved — fallback"
            );
            self.record_sound_fallback_reason("vec_append_other_len_unresolved");
        }
    }

    /// VecTruncate: `self.truncate(new_len)`.
    ///
    /// If `new_len < self.len`, length is set to `new_len`. Otherwise no-op.
    /// Data contents beyond `new_len` are logically dropped (unconstrained in model).
    pub(in crate::codegen_ay::chc) fn vec_op_truncate(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        collection_local: Option<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        let Some(coll_local) = collection_local else {
            self.record_sound_fallback_reason("vec_truncate_no_local");
            return;
        };
        let Some(len_var) = self.collections.len_state.get_len_var(coll_local).cloned() else {
            self.record_sound_fallback_reason("vec_truncate_no_len");
            return;
        };

        let new_len_arg =
            args.get(1).and_then(|a| self.translate_operand_with_modified(a, modified_locals));

        let Some(new_len_arg) = new_len_arg else {
            debug!(
                fn_name = %self.fn_name,
                "VecTruncate: could not translate new_len argument"
            );
            self.record_sound_fallback_reason("vec_truncate_no_new_len");
            return;
        };

        let old_len = self.collection_current_len(&len_var);
        // new_len = min(old_len, new_len_arg)
        // = ite(old_len < new_len_arg, old_len, new_len_arg)
        let truncated = old_len.clone().bvult(new_len_arg.clone());
        let effective_len = Expr::ite(truncated, old_len, new_len_arg);
        self.collection_len_set(&len_var, effective_len, acc);

        debug!(
            fn_name = %self.fn_name,
            coll_local,
            "VecTruncate: len = min(old_len, arg)"
        );
    }

    /// VecInsert: `self.insert(index, element)`.
    ///
    /// Inserts an element at position `index`, shifting all elements after it
    /// to the right. `len += 1`.
    pub(in crate::codegen_ay::chc) fn vec_op_insert(
        &mut self,
        collection_local: Option<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        let Some(coll_local) = collection_local else {
            self.record_sound_fallback_reason("vec_insert_no_local");
            return;
        };
        let Some(len_var) = self.collections.len_state.get_len_var(coll_local).cloned() else {
            self.record_sound_fallback_reason("vec_insert_no_len");
            return;
        };

        let old_len = self.collection_current_len(&len_var);
        let new_len = old_len.clone().bvadd(Expr::bitvec_const(1u64, POINTER_WIDTH));
        self.collection_len_set(&len_var, new_len.clone(), acc);

        // Capacity growth: cap = max(cap, new_len).
        if let Some(cap_var) = self.collections.len_state.get_cap_var(coll_local).cloned() {
            let old_cap = self.collection_current_cap(&cap_var);
            let grow_needed = old_cap.clone().bvult(new_len.clone());
            let new_cap = Expr::ite(grow_needed, new_len.clone(), old_cap);
            self.collection_cap_set(&cap_var, new_cap.clone(), acc);
            Self::emit_cap_ge_len(new_cap, new_len, acc.constraints);
        }

        debug!(
            fn_name = %self.fn_name,
            coll_local,
            "VecInsert: len += 1"
        );
    }

    /// VecRemove: `self.remove(index) -> T`.
    ///
    /// Removes and returns the element at position `index`, shifting all
    /// elements after it to the left. `len -= 1`. Return value is
    /// unconstrained (sound over-approximation).
    pub(in crate::codegen_ay::chc) fn vec_op_remove(
        &mut self,
        collection_local: Option<usize>,
        dest_local: usize,
        acc: &mut CallAccumulator<'_>,
    ) {
        let Some(coll_local) = collection_local else {
            self.record_sound_fallback_reason("vec_remove_no_local");
            acc.dests.push(dest_local);
            return;
        };
        let Some(len_var) = self.collections.len_state.get_len_var(coll_local).cloned() else {
            self.record_sound_fallback_reason("vec_remove_no_len");
            acc.dests.push(dest_local);
            return;
        };

        let old_len = self.collection_current_len(&len_var);
        let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        // Guard: only decrement if len > 0 (prevents underflow)
        let can_dec = old_len.clone().bvugt(zero.clone());
        let new_len = Expr::ite(can_dec, old_len.bvsub(one), zero);
        self.collection_len_set(&len_var, new_len, acc);

        // Return value (T) is unconstrained — push dest for identity.
        acc.dests.push(dest_local);

        debug!(
            fn_name = %self.fn_name,
            coll_local,
            dest_local,
            "VecRemove: len -= 1, return unconstrained"
        );
    }

    /// VecRetain/VecDedup: filtering operations.
    ///
    /// After the call, `len' <= old_len`. The exact new length depends on
    /// the predicate/equality — modeled as unconstrained with the bound
    /// `0 <= new_len <= old_len` (sound over-approximation).
    pub(in crate::codegen_ay::chc) fn vec_op_filter_inplace(
        &mut self,
        collection_local: Option<usize>,
        label: &str,
        acc: &mut CallAccumulator<'_>,
    ) {
        let Some(coll_local) = collection_local else {
            self.record_sound_fallback_reason("vec_filter_inplace_no_local");
            return;
        };
        let Some(len_var) = self.collections.len_state.get_len_var(coll_local).cloned() else {
            self.record_sound_fallback_reason("vec_filter_inplace_no_len");
            return;
        };

        let old_len = self.collection_current_len(&len_var);

        // new_len is fresh symbolic, constrained to [0, old_len]
        let fresh_len = super::declare_pending_var(
            super::chc_fresh_name("__vec_filter_len"),
            ay_bindings::Sort::bitvec(POINTER_WIDTH),
        );
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        acc.constraints.push(fresh_len.clone().bvuge(zero));
        acc.constraints.push(fresh_len.clone().bvule(old_len));
        self.collection_len_set(&len_var, fresh_len, acc);

        debug!(
            fn_name = %self.fn_name,
            coll_local,
            label,
            "Vec filter-in-place: 0 <= new_len <= old_len"
        );
    }

    /// VecDrain: `self.drain(range)`.
    ///
    /// Removes elements in `range` from the Vec. The returned iterator
    /// yields the removed elements. `len -= range.len()`.
    /// Sound over-approximation: new_len is fresh with `0 <= new_len <= old_len`.
    pub(in crate::codegen_ay::chc) fn vec_op_drain(
        &mut self,
        collection_local: Option<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        // Drain removes a range — model as filter_inplace since we don't
        // easily resolve the range bounds.
        self.vec_op_filter_inplace(collection_local, "drain", acc);
    }

    /// VecSplice: `self.splice(range, replace_with)`.
    ///
    /// Removes `range` from the Vec and replaces with elements from the
    /// iterator. Length change is `replacement_count - range_len`.
    /// Sound over-approximation: new_len is unconstrained (fresh symbolic >= 0).
    pub(in crate::codegen_ay::chc) fn vec_op_splice(
        &mut self,
        collection_local: Option<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        let Some(coll_local) = collection_local else {
            self.record_sound_fallback_reason("vec_splice_no_local");
            return;
        };
        let Some(len_var) = self.collections.len_state.get_len_var(coll_local).cloned() else {
            self.record_sound_fallback_reason("vec_splice_no_len");
            return;
        };

        // Splice can grow or shrink — new_len is fully unconstrained.
        // The only sound constraint is new_len >= 0 (unsigned).
        let fresh_len = super::declare_pending_var(
            super::chc_fresh_name("__vec_splice_len"),
            ay_bindings::Sort::bitvec(POINTER_WIDTH),
        );
        self.collection_len_set(&len_var, fresh_len.clone(), acc);

        // Cap must be >= len
        if let Some(cap_var) = self.collections.len_state.get_cap_var(coll_local).cloned() {
            let old_cap = self.collection_current_cap(&cap_var);
            let grow_needed = old_cap.clone().bvult(fresh_len.clone());
            let new_cap = Expr::ite(grow_needed, fresh_len.clone(), old_cap);
            self.collection_cap_set(&cap_var, new_cap.clone(), acc);
            Self::emit_cap_ge_len(new_cap, fresh_len, acc.constraints);
        }

        debug!(
            fn_name = %self.fn_name,
            coll_local,
            "VecSplice: len unconstrained (splice can grow or shrink)"
        );
    }

    /// VecSplitOff: `self.split_off(at) -> Vec<T>`.
    ///
    /// Returns a new Vec containing elements from `at` to end.
    /// `self.len = at`, new vec `len = old_len - at`.
    /// Sound over-approximation: dest is unconstrained, self.len bounded.
    pub(in crate::codegen_ay::chc) fn vec_op_split_off(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        collection_local: Option<usize>,
        dest_local: usize,
        acc: &mut CallAccumulator<'_>,
    ) {
        let Some(coll_local) = collection_local else {
            self.record_sound_fallback_reason("vec_split_off_no_local");
            acc.dests.push(dest_local);
            return;
        };
        let Some(len_var) = self.collections.len_state.get_len_var(coll_local).cloned() else {
            self.record_sound_fallback_reason("vec_split_off_no_len");
            acc.dests.push(dest_local);
            return;
        };

        let at_arg =
            args.get(1).and_then(|a| self.translate_operand_with_modified(a, modified_locals));

        if let Some(at) = at_arg {
            let old_len = self.collection_current_len(&len_var);
            // self.len = at (elements 0..at remain in self)
            // Ensure at <= old_len (Rust panics otherwise, but we model soundly)
            acc.constraints.push(at.clone().bvule(old_len.clone()));
            self.collection_len_set(&len_var, at.clone(), acc);

            // New Vec's length = old_len - at
            if let Some(dest_len_var) = self.collections.len_state.get_len_var(dest_local).cloned()
            {
                let new_vec_len = old_len.bvsub(at);
                self.collection_len_set(&dest_len_var, new_vec_len, acc);
            }
        } else {
            self.record_sound_fallback_reason("vec_split_off_no_at");
        }

        // Dest Vec data is unconstrained.
        acc.dests.push(dest_local);

        debug!(
            fn_name = %self.fn_name,
            coll_local,
            dest_local,
            "VecSplitOff: self.len = at, new vec unconstrained"
        );
    }

    /// VecLast: `self.last() -> Option<&T>`.
    ///
    /// Query operation — no mutation. Returns `Some(&last)` if non-empty,
    /// `None` if empty. Modeled as unconstrained Option return.
    pub(in crate::codegen_ay::chc) fn vec_op_last(
        &mut self,
        collection_local: Option<usize>,
        dest_local: usize,
        acc: &mut CallAccumulator<'_>,
    ) {
        // No mutation — Vec state is preserved.
        // Return value (Option<&T>) is unconstrained (sound over-approximation).
        acc.dests.push(dest_local);

        debug!(
            fn_name = %self.fn_name,
            ?collection_local,
            dest_local,
            "VecLast: query op, return unconstrained"
        );
    }
}
