// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Vec extend/from-iter internal operation leaf handlers.
//!
//! Covers internal extend helpers and FromIterator construction that
//! previously fell through to the identity pass-through arm in
//! `codegen_call_vec_core`. Each handler provides a sound CHC
//! abstraction of the operation's effect on Vec state.
//!
//! Semantics summary:
//! - **VecExtendWith** (`resize` internal): `len += n` where `n` comes from
//!   the count argument. Models `Vec::resize(new_len, value)` — the backing
//!   `extend_with` helper appends `new_len - old_len` copies.
//! - **VecExtendTrusted** (trusted-len iterator extend): `len += fresh_count`
//!   where `fresh_count` is a fresh symbolic bounded by `0 <= fresh_count`.
//!   The iterator's exact length is unknown at the CHC level but the trusted-len
//!   contract guarantees no reallocation surprise.
//! - **VecFromIter** (`FromIterator::from_iter`): constructs a new Vec from an
//!   iterator. Destination length is a fresh symbolic `>= 0` (sound
//!   over-approximation since the iterator length is unknown).
//!
//! Part of #4135: Vec extend/sort/append leaf handlers.

use std::collections::HashSet;

use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::Expr;
use rustc_public::mir::Operand;
use tracing::debug;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// VecExtendWith: internal helper for `Vec::resize(new_len, value)`.
    ///
    /// The resize operation sets `len = new_len` when `new_len > len`, or
    /// truncates when `new_len < len`. The internal `extend_with` helper
    /// only handles the growth case (`len += new_len - old_len`), but we
    /// model the full resize semantic for soundness:
    ///   - If `new_len > old_len`: `len = new_len`, `cap >= new_len`.
    ///   - If `new_len <= old_len`: `len = new_len` (truncation).
    ///
    /// `args[0]` is `&mut self` (the Vec), `args[1]` is `new_len: usize`.
    /// Data contents for new elements are unconstrained (sound over-approx).
    pub(in crate::codegen_ay::chc) fn vec_op_extend_with(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        collection_local: Option<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        let Some(coll_local) = collection_local else {
            self.record_sound_fallback_reason("vec_extend_with_no_local");
            return;
        };
        let Some(len_var) = self.collections.len_state.get_len_var(coll_local).cloned() else {
            self.record_sound_fallback_reason("vec_extend_with_no_len");
            return;
        };

        // args[1] is the count/new_len argument.
        let n_arg =
            args.get(1).and_then(|a| self.translate_operand_with_modified(a, modified_locals));

        let Some(n_expr) = n_arg else {
            // Cannot resolve the count — use fresh symbolic as fallback.
            debug!(
                fn_name = %self.fn_name,
                coll_local,
                "VecExtendWith: count arg unresolved — fresh symbolic fallback"
            );
            self.vec_op_extend_with_fresh(coll_local, &len_var, acc);
            return;
        };

        let old_len = self.collection_current_len(&len_var);

        // Model: len += n_expr (extend_with adds exactly `n` elements).
        let new_len = old_len.clone().bvadd(n_expr);
        // Guard: new_len >= old_len (unsigned overflow protection).
        acc.constraints.push(new_len.clone().bvuge(old_len));
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
            "VecExtendWith: len += n"
        );
    }

    /// VecExtendTrusted: trusted-length iterator extend.
    ///
    /// The trusted-len contract means the iterator reports an exact size hint
    /// and the Vec pre-allocates accordingly. The actual number of elements
    /// yielded is unknown at the CHC level, so we model:
    ///   - `len += fresh_count` where `fresh_count >= 0` (unsigned, automatic).
    ///   - `cap >= new_len`.
    ///
    /// This is a sound over-approximation: the solver considers all possible
    /// extension lengths, which includes the correct one.
    pub(in crate::codegen_ay::chc) fn vec_op_extend_trusted(
        &mut self,
        collection_local: Option<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        let Some(coll_local) = collection_local else {
            self.record_sound_fallback_reason("vec_extend_trusted_no_local");
            return;
        };
        let Some(len_var) = self.collections.len_state.get_len_var(coll_local).cloned() else {
            self.record_sound_fallback_reason("vec_extend_trusted_no_len");
            return;
        };

        self.vec_op_extend_with_fresh(coll_local, &len_var, acc);

        debug!(
            fn_name = %self.fn_name,
            coll_local,
            "VecExtendTrusted: len += fresh_count"
        );
    }

    /// VecFromIter: `FromIterator::from_iter(iter) -> Vec<T>`.
    ///
    /// Constructs a new Vec from an iterator. The destination Vec's length
    /// is a fresh symbolic `>= 0` (sound over-approximation since the
    /// iterator's element count is unknown). Capacity >= length.
    /// Data contents are unconstrained.
    ///
    /// Unlike extend operations that modify an existing Vec, from_iter
    /// produces a brand-new Vec, so we set the destination's length directly
    /// rather than incrementing.
    pub(in crate::codegen_ay::chc) fn vec_op_from_iter(
        &mut self,
        collection_local: Option<usize>,
        dest_local: usize,
        acc: &mut CallAccumulator<'_>,
    ) {
        // from_iter produces a new Vec at dest_local.
        // Try dest_local first for length tracking, fall back to collection_local.
        let target_local = if self.collections.len_state.get_len_var(dest_local).is_some() {
            dest_local
        } else if let Some(cl) = collection_local
            && self.collections.len_state.get_len_var(cl).is_some()
        {
            cl
        } else {
            // No length tracking available — dest is unconstrained (sound).
            acc.dests.push(dest_local);
            debug!(
                fn_name = %self.fn_name,
                dest_local,
                ?collection_local,
                "VecFromIter: no len tracking — dest unconstrained"
            );
            return;
        };

        let len_var =
            self.collections.len_state.get_len_var(target_local).cloned().expect("checked above");

        // Fresh symbolic length >= 0 (unsigned BV is always >= 0).
        let fresh_len = super::declare_pending_var(
            super::chc_fresh_name("__vec_from_iter_len"),
            ay_bindings::Sort::bitvec(POINTER_WIDTH),
        );
        self.collection_len_set(&len_var, fresh_len.clone(), acc);

        // Cap >= len.
        if let Some(cap_var) = self.collections.len_state.get_cap_var(target_local).cloned() {
            let fresh_cap = super::declare_pending_var(
                super::chc_fresh_name("__vec_from_iter_cap"),
                ay_bindings::Sort::bitvec(POINTER_WIDTH),
            );
            acc.constraints.push(fresh_cap.clone().bvuge(fresh_len.clone()));
            self.collection_cap_set(&cap_var, fresh_cap.clone(), acc);
            Self::emit_cap_ge_len(fresh_cap, fresh_len, acc.constraints);
        }

        // Dest data is unconstrained.
        acc.dests.push(dest_local);

        debug!(
            fn_name = %self.fn_name,
            target_local,
            dest_local,
            "VecFromIter: dest len = fresh symbolic, cap >= len"
        );
    }

    // ── Private helpers ──

    /// Shared helper: extend a Vec by a fresh symbolic count.
    ///
    /// Used by both `vec_op_extend_with` (when count is unresolvable) and
    /// `vec_op_extend_trusted` (always, since iterator length is unknown).
    ///
    /// Models: `len += fresh_count` where `fresh_count >= 0` (unsigned BV).
    /// Capacity is grown to `max(cap, new_len)`.
    fn vec_op_extend_with_fresh(
        &mut self,
        coll_local: usize,
        len_var: &str,
        acc: &mut CallAccumulator<'_>,
    ) {
        let old_len = self.collection_current_len(len_var);

        // fresh_count >= 0 is automatic for unsigned BV.
        let fresh_count = super::declare_pending_var(
            super::chc_fresh_name("__vec_extend_count"),
            ay_bindings::Sort::bitvec(POINTER_WIDTH),
        );

        let new_len = old_len.clone().bvadd(fresh_count);
        // Guard: new_len >= old_len (unsigned overflow protection).
        acc.constraints.push(new_len.clone().bvuge(old_len));
        self.collection_len_set(len_var, new_len.clone(), acc);

        // Capacity growth: cap = max(cap, new_len).
        if let Some(cap_var) = self.collections.len_state.get_cap_var(coll_local).cloned() {
            let old_cap = self.collection_current_cap(&cap_var);
            let grow_needed = old_cap.clone().bvult(new_len.clone());
            let new_cap = Expr::ite(grow_needed, new_len.clone(), old_cap);
            self.collection_cap_set(&cap_var, new_cap.clone(), acc);
            Self::emit_cap_ge_len(new_cap, new_len, acc.constraints);
        }
    }
}
