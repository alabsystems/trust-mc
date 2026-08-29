// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Precise (non-fabricating) encoding of `Iterator::fold` / `Iterator::sum`.
//!
//! The reduction arms used to answer `fold` with
//! `ite(has_remaining, <fresh unconstrained var>, init)` — the closure was
//! never applied and no element ever entered the accumulator, so the result
//! was an arbitrary value in a VALUE position. Any assertion about the
//! reduction was then trivially refutable, and the driver certified the
//! resulting counterexample Genuine (a false positive) because
//! `fresh_adapter_symbol` books its approximation on the
//! `record_aggregate_gap` channel, which `classify_ctrex` does not read.
//!
//! This module folds for real: for an iterator whose element sequence is
//! addressable — a slice/array/Vec iterator carrying `fld_data` / `fld_pos` /
//! `fld_len` — it emits the explicit reduction
//!
//! ```text
//! acc_0     = init
//! acc_{k+1} = ite(pos + k < len, f(acc_k, data[pos + k]), acc_k)
//! result    = acc_N
//! ```
//!
//! `N` is the unwind bound (`--default-unwind` / `#[kani::unwind(N)]`, else a
//! small default). The chain is claimed only where it is EXACT: it is returned
//! together with the coverage condition `len <= pos + N`, and the caller keeps
//! its previous over-approximation on the uncovered side. Precision is
//! therefore added, never removed.

use ay_bindings::{Expr, Sort};

use crate::codegen_ay::types::CtorFieldExt;
use rustc_public::mir::Operand;
use std::collections::HashSet;

use super::super::ChcCtx;
use super::super::codegen_ctx::globals::{chc_fresh_name, declare_pending_var};
use super::super::stubs_option_helpers::OptionHelpers;

/// Default replay bound when the harness declares no unwind value.
const DEFAULT_REDUCE_BOUND: usize = 8;

/// Hard cap on the emitted chain length, so a large `#[kani::unwind]` cannot
/// blow the formula up through this path.
const MAX_REDUCE_BOUND: usize = 32;

/// The addressable element sequence behind an iterator value.
pub(super) struct IterSeq {
    /// `Array(index_sort, elem_sort)` holding the elements.
    data: Expr,
    /// Current read position, normalized to the array's index width.
    pos: Expr,
    /// Element count, normalized to the array's index width.
    len: Expr,
}

/// An exact reduction chain plus the condition under which it is exact.
pub(super) struct PreciseReduction {
    /// `acc_N` — the folded accumulator (a bound CHC variable, not a tree).
    pub(super) acc: Expr,
    /// `len <= pos + N`: every element of the iterator was visited.
    pub(super) fully_covered: Expr,
    /// Defining equalities `acc_k = ite(...)`, one per step. Emitting the
    /// chain through bound variables instead of one nested term keeps the
    /// formula LINEAR in the bound; inlining it is exponential in the number
    /// of times the step function mentions its accumulator (an `acc + x`
    /// closure with its overflow check mentions it five times, so a bound of
    /// 6 produced a ~15k-node term that timed the solver out).
    pub(super) constraints: Vec<Expr>,
}

impl ChcCtx<'_, '_> {
    /// Replay bound for the explicit reduction chain.
    pub(super) fn reduce_replay_bound(&self) -> usize {
        let declared = if self.recursive_unwind_depth > 0 {
            self.recursive_unwind_depth as usize
        } else {
            DEFAULT_REDUCE_BOUND
        };
        declared.clamp(1, MAX_REDUCE_BOUND)
    }

    /// Decompose an iterator datatype value into `(data, pos, len)`.
    ///
    /// Recognizes the shapes `advance_iterator_expr` already walks: `fld_pos` /
    /// `fld_len` / `fld_data` directly on the iterator, a wrapped `fld_vec`
    /// collection carrying `fld_len` / `fld_data`, and adapter wrappers
    /// delegating through `fld_iter` / `fld_inner`.
    fn iterator_element_sequence(&self, iter_expr: &Expr) -> Option<IterSeq> {
        let iter_sort = iter_expr.sort().clone();
        let dt = iter_sort.datatype_sort()?;
        let ctor = dt.constructors.first()?;

        if let (Some(pos_f), Some(len_f), Some(data_f)) =
            (ctor.field("fld_pos"), ctor.field("fld_len"), ctor.field("fld_data"))
        {
            let pos = iter_expr.clone().field_select(&*dt.name, "fld_pos", pos_f.sort.clone());
            let len = iter_expr.clone().field_select(&*dt.name, "fld_len", len_f.sort.clone());
            let data = iter_expr.clone().field_select(&*dt.name, "fld_data", data_f.sort.clone());
            return Self::normalize_iter_seq(data, pos, len);
        }

        if let (Some(vec_f), Some(pos_f)) = (ctor.field("fld_vec"), ctor.field("fld_pos")) {
            let pos = iter_expr.clone().field_select(&*dt.name, "fld_pos", pos_f.sort.clone());
            let vec = iter_expr.clone().field_select(&*dt.name, "fld_vec", vec_f.sort.clone());
            let vec_sort = vec.sort().clone();
            let vec_dt = vec_sort.datatype_sort()?;
            let vec_ctor = vec_dt.constructors.first()?;
            let len_f = vec_ctor.field("fld_len")?;
            let data_f = vec_ctor.field("fld_data")?;
            let len = vec.clone().field_select(&*vec_dt.name, "fld_len", len_f.sort.clone());
            let data = vec.field_select(&*vec_dt.name, "fld_data", data_f.sort.clone());
            return Self::normalize_iter_seq(data, pos, len);
        }

        let inner_f = ctor.field("fld_iter").or_else(|| ctor.field("fld_inner"))?;
        let inner = iter_expr.clone().field_select(&*dt.name, &*inner_f.name, inner_f.sort.clone());
        self.iterator_element_sequence(&inner)
    }

    /// Bring `pos` and `len` to the array's index width.
    fn normalize_iter_seq(data: Expr, pos: Expr, len: Expr) -> Option<IterSeq> {
        let data_sort = data.sort().clone();
        let array = data_sort.array_sort()?;
        let index_width = array.index_sort.bitvec_width()?;
        let pos = Self::widen_unsigned_to(pos, index_width)?;
        let len = Self::widen_unsigned_to(len, index_width)?;
        Some(IterSeq { data, pos, len })
    }

    fn widen_unsigned_to(value: Expr, width: u32) -> Option<Expr> {
        let value_width = value.sort().bitvec_width()?;
        match value_width.cmp(&width) {
            std::cmp::Ordering::Equal => Some(value),
            std::cmp::Ordering::Less => Some(value.zero_extend(width - value_width)),
            std::cmp::Ordering::Greater => Some(value.extract(width - 1, 0)),
        }
    }

    /// Emit the explicit reduction chain, or `None` when the sequence is not
    /// addressable or the step function cannot be replayed.
    ///
    /// `step(ctx, acc, elem)` applies one reduction step; returning `None`
    /// abandons the whole chain (the caller then keeps its over-approximation),
    /// so a step that cannot be modelled never produces a partial fold.
    pub(super) fn precise_reduce_chain(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        init: &Expr,
        acc_sort: &Sort,
        mut step: impl FnMut(&mut Self, &Expr, &Expr) -> Option<Expr>,
    ) -> Option<PreciseReduction> {
        let (iter_expr, _) = self.iterator_receiver_expr_and_local(args, modified_locals)?;
        let seq = self.iterator_element_sequence(&iter_expr)?;
        let index_width = seq.pos.sort().bitvec_width()?;
        let bound = self.reduce_replay_bound();

        let mut acc = self.coerce_value_to_sort(init.clone(), acc_sort, true)?;
        let mut constraints = Vec::with_capacity(bound);
        for k in 0..bound {
            let offset = Expr::bitvec_const(k as u64, index_width);
            let idx = seq.pos.clone().bvadd(offset);
            let in_range = idx.clone().bvult(seq.len.clone());
            let elem = seq.data.clone().select(idx);
            let applied = step(self, &acc, &elem)?;
            let applied = self.coerce_value_to_sort(applied, acc_sort, true)?;
            let next = declare_pending_var(chc_fresh_name("iter_reduce_acc"), acc_sort.clone());
            constraints.push(next.clone().eq(Expr::ite(in_range, applied, acc)));
            acc = next;
        }

        let limit = seq.pos.bvadd(Expr::bitvec_const(bound as u64, index_width));
        let fully_covered = seq.len.bvule(limit);
        Some(PreciseReduction { acc, fully_covered, constraints })
    }
}
