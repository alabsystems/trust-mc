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
//! small default), raised without a declared unwind bound to the receiver's
//! static element count when the MIR shows one (`iterator_static_len`, which
//! also proves the chain complete, or `static_iter_len_bound`, which only
//! lengthens it). The chain is claimed only where it is EXACT: it is returned
//! together with the coverage condition `len <= pos + N`, and the caller keeps
//! its previous over-approximation on the uncovered side. Precision is
//! therefore added, never removed, and a length read by
//! `static_iter_len_bound` cannot affect soundness: coverage there is decided
//! by the program's own `len`, never by the bound.

use crate::codegen_ay::chc::codegen_ctx::ExactVar;
use ay_bindings::{Expr, Sort};

use crate::codegen_ay::types::CtorFieldExt;
use rustc_public::mir::Operand;
use std::collections::HashSet;

use super::super::ChcCtx;
use super::super::codegen_ctx::globals::chc_fresh_name;
use super::super::inline_body::DeferredInlineCheck;
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

/// One replayed reduction step: its value, and the obligations it carries
/// (a walked closure's checks, the `+` overflow of `sum`).
pub(super) struct ReductionStep {
    pub(super) value: Expr,
    pub(super) checks: Vec<DeferredInlineCheck>,
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
    /// Every replayed step's obligations, each under its step's
    /// `pos + k < len`. They read the chain's bound accumulators, so the host
    /// emits them with [`Self::constraints`] in the error rule's body.
    pub(super) step_checks: Vec<DeferredInlineCheck>,
    /// Under a declared unwind bound `U` with unwinding assertions on, the
    /// condition under which Kani's `fold` loop fails its unwinding assertion
    /// ([`ReduceUnwinding`]); `None` otherwise.
    pub(super) unwinding: Option<ReduceUnwinding>,
}

/// Kani's unwinding assertion on the `fold` loop a reduction runs in std,
/// per the receiver's measured rule (`crate::codegen_ay::reduce_loop_rule`).
pub(super) struct ReduceUnwinding {
    /// When the assertion can fail: `len > pos + U` or `len >= pos + U` per
    /// the receiver's measured rule, `len >= pos + U` for any other shape.
    pub(super) fails: Expr,
    /// The receiver's rule was measured, so `fails` is exact and a
    /// counterexample through it can be certified.
    pub(super) exact: bool,
    /// `exact`, and the chain replays at least `U` steps: every step Kani
    /// runs is replayed, and a step past the chain would run only after the
    /// unwinding assertion failed, which ends Kani's path there. The
    /// unreplayed-step check is then vacuous (and would only shadow the
    /// certified failure with an uncertified one).
    pub(super) covers_unreplayed: bool,
}

pub(super) use crate::codegen_ay::reduce_loop_rule::ReduceLoopRule;

pub(super) const REDUCE_UNWINDING_MESSAGE: &str = "unwinding assertion loop 0";

impl ChcCtx<'_, '_> {
    /// The measured unwinding rule of the std loop a `sum` / `fold` over the
    /// reduction's receiver (`args[0]`) runs ([`ReduceUnwinding`]); `None`
    /// for a shape that was not measured.
    pub(super) fn reduce_receiver_loop_rule(&self, args: &[Operand]) -> Option<ReduceLoopRule> {
        let ty = args.first().and_then(|arg| arg.ty(self.body.locals()).ok())?;
        crate::codegen_ay::reduce_loop_rule::reduce_loop_rule(self.resolve_body_ty(ty))
    }

    /// Is the reduction's receiver (`args[0]`) an iterator whose remaining
    /// elements are exactly its `data[pos..len]`: a `slice::Iter` /
    /// `slice::IterMut`, an `array::IntoIter` or a `vec::IntoIter`, behind
    /// references, `Copied`, or `Cloned` of a slice iterator over a primitive
    /// element (whose `clone` is a copy)?
    ///
    /// [`Self::iterator_element_sequence`] reads `fld_pos`/`fld_len`/
    /// `fld_data` wherever the value's sort carries them, and walks into
    /// `fld_iter`/`fld_inner`: for a `Filter`, a `Map`, a `Take`, a `Skip` or a
    /// `Rev` that is the INNER sequence, not the adapter's, so a replay over it
    /// would be the unfiltered, unmapped, untruncated or forward reduction.
    /// `Copied` yields the inner elements themselves; `Cloned` yields them only
    /// where `clone` is a copy, so a user `Clone` impl is never skipped.
    fn reduce_receiver_is_element_sequence(&self, args: &[Operand]) -> bool {
        use rustc_public::CrateDef;
        use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
        let Some(ty) = args.first().and_then(|arg| arg.ty(self.body.locals()).ok()) else {
            return false;
        };
        let first_type_arg = |args: &rustc_public::ty::GenericArgs| match args.0.first() {
            Some(GenericArgKind::Type(inner)) => Some(*inner),
            _ => None,
        };
        let mut ty = self.resolve_body_ty(ty);
        let mut cloned = false;
        for _ in 0..8 {
            match ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => ty = self.resolve_body_ty(inner),
                TyKind::RigidTy(RigidTy::Adt(def, adt_args)) => {
                    let krate = def.krate().name;
                    let path = def.name();
                    let last = path.rsplit("::").next().unwrap_or(&path);
                    let slice_iter = krate == "core"
                        && path.contains("slice")
                        && matches!(last, "Iter" | "IterMut");
                    if slice_iter && cloned {
                        // `Cloned<slice::Iter<T>>`: exact only where `T::clone` copies.
                        return first_type_arg(&adt_args).is_some_and(|elem| {
                            matches!(
                                self.resolve_body_ty(elem).kind(),
                                TyKind::RigidTy(
                                    RigidTy::Int(_)
                                        | RigidTy::Uint(_)
                                        | RigidTy::Float(_)
                                        | RigidTy::Bool
                                        | RigidTy::Char
                                )
                            )
                        });
                    }
                    let base = slice_iter
                        || (krate == "core" && path.contains("array") && last == "IntoIter")
                        || (krate == "alloc" && path.contains("vec") && last == "IntoIter");
                    if base {
                        return !cloned;
                    }
                    if krate != "core" || cloned {
                        return false;
                    }
                    let Some(inner) = first_type_arg(&adt_args) else {
                        return false;
                    };
                    match last {
                        "Copied" => {}
                        "Cloned" => cloned = true,
                        _ => return false,
                    }
                    ty = self.resolve_body_ty(inner);
                }
                _ => return false,
            }
        }
        false
    }

    /// An upper bound on the elements the iterator in `iter_local` can
    /// yield: the length `N` of the array an `iter` / `iter_mut` /
    /// `into_iter` made it from ([`Self::iterator_static_len`]), traced back
    /// through adapters that never add elements (`map`, `filter`, `copied`,
    /// `cloned`, `enumerate`, `skip`, `take`, `rev`, `step_by`, ...). `None`
    /// when the chain does not end at an array.
    pub(super) fn iterator_count_upper_bound(&self, iter_local: usize) -> Option<u64> {
        use rustc_public::mir::{Rvalue, StatementKind, TerminatorKind};
        let mut local = iter_local;
        for _ in 0..8 {
            if let Some(len) = self.iterator_static_len(local) {
                return Some(len);
            }
            if self.local_has_multiple_whole_definitions(local) {
                return None;
            }
            // `try_fold` takes `&mut self`: follow the borrow (or a copy of
            // one) to the iterator it names. What the iterator still yields
            // is at most what it was made with.
            let borrowed =
                self.body.blocks.iter().flat_map(|block| &block.statements).find_map(|stmt| {
                    match &stmt.kind {
                        StatementKind::Assign(lhs, rvalue)
                            if lhs.local == local && lhs.projection.is_empty() =>
                        {
                            match rvalue {
                                Rvalue::Ref(_, _, place) if place.projection.is_empty() => {
                                    Some(place.local)
                                }
                                Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..)
                                    if place.projection.is_empty() =>
                                {
                                    Some(place.local)
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    }
                });
            if let Some(borrowed) = borrowed {
                local = borrowed;
                continue;
            }
            let (func, args) =
                self.body.blocks.iter().find_map(|block| match &block.terminator.kind {
                    TerminatorKind::Call { func, args, destination, .. }
                        if destination.local == local && destination.projection.is_empty() =>
                    {
                        Some((func, args))
                    }
                    _ => None,
                })?;
            let path = self.resolve_callee_path(func)?;
            let method = path.rsplit("::").next()?;
            if !matches!(
                method,
                "map"
                    | "filter"
                    | "copied"
                    | "cloned"
                    | "enumerate"
                    | "skip"
                    | "take"
                    | "rev"
                    | "step_by"
                    | "inspect"
                    | "fuse"
                    | "peekable"
                    | "filter_map"
                    | "take_while"
                    | "skip_while"
                    | "map_while"
            ) {
                return None;
            }
            let (Operand::Copy(place) | Operand::Move(place)) = args.first()? else {
                return None;
            };
            if !place.projection.is_empty() {
                return None;
            }
            local = place.local;
        }
        None
    }

    /// Replay bound for the explicit reduction chain.
    pub(super) fn reduce_replay_bound(&self) -> usize {
        let declared = if self.recursive_unwind_depth > 0 {
            self.recursive_unwind_depth as usize
        } else {
            DEFAULT_REDUCE_BOUND
        };
        declared.clamp(1, MAX_REDUCE_BOUND)
    }

    /// An upper bound on the number of elements the iterator `receiver` can
    /// still yield, read from the MIR when it is static: the receiver is
    /// produced by a chain of calls (`<[T]>::iter`, `IntoIterator::into_iter`,
    /// count-preserving or count-reducing adapters such as `copied`, `cloned`,
    /// `map`, `filter`) whose first argument leads back, through casts and
    /// borrows, to an array `[T; N]`; or the receiver is a
    /// `core::array::IntoIter<T, N>`. `None` when no such `N` is found.
    ///
    /// Only the replay's LENGTH depends on it, never its exactness: coverage is
    /// still the program's own `len <= pos + bound`, so an `N` that is too
    /// small leaves the uncovered side over-approximated as before, and one
    /// that is too large only adds steps whose `pos + k < len` guard is false.
    pub(super) fn static_iter_len_bound(&self, receiver: &Operand) -> Option<usize> {
        use rustc_public::CrateDef;
        use rustc_public::mir::TerminatorKind;
        use rustc_public::ty::{RigidTy, TyKind};
        let (Operand::Copy(place) | Operand::Move(place)) = receiver else {
            return None;
        };
        if !place.projection.is_empty() {
            return None;
        }
        let mut current = place.local;
        let mut seen = HashSet::new();
        for _ in 0..8 {
            if !seen.insert(current) || current >= self.body.locals().len() {
                return None;
            }
            let ty = self.resolve_body_ty(self.body.locals()[current].ty);
            if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind()
                && def.krate().name == "core"
                && def.name().contains("array::")
                && def.name().ends_with("::IntoIter")
                && let Some(len) = args.0.iter().find_map(|arg| match arg {
                    rustc_public::ty::GenericArgKind::Const(len) => len.eval_target_usize().ok(),
                    _ => None,
                })
            {
                return usize::try_from(len).ok();
            }
            if let Some(len) = self.trace_static_array_len_through_casts(current) {
                return Self::try_eval_concrete_bv_usize(&len);
            }
            // The one call producing `current`; follow its first argument.
            if self.local_has_multiple_whole_definitions(current) {
                return None;
            }
            current = self.body.blocks.iter().find_map(|block| {
                let TerminatorKind::Call { args, destination, .. } = &block.terminator.kind else {
                    return None;
                };
                if destination.local != current || !destination.projection.is_empty() {
                    return None;
                }
                match args.first()? {
                    Operand::Copy(arg) | Operand::Move(arg) if arg.projection.is_empty() => {
                        Some(arg.local)
                    }
                    _ => None,
                }
            })?;
        }
        None
    }

    /// The length `N` of the array `[T; N]` an iterator local was made from:
    /// the argument of the `iter` / `iter_mut` / `into_iter` call that defines
    /// it, traced back through copies, unsizing casts and reborrows of single
    /// definitions. An upper bound on the elements the iterator can still
    /// yield. `None` when the local has another definition or the chain does
    /// not end at an array type.
    fn iterator_static_len(&self, iter_local: usize) -> Option<u64> {
        use rustc_public::mir::{ProjectionElem, Rvalue, StatementKind, TerminatorKind};
        use rustc_public::ty::{RigidTy, TyKind};
        if self.local_has_multiple_whole_definitions(iter_local) {
            return None;
        }
        let (func, args) =
            self.body.blocks.iter().find_map(|block| match &block.terminator.kind {
                TerminatorKind::Call { func, args, destination, .. }
                    if destination.local == iter_local && destination.projection.is_empty() =>
                {
                    Some((func, args))
                }
                _ => None,
            })?;
        let path = self.resolve_callee_path(func)?;
        let method = path.rsplit("::").next()?;
        if !matches!(method, "iter" | "iter_mut" | "into_iter") {
            return None;
        }
        let array_len = |ty: rustc_public::ty::Ty| -> Option<u64> {
            let ty = self.resolve_body_ty(ty);
            let inner = match ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => {
                    self.resolve_body_ty(inner)
                }
                _ => ty,
            };
            match inner.kind() {
                TyKind::RigidTy(RigidTy::Array(_, len)) => len.eval_target_usize().ok(),
                _ => None,
            }
        };
        let mut operand = args.first()?.clone();
        for _ in 0..8 {
            if let Some(len) = operand.ty(self.body.locals()).ok().and_then(array_len) {
                return Some(len);
            }
            let (Operand::Copy(place) | Operand::Move(place)) = &operand else {
                return None;
            };
            if !place.projection.is_empty()
                || self.local_has_multiple_whole_definitions(place.local)
            {
                return None;
            }
            let source =
                self.body.blocks.iter().flat_map(|block| &block.statements).find_map(|stmt| {
                    match &stmt.kind {
                        StatementKind::Assign(lhs, rvalue)
                            if lhs.local == place.local && lhs.projection.is_empty() =>
                        {
                            Some(rvalue)
                        }
                        _ => None,
                    }
                })?;
            operand = match source {
                Rvalue::Use(src, ..) | Rvalue::Cast(_, src, _) => src.clone(),
                // `&(*r)`, a reborrow, or `&a`.
                Rvalue::Ref(_, _, src) | Rvalue::AddressOf(_, src)
                    if src.projection.is_empty()
                        || matches!(src.projection.as_slice(), [ProjectionElem::Deref]) =>
                {
                    if src.projection.is_empty() {
                        return self
                            .body
                            .locals()
                            .get(src.local)
                            .and_then(|decl| array_len(decl.ty));
                    }
                    Operand::Copy(rustc_public::mir::Place {
                        local: src.local,
                        projection: Vec::new(),
                    })
                }
                _ => return None,
            };
        }
        None
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
    /// `step(ctx, acc, elem, in_range)` applies one reduction step; returning
    /// `None` abandons the whole chain (the caller then keeps its
    /// over-approximation), so a step that cannot be modelled never produces a
    /// partial fold. `in_range` is the condition under which the step is taken
    /// (`pos + k < len`), for a step whose obligation the caller states itself
    /// (the overflow check of an integer sum); the step's own `checks` are
    /// weakened by it here. `min_bound` lengthens the replay (to at most
    /// `MAX_REDUCE_BOUND`, and only without a declared unwind bound), for a
    /// caller that knows how many elements the receiver can have.
    pub(super) fn precise_reduce_chain(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        init: &Expr,
        acc_sort: &Sort,
        min_bound: Option<usize>,
        mut step: impl FnMut(&mut Self, &Expr, &Expr, &Expr) -> Option<ReductionStep>,
    ) -> Option<PreciseReduction> {
        // The chain folds `data[pos..len]` itself: exact only when the
        // receiver IS the element sequence. `iterator_element_sequence` also
        // descends through an adapter's `iter` field, so `filter`, `map`,
        // `skip`, `take` or `step_by` over a slice iterator folded the INNER
        // elements, unfiltered and unmapped: `[1; 4].iter().filter(..).sum()`
        // failed "attempt to add with overflow", certified Genuine, on a
        // program Kani proves (on main too, `f_filter_sum_safe`; walker
        // fail-closed review 6 round 2, finding 1 follow-up). Such a receiver
        // keeps the over-approximation.
        if !self.reduce_receiver_is_element_sequence(args) {
            return None;
        }
        let (iter_expr, iter_local) =
            self.iterator_receiver_expr_and_local(args, modified_locals)?;
        let seq = self.iterator_element_sequence(&iter_expr)?;
        let index_width = seq.pos.sort().bitvec_width()?;
        // An iterator over an array of constant length `N` yields at most `N`
        // elements: replaying `N` steps (up to the cap) makes the chain exact,
        // where the default bound of 8 left a ninth step to the reach check
        // that fails wherever the step can, so `sum` over nine `u8`s failed
        // closed even when it could not overflow (walker fail-closed review 6,
        // finding 7, `f3_sum_ninth_safe`). The chain is linear in the bound.
        //
        // Only without a declared unwind bound. Under `#[kani::unwind(U)]`
        // Kani's `fold` loop fails its unwinding assertion once more than `U`
        // elements remain, and the replay stays at `U` passes (the cap
        // aside): replaying all `N` made `fully_covered` hold, so neither the
        // unreplayed-step check nor anything else stated that failure, and
        // `sum` of five elements under `unwind(3)` verified clean where Kani
        // fails (walker fail-closed review 6 round 2, finding 1,
        // `rp2_reduce_unwind.rs`). The unwinding assertion itself is
        // [`PreciseReduction::unwinding`].
        let declared_unwind = self.recursive_unwind_depth > 0;
        let static_len = if declared_unwind {
            None
        } else {
            iter_local.and_then(|local| self.iterator_static_len(local))
        };
        let bound = match static_len {
            Some(len) if len <= MAX_REDUCE_BOUND as u64 => {
                self.reduce_replay_bound().max(len as usize)
            }
            _ => self.reduce_replay_bound(),
        };
        // A caller that read the receiver's element count another way
        // (`static_iter_len_bound`) lengthens the replay, under the same
        // no-declared-unwind condition; coverage stays `len <= pos + bound`.
        let bound = match min_bound {
            Some(min) if !declared_unwind => bound.max(min.min(MAX_REDUCE_BOUND)),
            _ => bound,
        };
        let unwinding = (declared_unwind && self.unwinding_assertions).then(|| {
            let rule = self.reduce_receiver_loop_rule(args);
            let unwind = Expr::bitvec_const(u64::from(self.recursive_unwind_depth), index_width);
            let limit = seq.pos.clone().bvadd(unwind);
            let fails = match rule {
                Some(ReduceLoopRule::PassesPastBound) => seq.len.clone().bvugt(limit),
                Some(ReduceLoopRule::ReachesBound) | None => seq.len.clone().bvuge(limit),
            };
            let exact = rule.is_some();
            let covers_unreplayed = exact && bound as u64 >= u64::from(self.recursive_unwind_depth);
            ReduceUnwinding { fails, exact, covers_unreplayed }
        });

        let mut acc = self.coerce_value_to_sort(init.clone(), acc_sort, true)?;
        let mut constraints = Vec::with_capacity(bound);
        let mut step_checks = Vec::new();
        for k in 0..bound {
            let offset = Expr::bitvec_const(k as u64, index_width);
            let idx = seq.pos.clone().bvadd(offset);
            let in_range = idx.clone().bvult(seq.len.clone());
            let elem = seq.data.clone().select(idx);
            let ReductionStep { value: applied, checks } = step(self, &acc, &elem, &in_range)?;
            let applied = self.coerce_value_to_sort(applied, acc_sort, true)?;
            step_checks.extend(checks.into_iter().map(|check| check.weaken_by_guard(&in_range)));
            let next = ExactVar::defined(chc_fresh_name("iter_reduce_acc"), acc_sort.clone());
            constraints.push(next.clone().eq(Expr::ite(in_range, applied, acc)));
            acc = next;
        }

        // An iterator whose array bounds it to `N <= bound` elements has no
        // element past the chain: every real execution is covered, and the
        // reduction's value is the chain's (no over-approximated remainder,
        // whose free symbol would keep a counterexample from certification).
        let fully_covered = if static_len.is_some_and(|len| len <= bound as u64) {
            Expr::bool_const(true)
        } else {
            let limit = seq.pos.bvadd(Expr::bitvec_const(bound as u64, index_width));
            seq.len.bvule(limit)
        };
        Some(PreciseReduction { acc, fully_covered, constraints, step_checks, unwinding })
    }
}
