// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Kani's unwinding assertion on the loops of a call the statement path
//! MODELS, under a declared unwind bound (walker fail-closed repair round 4,
//! the class of review 6 round 3 finding 6).
//!
//! A stub or pre-inline model replaces std code, and with it every loop Kani
//! unwinds: `[1u8, .., 8].contains(&x)`, `v.sort()`, `v.retain(..)`,
//! `v.dedup()` and `a.iter().eq(b.iter())` under `#[kani::unwind(2)]` verified
//! clean where Kani fails `unwinding assertion loop N`
//! (`tools/soundness-duals/model_call_unwind_dual.rs`). A modelled call whose
//! callee may loop (`obligation_free_walk::instance_may_loop`) therefore gets
//! a check: uncertified (a fresh `t`, `uncertified_check.rs`), so a failure of
//! it is never Genuine.
//!
//! The check fires only where the callee's loops CAN run `U` passes. Kani
//! fails a loop that tests before its body (`while`, `for`) exactly when it
//! runs `U` iterations, and one that tests after it when it runs `U + 1`;
//! either way, a loop that runs fewer than `U` iterations never fails. So
//! where every loop the callee runs (callees of callees included) is known to
//! run at most `B` iterations, the check is `B < U ∨ t`. The bounds below are
//! read from the frozen nightly's std sources, and each is restricted to
//! callees whose per-element work runs no loop of its own (a primitive
//! element type, or a closure / `Clone` / drop glue the loop walk proves
//! loop-free):
//!
//! | callee | bound |
//! | --- | --- |
//! | `<[T]>::contains` (primitive `T`) | the slice's length (`iter().any`, or `memchr` for bytes) |
//! | stable `sort`, `sort_by`, `sort_by_key` | `len - 1` up to 20 elements (insertion sort; driftsort above) |
//! | stable `sort` of `[P; M]` elements (primitive `P`) | `max(len - 1, M)` up to 20 elements |
//! | `retain`, `retain_mut`, `dedup`, `dedup_by`, `dedup_by_key` | the length |
//! | `<[T]>::reverse` | `max(len / 2, size_of::<T>() / 8)` (each swap's chunk loop) |
//! | `Vec::resize` | `max(len, new_len)` (`extend_with` or `truncate`) |
//! | `SpecFromElem::from_elem` | `n` (`extend_with`) |
//! | `<Vec<T> as Drop>::drop` | the length (the element drop loop) |
//! | `mem::swap`, `typed_swap_nonoverlapping` | `size_of::<T>() / 8` (`swap_nonoverlapping_bytes`'s chunk loop) |
//! | integer `pow` family | the exponent's bit length minus one |
//! | `Iterator::eq` / `ne` over a slice iterator, the other a slice or array iterator (primitive items) | the receiver's remaining length |
//! | `[T; N] == [U; N]`, `SpecArrayEq::spec_eq` (primitive or unit elements) | `N * max(size_of::<T>(), 1)` (`memcmp` runs per byte) |
//! | `[T] == [U]` (primitive or unit elements) | the left slice's length `* max(size_of::<T>(), 1)` |
//! | `Vec::extend` from a `Range` / `RangeInclusive` (integers, `char`) | its step count, or 0 when empty |
//! | `raw_eq::<T>` / `compare_bytes(.., n)` (Kani's `memcmp`) | `size_of::<T>()` / `n` bytes |
//! | `==` on an `Option`, `Result`, `Box`, reference or tuple of such arrays or scalars | the most bytes one part compares (`shared::compare_loops`) |
//! | `FlatMap::next` of a concrete `flat_map(|s| s.chars())` over `n` literals | `n` |
//!
//! The bound counts a loop's back edges, which is what Kani's assertion
//! counts (a `for` over `n` items takes `n`; `pow`'s `loop`, which leaves from
//! the middle of its last pass, takes one fewer than its passes). The closures
//! and function items a callee runs per element (a comparison, a `retain`
//! predicate, `Clone`, drop glue) must run no loop of their own, or the bound
//! does not apply.
//!
//! Anything else (a `HashMap` probe loop, any other `FlatMap::next`, a sort of more
//! than 20 elements, an element type with its own loops) keeps the plain
//! check. Measured in docs/chc-hole-fix-designs-2026-09-24.md, "Walker
//! fail-closed: repair rounds 3 and 4".

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::Operand;
use rustc_public::ty::{ClosureKind, RigidTy, Ty, TyKind};
use tracing::debug;
use trust_mc_core::violation::PropertyKind;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Stable sort runs insertion sort up to this length (`MAX_LEN_ALWAYS_INSERTION_SORT`).
const STABLE_SORT_INSERTION_MAX: u64 = 20;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// See the module docs. Emitted for a call the dispatch spine handled
    /// without replaying the callee's body (`codegen_call.rs`).
    pub(in crate::codegen_ay::chc) fn model_call_unwinding_check(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) {
        use super::codegen_call_virtual_inline::uncertified_check::{
            MODEL_CALL_LOOP_UNWIND_UNCERTIFIED, call_may_loop, uncertified_reach_check,
        };
        if self.recursive_unwind_depth == 0 || !self.unwinding_assertions || dcx.target.is_none() {
            return;
        }
        if matches!(
            self.detect_stub(dcx.func),
            Some(trust_mc_codegen_stubs::StubKind::IterFold | trust_mc_codegen_stubs::StubKind::IterSum)
        ) {
            return;
        }
        if !call_may_loop(self, dcx.func, self.body.locals()) {
            return;
        }
        let unwind = Expr::bitvec_const(u64::from(self.recursive_unwind_depth), POINTER_WIDTH);
        // A comparison's loops stop early: from the two compared values, the
        // condition under which one completes the bound's passes
        // (`shared::compare_loops::compare_reach`). Otherwise the bound.
        let reach = self.model_call_compare_reach(dcx);
        let bound = if reach.is_some() { None } else { self.model_call_trip_bound(dcx) };
        debug!(
            callee = dcx.callee_path.as_deref().unwrap_or("<unknown>"),
            bb_idx = dcx.bb_idx,
            bounded = bound.is_some(),
            data_dependent = reach.is_some(),
            "modelled call may run a loop past the declared unwind bound — uncertified check"
        );
        if reach.as_ref().is_some_and(crate::codegen_ay::shared::compare_loops::is_const_false) {
            return;
        }
        let t = uncertified_reach_check(self, MODEL_CALL_LOOP_UNWIND_UNCERTIFIED);
        let check = match (reach, bound) {
            (Some(reaches), _) => reaches.not().or(t),
            (None, Some(bound)) => bound.bvult(unwind).or(t),
            (None, None) => t,
        };
        let check = super::inline_body::DeferredInlineCheck {
            check,
            kind: PropertyKind::Other,
            message: Some(
                "unwinding assertion loop 0 (a loop in a call the CHC encoder models, under the \
                 declared unwind bound)"
                    .to_string(),
            ),
            write_mark: self.heap_state.write_mark(),
            merge_key: None,
        };
        self.emit_deferred_inline_checks_at(dcx.from_app, dcx.stmt_constraints, dcx.bb_idx, vec![check]);
    }

    /// Kani's unwinding assertion on the loop the kani library's
    /// `Arbitrary::any` runs for a `kani::any()` this lane models as a fresh
    /// value (`shared::kani_any_loops`): `kani::any::<[bool; N]>()` runs `N`
    /// passes, so under a declared unwind `U <= N` the assertion fails wherever
    /// the call is reached. Exact, and so certified.
    pub(in crate::codegen_ay::chc) fn kani_any_unwinding_check(
        &mut self,
        dcx: &DispatchCallContext<'_>,
    ) {
        if self.recursive_unwind_depth == 0 || !self.unwinding_assertions || dcx.target.is_none() {
            return;
        }
        let Ok(dest_ty) = dcx.destination.ty(self.body.locals()) else {
            return;
        };
        let passes = crate::codegen_ay::shared::kani_any_loops::kani_any_loop_passes(dest_ty);
        self.kani_any_passes_unwinding_check(dcx, passes);
    }

    /// The check of [`Self::kani_any_unwinding_check`] for a loop of `passes`
    /// passes the model does not run: it fails wherever the call is reached
    /// when the declared bound does not cover the loop.
    pub(in crate::codegen_ay::chc) fn kani_any_passes_unwinding_check(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        passes: u64,
    ) {
        if self.recursive_unwind_depth == 0 || !self.unwinding_assertions || dcx.target.is_none() {
            return;
        }
        if passes < u64::from(self.recursive_unwind_depth) {
            return;
        }
        debug!(passes, unwind = self.recursive_unwind_depth, "kani::any runs a loop past the declared unwind bound");
        let check = super::inline_body::DeferredInlineCheck {
            check: Expr::bool_const(false),
            kind: PropertyKind::Other,
            message: Some(crate::codegen_ay::shared::kani_any_loops::kani_any_unwind_message(passes)),
            write_mark: self.heap_state.write_mark(),
            merge_key: None,
        };
        self.emit_deferred_inline_checks_at(dcx.from_app, dcx.stmt_constraints, dcx.bb_idx, vec![check]);
    }

    /// A sound upper bound, as a pointer-width bitvector, on the iteration
    /// count of every loop the callee of `dcx` runs, or `None` (see the
    /// module docs for the table).
    fn model_call_trip_bound(&mut self, dcx: &DispatchCallContext<'_>) -> Option<Expr> {
        let path = self.model_call_callee_name(dcx.func)?;
        // The definition path carries the impl's generics in the middle
        // (`std::vec::Vec::<T, A>::retain`) and none on the method itself.
        let leaf = path.rsplit("::").next().unwrap_or(&path);
        let in_slice = path.contains("slice::<impl [T]>") || path.contains("slice::<impl [");
        let in_vec = path.contains("vec::Vec::<");
        let args = dcx.args;
        let const_bv = |n: u64| Expr::bitvec_const(n, POINTER_WIDTH);
        debug!(%path, leaf, in_slice, in_vec, "model call trip bound: callee");
        match leaf {
            "contains" if in_slice => {
                self.receiver_elem_is_primitive(args)?;
                self.model_call_receiver_len(args, 0, dcx)
            }
            "sort" if in_slice && self.receiver_elem_primitive_array_len(args).is_some() => {
                // Elements `[P; M]` of a primitive `P`, compared by core's
                // `Ord` for arrays: one loop over at most `M` elements per
                // comparison (`SliceOrd` / `SliceChain`, or `compare_bytes`
                // over `M` bytes for `u8` and `bool`), besides insertion
                // sort's own two loops of at most `len - 1` passes. The walk
                // of the comparison sees its loop and admits nothing, which
                // failed `vec![[x, 1u64], [x, 1]].sort()` under `unwind(3)`
                // where Kani proves it (walker fail-closed repair round 5,
                // `model_call_unwind_memcmp_dual.rs`).
                let elems = self.receiver_elem_primitive_array_len(args)?;
                let len = self.model_call_receiver_len(args, 0, dcx)?;
                let max = const_bv(u64::from(self.recursive_unwind_depth));
                Some(Expr::ite(
                    len.clone().bvule(const_bv(STABLE_SORT_INSERTION_MAX)),
                    bv_max(bv_saturating_dec(len), const_bv(elems)),
                    max,
                ))
            }
            "sort" | "sort_by" | "sort_by_key" if in_slice => {
                // Insertion sort up to 20 elements: an outer loop of len - 1
                // passes, and an inner shift of at most len - 1. The element
                // moves are copies; the comparisons are the closures and
                // function items the callee builds (`T::lt`, `|a, b| f(a) <
                // f(b)`), which must run no loop.
                self.closure_args_loop_free(args)?;
                self.callee_closures_loop_free(dcx.func)?;
                let len = self.model_call_receiver_len(args, 0, dcx)?;
                let max = const_bv(u64::from(self.recursive_unwind_depth));
                Some(Expr::ite(
                    len.clone().bvule(const_bv(STABLE_SORT_INSERTION_MAX)),
                    bv_saturating_dec(len),
                    max,
                ))
            }
            "retain" | "retain_mut" | "dedup" | "dedup_by" | "dedup_by_key" if in_vec => {
                let elem = self.receiver_elem_ty(args)?;
                self.drop_is_loop_free(elem)?;
                self.closure_args_loop_free(args)?;
                self.callee_closures_loop_free(dcx.func)?;
                self.model_call_receiver_len(args, 0, dcx)
            }
            "reverse" if in_slice => {
                // `len / 2` swaps, each `swap_nonoverlapping` of one element:
                // `size_of::<T>() / 8` chunk passes, the tail without a loop.
                let elem = self.receiver_elem_ty(args)?;
                let chunks = self.get_type_size(elem)? as u64 / 8;
                let len = self.model_call_receiver_len(args, 0, dcx)?;
                Some(bv_max(len.bvlshr(const_bv(1)), const_bv(chunks)))
            }
            "resize" if in_vec => {
                let elem = self.receiver_elem_ty(args)?;
                self.clone_is_loop_free(elem)?;
                self.drop_is_loop_free(elem)?;
                let len = self.model_call_receiver_len(args, 0, dcx)?;
                let new_len = self.model_call_usize_arg(args.get(1)?, dcx)?;
                Some(bv_max(len, new_len))
            }
            "from_elem" if path.contains("SpecFromElem") => {
                let elem_ty = args.first()?.ty(self.body.locals()).ok()?;
                self.clone_is_loop_free(elem_ty)?;
                self.model_call_usize_arg(args.get(1)?, dcx)
            }
            "drop" if path.contains("Vec<T, A> as std::ops::Drop") || path.contains("Vec<T, A> as core::ops::Drop") => {
                let elem = self.receiver_elem_ty(args)?;
                self.drop_is_loop_free(elem)?;
                self.model_call_receiver_len(args, 0, dcx)
            }
            "swap" if path.starts_with("std::mem::") || path.starts_with("core::mem::") => {
                // `swap_nonoverlapping(x, y, 1)`: one `for` over
                // `size_of::<T>() / 8` chunks; the tail swaps without a loop.
                let pointee = self.first_arg_pointee(args)?;
                Some(const_bv(self.get_type_size(pointee)? as u64 / 8))
            }
            "typed_swap_nonoverlapping" => {
                let pointee = self.first_arg_pointee(args)?;
                Some(const_bv(self.get_type_size(pointee)? as u64 / 8))
            }
            "pow" | "wrapping_pow" | "checked_pow" | "overflowing_pow" | "saturating_pow"
                if path.contains("num::<impl") =>
            {
                // Exponentiation by squaring: one pass per bit of the
                // exponent, the last of which leaves the loop, so its back
                // edge is taken bit_length - 1 times (the `while exp > 1`
                // variant runs bit_length - 1 passes).
                // `bit_length(exp) - 1 < U` exactly when `exp < 2^U` (measured
                // on Kani for exp in 1..=32, U in 1..=6, `probes/g1_pow_grid.rs`),
                // stated as that one comparison: the bound is 0 or U.
                let exp = self.translate_operand_with_modified(args.get(1)?, dcx.modified_locals)?;
                let width = exp.sort().bitvec_width()?;
                let unwind = self.recursive_unwind_depth;
                if unwind >= width {
                    return Some(const_bv(0));
                }
                let limit = Expr::bitvec_const(1u128 << unwind, width);
                Some(Expr::ite(exp.bvult(limit), const_bv(0), const_bv(u64::from(unwind))))
            }
            "next" if path.contains("FlatMap<") || path.contains("flatten::Flatten") => {
                // A concrete `flat_map(|s| s.chars())` over `n` string
                // literals (`codegen_iter_constructor`, traced exactly):
                // `FlattenCompat::next`'s one loop takes a back edge per
                // inner iterator it fetches, at most `n`; `Chars::next`, the
                // slice iterator's `next` and the closure run no loop. It
                // kept the plain check, which failed corpus
                // `Iterator/flat_map.rs` under `unwind(3)` where Kani proves
                // it (walker fail-closed repair round 5).
                let (_, iter_local) = self.iterator_receiver_expr_and_local(args, dcx.modified_locals)?;
                let outer = *self.collections.flatten_outer_len.get(&iter_local?)?;
                Some(const_bv(outer as u64))
            }
            "raw_eq" if path.ends_with("intrinsics::raw_eq") => {
                // Kani's `memcmp` over `size_of::<T>()` bytes, one pass per
                // byte; an array `==` the harness inliner unfolded reaches it.
                let TyKind::RigidTy(RigidTy::FnDef(_, generics)) = dcx.func.ty(self.body.locals()).ok()?.kind()
                else {
                    return None;
                };
                let compared = generics.0.iter().find_map(|arg| match arg {
                    rustc_public::ty::GenericArgKind::Type(ty) => Some(*ty),
                    _ => None,
                })?;
                Some(const_bv(self.get_type_size(compared)? as u64))
            }
            "compare_bytes" if path.ends_with("intrinsics::compare_bytes") => {
                // Kani's `memcmp` over the `bytes` argument, one pass per byte.
                self.model_call_usize_arg(args.get(2)?, dcx)
            }
            "eq" | "ne" | "spec_eq" | "spec_ne"
                if (path.starts_with("<[") && path.contains("PartialEq"))
                    || path.contains("PartialEq<[U; N]> for [T; N]")
                    || path.contains("SpecArrayEq<") =>
            {
                // `SpecArrayEq::spec_eq`, the array comparison's body, is what
                // an inlined `Box<[P; N]>` comparison reaches; without the
                // spelling `Box::new([1u8, 2, 3, 4]) == ..` under `unwind(5)`
                // failed closed where Kani proves it (walker fail-closed
                // review, round 1 of the repair after the merge with main,
                // `model_call_unwind_wrapped_eq_dual.rs` `w4`).
                // `[T; N] == [U; N]` with primitive (or unit) elements: one
                // comparison loop over the `N` elements (`SpecArrayEq`, the
                // slice comparison), or a bytewise compare without one. The
                // callee prints as the instance (`<[u8; 4] as PartialEq>::eq`)
                // or as its definition (`std::array::equality::<impl
                // PartialEq<[U; N]> for [T; N]>::eq`); only the first was
                // matched, and `mem_swap.rs` / `mem_replace.rs` failed their
                // array comparisons closed under `unwind(9)` where main and
                // Kani prove them.
                let ty = args.first()?.ty(self.body.locals()).ok()?;
                let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = ty.kind() else {
                    return None;
                };
                let TyKind::RigidTy(RigidTy::Array(elem, len)) = inner.kind() else {
                    return None;
                };
                (is_primitive(elem) || is_unit(elem)).then_some(())?;
                let len = len.eval_target_usize().ok()?;
                Some(const_bv(len.checked_mul(self.compared_units(elem)?)?))
            }
            "eq" | "ne" if path.contains("PartialEq<[U]> for [T]") => {
                // Slice equality with primitive (or unit) elements: the
                // lengths first, then one loop over the elements
                // (`iter().zip(..).all(..)`) or a bytewise compare.
                let elem = self.receiver_elem_ty(args)?;
                (is_primitive(elem) || is_unit(elem)).then_some(())?;
                let units = self.compared_units(elem)?;
                let len = self.model_call_receiver_len(args, 0, dcx)?;
                if units == 1 {
                    return Some(len);
                }
                if let ay_bindings::ExprValue::BitVecConst { value, .. } = len.value()
                    && let Ok(len) = u64::try_from(value)
                {
                    return Some(const_bv(len.checked_mul(units).unwrap_or(u64::MAX)));
                }
                // `len * units` without wrapping: past the pointer width the
                // count is the most a loop can run.
                let units = const_bv(units);
                let max = const_bv(u64::MAX);
                Some(Expr::ite(
                    len.clone().bvugt(max.bvudiv(units.clone())),
                    const_bv(u64::MAX),
                    len.bvmul(units),
                ))
            }
            "extend" if path.contains("Vec<T, A> as std::iter::Extend") => {
                // From a `Range` / `RangeInclusive` of integers or `char`:
                // `for_each` over its elements (`extend_trusted`). Kani fails
                // exactly when the range takes `U` steps for both kinds
                // (measured for `0..n`, `0..=n`, `2..5`, `5..3` and U in
                // 1..=7, `probes/g3_extend_grid.rs`: `RangeInclusive`'s fold
                // yields its last element after the loop), so the bound is
                // the step count, in the element type's own order and over
                // the surrogate gap for `char` (`range_span.rs`), or 0 for an
                // empty range. It compared zero-extended bounds unsigned,
                // which bounded `-2i32..3` by 0 and discharged Kani's
                // unwinding assertion (walker fail-closed repair round 5,
                // `range_extend_kinds_dual.rs`).
                let source = args.get(1)?;
                let ty = source.ty(self.body.locals()).ok()?;
                let (step, inclusive) = super::range_span::RangeStep::of_range_ty(ty)?;
                let (Operand::Copy(place) | Operand::Move(place)) = source else {
                    return None;
                };
                if !place.projection.is_empty() {
                    return None;
                }
                let (start, end) = self.resolve_range_bounds_from_local(place.local, dcx.modified_locals)?;
                let span = super::range_span::range_span(step, &start, &end)?;
                Some(span.loop_trips(inclusive))
            }
            "eq" | "ne" if path.contains("Iterator") => {
                // `iter_compare` runs one loop, `a.try_for_each(..)` over the
                // receiver, calling `b.next()` once per element and once
                // after it. Only the receiver's loop is bounded here, so the
                // other operand must run no loop in its `next`: a slice or
                // array iterator (or what one comes from by `IntoIterator`)
                // with primitive items. A `Filter` there runs a `find` loop
                // per call, and the receiver's length bounded it, which
                // discharged Kani's unwinding assertion on
                // `[1u32].iter().eq([1, 2, 3, 4, 5].iter().filter(..))` under
                // `unwind(3)` (walker fail-closed repair round 5,
                // `model_call_unwind_iter_eq_dual.rs`).
                let other_ty = args.get(1)?.ty(self.body.locals()).ok()?;
                loop_free_next_primitive_items(other_ty).then_some(())?;
                let receiver_ty = args.first()?.ty(self.body.locals()).ok()?;
                let TyKind::RigidTy(RigidTy::Adt(def, iter_args)) = receiver_ty.kind() else {
                    return None;
                };
                if !(def.name().contains("slice") && def.name().ends_with("Iter")) {
                    return None;
                }
                let elem = iter_args.0.iter().find_map(|arg| match arg {
                    rustc_public::ty::GenericArgKind::Type(ty) => Some(*ty),
                    _ => None,
                })?;
                is_primitive(elem).then_some(())?;
                let (iter_expr, _) = self.iterator_receiver_expr_and_local(args, dcx.modified_locals)?;
                let remaining = self.try_extract_iterator_remaining_len(&iter_expr)?;
                coerce_to_ptr_width(remaining)
            }
            "eq" | "ne" if path.contains("PartialEq") => {
                // `Option`, `Result`, `Box`, a reference or a tuple compares
                // its parts with no loop of its own; a part `[P; N]` of a
                // primitive or unit `P` runs Kani's `memcmp` over its bytes
                // (`shared::compare_loops`). Without the row
                // `Some([1u8, 2, 3, 4]) == ..` under `unwind(5)` failed closed
                // where main and Kani prove it (walker fail-closed review,
                // round 1 of the repair after the merge with main,
                // `model_call_unwind_wrapped_eq_dual.rs`). A `str`, slice or
                // `Vec` part keeps the plain check.
                use crate::codegen_ay::shared::compare_loops::{compare_loops, is_compared_wrapper};
                let pointee = self.first_arg_pointee(args)?;
                if !is_compared_wrapper(pointee) {
                    return None;
                }
                let size_of = |ty: Ty| self.get_type_size(ty).map(|bytes| bytes as u64);
                compare_loops(pointee, &size_of).constant_bound().map(const_bv)
            }
            _ => None,
        }
    }

    /// The data-dependent condition of a comparison's unwinding assertion:
    /// for `raw_eq::<T>` and for `==` / `!=` on an array, slice, `str`, `Vec`,
    /// or an `Option`, `Result` or tuple of them, true exactly when one of the
    /// loops Kani runs completes the declared bound's passes, read from the
    /// two values (`shared::compare_loops`). The bound alone read the loops as
    /// data-independent, so `([9u8, 2, 3, 4], 1u8) != ([1, 2, 3, 4], 1)` and
    /// `[1.0f32, 2.0, 3.0, 4.0] == ..` under `unwind(6)` failed closed where
    /// main and Kani prove them (walker fail-closed review, round 2 of the
    /// repair after the merge with main, `model_call_unwind_early_exit_dual.rs`).
    /// `None` when the callee is not such a comparison or a value is not read.
    fn model_call_compare_reach(&mut self, dcx: &DispatchCallContext<'_>) -> Option<Expr> {
        use super::codegen_call_misc::{CallMisc, Referent};
        use crate::codegen_ay::shared::compare_loops::{compare_reach, raw_eq_reach};
        let path = self.model_call_callee_name(dcx.func)?;
        let leaf = path.rsplit("::").next().unwrap_or(&path);
        let raw = leaf == "raw_eq" && path.ends_with("intrinsics::raw_eq");
        let is_eq = matches!(leaf, "eq" | "ne" | "spec_eq" | "spec_ne")
            && (path.contains("PartialEq") || path.contains("SpecArrayEq<"))
            && !path.contains("Iterator");
        if !raw && !is_eq {
            return None;
        }
        let pointee = self.first_arg_pointee(dcx.args)?;
        let unwind = u64::from(self.recursive_unwind_depth);
        if let TyKind::RigidTy(RigidTy::Str | RigidTy::Slice(_)) = pointee.kind() {
            // A `str` or slice: the two views the slice comparison reads
            // (`resolve_slice_backing`, the data at its offset).
            use crate::codegen_ay::shared::compare_loops::{SliceView, slice_compare_reach};
            let elem = match pointee.kind() {
                TyKind::RigidTy(RigidTy::Slice(elem)) => Some(elem),
                _ => None,
            };
            let view = |ctx: &mut Self, arg: &Operand| {
                let backing = ctx.resolve_slice_backing(arg, dcx.modified_locals)?;
                Some(SliceView {
                    len: backing.len.as_expr().clone(),
                    data: backing.data.as_expr().clone(),
                    offset: backing.offset.as_expr().clone(),
                })
            };
            let lhs = view(self, dcx.args.first()?)?;
            let rhs = view(self, dcx.args.get(1)?)?;
            let size_of = |ty: Ty| self.get_type_size(ty).map(|bytes| bytes as u64);
            let reach = slice_compare_reach(elem, &lhs, &rhs, unwind, &size_of);
            debug!(found = reach.is_some(), "model call compare reach: slice views");
            return Some(reach?.reaches);
        }
        let value = |ctx: &mut Self, arg: &Operand| {
            match ctx.resolve_ref_or_const_referent_tagged(arg, dcx.modified_locals)? {
                Referent::Value(val) => Some(val.into_expr()),
                Referent::Unreported(_) => None,
            }
        };
        let lhs = value(self, dcx.args.first()?);
        let rhs = value(self, dcx.args.get(1)?);
        debug!(
            lhs = ?lhs.as_ref().map(|e| e.sort().clone()),
            rhs = ?rhs.as_ref().map(|e| e.sort().clone()),
            ?pointee,
            "model call compare reach: referents"
        );
        let (lhs, rhs) = (lhs?, rhs?);
        let size_of = |ty: Ty| self.get_type_size(ty).map(|bytes| bytes as u64);
        let reach = if raw {
            raw_eq_reach(pointee, &lhs, &rhs, unwind, &size_of)
        } else {
            compare_reach(pointee, &lhs, &rhs, unwind, &size_of)
        };
        debug!(found = reach.is_some(), "model call compare reach: values");
        Some(reach?.reaches)
    }

    /// The callee's path as the instance the call resolves to names it.
    fn model_call_callee_name(&self, func: &Operand) -> Option<String> {
        let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func.ty(self.body.locals()).ok()?.kind() else {
            return None;
        };
        // The generic definition path (`<std::vec::Vec<T, A> as
        // std::ops::Drop>::drop`), not the substituted instance name.
        let instance = Instance::resolve(def, &args).ok()?;
        Some(instance.def.name())
    }

    /// The element type of the collection the first argument refers to (a
    /// slice, array or `Vec`, through references and raw pointers), or the
    /// pointee of a pointer to anything else.
    fn receiver_elem_ty(&self, args: &[Operand]) -> Option<Ty> {
        let ty = args.first()?.ty(self.body.locals()).ok()?;
        let pointee = match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => inner,
            _ => ty,
        };
        Some(match pointee.kind() {
            TyKind::RigidTy(RigidTy::Slice(elem) | RigidTy::Array(elem, _)) => elem,
            TyKind::RigidTy(RigidTy::Adt(def, adt_args)) if def.name().ends_with("Vec") => {
                adt_args.0.iter().find_map(|arg| match arg {
                    rustc_public::ty::GenericArgKind::Type(ty) => Some(*ty),
                    _ => None,
                })?
            }
            _ => pointee,
        })
    }

    /// The loop passes one element of `elem` costs a comparison: Kani runs a
    /// bytewise-comparable element (`raw_eq`, `compare_bytes`) through CBMC's
    /// `memcmp`, one pass per BYTE, and anything else one pass per element,
    /// so the size in bytes (at least 1) bounds both. The table counted
    /// elements, and `[x, 7u32] == [x, 7]` (eight bytes) was bounded by 2
    /// under `unwind(3)` (walker fail-closed repair round 5,
    /// `model_call_unwind_memcmp_dual.rs`).
    ///
    /// A float is not bytewise-comparable (`core/src/cmp/bytewise.rs`): its
    /// arrays and slices compare element by element, one pass each, and
    /// `[1.0f32, 2.0, 3.0, 4.0] == ..` under `unwind(6)` was bounded by 16
    /// (walker fail-closed review, round 2 of the repair after the merge with
    /// main).
    fn compared_units(&self, elem: Ty) -> Option<u64> {
        if matches!(elem.kind(), TyKind::RigidTy(RigidTy::Float(_))) {
            return Some(1);
        }
        Some((self.get_type_size(elem)? as u64).max(1))
    }

    /// `M` when the first argument's elements are arrays `[P; M]` of a
    /// primitive `P`.
    fn receiver_elem_primitive_array_len(&self, args: &[Operand]) -> Option<u64> {
        let elem = self.receiver_elem_ty(args)?;
        let TyKind::RigidTy(RigidTy::Array(inner, len)) = elem.kind() else {
            return None;
        };
        is_primitive(inner).then_some(())?;
        len.eval_target_usize().ok()
    }

    /// The pointee of the first argument, a reference or raw pointer.
    fn first_arg_pointee(&self, args: &[Operand]) -> Option<Ty> {
        match args.first()?.ty(self.body.locals()).ok()?.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => Some(inner),
            _ => None,
        }
    }

    /// The receiver's element type when it is a primitive.
    fn receiver_elem_is_primitive(&self, args: &[Operand]) -> Option<Ty> {
        let elem = self.receiver_elem_ty(args)?;
        is_primitive(elem).then_some(elem)
    }

    /// `Some(())` when every closure or function-item argument runs no loop.
    fn closure_args_loop_free(&self, args: &[Operand]) -> Option<()> {
        use super::codegen_call_virtual_inline::uncertified_check::instance_may_loop_cached;
        let stubs = crate::kani_middle::transform::walker_stub_map();
        for arg in args.iter().skip(1) {
            let ty = arg.ty(self.body.locals()).ok()?;
            let ty = match ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
                _ => ty,
            };
            let instance = match ty.kind() {
                TyKind::RigidTy(RigidTy::Closure(def, closure_args)) => {
                    [ClosureKind::FnMut, ClosureKind::Fn, ClosureKind::FnOnce]
                        .into_iter()
                        .find_map(|kind| Instance::resolve_closure(def, &closure_args, kind).ok())?
                }
                TyKind::RigidTy(RigidTy::FnDef(def, fn_args)) => Instance::resolve(def, &fn_args).ok()?,
                TyKind::RigidTy(RigidTy::FnPtr(..)) => return None,
                _ => continue,
            };
            if instance_may_loop_cached(self, instance, &stubs) {
                return None;
            }
        }
        Some(())
    }

    /// `Some(())` when every closure the callee's body builds, and every
    /// function item it passes as a value, runs no loop (the comparison
    /// `stable_sort` is handed, `dedup`'s `|a, b| a == b`).
    fn callee_closures_loop_free(&self, func: &Operand) -> Option<()> {
        use super::codegen_call_virtual_inline::uncertified_check::instance_may_loop_cached;
        use crate::callee_body::CalleeBody;
        use rustc_public::mir::{AggregateKind, Rvalue, StatementKind, TerminatorKind};
        let TyKind::RigidTy(RigidTy::FnDef(def, fn_args)) = func.ty(self.body.locals()).ok()?.kind() else {
            return None;
        };
        let callee = Instance::resolve(def, &fn_args).ok()?;
        let body = callee.callee_body()?;
        let stubs = crate::kani_middle::transform::walker_stub_map();
        for block in &body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(_, Rvalue::Aggregate(AggregateKind::Closure(cdef, cargs), _)) =
                    &stmt.kind
                {
                    let instance = [ClosureKind::FnMut, ClosureKind::Fn, ClosureKind::FnOnce]
                        .into_iter()
                        .find_map(|kind| Instance::resolve_closure(*cdef, cargs, kind).ok())?;
                    if instance_may_loop_cached(self, instance, &stubs) {
                        return None;
                    }
                }
            }
            if let TerminatorKind::Call { args, .. } = &block.terminator.kind {
                // A closure without captures is a zero-sized CONSTANT, not an
                // aggregate: `Vec::dedup` passes `|a, b| a == b` to `dedup_by`
                // as one, so its `&str` comparison (`compare_bytes`, a loop in
                // Kani) went unread and `vec!["abcdef", "abcdef"].dedup()`
                // under `unwind(3)` verified clean where Kani fails (walker
                // fail-closed repair round 5, `model_call_unwind_memcmp_dual.rs`).
                for arg in args {
                    let Ok(arg_ty) = arg.ty(body.locals()) else {
                        return None;
                    };
                    let arg_ty = match arg_ty.kind() {
                        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
                        _ => arg_ty,
                    };
                    let instance = match arg_ty.kind() {
                        TyKind::RigidTy(RigidTy::FnDef(fdef, fargs)) => Instance::resolve(fdef, &fargs).ok()?,
                        TyKind::RigidTy(RigidTy::Closure(cdef, cargs)) => {
                            [ClosureKind::FnMut, ClosureKind::Fn, ClosureKind::FnOnce]
                                .into_iter()
                                .find_map(|kind| Instance::resolve_closure(cdef, &cargs, kind).ok())?
                        }
                        _ => continue,
                    };
                    if instance_may_loop_cached(self, instance, &stubs) {
                        return None;
                    }
                }
            }
        }
        Some(())
    }

    /// `Some(())` when `<ty as Clone>::clone` runs no loop (a `Copy`
    /// primitive, or a clone the loop walk proves loop-free).
    fn clone_is_loop_free(&self, ty: Ty) -> Option<()> {
        if is_primitive(ty) {
            return Some(());
        }
        let TyKind::RigidTy(RigidTy::Adt(def, adt_args)) = ty.kind() else {
            return None;
        };
        // `Vec<P>` of a primitive `P`: `to_vec` copies (`ConvertVec` for
        // `Copy`), with no loop.
        if def.name().ends_with("Vec") {
            let elem = adt_args.0.iter().find_map(|arg| match arg {
                rustc_public::ty::GenericArgKind::Type(ty) => Some(*ty),
                _ => None,
            })?;
            return is_primitive(elem).then_some(());
        }
        None
    }

    /// `Some(())` when dropping a `ty` runs no loop. Rule A
    /// (`shared/mono_ty.rs`): a `ty` with unresolved parameters has no drop
    /// glue to inspect, so it is not known loop-free.
    fn drop_is_loop_free(&self, ty: Ty) -> Option<()> {
        use super::codegen_call_virtual_inline::uncertified_check::instance_may_loop_cached;
        let drop = crate::codegen_ay::shared::mono_ty::drop_in_place(ty)?;
        if drop.is_empty_shim() {
            return Some(());
        }
        let stubs = crate::kani_middle::transform::walker_stub_map();
        (!instance_may_loop_cached(self, drop, &stubs)).then_some(())
    }

    /// The current length of the collection argument `idx` refers to, as the
    /// collection models read it: the length state of the local the argument
    /// borrows (directly, or through the slice a `Vec` deref produced), or an
    /// array's static length. NOT the length var of the reference temporary
    /// itself: that one is seeded when the borrow is taken and was measured
    /// stale (`u3_vec_retain_u8_safe` read the entry value of `&mut v`'s
    /// length, unconstrained, where `v` held six elements).
    fn model_call_receiver_len(
        &self,
        args: &[Operand],
        idx: usize,
        _dcx: &DispatchCallContext<'_>,
    ) -> Option<Expr> {
        let arg = args.get(idx)?;
        let (Operand::Copy(place) | Operand::Move(place)) = arg else {
            return None;
        };
        if !place.projection.is_empty() {
            return None;
        }
        let len_of = |local: usize| {
            self.collections.len_state.get_len_var(local).cloned().map(|var| self.collection_current_len(&var))
        };
        let array_len = |ty: Ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::Array(_, len)) => len.eval_target_usize().ok(),
            _ => None,
        };
        if let Some(target) = self.ref_resolution.ref_targets.get(&place.local)
            && target.projections.is_empty()
        {
            if let Some(len) = len_of(target.local) {
                return coerce_to_ptr_width(len);
            }
            if let Some(len) = self.body.locals().get(target.local).and_then(|decl| array_len(decl.ty)) {
                return Some(Expr::bitvec_const(len, POINTER_WIDTH));
            }
        }
        if let Some(&vec_local) = self.ref_resolution.slice_to_vec_local.get(&place.local)
            && let Some(len) = len_of(vec_local)
        {
            return coerce_to_ptr_width(len);
        }
        // The slice's own length as the lane tracks it for its bounds checks
        // (`ref_resolution.subslice_len`: a `str::as_bytes` view, a subslice,
        // a `Vec`'s slice view): `"hello" == "hello"` (`Slice/main.rs`),
        // `my_vec == [72, 105]` and `v[0..n] == w` compared their bytes
        // through a slice comparison whose length nothing else gave.
        if let Some(len) = self.ref_resolution.subslice_len.get(&place.local) {
            return coerce_to_ptr_width(len.clone());
        }
        let ty = arg.ty(self.body.locals()).ok()?;
        if let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = ty.kind()
            && let Some(len) = array_len(inner)
        {
            return Some(Expr::bitvec_const(len, POINTER_WIDTH));
        }
        // A slice made by unsizing a reference to an array (the argument's
        // one definition is `&[T; N] as &[T]`): the array's static length.
        if let Some(len) = self.unsized_array_len(place.local) {
            return Some(Expr::bitvec_const(len, POINTER_WIDTH));
        }
        debug!(idx, arg = ?arg, "model call trip bound: no length for the argument");
        None
    }

    /// The static length `N` of the array a slice local was unsized from,
    /// when its only definition in the body is a `PointerCoercion(Unsize)`
    /// cast of an `&[T; N]` / `&mut [T; N]`, a full-range index of an
    /// `[T; N]`, or a full-range index (`<[T] as Index<RangeFull>>::index`,
    /// `index_mut`) of such a slice, through reborrows (`&(*x)`) and copies:
    /// an array `==` the harness inliner unfolded compares `a[..]` with
    /// `b[..]` (`model_call_unwind_bound_dual.rs` `b5`).
    fn unsized_array_len(&self, local: usize) -> Option<u64> {
        self.unsized_array_len_at(local, 6)
    }

    fn unsized_array_len_at(&self, local: usize, depth: u32) -> Option<u64> {
        use rustc_public::mir::{CastKind, PointerCoercion, Rvalue, StatementKind, TerminatorKind};
        enum Def<'a> {
            Unsize(&'a Operand),
            FullIndex(&'a Operand, &'a [Operand]),
            // `&(*x)`, `&mut (*x)` or a plain copy of `x`: the same slice.
            Same(usize),
        }
        let mut found: Option<Def<'_>> = None;
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                    continue;
                };
                if place.local != local {
                    continue;
                }
                if found.is_some() || !place.projection.is_empty() {
                    return None;
                }
                found = Some(match rvalue {
                    Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), op, _) => Def::Unsize(op),
                    Rvalue::Ref(_, _, src)
                        if matches!(src.projection.as_slice(), [rustc_public::mir::ProjectionElem::Deref]) =>
                    {
                        Def::Same(src.local)
                    }
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) if src.projection.is_empty() => {
                        Def::Same(src.local)
                    }
                    _ => return None,
                });
            }
            if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                && destination.local == local
            {
                if found.is_some() || !destination.projection.is_empty() {
                    return None;
                }
                found = Some(Def::FullIndex(func, args));
            }
        }
        match found? {
            Def::Unsize(op) => {
                let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = op.ty(self.body.locals()).ok()?.kind() else {
                    return None;
                };
                let TyKind::RigidTy(RigidTy::Array(_, len)) = inner.kind() else {
                    return None;
                };
                len.eval_target_usize().ok()
            }
            Def::Same(src) => {
                if depth == 0 {
                    return None;
                }
                self.unsized_array_len_at(src, depth - 1)
            }
            Def::FullIndex(func, args) => {
                if depth == 0 {
                    return None;
                }
                let TyKind::RigidTy(RigidTy::FnDef(def, generics)) = func.ty(self.body.locals()).ok()?.kind() else {
                    return None;
                };
                let name = def.name();
                if !(name.ends_with("ops::Index::index") || name.ends_with("ops::IndexMut::index_mut")) {
                    return None;
                }
                let types: Vec<Ty> = generics
                    .0
                    .iter()
                    .filter_map(|arg| match arg {
                        rustc_public::ty::GenericArgKind::Type(ty) => Some(*ty),
                        _ => None,
                    })
                    .collect();
                let [self_ty, idx_ty] = types.as_slice() else {
                    return None;
                };
                let TyKind::RigidTy(RigidTy::Adt(idx_def, _)) = idx_ty.kind() else {
                    return None;
                };
                if !idx_def.name().ends_with("ops::RangeFull") {
                    return None;
                }
                match self_ty.kind() {
                    // `a[..]` of an array: its static length.
                    TyKind::RigidTy(RigidTy::Array(_, len)) => return len.eval_target_usize().ok(),
                    TyKind::RigidTy(RigidTy::Slice(_)) => {}
                    _ => return None,
                }
                let (Operand::Copy(place) | Operand::Move(place)) = args.first()? else {
                    return None;
                };
                if !place.projection.is_empty() {
                    return None;
                }
                self.unsized_array_len_at(place.local, depth - 1)
            }
        }
    }

    /// A `usize` argument's value at the call.
    fn model_call_usize_arg(&mut self, arg: &Operand, dcx: &DispatchCallContext<'_>) -> Option<Expr> {
        coerce_to_ptr_width(self.translate_operand_with_modified(arg, dcx.modified_locals)?)
    }
}

/// An integer, `bool`, `char` or float: no loop in its `==`, `<`, clone or
/// drop.
fn is_primitive(ty: Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(
            RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Bool | RigidTy::Char | RigidTy::Float(_)
        )
    )
}

/// Does `ty`, as the `other` operand of `Iterator::eq` (an `IntoIterator`),
/// iterate with a `next` that runs no loop and yields primitive items (or
/// references to them)? A `core::slice::Iter`, a `core::array::IntoIter`, an
/// array by value, or a reference to a slice, an array or a `Vec`.
fn loop_free_next_primitive_items(ty: Ty) -> bool {
    let first_type_arg = |args: &rustc_public::ty::GenericArgs| {
        args.0.iter().find_map(|arg| match arg {
            rustc_public::ty::GenericArgKind::Type(ty) => Some(*ty),
            _ => None,
        })
    };
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Array(elem, _)) => is_primitive(elem),
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => match inner.kind() {
            TyKind::RigidTy(RigidTy::Slice(elem) | RigidTy::Array(elem, _)) => is_primitive(elem),
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                let name = def.name();
                name.rsplit("::").next() == Some("Vec")
                    && name.contains("vec")
                    && first_type_arg(&args).is_some_and(is_primitive)
            }
            _ => false,
        },
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let name = def.name();
            let last = name.rsplit("::").next().unwrap_or(&name);
            let iterator = (last == "Iter" && name.contains("slice"))
                || (last == "IntoIter" && name.contains("array"));
            iterator && first_type_arg(&args).is_some_and(is_primitive)
        }
        _ => false,
    }
}

/// The unit type `()`.
fn is_unit(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Tuple(elems)) if elems.is_empty())
}

/// `a - 1`, or 0 for `a == 0`, unsigned.
fn bv_saturating_dec(a: Expr) -> Expr {
    let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
    Expr::ite(a.clone().eq(zero.clone()), zero, a.bvsub(Expr::bitvec_const(1u64, POINTER_WIDTH)))
}

/// `max(a, b)`, unsigned.
fn bv_max(a: Expr, b: Expr) -> Expr {
    Expr::ite(a.clone().bvuge(b.clone()), a, b)
}

/// `value` as an unsigned pointer-width bitvector, or `None` for a non-bitvector
/// or a wider value.
fn coerce_to_ptr_width(value: Expr) -> Option<Expr> {
    let width = value.sort().bitvec_width()?;
    match width.cmp(&POINTER_WIDTH) {
        std::cmp::Ordering::Equal => Some(value),
        std::cmp::Ordering::Less => Some(value.zero_extend(POINTER_WIDTH - width)),
        std::cmp::Ordering::Greater => None,
    }
}
