// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Iterator adapter semantic model helpers for AY statement codegen.
//!
//! Split from `collections/iter.rs` to keep core iterator state-transition logic
//! focused on concrete iterator types while adapter over-approximation remains here.

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::{BasicBlockIdx, BinOp, Operand, Place};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::{debug, warn};

use super::super::IntoOption;
use super::super::StatementCodegen;
use super::super::dispatch::InlineArgValue;
use super::super::{AdapterStage, AdapterStageKind};

/// Parameter layout of a terminal fold/try_fold closure, as resolved from its
/// instance body. The closure may inline as its DIRECT body (`[env, acc, item]`)
/// or as the rust-call SHIM (`[env, (acc, item)]`).
enum FoldArgShape {
    Direct { env_ty: Ty, acc_ty: Ty, item_ty: Ty },
    Tupled { env_ty: Ty, tuple_ty: Ty },
}
use super::iter::get_bmc_iterator_unsound_skip_count;
use crate::codegen_ay::context::{
    get_unconstrained_assignment_count, get_unsupported_construct_fallback_count,
};
use crate::codegen_ay::float_arithmetic::{
    bv_float_binop, bv_float_binop_chc, bv_float_binop_generates_nan, float_width_to_eb_sb,
};
use crate::codegen_ay::iter_sum_summand::{SumSummand, classify_iter_sum};
use crate::codegen_ay::provenance::Val;
use crate::codegen_ay::types::{CtorFieldExt, POINTER_WIDTH, bool_sort, ptr_sort};

/// The description rustc gives the overflow check of `a + b`, which std's
/// integer `Sum` performs per element.
const ADD_OVERFLOW_MESSAGE: &str = "attempt to add with overflow";

/// The one field of the datatype this lane gives a `Wrapping<T>` or
/// `Saturating<T>` (`Saturating_u8_mk (fld_0 (_ BitVec 8))`): the sum is
/// computed over that field and rebuilt with the constructor.
struct SumNewtype {
    datatype: String,
    constructor: String,
    field: String,
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    pub(in crate::codegen_ay::statement) fn codegen_iter_map_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("Iterator::map requires at least 1 arg (self)");
            return target;
        }

        let iter_expr = self.codegen_operand(&args[0]);
        if let Some(iter_expr) = iter_expr {
            let map_iter = self.make_map_iterator(iter_expr);
            self.assign_value_to_place(destination, map_iter);
            self.record_adapter_stage(args, destination, AdapterStageKind::Map);
        } else {
            self.codegen_symbolic_result(destination);
        }
        target
    }

    pub(in crate::codegen_ay::statement) fn codegen_iter_filter_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("Iterator::filter requires at least 1 arg (self)");
            return target;
        }

        let iter_expr = self.codegen_operand(&args[0]);
        if let Some(iter_expr) = iter_expr {
            let filter_iter = self.make_filter_iterator(iter_expr);
            self.assign_value_to_place(destination, filter_iter);
            self.record_adapter_stage(args, destination, AdapterStageKind::Filter);
        } else {
            self.codegen_symbolic_result(destination);
        }
        target
    }

    /// Iterator::zip(self, other) -> Zip<Self, Other> — pairs two iterators.
    /// Over-approximated: destination gets symbolic value since Zip adapter sort
    /// is typically flattened to BV64 in both encodings. Part of #3381.
    pub(in crate::codegen_ay::statement) fn codegen_iter_zip_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("Iterator::zip requires at least 1 arg (self)");
            return target;
        }

        // Zip wraps two iterators. The output sort is typically opaque (BV64),
        // so we produce a symbolic result. The CHC encoding handles remaining_len
        // propagation via adapter_remaining_len side-channel.
        self.codegen_symbolic_result(destination);
        target
    }

    /// Zip<A, B>::next(&mut self) -> Option<(A::Item, B::Item)>.
    /// Over-approximated: the tuple payload is symbolic. Follows the same pattern
    /// as MapNext — advance the inner iterator (if Datatype) and produce
    /// Option<symbolic> or symbolic fallback. Part of #3381.
    pub(in crate::codegen_ay::statement) fn codegen_zip_next_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("Zip::next requires 1 arg (self)");
            return target;
        }

        // Try the Datatype path: resolve inner iterator and advance.
        // Zip adapters have fld_a/fld_b (or fld_iter for single-wrapped),
        // but in practice the sort is typically BV64 (opaque).
        if let Some((base, zip_iter)) = self.resolve_collection_base(&args[0]) {
            // Try fld_a first (standard Zip field), then fld_iter (adapter wrapper)
            let advance_result = self
                .advance_wrapped_iterator(&zip_iter, "fld_a")
                .or_else(|| self.advance_wrapped_iterator(&zip_iter, "fld_iter"));
            if let Some((new_inner, inner_result)) = advance_result {
                self.declare_inner_option_sort(&inner_result);
                let new_zip = self.update_wrapped_iterator(&zip_iter, new_inner);
                self.env_update(base, new_zip);

                if let Some(option_sort) =
                    self.resolve_adapter_option_sort(destination, &inner_result)
                    && let Some(payload_sort) = Self::option_payload_sort(&option_sort)
                {
                    let sym_name = self.ctx.fresh_name("zip_next_value");
                    let sym_value = self.ctx.declare_var(&sym_name, payload_sort);
                    self.ctx.bmc_sound_havoc("zip_next_value");
                    let some_value = self.make_option_some(&option_sort, sym_value);
                    let none_value = self.make_option_none(&option_sort);
                    let inner_is_some = self.make_option_is_some(&inner_result);
                    let result = Expr::ite(inner_is_some, some_value, none_value);
                    self.assign_value_to_place(destination, result);
                    return target;
                }
            }
        }

        // Fallback: symbolic result (sound over-approximation).
        debug!("ZipNext: falling back to symbolic result");
        self.codegen_symbolic_result(destination);
        target
    }

    pub(in crate::codegen_ay::statement) fn codegen_iter_fold_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // First attempt the SOUND element-wise unroll that replays the recorded
        // Filter/Map closures and threads the fold/try_fold accumulator closure
        // (mirrors `codegen_iter_all_any`). Returns true iff a sound result was
        // assigned; otherwise fall through to the fail-closed havoc below.
        if self.try_iter_fold_unroll(args, destination) {
            return target;
        }

        if args.len() >= 2
            // `fold`/`try_fold` take `self` BY VALUE: the receiver operand
            // translates to the iterator value, not to its address.
            && let Some(iter_expr) = self.codegen_operand(&args[0]).map(Val::of_value)
            && let Some(init_expr) = self.codegen_operand(&args[1])
            && let Some(has_remaining) = self.iter_has_remaining_items(&iter_expr)
        {
            // SOUNDNESS: use the DESTINATION sort, not `init_expr.sort()`. For
            // `try_fold` the result is `Result<Acc, E>` / `ControlFlow`, NOT the
            // accumulator sort, so seeding the symbolic with the init sort builds an
            // ILL-SORTED value that corrupts the downstream `?` / `.ok()` desugaring
            // (the discriminant read of a bitvector-as-enum is garbage, which was
            // observed to make the consuming path VACUOUSLY infeasible — a spurious
            // "no checks" / vacuous proof). With the destination sort the havoc is a
            // well-typed symbolic over-approximation. Fall back to the init sort
            // only when the destination sort cannot be inferred.
            let sym_sort =
                self.infer_sort_from_place(destination).unwrap_or_else(|| init_expr.sort().clone());
            let sym_name = self.ctx.fresh_name("iter_fold_value");
            let symbolic_result = self.ctx.declare_var(&sym_name, sym_sort);
            let result = Expr::ite(has_remaining.into_expr(), symbolic_result, init_expr);
            self.assign_value_to_place(destination, result);
            // FAIL-CLOSED: the per-element fold closure is captured into the opaque
            // Filter/Map adapter value and is not recoverable at the fold call site,
            // so the accumulator is HAVOCED. For `try_fold` the havoc is a symbolic
            // MULTI-VARIANT enum (`Result`/`ControlFlow`), which the model further
            // approximates (variant-0 defaulting) — this can make the consuming path
            // VACUOUSLY infeasible and yield a spurious "verified". Record a fallback
            // so the verdict DEMOTES instead of falsely passing. (The over-approx
            // value is still emitted; only the verdict is fail-closed.)
            self.ctx.unsupported_with_fallback(
                "iter_fold_unmodeled",
                "fold/try_fold accumulator havoced (closure not recoverable at call site)",
            );
            return target;
        }

        debug!("IterFold: falling back to symbolic result");
        self.ctx
            .unsupported_with_fallback("iter_fold_unmodeled", "fold/try_fold symbolic fallback");
        self.codegen_symbolic_result(destination);
        target
    }

    pub(in crate::codegen_ay::statement) fn codegen_iter_sum_stub(
        &mut self,
        func: Option<&Operand>,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // What the call adds, from its Rust types (`iter_sum_summand`): the
        // SMT sort alone cannot tell a float, an overflow-checked integer, a
        // `Saturating` or a user `Sum` impl apart. Read from THIS call's
        // callee operand: two sums can write one place.
        let summand = func
            .map_or(SumSummand::Unknown, |func| classify_iter_sum(self.body, func, destination));

        // First attempt the SOUND element-wise unroll (replays recorded
        // Filter/Map closures and sums the kept, mapped elements). Returns true
        // iff a sound result was assigned; otherwise fall through to the
        // fail-closed havoc below.
        if self.try_iter_sum_unroll(args, destination, summand) {
            return target;
        }

        if !args.is_empty()
            // `sum` takes `self` BY VALUE: the receiver operand translates to
            // the iterator value, not to its address.
            && let Some(iter_expr) = self.codegen_operand(&args[0]).map(Val::of_value)
            && let Some(result_sort) = self.infer_sort_from_place(destination)
            && let Some(has_remaining) = self.iter_has_remaining_items(&iter_expr)
        {
            let sym_name = self.ctx.fresh_name("iter_sum_value");
            let symbolic_result = self.ctx.declare_var(&sym_name, result_sort.clone());
            // The empty sum is `Sum::sum` of no items: `0`, or `-0.0` for a
            // float. For an impl this stub does not know, it is unknown too,
            // so the havoc covers that case as well.
            let result = match Self::sum_identity(summand, &result_sort) {
                Some(identity) => Expr::ite(has_remaining.into_expr(), symbolic_result, identity),
                None => symbolic_result,
            };
            self.assign_value_to_place(destination, result);
            // FAIL-CLOSED: see `codegen_iter_fold_stub`. The summed values are not
            // recovered here (the map/filter closures are not threaded to the sum
            // call site), so the total is havoced. Record a fallback so the verdict
            // DEMOTES rather than passing on an unmodelled accumulation.
            self.ctx.unsupported_with_fallback("iter_sum_unmodeled", "sum accumulator havoced");
            return target;
        }

        debug!("IterSum: falling back to symbolic result");
        self.ctx.unsupported_with_fallback("iter_sum_unmodeled", "sum symbolic fallback");
        self.codegen_symbolic_result(destination);
        target
    }

    /// Declare the `Option` sort of an adapter's INNER `next()` result. It is
    /// built from the element's sort (`Option_bv8`), not from the program's
    /// `Option` type (`Option_u8`), occurs only inside the stub's terms, and
    /// was never declared: every query that reached the solver with a `Map`,
    /// `Filter` or `Zip` `next()` in it was rejected (`unknown constant
    /// Some_Option_bv8`) and came out INCONCLUSIVE (AY alignment round 8,
    /// review round 5).
    fn declare_inner_option_sort(&mut self, inner_result: &Expr) {
        let sort = inner_result.sort().clone();
        self.ctx.ensure_datatype_declared(&sort);
    }

    /// The conservative check for the closures of a receiver's adapter chain
    /// that a stub does not run (`iter_closure_obligation`): a fresh flag
    /// alone, so the check fails whenever the call is reached, and booked as a
    /// sound havoc so a counterexample of this harness is never certified
    /// Genuine.
    pub(in crate::codegen_ay::statement) fn record_unmodeled_closure_check(&mut self) {
        let name = self.ctx.fresh_name("iter_adapter_closure_unmodeled");
        let flag = self.ctx.declare_var(&name, bool_sort());
        self.ctx.bmc_sound_havoc("iter_adapter_closure_unmodeled");
        self.record_violation_guarded_with_message(
            flag,
            "unsupported_check",
            Some(crate::codegen_ay::iter_closure_obligation::UNMODELED_CLOSURE_MESSAGE.to_string()),
        );
    }

    pub(in crate::codegen_ay::statement) fn codegen_map_next_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("Map::next requires 1 arg (self)");
            return target;
        }

        if let Some((base, map_iter)) = self.resolve_collection_base(&args[0])
            && let Some((new_inner, inner_result)) =
                self.advance_wrapped_iterator(&map_iter, "fld_iter")
        {
            self.declare_inner_option_sort(&inner_result);
            let new_map = self.update_wrapped_iterator(&map_iter, new_inner);
            self.env_update(base, new_map);

            if let Some(option_sort) = self.resolve_adapter_option_sort(destination, &inner_result)
                && let Some(mapped_sort) = Self::option_payload_sort(&option_sort)
            {
                let mapped_name = self.ctx.fresh_name("map_next_value");
                let mapped_value = self.ctx.declare_var(&mapped_name, mapped_sort);
                self.ctx.bmc_sound_havoc("map_next_value");
                let some_value = self.make_option_some(&option_sort, mapped_value);
                let none_value = self.make_option_none(&option_sort);
                let inner_is_some = self.make_option_is_some(&inner_result);
                let result = Expr::ite(inner_is_some, some_value, none_value);
                self.assign_value_to_place(destination, result);
                return target;
            }
        }

        self.codegen_symbolic_result(destination);
        target
    }

    pub(in crate::codegen_ay::statement) fn codegen_filter_next_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("Filter::next requires 1 arg (self)");
            return target;
        }

        if let Some((base, filter_iter)) = self.resolve_collection_base(&args[0])
            && let Some((new_inner, inner_result)) =
                self.advance_wrapped_iterator(&filter_iter, "fld_iter")
        {
            self.declare_inner_option_sort(&inner_result);
            let new_filter = self.update_wrapped_iterator(&filter_iter, new_inner);
            self.env_update(base, new_filter);

            if let Some(option_sort) = self.resolve_adapter_option_sort(destination, &inner_result)
                && let Some(item_sort) = Self::option_payload_sort(&option_sort)
            {
                let item_name = self.ctx.fresh_name("filter_next_value");
                let item_value = self.ctx.declare_var(&item_name, item_sort);
                let keep_name = self.ctx.fresh_name("filter_next_keep");
                let keep_item = self.ctx.declare_var(&keep_name, bool_sort());
                self.ctx.bmc_sound_havoc("filter_next_value");
                let some_value = self.make_option_some(&option_sort, item_value);
                let none_value = self.make_option_none(&option_sort);
                let when_inner_some = Expr::ite(keep_item, some_value, none_value.clone());
                let inner_is_some = self.make_option_is_some(&inner_result);
                let result = Expr::ite(inner_is_some, when_inner_some, none_value);
                self.assign_value_to_place(destination, result);
                return target;
            }
        }

        self.codegen_symbolic_result(destination);
        target
    }

    #[must_use]
    fn resolve_adapter_option_sort(
        &self,
        destination: &Place,
        inner_result: &Expr,
    ) -> Option<Sort> {
        self.infer_sort_from_place(destination).filter(Self::is_option_like_sort).or_else(|| {
            let sort = inner_result.sort().clone();
            Self::is_option_like_sort(&sort).then_some(sort)
        })
    }

    #[must_use]
    fn is_option_like_sort(sort: &Sort) -> bool {
        use crate::codegen_ay::names;
        let Some(dt) = sort.datatype_sort() else {
            return false;
        };
        let has_none = dt.constructors.iter().any(|ctor| names::is_none_constructor(&ctor.name));
        let has_some = dt.constructors.iter().any(|ctor| names::is_some_constructor(&ctor.name));
        if has_none && has_some {
            return true;
        }
        let has_empty_variant = dt.constructors.iter().any(|ctor| ctor.fields.is_empty());
        let has_payload_variant = dt.constructors.iter().any(|ctor| ctor.fields.len() == 1);
        has_empty_variant && has_payload_variant
    }

    #[must_use]
    fn option_payload_sort(option_sort: &Sort) -> Option<Sort> {
        use crate::codegen_ay::names;
        let dt = option_sort.datatype_sort()?;
        for ctor in &dt.constructors {
            if names::is_some_constructor(&ctor.name) {
                return ctor.fields.first().map(|field| field.sort.clone());
            }
        }
        for ctor in &dt.constructors {
            if ctor.fields.len() == 1 && !names::is_none_constructor(&ctor.name) {
                return Some(ctor.fields[0].sort.clone());
            }
        }
        None
    }

    /// `has_remaining` predicate for an iterator RECEIVER VALUE.
    ///
    /// Address-vs-value (wave 1): `iter_expr` is the iterator datatype itself —
    /// a [`Val`], never a location — so `fld_pos` is a VALUE too. The old guard
    /// here read `pos.sort().bitvec_width() == Some(POINTER_WIDTH)`, i.e. "is
    /// the cursor a pointer?", which is nonsense for a value and only ever
    /// happened to work because it agreed with the width of the thing `pos` is
    /// compared against. The real precondition is that `bvult`'s two operands
    /// agree in width, so the test is now against `len`'s own sort. `len` is
    /// selected at `ptr_sort()` and `vec_field_select` returns that sort on both
    /// its branches, so the two tests accept exactly the same expressions.
    #[must_use]
    fn iter_has_remaining_items(&mut self, iter_expr: &Val) -> Option<Val> {
        use crate::codegen_ay::types::ptr_sort;

        let iter_expr = iter_expr.as_expr();
        let dt = iter_expr.sort().datatype_sort()?;
        let ctor = dt.constructors.first()?;

        if let (Some(vec_field), Some(pos_field)) = (ctor.field("fld_vec"), ctor.field("fld_pos")) {
            let vec = iter_expr.clone().field_select(&dt.name, "fld_vec", vec_field.sort.clone());
            let pos = iter_expr.clone().field_select(&dt.name, "fld_pos", pos_field.sort.clone());
            let len = self.vec_field_select_declared(&vec, "fld_len", ptr_sort());

            if pos.sort().bitvec_width() == len.sort().bitvec_width() {
                // Comparison of two values: a value again.
                return Some(Val::of_value(pos.bvult(len)));
            }
        }

        if let Some(inner_field) = ctor.field("fld_iter") {
            // A field of a value is a value.
            let inner = Val::of_value(iter_expr.clone().field_select(
                &dt.name,
                "fld_iter",
                inner_field.sort.clone(),
            ));
            return self.iter_has_remaining_items(&inner);
        }

        None
    }

    /// Sound bounded-unroll of `Iterator::all` / `Iterator::any` over a
    /// slice/Vec iterator with a CONCRETE remaining range.
    ///
    /// Invokes the predicate closure on each element via the value-returning
    /// mini-inliner (`inline_instance_value`) and folds the per-element booleans
    /// (AND for `all`, OR for `any`). This replaces the prior behaviour where
    /// `Iterator::all`/`any` fell through to the unsupported-call fallback and
    /// were HAVOCED (the closure skipped entirely) — soundness-critical: a
    /// havoc-ed `all` over-/under-approximates the conjunction arbitrarily.
    ///
    /// SOUNDNESS — fail-closed at every step. A result is assigned to the
    /// destination ONLY when:
    ///   1. the receiver resolves to a `{fld_vec, fld_pos}` iterator whose Vec
    ///      has a CONCRETE `[pos, len)` range within `MAX_ALL_ANY_UNROLL`;
    ///   2. the predicate closure resolves and inlines to a `bool` for EVERY
    ///      element; and
    ///   3. NO new `unsupported_construct_fallback` / iterator-unsound-skip is
    ///      recorded while inlining the closures (i.e. the per-element
    ///      evaluation was itself fully sound, not an inner over-approximation).
    /// On any miss the destination is left unconstrained (the prior
    /// over-approximation is preserved, never a silent pass). When the miss is
    /// not already accounted for by an inner fallback, a single
    /// `unsupported_with_fallback` is recorded so the verdict still demotes.
    pub(in crate::codegen_ay::statement) fn codegen_iter_all_any(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        is_all: bool,
    ) -> Option<BasicBlockIdx> {
        const MAX_ALL_ANY_UNROLL: u64 = 16;
        let label = if is_all { "iter_all_unmodeled" } else { "iter_any_unmodeled" };

        if args.len() < 2 {
            self.ctx.unsupported_with_fallback(label, "missing iterator/closure args");
            return target;
        }

        // Resolve the iterator receiver value: {fld_vec, fld_pos}.
        let Some((_iter_base, iter)) = self.resolve_collection_base(&args[0]) else {
            self.ctx.unsupported_with_fallback(label, "unresolved iterator receiver");
            return target;
        };
        let Some((start, end, data)) = self.resolve_iter_concrete_range(&iter) else {
            self.ctx.unsupported_with_fallback(label, "non-concrete iterator range");
            return target;
        };
        if end < start || end - start > MAX_ALL_ANY_UNROLL {
            self.ctx.unsupported_with_fallback(label, "iterator range exceeds unroll bound");
            return target;
        }

        // Resolve the predicate closure instance and its [receiver, item] layout.
        let closure_op = &args[1];
        let Some(closure_ty) = closure_op.ty(self.body.locals()).into_option() else {
            self.ctx.unsupported_with_fallback(label, "closure type unrecoverable");
            return target;
        };
        let Some(closure_instance) = self.resolve_closure_instance(closure_ty) else {
            self.ctx.unsupported_with_fallback(label, "closure instance unresolved");
            return target;
        };
        let Some(closure_value) = self.codegen_operand(closure_op) else {
            self.ctx.unsupported_with_fallback(label, "closure value untranslatable");
            return target;
        };
        let Some(body) = self.ctx.body_or_instance_body(closure_instance) else {
            self.ctx.unsupported_with_fallback(label, "closure body unavailable");
            return target;
        };
        let arg_locals = body.arg_locals();
        debug!(n = arg_locals.len(), "codegen_iter_all_any: predicate closure resolved");
        if arg_locals.len() != 2 {
            self.ctx.unsupported_with_fallback(label, "closure arity != 2");
            return target;
        }
        let recv_ty = arg_locals[0].ty;
        let item_ty = arg_locals[1].ty;

        // Snapshot soundness counters: any increase while inlining the closures
        // means an element evaluation descended into an unmodeled/havoced fold,
        // so the unrolled conjunction would be tainted -> fail closed. The
        // plain-unsupported and unconstrained-assignment totals are included:
        // a `ctx.unsupported(..)` cut (assert-if-reachable + downstream
        // unreachability) or a silently-unconstrained assign inside an inlined
        // element closure taints the unroll exactly like a havoced fold, but
        // bumps neither of the two counters previously checked.
        let fb_before = get_unsupported_construct_fallback_count();
        let skip_before = get_bmc_iterator_unsound_skip_count();
        let un_before = self.ctx.unsupported_construct_total();
        let uc_before = get_unconstrained_assignment_count();

        let item_dt_sort = Self::infer_sort_from_ty(item_ty).filter(|s| s.is_datatype());
        let mut results: Vec<Expr> = Vec::with_capacity((end - start) as usize);
        for i in start..end {
            let idx = Expr::bitvec_const(u128::from(i), POINTER_WIDTH);
            let mut elem = data.clone().select(idx);
            if let Some(dt_sort) = &item_dt_sort {
                if elem.sort().is_bitvec() {
                    if let Some(rebuilt) =
                        crate::codegen_ay::types::unflatten_bitvec_to_datatype(&elem, dt_sort)
                    {
                        elem = rebuilt;
                    }
                }
            }
            let recv_param =
                self.build_inline_arg_for_value("iter_pred_recv", closure_value.clone(), recv_ty);
            if let Some(pointee_base) = recv_param.pointee_base.clone() {
                if let Operand::Copy(pl) | Operand::Move(pl) = closure_op {
                    let caller_base = self.ssa_base_name(pl);
                    for (suffix, target) in self.collect_nested_arg_ref_pointees(&caller_base) {
                        if !suffix.is_empty() {
                            let mut key = String::with_capacity(pointee_base.len() + suffix.len());
                            key.push_str(&pointee_base);
                            key.push_str(&suffix);
                            self.ref_pointees.insert(std::sync::Arc::from(key.as_str()), target);
                        }
                    }
                }
            }
            let item_param = self.build_inline_arg_for_value("iter_pred_item", elem, item_ty);
            let params = vec![recv_param, item_param];
            // Give THIS element's closure inline (and its whole nested call
            // subtree) a disjoint SSA namespace. Without it, every element
            // reuses the same `<closure>::local_N` / nested `<eval>::local_N`
            // frame names, so z3 forces element 0's evaluation EQUAL to element
            // 1's (a vacuous verify where a wrong OR-property passes just like
            // the correct AND). The salt is restored right after so the
            // caller-frame (harness) naming is untouched. Nested unrolls get
            // fresh salts via the monotonic counter.
            let elem_salt = self.ctx.next_inline_frame_salt();
            let prev_salt = self.ctx.set_inline_frame_salt(Some(elem_salt));
            let inlined = self.inline_instance_value(closure_instance, &params);
            self.ctx.set_inline_frame_salt(prev_salt);
            let Some(r) = inlined else {
                if get_unsupported_construct_fallback_count() == fb_before {
                    self.ctx.unsupported_with_fallback(label, "predicate closure inline declined");
                }
                return target;
            };
            if !r.sort().is_bool() {
                if get_unsupported_construct_fallback_count() == fb_before {
                    self.ctx.unsupported_with_fallback(label, "predicate result not bool");
                }
                return target;
            }
            results.push(r);
        }

        if get_unsupported_construct_fallback_count() != fb_before
            || get_bmc_iterator_unsound_skip_count() != skip_before
            || self.ctx.unsupported_construct_total() != un_before
            || get_unconstrained_assignment_count() != uc_before
        {
            // The per-element evaluation was not fully sound (descended into an
            // unmodeled fold / havoc / unsupported-construct cut / unconstrained
            // assign). Leave the destination unconstrained so the prior
            // over-approximation stands, and record a fallback so the verdict
            // demotion pipeline sees the taint even when only the plain
            // (counter-less) unsupported record was bumped.
            debug!("codegen_iter_all_any: element eval not fully sound; preserving over-approx");
            if get_unsupported_construct_fallback_count() == fb_before {
                self.ctx.unsupported_with_fallback(
                    label,
                    "per-element closure hit an unsupported construct or unconstrained assign",
                );
            }
            return target;
        }

        let combined = if is_all {
            results.into_iter().fold(Expr::bool_const(true), Expr::and)
        } else {
            results.into_iter().fold(Expr::bool_const(false), Expr::or)
        };
        debug!(is_all, n = end - start, "codegen_iter_all_any: SOUND bounded unroll emitted");
        self.assign_value_to_place(destination, combined);
        target
    }

    /// Record a `Filter`/`Map` adapter stage so a downstream terminal
    /// `sum`/`fold`/`try_fold` can replay the per-element closure. The chain for
    /// the destination adapter inherits the receiver adapter's chain plus this
    /// stage. Keyed by the UNVERSIONED base SSA name (`ssa_base_name` /
    /// `get_map_base_from_ref` agree on the base), so the def here and the use at
    /// the terminal resolve to the same key on a straight-line chain.
    ///
    /// SOUNDNESS: best-effort recording only — if the closure value/type cannot
    /// be recovered, NOTHING is recorded, which leaves the chain count below the
    /// adapter's wrapper depth so the terminal fails closed (see
    /// `resolve_adapter_elements`). Never makes a terminal pass unsoundly.
    fn record_adapter_stage(
        &mut self,
        args: &[Operand],
        destination: &Place,
        kind: AdapterStageKind,
    ) {
        if args.len() < 2 {
            return;
        }
        let recv_chain = self
            .get_map_base_from_ref(&args[0])
            .and_then(|b| self.adapter_closures.get(&b).cloned())
            .unwrap_or_default();
        let Some(closure_ty) = args[1].ty(self.body.locals()).into_option() else {
            return;
        };
        let Some(closure_value) = self.codegen_operand(&args[1]) else {
            return;
        };
        let closure_arg_base = match &args[1] {
            Operand::Copy(place) | Operand::Move(place) => {
                Some(std::sync::Arc::from(self.ssa_base_name(place).as_str()))
            }
            Operand::Constant(_) => None,
            #[cfg(trust_toolchain)]
            Operand::RuntimeChecks(_) => None,
        };
        let mut chain = recv_chain;
        chain.push(AdapterStage { kind, closure_ty, closure_value, closure_arg_base });
        let dest_base: std::sync::Arc<str> =
            std::sync::Arc::from(self.ssa_base_name(destination).as_str());
        self.adapter_closures.insert(dest_base, chain);
    }

    /// Peel `fld_iter` adapter wrappers off an iterator value until a concrete
    /// `{fld_vec, fld_pos}` slice iterator (or a non-wrapper) is reached,
    /// returning the inner iterator and the number of wrappers peeled. Used to
    /// cross-check the peeled wrapper depth against the recorded closure-stage
    /// count (mismatch => fail closed).
    fn peel_adapter_wrappers(&self, adapter: &Expr) -> (Expr, usize) {
        let mut cur = self.deep_resolve_value(adapter);
        let mut depth = 0usize;
        for _ in 0..32 {
            // Value-transparent wrappers (Copied/Cloned) peel WITHOUT counting:
            // they record no closure stage, so counting them would break the
            // depth == recorded-stage-count fail-closed cross-check.
            let peeled = self.peel_transparent_iter_wrappers(&cur);
            if !std::ptr::eq(peeled.value(), cur.value()) {
                cur = peeled;
            }
            let Some(dt) = cur.sort().datatype_sort() else { break };
            let Some(ctor) = dt.constructors.first() else { break };
            let has_vec = ctor.fields.iter().any(|f| f.name == "fld_vec");
            let has_iter = ctor.fields.iter().any(|f| f.name == "fld_iter");
            // A slice/Vec iterator (has fld_vec) is the base; stop. A wrapper has
            // fld_iter and no fld_vec.
            if has_vec || !has_iter {
                break;
            }
            match Self::ctor_field(&cur, "fld_iter") {
                Some(inner) => {
                    cur = self.deep_resolve_value(&inner);
                    depth += 1;
                }
                None => break,
            }
        }
        (cur, depth)
    }

    /// Peel value-transparent iterator wrappers — `Copied<I>` / `Cloned<I>`
    /// (datatype `Copied_*`/`Cloned_*`, single ctor, single `fld_it` field) —
    /// off a RESOLVED iterator value (G2 Wall B). Under value semantics
    /// (#3133) the model stores element VALUES (references are transparent),
    /// so these adapters are the identity on the element stream; peeling is
    /// faithful and does NOT count as an adapter stage.
    ///
    /// Deliberately name+shape-gated: generic single-field peeling would also
    /// strip `Map`/`Filter` wrappers, silently dropping their closures — a
    /// spurious-SUCCESS surface. Fails closed (returns the input) on any
    /// mismatch.
    fn peel_transparent_iter_wrappers(&self, expr: &Expr) -> Expr {
        let mut cur = expr.clone();
        for _ in 0..8 {
            let Some(dt) = cur.sort().datatype_sort() else { break };
            let name_ok = crate::codegen_ay::names::is_copied_or_cloned_sort_name(&dt.name);
            if !name_ok || dt.constructors.len() != 1 {
                break;
            }
            let ctor = &dt.constructors[0];
            if ctor.fields.len() != 1 || ctor.fields[0].name != "fld_it" {
                break;
            }
            match Self::ctor_field(&cur, "fld_it") {
                Some(inner) => cur = self.deep_resolve_value(&inner),
                None => break,
            }
        }
        cur
    }

    /// Replay the recorded `Filter`/`Map` adapter chain over a CONCRETE-range
    /// slice iterator, returning per-element `(keep, value)` pairs (`keep` is the
    /// conjoined filter predicate, `value` is the mapped element). Mirrors the
    /// soundness discipline of `codegen_iter_all_any`: fail-closed on any miss,
    /// snapshot the fallback/unsound-skip counters and abandon (preserving the
    /// over-approximation) if an inner element evaluation descended into a havoc.
    ///
    /// Returns `None` to signal the caller MUST fall through to its fail-closed
    /// havoc path. A returned `Some` is SOUND: every wrapper had a recorded
    /// closure (depth == stage count) and every per-element closure inlined to a
    /// well-sorted value with no inner over-approximation.
    fn resolve_adapter_elements(
        &mut self,
        recv_op: &Operand,
        label: &'static str,
    ) -> Option<Vec<(Expr, Expr)>> {
        const MAX_UNROLL: u64 = 16;

        let Some((recv_base, adapter_expr)) = self.resolve_collection_base(recv_op) else {
            debug!(label, "resolve_adapter_elements: bail resolve_collection_base");
            return None;
        };
        let stages = self.adapter_closures.get(&recv_base).cloned().unwrap_or_default();
        let (slice_iter, depth) = self.peel_adapter_wrappers(&adapter_expr);
        debug!(
            label,
            %recv_base,
            n_stages = stages.len(),
            depth,
            adapter = %Self::describe_expr(&adapter_expr, 4),
            "resolve_adapter_elements: resolved base/chain/depth"
        );
        if depth != stages.len() {
            // Incomplete (or over-recorded) chain: at least one wrapper has no
            // recovered closure, so a replay would silently drop a filter/map.
            // Fail closed (caller records the demotion).
            debug!(
                depth,
                stages = stages.len(),
                "resolve_adapter_elements: wrapper depth != recorded stages; fail closed"
            );
            return None;
        }
        let Some((start, end, data)) = self.resolve_iter_concrete_range(&slice_iter) else {
            debug!(label, slice = %Self::describe_expr(&slice_iter, 5), "resolve_adapter_elements: bail non-concrete range");
            return None;
        };
        if end < start || end - start > MAX_UNROLL {
            debug!(label, start, end, "resolve_adapter_elements: bail range bound");
            return None;
        }

        let fb_before = get_unsupported_construct_fallback_count();
        let skip_before = get_bmc_iterator_unsound_skip_count();
        // Same blindspot fix as codegen_iter_all_any: a plain `unsupported()`
        // cut or an unconstrained assign inside an inlined stage closure taints
        // the replay but bumps neither counter above.
        let un_before = self.ctx.unsupported_construct_total();
        let uc_before = get_unconstrained_assignment_count();

        let mut out: Vec<(Expr, Expr)> = Vec::with_capacity((end - start) as usize);
        for i in start..end {
            let idx = Expr::bitvec_const(u128::from(i), POINTER_WIDTH);
            let mut keep = Expr::bool_const(true);
            // Fold `select(store_chain, i)` to the concretely-stored element under
            // the array axiom (see `deep_resolve_value`), so a nested-collection
            // element (each `PbTerm` here) is a concrete constructor whose inner
            // `.lits.iter()` then resolves a concrete length instead of bottoming
            // out at an unresolved `Select` and failing closed.
            let mut value = self.deep_resolve_value(&data.clone().select(idx));
            // Give THIS element's stage-closure inlines (filter/map) — and their
            // whole nested call subtree (`eval_term` -> `eval_lit` -> ...) — a
            // disjoint SSA namespace, exactly as `codegen_iter_all_any` does. Each
            // element allocates ONE fresh salt (shared across its filter+map
            // stages, which are distinct closure instances anyway). Without it,
            // every element reuses the same `<closure>::local_N` / nested
            // `<eval>::local_N` frame names, so z3 forces element 0's keep+mapped
            // value EQUAL to element 1's — collapsing the sum's per-term
            // contributions into one shared, under-constrained pair (a vacuous /
            // spurious-CEX surface). Restored immediately after each inline so the
            // caller frame stays untouched; nested unrolls get fresh salts via the
            // monotonic counter.
            let elem_salt = self.ctx.next_inline_frame_salt();
            for stage in &stages {
                let Some(instance) = self.resolve_closure_instance(stage.closure_ty) else {
                    if get_unsupported_construct_fallback_count() == fb_before {
                        self.ctx.unsupported_with_fallback(label, "adapter closure unresolved");
                    }
                    return None;
                };
                let Some(body) = self.ctx.body_or_instance_body(instance) else {
                    if get_unsupported_construct_fallback_count() == fb_before {
                        self.ctx
                            .unsupported_with_fallback(label, "adapter closure body unavailable");
                    }
                    return None;
                };
                let arg_locals = body.arg_locals();
                debug!(kind = ?stage.kind, n = arg_locals.len(), "resolve_adapter_elements: stage closure resolved");
                if arg_locals.len() != 2 {
                    if get_unsupported_construct_fallback_count() == fb_before {
                        self.ctx.unsupported_with_fallback(label, "adapter closure arity != 2");
                    }
                    return None;
                }
                let recv_ty = arg_locals[0].ty;
                let item_ty = arg_locals[1].ty;
                let recv_param = self.build_inline_arg_for_value(
                    "adapter_recv",
                    stage.closure_value.clone(),
                    recv_ty,
                );
                // Graft the closure's captured-reference pointees onto the receiver
                // (closure-environment) base, exactly as `codegen_iter_all_any` does
                // for its predicate. Without this, a stage closure that captures a
                // `&T` (e.g. the filter `|term| eval_term(term, assignment)`
                // capturing `assignment: &[bool]`) loses the pointee link, so the
                // inlined body derefs a FRESH symbolic for the capture — leaving the
                // per-element result under-constrained (a spurious-CEX surface).
                if let Some(pointee_base) = recv_param.pointee_base.clone()
                    && let Some(caller_base) = stage.closure_arg_base.as_deref()
                {
                    for (suffix, target) in self.collect_nested_arg_ref_pointees(caller_base) {
                        if !suffix.is_empty() {
                            let mut key = String::with_capacity(pointee_base.len() + suffix.len());
                            key.push_str(&pointee_base);
                            key.push_str(&suffix);
                            self.ref_pointees.insert(std::sync::Arc::from(key.as_str()), target);
                        }
                    }
                }
                let item_param =
                    self.build_inline_arg_for_value("adapter_item", value.clone(), item_ty);
                let prev_salt = self.ctx.set_inline_frame_salt(Some(elem_salt));
                let inlined = self.inline_instance_value(instance, &[recv_param, item_param]);
                self.ctx.set_inline_frame_salt(prev_salt);
                let Some(r) = inlined else {
                    if get_unsupported_construct_fallback_count() == fb_before {
                        self.ctx
                            .unsupported_with_fallback(label, "adapter closure inline declined");
                    }
                    return None;
                };
                match stage.kind {
                    AdapterStageKind::Filter => {
                        if !r.sort().is_bool() {
                            if get_unsupported_construct_fallback_count() == fb_before {
                                self.ctx
                                    .unsupported_with_fallback(label, "filter predicate not bool");
                            }
                            return None;
                        }
                        keep = Expr::and(keep, r);
                    }
                    AdapterStageKind::Map => {
                        value = r;
                    }
                }
            }
            out.push((keep, value));
        }

        if get_unsupported_construct_fallback_count() != fb_before
            || get_bmc_iterator_unsound_skip_count() != skip_before
            || self.ctx.unsupported_construct_total() != un_before
            || get_unconstrained_assignment_count() != uc_before
        {
            // Inner element evaluation was not fully sound (descended into an
            // unmodeled/havoced construct, an unsupported-construct cut, or an
            // unconstrained assign); the unrolled result would be tainted.
            // Leave over-approx in place and make sure the demotion pipeline
            // sees the taint even when only a counter-less record was bumped.
            debug!("resolve_adapter_elements: inner eval not fully sound; preserving over-approx");
            if get_unsupported_construct_fallback_count() == fb_before {
                self.ctx.unsupported_with_fallback(
                    label,
                    "stage closure hit an unsupported construct or unconstrained assign",
                );
            }
            return None;
        }

        Some(out)
    }

    /// `collect` into a `Vec` over a `map` chain on a concrete slice
    /// iterator (by its MIR type: `filter_map` records a `Map` stage too, and
    /// its elements are `Option`s, `is_map_chain_over_slice_iter`): the
    /// mapped elements, each closure replayed in order as Kani runs it (its
    /// checks included), and the count as the length.
    /// `[1u8, 2, 3].iter().map(|v| { assert!(*v < 200); *v }).collect()`
    /// failed closed (`iter_collect_adapter_unmodeled`, walker fail-closed
    /// review 6 round 3) where main proved it by collecting the unmapped
    /// elements, which dropped the closure's assert and missed its bug twin
    /// (walker fail-closed repair round 5,
    /// `closure_helper_obligation_dual.rs` `h05`). `None` (the caller fails
    /// closed) for a chain with a `filter`, an element the replay cannot
    /// resolve, no element, or a declared unwind bound the loop over the
    /// elements reaches: `SpecFromIter` for a `TrustedLen` `Map` extends
    /// through `for_each`, the inner iterator's `fold`, one pass per element
    /// (`reduce_loop_rule`: a slice iterator's do-while fails past `U`
    /// passes; three elements under `unwind(3)` pass on Kani).
    pub(in crate::codegen_ay::statement) fn try_collect_map_chain(
        &mut self,
        recv: &Operand,
        destination: &Place,
    ) -> Option<Expr> {
        if !is_map_chain_over_slice_iter(recv.ty(self.body.locals()).into_option()?) {
            return None;
        }
        // The `Vec<T>` the elements must be `T`s of.
        let dest_ty = destination.ty(self.body.locals()).into_option()?;
        let TyKind::RigidTy(RigidTy::Adt(dest_def, dest_args)) = dest_ty.kind() else {
            return None;
        };
        if !rustc_public::CrateDef::name(&dest_def).ends_with("vec::Vec") {
            return None;
        }
        let dest_elem = dest_args.0.iter().find_map(|arg| match arg {
            rustc_public::ty::GenericArgKind::Type(ty) => Some(*ty),
            _ => None,
        })?;
        let dest_elem_sort = Self::infer_sort_from_ty(dest_elem)?;
        let elements = self.resolve_adapter_elements(recv, "iter_collect_adapter_unmodeled")?;
        if elements
            .iter()
            .any(|(keep, _)| !matches!(keep.value(), ay_bindings::ExprValue::BoolConst(true)))
        {
            return None;
        }
        let count = elements.len() as u64;
        let config = &self.ctx.config;
        if config.has_explicit_unwind && config.unwinding_assertions {
            use crate::codegen_ay::reduce_loop_rule::{ReduceLoopRule, reduce_loop_rule};
            let rule = recv.ty(self.body.locals()).into_option().and_then(reduce_loop_rule);
            if ReduceLoopRule::fails_at(rule, count, u64::from(config.unwind_depth)) {
                return None;
            }
        }
        let elem_sort = dest_elem_sort;
        if elements.iter().any(|(_, value)| *value.sort() != elem_sort) {
            return None;
        }
        let data_sort = ay_bindings::Sort::array(ptr_sort(), elem_sort.clone());
        let base_name = self.ctx.fresh_name("collect_map_data");
        let base = self.ctx.declare_var(&base_name, data_sort);
        let data = elements.into_iter().enumerate().fold(base, |data, (i, (_, value))| {
            data.store(Expr::bitvec_const(i as u64, POINTER_WIDTH), value)
        });
        debug!(count, "IterCollect: collected a map chain element by element");
        // The loop over the elements stays within a declared bound (checked
        // above): no generic modelled-call check after this stub.
        self.stub_stated_unwinding = true;
        Some(self.make_vec_from_parts(elem_sort, Expr::bitvec_const(count, POINTER_WIDTH), data))
    }

    /// Kani's unwinding assertion on the std loop a reduction runs, for the
    /// element-wise unroll over `count` elements (a concrete range), under a
    /// declared unwind bound with unwinding assertions on. The unroll replays
    /// every element and stated nothing about the loop, so `sum` over five
    /// elements under `#[kani::unwind(4)]` verified clean where Kani fails
    /// (walker fail-closed review 6 round 2, finding 8). Where the receiver's
    /// rule was measured (`reduce_loop_rule`), a loop that fails is a
    /// violation, "unwinding assertion loop 0", under the path condition;
    /// for any other shape, and for `try_fold` (whose loop can also stop
    /// early), a loop that can fail (`count >= U`) fails closed.
    fn record_reduce_unwinding(
        &mut self,
        args: &[Operand],
        count: u64,
        label: &'static str,
        try_fold: bool,
    ) {
        use crate::codegen_ay::reduce_loop_rule::{ReduceLoopRule, reduce_loop_rule};
        let config = &self.ctx.config;
        if !config.has_explicit_unwind || !config.unwinding_assertions {
            return;
        }
        let unwind = u64::from(config.unwind_depth);
        let rule = if try_fold {
            None
        } else {
            args.first()
                .and_then(|receiver| receiver.ty(self.body.locals()).into_option())
                .and_then(reduce_loop_rule)
        };
        if !ReduceLoopRule::fails_at(rule, count, unwind) {
            return;
        }
        if rule.is_some() {
            self.record_violation_guarded_with_message(
                Expr::bool_const(true),
                "unwind_assert",
                Some("unwinding assertion loop 0".to_string()),
            );
        } else {
            self.ctx.unsupported_with_fallback(
                label,
                "reduction loop may fail its unwinding assertion (unmeasured iterator shape)",
            );
        }
    }

    /// Sound element-wise unroll of `Iterator::sum` over a recorded
    /// `Filter`/`Map` chain (the missing closure side of `codegen_iter_sum_stub`).
    /// Returns `true` iff a sound `sum` value was assigned to `destination`.
    ///
    /// The arithmetic is std's `Sum` impl for the call's Rust types
    /// (`summand`), never a guess from the sort:
    ///
    /// * an integer adds with `bvadd` and, per kept element, records the
    ///   "attempt to add with overflow" check std's `a + b` carries under
    ///   `#[rustc_inherit_overflow_checks]` (filtered under
    ///   `--no-overflow-checks` like every overflow check);
    /// * `Wrapping<int>` adds with `bvadd` and never panics;
    /// * `Saturating<uN>` adds with `bvadd` and saturates to all ones on a
    ///   carry (`uN::saturating_add`); it never panics. `Wrapping` and
    ///   `Saturating` have a one-field datatype sort here, so the sum is taken
    ///   over that field ([`SumNewtype`]);
    /// * a float starts from `-0.0` and adds kept elements with IEEE 754
    ///   `fp.add` (RNE) over the bit patterns. A dropped element is SKIPPED, not
    ///   added as zero: `-0.0 + +0.0` is `+0.0`, so adding a zero for it would
    ///   change the sign of the result;
    /// * anything else is not unrolled (the caller havocs it).
    fn try_iter_sum_unroll(
        &mut self,
        args: &[Operand],
        destination: &Place,
        summand: SumSummand,
    ) -> bool {
        if args.is_empty() || summand == SumSummand::Unknown {
            return false;
        }
        let Some(result_sort) = self.infer_sort_from_place(destination) else {
            return false;
        };
        let Some((scalar_sort, newtype)) = Self::sum_scalar_layout(summand, &result_sort) else {
            return false;
        };
        let Some(zero) = Self::sum_identity(summand, &scalar_sort) else {
            return false;
        };
        let Some(elements) = self.resolve_adapter_elements(&args[0], "iter_sum_unmodeled") else {
            return false;
        };
        // Every mapped element must carry the accumulator sort (rejects e.g. an
        // `Option`-returning filter_map mis-recorded as a map).
        if !elements.iter().all(|(_, v)| v.sort() == &result_sort) {
            return false;
        }
        let count = elements.len() as u64;
        let nan_checks = self.ctx.config.nan_checks;
        if matches!(summand, SumSummand::Float { .. })
            && !nan_checks
            && local_is_never_read(self.body, destination)
        {
            // Nothing reads the float sum, and without `--nan-check` std's
            // `a + b` carries no check: its value is unobservable, so a fresh
            // value is exact. The `fp.add` chain it replaces is not: ay
            // `d80d17a90` answers `unknown` for every query that carries one
            // over symbolic operands beside the iterator's datatypes, so a
            // harness whose real bug lies elsewhere was INCONCLUSIVE where
            // main reported it FAILED Genuine (AY alignment round 8, review
            // round 5, finding 2). The adapter closures above were still
            // replayed for their checks.
            let name = self.ctx.fresh_name("iter_sum_unread");
            let value = self.ctx.declare_var(&name, result_sort);
            self.record_reduce_unwinding(args, count, "iter_sum_unmodeled", false);
            self.assign_value_to_place(destination, value);
            return true;
        }
        let mut acc = zero;
        // The accumulator is a NaN (a fresh NaN-constrained value, below).
        let mut acc_is_nan = false;
        for (keep, v) in elements {
            let v = match &newtype {
                Some(newtype) => {
                    v.field_select(&newtype.datatype, &newtype.field, scalar_sort.clone())
                }
                None => v,
            };
            acc = match summand {
                SumSummand::Int { width, signed } => {
                    // A dropped element contributes `0`, which never overflows,
                    // so the check needs no `keep` guard of its own.
                    let contrib = Expr::ite(keep, v, Expr::bitvec_const(0u128, width));
                    if let Some((no_overflow, label)) =
                        self.overflow_check(BinOp::Add, &acc, &contrib, signed)
                    {
                        self.record_violation_guarded_with_message(
                            no_overflow.not(),
                            label,
                            Some(ADD_OVERFLOW_MESSAGE.to_string()),
                        );
                    }
                    acc.bvadd(contrib)
                }
                SumSummand::WrappingInt { width } => {
                    acc.bvadd(Expr::ite(keep, v, Expr::bitvec_const(0u128, width)))
                }
                SumSummand::SaturatingUint { width } => {
                    let sum =
                        acc.clone().bvadd(Expr::ite(keep, v, Expr::bitvec_const(0u128, width)));
                    // An unsigned add carries out exactly when its wrapped
                    // result is below an operand.
                    let carry = sum.clone().bvult(acc);
                    let max = Expr::bitvec_const(!0u128 >> (128 - width), width);
                    // One SSA name per step: the accumulator occurs twice in
                    // the step, so an inline term would double with each element.
                    let name = self.ctx.fresh_name("iter_sum_acc");
                    let var = self.ctx.declare_var(&name, scalar_sort.clone());
                    self.ctx.assert(var.clone().eq(Expr::ite(carry, max, sum)));
                    var
                }
                SumSummand::Float { width } => {
                    // Kani's "NaN on addition" (CBMC `--nan-check`) on std's
                    // `a + b`, for a kept element: the sum carried none, so
                    // `[f32::INFINITY, f32::NEG_INFINITY].iter().sum()` passed
                    // under the flag (AY alignment round 8, review round 5).
                    if nan_checks {
                        match bv_float_binop_generates_nan(BinOp::Add, &acc, &v, width) {
                            Some(generates_nan) => self.record_violation_guarded(
                                keep.clone().and(generates_nan),
                                "nan_check_add",
                            ),
                            None => {
                                self.record_violation_guarded(keep.clone(), "unsupported_check")
                            }
                        }
                    }
                    // Concrete operands fold on the host, which adds in IEEE 754
                    // binary32/binary64 with round-to-nearest-even, the
                    // semantics the program has. A NaN result's bit pattern is
                    // not determined, so it is a fresh value constrained to be
                    // a NaN, in bit-vectors: an `fp.add` term of constants
                    // would leave ay `d80d17a90` answering `unknown` beside the
                    // iterator's datatypes. NaN plus anything is a NaN.
                    let host_nan = acc_is_nan || Self::float_add_folds_to_nan(&acc, &v, width);
                    match (keep.value(), Self::fold_float_add(&acc, &v, width)) {
                        (ExprValue::BoolConst(false), _) => acc,
                        (ExprValue::BoolConst(true), Some(folded)) if !acc_is_nan => folded,
                        _ if host_nan => {
                            let Some(nan) = self.fresh_float_nan(width, &scalar_sort) else {
                                return false;
                            };
                            // A dropped element leaves the accumulator, which
                            // is a NaN only if it already was one.
                            match keep.value() {
                                ExprValue::BoolConst(true) => {
                                    acc_is_nan = true;
                                    nan
                                }
                                _ => {
                                    let name = self.ctx.fresh_name("iter_sum_acc");
                                    let var = self.ctx.declare_var(&name, scalar_sort.clone());
                                    self.ctx.assert(var.clone().eq(Expr::ite(keep, nan, acc)));
                                    var
                                }
                            }
                        }
                        // A filtered element of a constant sum: the folded sum
                        // or the accumulator, in bit-vectors.
                        (_, Some(folded)) => {
                            let name = self.ctx.fresh_name("iter_sum_acc");
                            let var = self.ctx.declare_var(&name, scalar_sort.clone());
                            self.ctx.assert(var.clone().eq(Expr::ite(keep, folded, acc)));
                            var
                        }
                        _ => {
                            let Some(added) = bv_float_binop(BinOp::Add, acc.clone(), v, width)
                            else {
                                return false;
                            };
                            // One SSA name per step: the accumulator occurs twice
                            // in `ite(keep, acc + v, acc)`, so an inline term
                            // would double in size with every element.
                            let step = Expr::ite(keep, added, acc);
                            let name = self.ctx.fresh_name("iter_sum_acc");
                            let var = self.ctx.declare_var(&name, scalar_sort.clone());
                            self.ctx.assert(var.clone().eq(step));
                            var
                        }
                    }
                }
                SumSummand::Unknown => return false,
            };
        }
        self.record_reduce_unwinding(args, count, "iter_sum_unmodeled", false);
        debug!(?summand, "try_iter_sum_unroll: SOUND filter/map/sum unroll emitted");
        let result = match newtype {
            Some(newtype) => Expr::datatype_constructor(
                newtype.datatype,
                newtype.constructor,
                vec![acc],
                result_sort,
            ),
            None => acc,
        };
        self.assign_value_to_place(destination, result);
        true
    }

    /// The bitvector `summand` adds at the destination sort `sort`, and the
    /// newtype it is wrapped in there: `sort` itself when it is that
    /// bitvector, or the one field of a one-constructor datatype for std's
    /// `Wrapping` and `Saturating` (which are `struct Wrapping<T>(pub T)`).
    /// `None` when the sort fits neither.
    fn sum_scalar_layout(summand: SumSummand, sort: &Sort) -> Option<(Sort, Option<SumNewtype>)> {
        let width = summand.width()?;
        if sort.bitvec_width() == Some(width) {
            return Some((sort.clone(), None));
        }
        if !matches!(summand, SumSummand::WrappingInt { .. } | SumSummand::SaturatingUint { .. }) {
            return None;
        }
        let datatype = sort.datatype_sort()?;
        let [constructor] = datatype.constructors.as_slice() else {
            return None;
        };
        let [field] = constructor.fields.as_slice() else {
            return None;
        };
        if field.sort.bitvec_width() != Some(width) {
            return None;
        }
        Some((
            field.sort.clone(),
            Some(SumNewtype {
                datatype: datatype.name.clone(),
                constructor: constructor.name.clone(),
                field: field.name.clone(),
            }),
        ))
    }

    /// `a + b` of two concrete float bit patterns, folded exactly; `None` when
    /// either is not a constant, the width has no host type, or the sum is NaN.
    fn fold_float_add(a: &Expr, b: &Expr, width: u32) -> Option<Expr> {
        let folded = bv_float_binop_chc(BinOp::Add, a.clone(), b.clone(), width)?;
        let ExprValue::BitVecConst { value, .. } = folded.value() else {
            return None;
        };
        let bits = u128::try_from(value).ok()?;
        let (eb, sb) = float_width_to_eb_sb(width)?;
        let exponent_mask = ((1u128 << eb) - 1) << (sb - 1);
        let significand_mask = (1u128 << (sb - 1)) - 1;
        let is_nan = bits & exponent_mask == exponent_mask && bits & significand_mask != 0;
        (!is_nan).then_some(folded)
    }

    /// Do `a` and `b` both fold to constants whose host sum is a NaN?
    fn float_add_folds_to_nan(a: &Expr, b: &Expr, width: u32) -> bool {
        let Some(folded) = bv_float_binop_chc(BinOp::Add, a.clone(), b.clone(), width) else {
            return false;
        };
        let ExprValue::BitVecConst { value, .. } = folded.value() else {
            return false;
        };
        let (Ok(bits), Some((eb, sb))) = (u128::try_from(value), float_width_to_eb_sb(width))
        else {
            return false;
        };
        let exponent_mask = ((1u128 << eb) - 1) << (sb - 1);
        let significand_mask = (1u128 << (sb - 1)) - 1;
        bits & exponent_mask == exponent_mask && bits & significand_mask != 0
    }

    /// A fresh float of `width` bits constrained to be a NaN (exponent all
    /// ones, significand nonzero): any NaN the operation may produce.
    fn fresh_float_nan(&mut self, width: u32, sort: &Sort) -> Option<Expr> {
        let (eb, sb) = float_width_to_eb_sb(width)?;
        let name = self.ctx.fresh_name("iter_sum_nan");
        let var = self.ctx.declare_var(&name, sort.clone());
        let mantissa = sb - 1;
        let exponent_all_ones =
            var.clone().extract(width - 2, mantissa).eq(Expr::bitvec_const((1u128 << eb) - 1, eb));
        let significand_nonzero =
            var.clone().extract(mantissa - 1, 0).eq(Expr::bitvec_const(0u128, mantissa)).not();
        self.ctx.assert(exponent_all_ones.and(significand_nonzero));
        Some(var)
    }

    /// The empty sum of `summand` as an expression of `sort`, when known.
    fn sum_identity(summand: SumSummand, sort: &Sort) -> Option<Expr> {
        let (bits, width) = summand.identity_bits()?;
        (sort.bitvec_width() == Some(width)).then(|| Expr::bitvec_const(bits, width))
    }

    /// Sound element-wise unroll of `Iterator::fold` / `Iterator::try_fold` over a
    /// recorded `Filter`/`Map` chain, threading the terminal fold closure
    /// element-wise. Handles both plain `fold` (accumulator-sorted return) and
    /// `try_fold` (`Result`-returning closure with `?` short-circuit). Returns
    /// `true` iff a sound value was assigned to `destination`.
    fn try_iter_fold_unroll(&mut self, args: &[Operand], destination: &Place) -> bool {
        debug!(nargs = args.len(), "try_iter_fold_unroll: enter");
        if args.len() < 3 {
            debug!("try_iter_fold_unroll: bail args.len()<3");
            return false;
        }
        let Some(init) = self.codegen_operand(&args[1]) else {
            debug!("try_iter_fold_unroll: bail init codegen_operand");
            return false;
        };
        let Some(closure_ty) = args[2].ty(self.body.locals()).into_option() else {
            debug!("try_iter_fold_unroll: bail closure_ty");
            return false;
        };
        let Some(fold_instance) = self.resolve_closure_instance(closure_ty) else {
            debug!("try_iter_fold_unroll: bail resolve_closure_instance");
            return false;
        };
        let Some(closure_value) = self.codegen_operand(&args[2]) else {
            debug!("try_iter_fold_unroll: bail closure_value codegen_operand");
            return false;
        };
        let Some(fold_body) = self.ctx.body_or_instance_body(fold_instance) else {
            debug!("try_iter_fold_unroll: bail fold_body");
            return false;
        };
        let fold_arg_locals = fold_body.arg_locals();
        // The fold closure resolves either to its DIRECT body
        // (`[env, acc, item]`, 3 locals) or — the common case for a 2-param
        // closure invoked through `FnMut/FnOnce::call*` — to the rust-call SHIM
        // (`[env, (acc, item)]`, 2 locals with a 2-tuple). Build the right param
        // layout for each (see `inline_fold_closure`).
        let arg_shape = match fold_arg_locals.len() {
            3 => FoldArgShape::Direct {
                env_ty: fold_arg_locals[0].ty,
                acc_ty: fold_arg_locals[1].ty,
                item_ty: fold_arg_locals[2].ty,
            },
            2 => {
                let tuple_ty = fold_arg_locals[1].ty;
                let TyKind::RigidTy(RigidTy::Tuple(fields)) = tuple_ty.kind() else {
                    debug!("try_iter_fold_unroll: bail 2-local closure arg not a tuple");
                    return false;
                };
                if fields.len() != 2 {
                    debug!(n = fields.len(), "try_iter_fold_unroll: bail tuple arity != 2");
                    return false;
                }
                FoldArgShape::Tupled { env_ty: fold_arg_locals[0].ty, tuple_ty }
            }
            n => {
                debug!(n, inst = %fold_instance.name(), "try_iter_fold_unroll: bail arg_locals shape");
                return false;
            }
        };

        let Some(elements) = self.resolve_adapter_elements(&args[0], "iter_fold_unmodeled") else {
            debug!("try_iter_fold_unroll: bail resolve_adapter_elements");
            return false;
        };

        let acc_sort = init.sort().clone();
        let Some(result_sort) = self.infer_sort_from_place(destination) else {
            debug!("try_iter_fold_unroll: bail result_sort");
            return false;
        };
        debug!(
            result_sort = ?result_sort.inner(),
            acc_sort = ?acc_sort.inner(),
            n_elems = elements.len(),
            "try_iter_fold_unroll: resolved elements + sorts"
        );

        // Distinguish plain fold (return sort == accumulator sort) from try_fold
        // (return sort is a `Result<Acc, E>` whose Ok payload is the accumulator).
        let try_fold_parts: Option<(String, String, String, Sort)> = if result_sort == acc_sort {
            None
        } else {
            let Some(dt_name) = result_sort.datatype_name().map(str::to_string) else {
                debug!("try_iter_fold_unroll: bail result_sort not datatype (try_fold)");
                return false;
            };
            let Some(ok_ctor) =
                Self::find_result_constructor(&result_sort, "Ok", &dt_name).map(str::to_string)
            else {
                debug!(%dt_name, "try_iter_fold_unroll: bail no Ok constructor");
                return false;
            };
            let ok_field = result_sort
                .datatype_sort()
                .and_then(|dt| dt.constructors.iter().find(|c| c.name == ok_ctor).cloned())
                .and_then(|c| c.fields.first().cloned());
            let Some(ok_field) = ok_field else {
                return false;
            };
            if ok_field.sort != acc_sort {
                return false;
            }
            Some((dt_name, ok_ctor, ok_field.name.clone(), ok_field.sort.clone()))
        };

        let snapshot_fb = get_unsupported_construct_fallback_count();
        let snapshot_skip = get_bmc_iterator_unsound_skip_count();
        let count = elements.len() as u64;
        let is_try_fold = try_fold_parts.is_some();

        let final_value = match &try_fold_parts {
            // Plain fold: acc' = ite(keep, closure(acc, item), acc).
            None => {
                let mut acc = init;
                for (keep, value) in elements {
                    let r = self.inline_fold_closure(
                        fold_instance,
                        closure_value.clone(),
                        &arg_shape,
                        acc.clone(),
                        value,
                    );
                    let Some(r) = r else {
                        debug!("try_iter_fold_unroll: bail fold closure inline declined");
                        return false;
                    };
                    if r.sort() != &acc_sort {
                        debug!(got = ?r.sort().inner(), "try_iter_fold_unroll: bail fold r.sort != acc");
                        return false;
                    }
                    acc = Expr::ite(keep, r, acc);
                }
                acc
            }
            // try_fold: state: Result<Acc,E>, start Ok(init); each kept element
            // advances state ONLY while it is still Ok (the `?` short-circuit).
            Some((dt_name, ok_ctor, ok_field_name, ok_field_sort)) => {
                let mut state = Expr::datatype_constructor(
                    dt_name.clone(),
                    ok_ctor.clone(),
                    vec![init],
                    result_sort.clone(),
                );
                for (keep, value) in elements {
                    let acc =
                        state.clone().field_select(dt_name, ok_field_name, ok_field_sort.clone());
                    let r = self.inline_fold_closure(
                        fold_instance,
                        closure_value.clone(),
                        &arg_shape,
                        acc,
                        value,
                    );
                    let Some(r) = r else {
                        debug!("try_iter_fold_unroll: bail try_fold closure inline declined");
                        return false;
                    };
                    if r.sort() != &result_sort {
                        debug!(got = ?r.sort().inner(), "try_iter_fold_unroll: bail try_fold r.sort != result");
                        return false;
                    }
                    let still_ok = state.clone().is_constructor(dt_name, ok_ctor);
                    let advance = Expr::and(keep, still_ok);
                    state = Expr::ite(advance, r, state);
                }
                state
            }
        };

        if get_unsupported_construct_fallback_count() != snapshot_fb
            || get_bmc_iterator_unsound_skip_count() != snapshot_skip
        {
            // The terminal fold closure inline descended into a havoc; fail closed.
            debug!("try_iter_fold_unroll: bail inner fold eval not fully sound");
            return false;
        }

        self.record_reduce_unwinding(args, count, "iter_fold_unmodeled", is_try_fold);
        debug!("try_iter_fold_unroll: SOUND filter/map/fold unroll emitted");
        self.assign_value_to_place(destination, final_value);
        true
    }

    /// Inline the terminal fold closure on `(acc, item)` (closure env is arg 0),
    /// laying out the parameters per the resolved `FoldArgShape`. Returns the
    /// closure's result value, or `None` to fail closed.
    fn inline_fold_closure(
        &mut self,
        instance: rustc_public::mir::mono::Instance,
        closure_value: Expr,
        shape: &FoldArgShape,
        acc: Expr,
        item: Expr,
    ) -> Option<Expr> {
        match *shape {
            FoldArgShape::Direct { env_ty, acc_ty, item_ty } => {
                let recv_param =
                    self.build_inline_arg_for_value("fold_recv", closure_value, env_ty);
                let acc_param = self.build_inline_arg_for_value("fold_acc", acc, acc_ty);
                let item_param = self.build_inline_arg_for_value("fold_item", item, item_ty);
                self.inline_instance_value(instance, &[recv_param, acc_param, item_param])
            }
            FoldArgShape::Tupled { env_ty, tuple_ty, .. } => {
                let recv_param =
                    self.build_inline_arg_for_value("fold_recv", closure_value, env_ty);
                // Pack (acc, item) into a 2-field tuple datatype matching the
                // rust-call args tuple. The selector-over-constructor datatype
                // axiom lets the SMT recover `_2.0`/`_2.1` even though codegen
                // does not fold the projection.
                let tuple_sort = Self::infer_sort_from_ty(tuple_ty)?;
                let dt = tuple_sort.datatype_sort()?;
                let ctor = dt.constructors.first()?;
                if ctor.fields.len() != 2 {
                    return None;
                }
                let tuple_value = Expr::datatype_constructor(
                    dt.name.clone(),
                    ctor.name.clone(),
                    vec![acc, item],
                    tuple_sort.clone(),
                );
                let tuple_param =
                    self.build_inline_arg_for_value("fold_args", tuple_value, tuple_ty);
                self.inline_instance_value(instance, &[recv_param, tuple_param])
            }
        }
    }

    /// Resolve a `{fld_vec, fld_pos}` iterator value to a concrete `[start,end)`
    /// element range plus the backing data array, by folding constructor field
    /// accesses (`field_select` does not fold, so we read the constructor args
    /// directly). Returns `None` if any of pos/len is not a concrete bitvector.
    fn resolve_iter_concrete_range(&mut self, iter: &Expr) -> Option<(u64, u64, Expr)> {
        // `assign_value_to_place` stores only the SSA *variable* in the env; the
        // folded constructor lives in `ssa_concrete_values` (often wrapped in a
        // path-condition `ite`). Resolve the var through that cache, then read
        // fields with `field_select`, which for SINGLE-CTOR datatypes folds
        // selector-over-constructor AND distributes through `ite`, collapsing to
        // a literal when every branch agrees (sound by the datatype axiom +
        // congruence). On any miss/disagreement the read stays a selector/`ite`
        // and `concrete_bv_u64` fails -> fail closed (no havoc).
        // Resolve the iterator value, folding BOTH SSA links / first-definition
        // `ite`s AND selector-over-constructor reads. NOTE: we do not rely on
        // `Expr::field_select` to fold — the pinned `ay-bindings` rev's
        // `field_select` always builds an unfolded `DatatypeSelector` (the
        // selector-over-constructor fold lives only in a later rev), so reads via
        // it (e.g. the `Vec -> [T]` unsize threads the slice `fld_len` as
        // `Sel(Vec.fld_len of <vec-var>)`) would never collapse to a literal and
        // the range would stay non-concrete. `deep_resolve_value` + `ctor_field`
        // perform those folds (sound by the datatype axiom, single-ctor only),
        // failing closed on any miss.
        let iter = self.deep_resolve_value(iter);
        // See through value-transparent Copied/Cloned wrappers (G2 Wall B) so a
        // `.iter().copied()` receiver still exposes the {fld_vec, fld_pos} base.
        let iter = self.peel_transparent_iter_wrappers(&iter);
        debug!(iter = %Self::describe_expr(&iter, 4), "resolve_iter_concrete_range: post deep_resolve iter");
        let vec = self.deep_resolve_value(&Self::ctor_field(&iter, "fld_vec")?);
        let pos = self.deep_resolve_value(&Self::ctor_field(&iter, "fld_pos")?);
        debug!(vec = %Self::describe_expr(&vec, 5), pos = %Self::describe_expr(&pos, 3), "resolve_iter_concrete_range: post deep_resolve vec/pos");
        let len = self.deep_resolve_value(&Self::ctor_field(&vec, "fld_len")?);
        let data = self.deep_resolve_value(&Self::ctor_field(&vec, "fld_data")?);
        debug!(len = %Self::describe_expr(&len, 3), len_concrete = ?Self::concrete_bv_u64(&len), pos_concrete = ?Self::concrete_bv_u64(&pos), "resolve_iter_concrete_range: folded range");

        let start = Self::concrete_bv_u64(&pos)?;
        let end = Self::concrete_bv_u64(&len)?;
        Some((start, end, data))
    }

    /// Follow `Var -> ssa_concrete_values[name]` links to a (bounded) fixpoint, so
    /// an iterator/collection value copied across several SSA temporaries
    /// (`Var_A == Var_B`, ...) still resolves to its underlying constructor / `ite`.
    /// Single-step `resolve_concrete_expr` stops at the first hop, which is
    /// insufficient when the value is threaded through copies (the common case for
    /// a `slice.iter()` consumed by `.all()`/`.any()`).
    ///
    /// SOUNDNESS: only equality links (`lhs == rhs` SSA definitions) are followed,
    /// so the resolved expression is provably equal to the input. In particular
    /// `ite` nodes are NOT peeled here — a path-guarded definition
    /// `ite(pc, value, pre-state)` is left intact so the downstream `field_select`
    /// folds it ONLY when both branches agree (sound by congruence), and otherwise
    /// leaves a non-constant that fails the concrete check -> fail closed. (Peeling
    /// the `then` branch would be unsound when the consumer's path condition does
    /// not imply `pc`, e.g. an `it = if c { a.iter() } else { b.iter() }` merge.)
    fn deep_resolve_concrete(&self, expr: &Expr) -> Expr {
        let mut cur = self.resolve_concrete_expr(expr);
        for _ in 0..64 {
            match cur.value() {
                ExprValue::Var { name } => match self.ssa_concrete_values.get(name) {
                    Some(next) if next.value() != cur.value() => cur = next.clone(),
                    _ => break,
                },
                // First-definition / SSA pre-state `ite`: when the else-branch is a
                // fresh `__ssa_init` havoc placeholder (a value-of-this-base before
                // its first definition on the current path), peel to the then-branch
                // so single-ctor field folding can collapse to a literal.
                //
                // SOUNDNESS: the else-branch is NOT a real alternative value — it is
                // the untaken-path/pre-state symbolic for a base whose first (and, at
                // this point, only) definition is `then` under `pc`. It is never the
                // live value where the downstream consumer's result is actually used:
                // the bounded `all`/`any` unroll assigns its result via
                // `assign_value_to_place`, which re-guards it with the current path
                // condition, and the iterator is constructed on the SAME path (no
                // branch separates `x.iter()` from `.all(..)`), so whenever the
                // result is used `pc` holds and the iterator equals `then`. Real
                // value-merges (`it = if c { a.iter() } else { b.iter() }`) carry a
                // constructor / prior-`ite` else, NOT an `__ssa_init` placeholder, so
                // they are left intact (fail-closed) exactly as before.
                ExprValue::Ite { then_expr, else_expr, .. }
                    if Self::is_ssa_init_placeholder(else_expr) =>
                {
                    cur = then_expr.clone();
                }
                _ => break,
            }
        }
        cur
    }

    /// Resolve an expression to its underlying concrete value, folding SSA
    /// variable links / first-definition `ite`s (via `deep_resolve_concrete`) AND
    /// `selector-over-constructor` reads. The pinned `ay-bindings` rev's
    /// `field_select` never folds, so collection/iterator fields threaded through
    /// it (e.g. the `Vec -> [T]` unsize) bottom out at `Sel(field of <ctor/var>)`;
    /// this recovers the literal by resolving the selector's receiver and reading
    /// the constructor argument positionally.
    ///
    /// SOUNDNESS: every step is value-preserving — SSA equality links, the
    /// `__ssa_init` first-definition peel (see `deep_resolve_concrete`), and the
    /// `(sel_i (mk a..)) = a_i` datatype axiom. Bounded structural recursion;
    /// fails closed (returns the best partial resolution, leaving a non-constant
    /// that `concrete_bv_u64` rejects) on any miss.
    pub(in crate::codegen_ay::statement) fn deep_resolve_value(&self, expr: &Expr) -> Expr {
        self.deep_resolve_value_bounded(expr, 0)
    }

    fn deep_resolve_value_bounded(&self, expr: &Expr, depth: usize) -> Expr {
        const MAX_DEPTH: usize = 48;
        let cur = self.deep_resolve_concrete(expr);
        if depth >= MAX_DEPTH {
            return cur;
        }
        if let ExprValue::DatatypeSelector { selector_name, expr: inner, .. } = cur.value() {
            let inner = self.deep_resolve_value_bounded(inner, depth + 1);
            if let Some(field) = Self::ctor_field(&inner, selector_name) {
                return self.deep_resolve_value_bounded(&field, depth + 1);
            }
        }
        // Bounded const-fold of Ite when condition folds to a concrete Bool
        // (e.g. `Vec::pop` sets `fld_len` to `ite(bvugt(old_len, 0), bvsub(old_len, 1), 0)`).
        if let ExprValue::Ite { cond, then_expr, else_expr } = cur.value() {
            let cond_val = match cond.value() {
                ExprValue::BoolConst(b) => Some(*b),
                ExprValue::BvUGt(a, b) | ExprValue::BvULt(a, b) | ExprValue::Eq(a, b) => {
                    let ra = self.deep_resolve_value_bounded(a, depth + 1);
                    let rb = self.deep_resolve_value_bounded(b, depth + 1);
                    if let (
                        ExprValue::BitVecConst { value: va, width: wa },
                        ExprValue::BitVecConst { value: vb, width: wb },
                    ) = (ra.value(), rb.value())
                        && wa == wb
                        && *wa <= 64
                        && let (Ok(ua), Ok(ub)) =
                            (u64::try_from(va.clone()), u64::try_from(vb.clone()))
                    {
                        Some(match cond.value() {
                            ExprValue::BvUGt(..) => ua > ub,
                            ExprValue::BvULt(..) => ua < ub,
                            _ => ua == ub,
                        })
                    } else {
                        None
                    }
                }
                _ => None,
            };
            if let Some(b) = cond_val {
                let chosen = if b { then_expr } else { else_expr };
                return self.deep_resolve_value_bounded(chosen, depth + 1);
            }
        }
        // Bounded const-fold of BvAdd/BvSub: a push-built `Vec`'s `fld_len` is
        // an UNFOLDED `bvadd(bvadd(0, 1), 1)` chain (one bvadd per VecPush), so
        // without folding the range reader's `concrete_bv_u64` rejects it and
        // `.all()`/adapter replay fail closed (G2 Wall C). Fold ONLY when both
        // operands resolve to same-width BitVecConsts that fit u64; the result
        // wraps mod 2^w (exact bvadd/bvsub semantics). Anything else returns
        // the partial resolution — the existing fail-closed bails untouched.
        if let ExprValue::BvAdd(a, b) | ExprValue::BvSub(a, b) = cur.value() {
            let ra = self.deep_resolve_value_bounded(a, depth + 1);
            let rb = self.deep_resolve_value_bounded(b, depth + 1);
            if let (
                ExprValue::BitVecConst { value: va, width: wa },
                ExprValue::BitVecConst { value: vb, width: wb },
            ) = (ra.value(), rb.value())
                && wa == wb
                && *wa <= 64
                && let (Ok(ua), Ok(ub)) = (u64::try_from(va.clone()), u64::try_from(vb.clone()))
            {
                let raw = match cur.value() {
                    ExprValue::BvAdd(..) => ua.wrapping_add(ub),
                    _ => ua.wrapping_sub(ub),
                };
                let folded = if *wa < 64 { raw & ((1u64 << *wa) - 1) } else { raw };
                return Expr::bitvec_const(folded, *wa);
            }
        }
        // Bounded select-over-store fold (array read axiom). A `Vec`/slice built by
        // pushes stores each element into `fld_data` as
        // `store(store(base, k0, e0), k1, e1) ...`; reading element `i` is
        // `select(<that store chain>, i)`. The pinned `ay-bindings` `select` does
        // not fold, so a nested collection element (e.g. each `PbTerm` a
        // `.filter(..).map(..).sum()` element-wise replay must expose so its inner
        // `.lits.iter()` gets a concrete length) bottoms out at an unresolved
        // `Select` and the inner range reader fails closed. Resolve it here.
        //
        // SOUNDNESS: pure McCarthy array axiom — `select(store(a,k,v),i) = v` when
        // `i == k`, else `select(a,i)` — applied ONLY when the query index AND the
        // store index both resolve to concrete equal-or-unequal bitvec constants.
        // On a non-concrete store index (can't decide `i == k`) or a non-`Store`
        // base reached without a match (the symbolic backing array holds unknown
        // values), returns the partial resolution unchanged -> fail closed. Never
        // fabricates an element.
        if let ExprValue::Select { array, index } = cur.value() {
            let r_index = self.deep_resolve_value_bounded(index, depth + 1);
            if let Some(qi) = Self::concrete_bv_u64(&r_index)
                && let Some(folded) = self.fold_select_over_store(array, qi, depth + 1)
            {
                return folded;
            }
        }
        cur
    }

    /// Fold `select(store_chain, qi)` to the stored value under the McCarthy array
    /// axiom, with `qi` a concrete index. Walks the resolved store chain top-down:
    /// on a concrete store index equal to `qi`, returns that value (resolved); on a
    /// concrete unequal index, recurses into the underlying array; on any
    /// non-concrete store index or a non-`Store` base (symbolic backing array),
    /// returns `None` (fail closed — the read is not decidable by the axiom alone).
    fn fold_select_over_store(&self, array: &Expr, qi: u64, depth: usize) -> Option<Expr> {
        const MAX_STORE_WALK: usize = 64;
        let mut cur = self.deep_resolve_value_bounded(array, depth);
        for _ in 0..MAX_STORE_WALK {
            let ExprValue::Store { array: inner, index, value } = cur.value() else {
                return None;
            };
            let ki = Self::concrete_bv_u64(&self.deep_resolve_value_bounded(index, depth))?;
            if ki == qi {
                return Some(self.deep_resolve_value_bounded(value, depth));
            }
            cur = self.deep_resolve_value_bounded(inner, depth);
        }
        None
    }

    /// True iff `e` is a bare SSA pre-state placeholder variable (`*__ssa_init_*`),
    /// i.e. the symbolic "value before first definition" minted by
    /// `get_or_declare_ssa_init_symbol` for path-guarded SSA definitions.
    fn is_ssa_init_placeholder(e: &Expr) -> bool {
        matches!(e.value(), ExprValue::Var { name } if name.contains("__ssa_init_"))
    }

    /// Fold a named field out of a single-constructor datatype VALUE positionally:
    /// `(fld_i (mk a_0 .. a_n)) = a_i`. Sound by the datatype axiom. Replaces the
    /// reliance on `Expr::field_select` folding, which the pinned `ay-bindings` rev
    /// does NOT do (it always emits an unfolded `DatatypeSelector`).
    ///
    /// Fails closed (`None`) unless `expr` is a `DatatypeConstructor` whose declared
    /// sort is a single-constructor datatype containing `field_name` at an index
    /// present in the value's argument list — never returns a wrong field.
    pub(in crate::codegen_ay::statement) fn ctor_field(
        expr: &Expr,
        field_name: &str,
    ) -> Option<Expr> {
        let ExprValue::DatatypeConstructor { args, .. } = expr.value() else {
            return None;
        };
        let dt = expr.sort().datatype_sort()?;
        if dt.constructors.len() != 1 {
            return None;
        }
        let ctor = dt.constructors.first()?;
        let idx = ctor.fields.iter().position(|f| f.name == field_name)?;
        args.get(idx).cloned()
    }

    /// Extract a concrete `u64` from a bitvector-constant expression.
    pub(in crate::codegen_ay::statement) fn concrete_bv_u64(e: &Expr) -> Option<u64> {
        match e.value() {
            ExprValue::BitVecConst { value, .. } => u64::try_from(value.clone()).ok(),
            _ => None,
        }
    }

    /// Depth-limited structural label of an `Expr` for BMC iterator diagnostics.
    fn describe_expr(e: &Expr, depth: usize) -> String {
        if depth == 0 {
            return "..".to_string();
        }
        match e.value() {
            ExprValue::Var { name } => format!("Var({name})"),
            ExprValue::BitVecConst { value, width } => format!("Bv({value}:{width})"),
            ExprValue::IntConst(v) => format!("Int({v})"),
            ExprValue::BoolConst(b) => format!("Bool({b})"),
            ExprValue::Ite { cond, then_expr, else_expr } => format!(
                "Ite(c={}, t={}, e={})",
                Self::describe_expr(cond, depth - 1),
                Self::describe_expr(then_expr, depth - 1),
                Self::describe_expr(else_expr, depth - 1)
            ),
            ExprValue::DatatypeConstructor { datatype_name, constructor_name, args } => format!(
                "Ctor({datatype_name}::{constructor_name}[{}])",
                args.iter()
                    .map(|a| Self::describe_expr(a, depth - 1))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            ExprValue::DatatypeSelector { datatype_name, selector_name, expr } => format!(
                "Sel({datatype_name}.{selector_name} of {})",
                Self::describe_expr(expr, depth - 1)
            ),
            ExprValue::Select { array, index } => format!(
                "ArrSel({}[{}])",
                Self::describe_expr(array, depth - 1),
                Self::describe_expr(index, depth - 1)
            ),
            other => format!("{:?}", std::mem::discriminant(other)),
        }
    }

    /// Build an `InlineArgValue` for seeding a closure parameter from a value
    /// expression. Reference/pointer params get a fresh pointer expr plus a
    /// pointee env entry holding the value (so callee derefs resolve); value
    /// params pass the expression directly.
    fn build_inline_arg_for_value(&mut self, prefix: &str, value: Expr, ty: Ty) -> InlineArgValue {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(..)) | TyKind::RigidTy(RigidTy::RawPtr(..)) => {
                // Count leading reference / raw-pointer levels of `ty`. An iterator
                // adapter's predicate receives `&Self::Item`, so a `slice::Iter`
                // (`Item = &T`) hands its `.filter` closure a DOUBLE reference
                // `&&T`, while `.map` / a `.copied()` stream see `&T` / `T`. The
                // replay's `value` is the single element datatype `T`, so build ONE
                // pointee level per reference: dereferencing the param `ref_depth`
                // times must reach `value`. With only one level, the innermost
                // deref of a `&&T` param reads a FRESH symbolic — disconnecting the
                // element data (an under-constrained / spurious-CEX surface).
                let mut ref_depth = 0usize;
                let mut cur_ty = ty;
                loop {
                    let inner = match cur_ty.kind() {
                        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
                        TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => inner,
                        _ => break,
                    };
                    ref_depth += 1;
                    cur_ty = inner;
                }
                // Innermost pointee holds the real value.
                let innermost_name = self.ctx.fresh_name(prefix);
                let mut cur_pointee: std::sync::Arc<str> =
                    std::sync::Arc::from(innermost_name.as_str());
                self.env_update(std::sync::Arc::clone(&cur_pointee), value);
                // One intermediate pointer-valued pointee per ADDITIONAL reference
                // level, chained via `ref_pointees` so successive derefs walk in.
                for _ in 1..ref_depth {
                    let mid_name = self.ctx.fresh_name(prefix);
                    let mid: std::sync::Arc<str> = std::sync::Arc::from(mid_name.as_str());
                    let mid_ptr_name = self.ctx.fresh_name(prefix);
                    let mid_ptr = self.ctx.declare_var(&mid_ptr_name, ptr_sort());
                    self.env_update(std::sync::Arc::clone(&mid), mid_ptr);
                    self.ref_pointees.insert(std::sync::Arc::clone(&mid), cur_pointee);
                    cur_pointee = mid;
                }
                let ptr_name = self.ctx.fresh_name(prefix);
                let ptr = self.ctx.declare_var(&ptr_name, ptr_sort());
                InlineArgValue {
                    expr: ptr,
                    pointee_base: Some(cur_pointee),
                    flattened_entries: Vec::new(),
                    nested_ref_pointees: Vec::new(),
                }
            }
            _ => InlineArgValue {
                expr: value,
                pointee_base: None,
                flattened_entries: Vec::new(),
                nested_ref_pointees: Vec::new(),
            },
        }
    }

    /// The zero of a sort. Test-only since review round 2: the sum stub reads
    /// its identity from the call's Rust types (`SumSummand::identity_bits`).
    #[cfg(test)]
    #[must_use]
    fn zero_expr_for_sort(sort: &Sort) -> Option<Expr> {
        use ay_bindings::SortInner;
        match sort.inner() {
            SortInner::Bool => Some(Expr::bool_const(false)),
            SortInner::BitVec(bv) => Some(Expr::bitvec_const(0, bv.width)),
            SortInner::Int => Some(Expr::int_const(0)),
            SortInner::Real => Some(Expr::real_const(0)),
            SortInner::Array(_)
            | SortInner::Datatype(_)
            | SortInner::String
            | SortInner::FloatingPoint(_, _)
            | SortInner::Uninterpreted(_)
            | SortInner::RegLan => None,
            _ => None,
        }
    }
}

/// Is `place` a bare local of `body` that nothing reads? It may be written by
/// calls (the one being encoded, or another arm's call into the same local),
/// and otherwise appear only in storage markers and the no-op `PlaceMention`
/// and `FakeRead` statements. Any other mention, a borrow included, is a read;
/// so is the return place and every argument local.
fn local_is_never_read(body: &rustc_public::mir::Body, place: &Place) -> bool {
    use rustc_public::mir::visit::{
        Location, MirVisitor, PlaceContext, statement_location, terminator_location,
    };
    use rustc_public::mir::{Local, Statement, StatementKind, TerminatorKind};

    struct Reads {
        local: Local,
        read: bool,
    }
    impl MirVisitor for Reads {
        fn visit_statement(&mut self, stmt: &Statement, location: Location) {
            match &stmt.kind {
                StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::PlaceMention(_)
                | StatementKind::FakeRead(..) => {}
                _ => self.super_statement(stmt, location),
            }
        }
        fn visit_local(&mut self, local: &Local, _ptx: PlaceContext, _location: Location) {
            if *local == self.local {
                self.read = true;
            }
        }
    }

    if !place.projection.is_empty() || place.local == 0 || place.local <= body.arg_locals().len() {
        return false;
    }
    let mut reads = Reads { local: place.local, read: false };
    for (bb, block) in body.blocks.iter().enumerate() {
        for (idx, stmt) in block.statements.iter().enumerate() {
            reads.visit_statement(stmt, statement_location(body, &bb, idx));
        }
        let location = terminator_location(body, &bb);
        match &block.terminator.kind {
            TerminatorKind::Call { func, args, destination, .. }
                if destination.local == place.local && destination.projection.is_empty() =>
            {
                reads.visit_operand(func, location);
                for arg in args {
                    reads.visit_operand(arg, location);
                }
            }
            _ => reads.visit_terminator(&block.terminator, location),
        }
        if reads.read {
            return false;
        }
    }
    !reads.read
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen_ay::names::enum_sort;
    use crate::codegen_ay::types::int_sort;

    type SC<'a, 'tcx, 't> = super::super::super::StatementCodegen<'a, 'tcx, 't>;

    fn option_sort() -> Sort {
        enum_sort(
            "Option_u32",
            [("None", Vec::<(&str, Sort)>::new()), ("Some", vec![("value", Sort::bv32())])],
        )
    }

    fn non_option_enum_sort() -> Sort {
        enum_sort(
            "Status",
            [("Ready", Vec::<(&str, Sort)>::new()), ("Running", vec![("progress", Sort::bv32())])],
        )
    }

    fn result_unit_err_sort() -> Sort {
        enum_sort(
            "Result_unit_E",
            [("Ok", Vec::<(&str, Sort)>::new()), ("Err", vec![("err", Sort::bv32())])],
        )
    }

    #[test]
    fn test_is_option_like_sort_true_for_option() {
        assert!(SC::is_option_like_sort(&option_sort()));
    }

    #[test]
    fn test_is_option_like_sort_structural_fallback_accepts_non_option_enum() {
        let sort = non_option_enum_sort();
        assert!(
            SC::is_option_like_sort(&sort),
            "structural fallback still accepts non-Option enums with empty + 1-field variants"
        );
    }

    #[test]
    fn test_is_option_like_sort_structural_fallback_accepts_result() {
        let sort = result_unit_err_sort();
        assert!(
            SC::is_option_like_sort(&sort),
            "structural fallback accepts Result<(), E> - document this known limitation"
        );
    }

    #[test]
    fn test_is_option_like_sort_false_for_non_datatype() {
        assert!(!SC::is_option_like_sort(&Sort::bv32()));
        assert!(!SC::is_option_like_sort(&bool_sort()));
        assert!(!SC::is_option_like_sort(&int_sort()));
    }

    #[test]
    fn test_option_payload_sort_extracts_some_field_by_name() {
        let sort = option_sort();
        let payload = SC::option_payload_sort(&sort);
        assert_eq!(payload, Some(Sort::bv32()));
    }

    #[test]
    fn test_option_payload_sort_prefers_some_over_structural() {
        let sort = enum_sort(
            "OptionPlus",
            [
                ("None", Vec::<(&str, Sort)>::new()),
                ("Some", vec![("value", Sort::bv32())]),
                ("Extra", vec![("data", Sort::bv64())]),
            ],
        );
        let payload = SC::option_payload_sort(&sort);
        assert_eq!(payload, Some(Sort::bv32()));
    }

    #[test]
    fn test_option_payload_sort_falls_back_to_structural_for_non_option() {
        let sort = non_option_enum_sort();
        let payload = SC::option_payload_sort(&sort);
        assert_eq!(payload, Some(Sort::bv32()));
    }

    #[test]
    fn test_option_payload_sort_returns_none_for_all_empty() {
        let sort = enum_sort("AllEmpty", [("A", Vec::<(&str, Sort)>::new()), ("B", vec![])]);
        assert_eq!(SC::option_payload_sort(&sort), None);
    }

    // =========================================================================
    // zero_expr_for_sort tests (proof_coverage)
    // =========================================================================

    #[test]
    fn test_zero_expr_for_sort_bool() {
        let result = SC::zero_expr_for_sort(&bool_sort());
        assert!(result.is_some());
        let expr = result.expect("bool should produce zero expr");
        assert_eq!(expr, Expr::bool_const(false));
    }

    #[test]
    fn test_zero_expr_for_sort_bitvec() {
        let result = SC::zero_expr_for_sort(&Sort::bv32());
        assert!(result.is_some());
        let expr = result.expect("bv32 should produce zero expr");
        assert_eq!(expr, Expr::bitvec_const(0, 32));
    }

    #[test]
    fn test_zero_expr_for_sort_int() {
        let result = SC::zero_expr_for_sort(&int_sort());
        assert!(result.is_some());
        let expr = result.expect("int should produce zero expr");
        assert_eq!(expr, Expr::int_const(0));
    }

    #[test]
    fn test_zero_expr_for_sort_real() {
        let result = SC::zero_expr_for_sort(&Sort::real());
        assert!(result.is_some());
        let expr = result.expect("real should produce zero expr");
        assert_eq!(expr, Expr::real_const(0));
    }

    #[test]
    fn test_zero_expr_for_sort_array_returns_none() {
        let arr_sort = Sort::array(Sort::bv32(), Sort::bv32());
        assert!(SC::zero_expr_for_sort(&arr_sort).is_none());
    }

    #[test]
    fn test_zero_expr_for_sort_datatype_returns_none() {
        let dt_sort = option_sort();
        assert!(SC::zero_expr_for_sort(&dt_sort).is_none());
    }
}

/// Is `ty` a chain of core's `Map` adapters (and the value-preserving
/// `Copied` / `Cloned`) over a slice iterator, with at least one `Map`? Read
/// from the MIR type, not the recorded stages: `filter_map` is recorded as a
/// `Map` stage (`IterFilterMap` shares `codegen_iter_map_stub`).
fn is_map_chain_over_slice_iter(ty: Ty) -> bool {
    use rustc_public::CrateDef;
    let mut ty = ty;
    let mut maps = 0usize;
    for _ in 0..16 {
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
            return false;
        };
        let name = def.name();
        let last = name.rsplit("::").next().unwrap_or(&name);
        let core_iter = name.starts_with("core::iter::") || name.starts_with("std::iter::");
        match last {
            "Map" if core_iter => maps += 1,
            "Copied" | "Cloned" if core_iter => {}
            "Iter" if name.contains("slice") => return maps > 0,
            _ => return false,
        }
        let Some(inner) = args.0.iter().find_map(|arg| match arg {
            rustc_public::ty::GenericArgKind::Type(inner) => Some(*inner),
            _ => None,
        }) else {
            return false;
        };
        ty = inner;
    }
    false
}
