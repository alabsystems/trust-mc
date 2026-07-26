// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Utility builders for iterator adapter call handling.
//!
//! Extracted from `codegen_call_iterator_adapter.rs` per #2884 (500 LOC threshold).
//! Moved into directory module per #4129.

use std::collections::HashSet;

use ay_bindings::{Expr, Sort, SortInner};
use rustc_public::mir::Operand;

use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{CtorFieldExt, SignExtension, bool_sort};

use super::super::stubs_option_helpers::{OptionHelpers, option_value_sort};
use super::super::{ChcCtx, chc_fresh_name, declare_pending_var};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Build Option-shaped result for adapter `next()` calls.
    ///
    /// Returns `(option_result, raw_payload)` where `raw_payload` is the
    /// unconstrained symbolic payload before it was wrapped in Some/None.
    /// Callers can use `raw_payload` to add constraints (e.g., Part of #4112).
    pub(in crate::codegen_ay::chc) fn build_adapter_next_result(
        &mut self,
        stub: StubKind,
        has_remaining: Expr,
        out_sort: &Sort,
    ) -> (Option<Expr>, Option<Expr>) {
        let payload_sort = match Self::adapter_option_payload_sort(out_sort) {
            Some(s) => s,
            None => return (None, None),
        };
        let payload = self.fresh_adapter_symbol("iter_next_value", payload_sort);
        let some_value = match self.make_some_expr_for_option(payload.clone(), out_sort) {
            Some(s) => s,
            None => return (None, Some(payload)),
        };
        let none_value = match self.make_none_expr_for_option(out_sort) {
            Some(n) => n,
            None => return (None, Some(payload)),
        };

        match stub {
            StubKind::FilterNext => {
                let keep_item = self.fresh_adapter_symbol("filter_next_keep", bool_sort());
                let when_some = Expr::ite(keep_item, some_value, none_value.clone());
                (Some(Expr::ite(has_remaining, when_some, none_value)), Some(payload))
            }
            StubKind::MapNext | StubKind::FlattenNext | StubKind::ChainNext | StubKind::ZipNext => {
                (Some(Expr::ite(has_remaining, some_value, none_value)), Some(payload))
            }
            _other => (None, None), // external enum: StubKind
        }
    }

    /// Build Option<T> result for RangeIteratorImpl::spec_next.
    ///
    /// Returns Some(current_start) when `start < end`, else None.
    pub(in crate::codegen_ay::chc) fn build_range_next_result(
        &mut self,
        has_remaining: Expr,
        current_item: Expr,
        out_sort: &Sort,
    ) -> Option<Expr> {
        let payload_sort = Self::adapter_option_payload_sort(out_sort)?;
        let payload = self.coerce_value_to_sort(current_item, &payload_sort, false)?;
        let some_value = self.make_some_expr_for_option(payload, out_sort)?;
        let none_value = self.make_none_expr_for_option(out_sort)?;
        Some(Expr::ite(has_remaining, some_value, none_value))
    }

    /// Resolve the first adapter receiver argument and, when possible, its local.
    pub(in crate::codegen_ay::chc) fn iterator_receiver_expr_and_local(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<(Expr, Option<usize>)> {
        let receiver = args.first()?;
        let iter_expr = self
            .get_collection_arg(receiver, modified_locals)
            .or_else(|| self.resolve_ref_operand(receiver, modified_locals))
            .or_else(|| self.translate_operand_with_modified(receiver, modified_locals))?;

        let iter_local = if let Operand::Copy(place) | Operand::Move(place) = receiver {
            let ref_local: usize = place.local;
            Some(self.ref_resolution.ref_targets.get(&ref_local).map_or(ref_local, |rt| rt.local))
        } else {
            None
        };
        Some((iter_expr, iter_local))
    }

    /// Build a symbolic value used by iterator adapter modeling.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn fresh_adapter_symbol(
        &self,
        prefix: &str,
        sort: Sort,
    ) -> Expr {
        // Part of #3447: adapter symbol is unconstrained (over-approximation).
        self.record_aggregate_gap("iter_adapter_symbol_unconstrained");
        declare_pending_var(chc_fresh_name(prefix), sort)
    }

    /// Compute a best-effort "has remaining items" condition and updated iterator.
    ///
    /// Supports:
    /// - direct iterators with `(fld_pos, fld_len)`
    /// - vec iterators with `(fld_vec, fld_pos)` and `fld_vec.fld_len`
    /// - wrapped adapters with `fld_iter` / `fld_inner`
    #[must_use]
    pub(in crate::codegen_ay::chc) fn advance_iterator_expr(
        &mut self,
        iter_expr: &Expr,
    ) -> Option<(Expr, Expr)> {
        let dt = iter_expr.sort().datatype_sort()?;
        let ctor = dt.constructors.first()?;

        if let (Some(pos_field), Some(len_field)) = (ctor.field("fld_pos"), ctor.field("fld_len")) {
            // field_select accepts impl Into<String> — pass &str to avoid String clones
            let pos = iter_expr.clone().field_select(&*dt.name, "fld_pos", pos_field.sort.clone());
            let len = iter_expr.clone().field_select(&*dt.name, "fld_len", len_field.sort.clone());
            let (has_remaining, pos_for_update) = Self::adapter_pos_lt_len(pos, len)?;
            let pos_width = pos_for_update.sort().bitvec_width()?;
            let one = Expr::bitvec_const(1u64, pos_width);
            let next_pos =
                Expr::ite(has_remaining.clone(), pos_for_update.clone().bvadd(one), pos_for_update);
            let new_iter = self.rebuild_datatype_with_field(iter_expr, "fld_pos", next_pos)?;
            return Some((new_iter, has_remaining));
        }

        if let (Some(vec_field), Some(pos_field)) = (ctor.field("fld_vec"), ctor.field("fld_pos")) {
            let vec = iter_expr.clone().field_select(&*dt.name, "fld_vec", vec_field.sort.clone());
            let pos = iter_expr.clone().field_select(&*dt.name, "fld_pos", pos_field.sort.clone());

            // Clone Sort (O(1) Arc) so dt borrows from vec_sort, not vec.
            let vec_sort = vec.sort().clone();
            let vec_dt = vec_sort.datatype_sort()?;
            let vec_ctor = vec_dt.constructors.first()?;
            let len_field = vec_ctor.field("fld_len")?;
            let len = vec.field_select(&*vec_dt.name, "fld_len", len_field.sort.clone());

            let (has_remaining, pos_for_update) = Self::adapter_pos_lt_len(pos, len)?;
            let pos_width = pos_for_update.sort().bitvec_width()?;
            let one = Expr::bitvec_const(1u64, pos_width);
            let next_pos =
                Expr::ite(has_remaining.clone(), pos_for_update.clone().bvadd(one), pos_for_update);
            let new_iter = self.rebuild_datatype_with_field(iter_expr, "fld_pos", next_pos)?;
            return Some((new_iter, has_remaining));
        }

        if let Some(inner_field) = ctor.field("fld_iter").or_else(|| ctor.field("fld_inner")) {
            let inner_iter = iter_expr.clone().field_select(
                &*dt.name,
                &*inner_field.name,
                inner_field.sort.clone(),
            );
            if let Some((advanced_inner, has_remaining)) = self.advance_iterator_expr(&inner_iter) {
                let new_iter =
                    self.rebuild_datatype_with_field(iter_expr, &inner_field.name, advanced_inner)?;
                return Some((new_iter, has_remaining));
            }
        }

        None
    }

    /// Rebuild a datatype expression while replacing a single field value.
    pub(in crate::codegen_ay::chc) fn rebuild_datatype_with_field(
        &self,
        base_expr: &Expr,
        replaced_field: &str,
        replacement: Expr,
    ) -> Option<Expr> {
        let dt = base_expr.sort().datatype_sort()?;
        let ctor = dt.constructors.first()?;

        // field_select/datatype_constructor accept impl Into<String> — pass &str to avoid String clones
        // Use Option::take() for replacement since it matches exactly one field in the loop.
        let mut replacement = Some(replacement);
        let mut args = Vec::with_capacity(ctor.fields.len());
        for field in &ctor.fields {
            if field.name == replaced_field {
                let r = replacement.take()?;
                let value = self.coerce_value_to_sort(r, &field.sort, false)?;
                args.push(value);
            } else {
                args.push(base_expr.clone().field_select(
                    &*dt.name,
                    &*field.name,
                    field.sort.clone(),
                ));
            }
        }
        Some(Expr::datatype_constructor(&*dt.name, &*ctor.name, args, base_expr.sort().clone()))
    }

    /// Construct a map/filter adapter value with the provided inner iterator.
    pub(in crate::codegen_ay::chc) fn construct_adapter_with_inner_iter(
        &self,
        adapter_sort: &Sort,
        inner_iter: Expr,
    ) -> Option<Expr> {
        let dt = adapter_sort.datatype_sort()?;
        let ctor = dt.constructors.first()?;
        let inner_field = ctor
            .fields
            .iter()
            .find(|field| field.name == "fld_iter" || field.name == "fld_inner")?;
        // Use Option::take() since inner matches exactly one field in the loop.
        let mut coerced_inner =
            Some(self.coerce_value_to_sort(inner_iter, &inner_field.sort, false)?);

        let mut args = Vec::with_capacity(ctor.fields.len());
        for field in &ctor.fields {
            if field.name == inner_field.name {
                args.push(coerced_inner.take()?);
            } else {
                // Part of #3447: Record that adapter fields (closures, etc.)
                // are unconstrained symbolics — sound over-approximation.
                self.record_aggregate_gap("iter_adapter_field_unconstrained");
                args.push(self.fresh_adapter_symbol("iter_adapter_field", field.sort.clone()));
            }
        }

        // datatype_constructor accepts impl Into<String> — pass &str to avoid String clones
        Some(Expr::datatype_constructor(&*dt.name, &*ctor.name, args, adapter_sort.clone()))
    }

    /// Extract the original Vec from a direct VecIntoIter for identity `collect()`.
    /// Returns `ite(pos == 0, vec, symbolic_vec)`. Does not traverse adapter chains.
    /// Part of #3348.
    pub(in crate::codegen_ay::chc) fn try_collect_vec_from_iterator(
        &self,
        iter_expr: &Expr,
    ) -> Option<Expr> {
        let (vec_expr, pos) = self.find_vec_in_iterator_chain(iter_expr)?;
        let pos_width = pos.sort().bitvec_width()?;
        let pos_zero = pos.eq(Expr::bitvec_const(0u64, pos_width));
        let sym = self.fresh_adapter_symbol("iter_collect_vec", vec_expr.sort().clone());
        Some(Expr::ite(pos_zero, vec_expr, sym))
    }

    /// Extract the remaining element count from an iterator chain.
    ///
    /// Traverses through adapter wrappers to find the base iterator's
    /// `(fld_pos, fld_len)` or `(fld_vec.fld_len, fld_pos)` and returns
    /// `len - pos` (the number of elements remaining to be consumed).
    ///
    /// Part of #3348: length propagation for IterCollect.
    pub(in crate::codegen_ay::chc) fn try_extract_iterator_remaining_len(
        &self,
        iter_expr: &Expr,
    ) -> Option<Expr> {
        let dt = iter_expr.sort().datatype_sort()?;
        let ctor = dt.constructors.first()?;

        // Direct iterator with fld_pos/fld_len.
        if let (Some(pos_field), Some(len_field)) = (ctor.field("fld_pos"), ctor.field("fld_len")) {
            let pos = iter_expr.clone().field_select(&*dt.name, "fld_pos", pos_field.sort.clone());
            let len = iter_expr.clone().field_select(&*dt.name, "fld_len", len_field.sort.clone());
            return Self::bv_saturating_sub(len, pos);
        }

        // VecIntoIter with fld_vec/fld_pos: length from fld_vec.fld_len.
        if let (Some(vec_field), Some(pos_field)) = (ctor.field("fld_vec"), ctor.field("fld_pos")) {
            let vec_val =
                iter_expr.clone().field_select(&*dt.name, "fld_vec", vec_field.sort.clone());
            let pos = iter_expr.clone().field_select(&*dt.name, "fld_pos", pos_field.sort.clone());
            let vec_sort = vec_val.sort().clone();
            let vec_dt = vec_sort.datatype_sort()?;
            let vec_ctor = vec_dt.constructors.first()?;
            let len_field = vec_ctor.field("fld_len")?;
            let len = vec_val.field_select(&*vec_dt.name, "fld_len", len_field.sort.clone());
            return Self::bv_saturating_sub(len, pos);
        }

        // Wrapped adapter: recurse through fld_iter/fld_inner.
        if let Some(inner_field) = ctor.field("fld_iter").or_else(|| ctor.field("fld_inner")) {
            let inner = iter_expr.clone().field_select(
                &*dt.name,
                &*inner_field.name,
                inner_field.sort.clone(),
            );
            return self.try_extract_iterator_remaining_len(&inner);
        }

        None
    }

    /// True only when the iterator position is syntactically known to be zero.
    ///
    /// Concrete adapter payloads describe the full output sequence at iterator
    /// construction time. Replaying that sequence at `collect()` is sound only
    /// before any item has been consumed.
    pub(in crate::codegen_ay::chc) fn iterator_position_is_definitely_zero(
        &self,
        iter_expr: &Expr,
    ) -> bool {
        self.try_extract_iterator_position(iter_expr)
            .and_then(|pos| Self::try_eval_concrete_bv_usize(&pos))
            == Some(0)
    }

    fn try_extract_iterator_position(&self, iter_expr: &Expr) -> Option<Expr> {
        if iter_expr.sort().bitvec_width().is_some() {
            return Some(iter_expr.clone());
        }

        let dt = iter_expr.sort().datatype_sort()?;
        let ctor = dt.constructors.first()?;

        if let Some(pos_field) = ctor.field("fld_pos") {
            return Some(iter_expr.clone().field_select(
                &*dt.name,
                "fld_pos",
                pos_field.sort.clone(),
            ));
        }

        if let Some(inner_field) = ctor.field("fld_iter").or_else(|| ctor.field("fld_inner")) {
            let inner = iter_expr.clone().field_select(
                &*dt.name,
                &*inner_field.name,
                inner_field.sort.clone(),
            );
            return self.try_extract_iterator_position(&inner);
        }

        None
    }

    /// Find the Vec and position from a direct VecIntoIter expression.
    /// Returns `(fld_vec_expr, fld_pos_expr)`. Does NOT recurse through adapters.
    fn find_vec_in_iterator_chain(&self, iter_expr: &Expr) -> Option<(Expr, Expr)> {
        let dt = iter_expr.sort().datatype_sort()?;
        let ctor = dt.constructors.first()?;

        // Only match direct VecIntoIter with fld_vec/fld_pos.
        if let (Some(vec_field), Some(pos_field)) = (ctor.field("fld_vec"), ctor.field("fld_pos")) {
            let vec_val =
                iter_expr.clone().field_select(&*dt.name, "fld_vec", vec_field.sort.clone());
            let pos = iter_expr.clone().field_select(&*dt.name, "fld_pos", pos_field.sort.clone());
            return Some((vec_val, pos));
        }

        None
    }

    /// Bitvector saturating subtraction: `max(a - b, 0)`.
    ///
    /// Returns `ite(a >= b, a - b, 0)` after width-normalizing both operands.
    fn bv_saturating_sub(a: Expr, b: Expr) -> Option<Expr> {
        let a_width = a.sort().bitvec_width()?;
        let b_width = b.sort().bitvec_width()?;
        let width = a_width.max(b_width);
        let a_norm = if a_width == width {
            a
        } else {
            crate::codegen_ay::types::coerce_bitvec_width_safe(a, width, SignExtension::ZeroExtend)
        };
        let b_norm = if b_width == width {
            b
        } else {
            crate::codegen_ay::types::coerce_bitvec_width_safe(b, width, SignExtension::ZeroExtend)
        };
        let zero = Expr::bitvec_const(0u64, width);
        let diff = a_norm.clone().bvsub(b_norm.clone());
        Some(Expr::ite(a_norm.bvuge(b_norm), diff, zero))
    }

    /// Return payload sort for Option-like result sorts (enum or struct encoding).
    pub(in crate::codegen_ay::chc) fn adapter_option_payload_sort(
        option_sort: &Sort,
    ) -> Option<Sort> {
        option_value_sort(option_sort).or_else(|| {
            let dt = option_sort.datatype_sort()?;
            let ctor = dt.constructors.first()?;
            if ctor.fields.len() >= 2 && ctor.fields.first()?.name == "is_some" {
                return ctor.fields.get(1).map(|field| field.sort.clone());
            }
            None
        })
    }

    /// Produce a zero/identity constant for sum-like result sorts.
    pub(in crate::codegen_ay::chc) fn adapter_zero_expr_for_sort(sort: &Sort) -> Option<Expr> {
        match sort.inner() {
            SortInner::Bool => Some(Expr::bool_const(false)),
            SortInner::BitVec(bv) => Some(Expr::bitvec_const(0u64, bv.width)),
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
