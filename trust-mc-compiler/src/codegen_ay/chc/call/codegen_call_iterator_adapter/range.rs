// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Range-specific helpers for iterator adapter CHC call codegen.
//! Moved into directory module per #4129.

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use std::collections::HashSet;

use crate::codegen_ay::types::{CtorFieldExt, SignExtension, coerce_bitvec_width_safe};

use super::super::ChcCtx;
use super::super::codegen_ctx::diagnostics::CellCounter;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Resolve a field expression for a flattened local from input/output state vars.
    ///
    /// Part of #2876: When a concrete value was previously recorded in
    /// `flattened_field_env`, return that value instead of a state variable
    /// reference. This prevents tautological `out == out` constraints when
    /// consecutive field stores replace each other's constraints via
    /// `constrain_flattened_fields`.
    ///
    /// Part of #3474: The env lookup is now unconditional (not gated on
    /// `modified_locals`). When a flattened local is storage-dead at the
    /// current block but was constrained in a previous block (e.g. VecFromElem
    /// populating a temporary that is later consumed by aggregate
    /// construction), the env holds the concrete value. Without this fallback,
    /// dead locals produce free variables in the CHC relation, making
    /// constraints vacuous and causing spurious counterexamples.
    pub(in crate::codegen_ay::chc) fn flattened_local_field_expr(
        &self,
        local_idx: usize,
        field_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // Check per-field expression env first — always, not just for
        // modified locals (Part of #2876, #3474).
        if let Some(expr) = self.encode.flattened_field_env.get(&(local_idx, field_idx)) {
            return Some(expr.clone());
        }
        let base_idx = self.try_state_idx_for_local(local_idx)?;
        let slot = base_idx + field_idx;
        let vars = if modified_locals.contains(&local_idx) {
            &self.state_var_mgr.output_state_vars
        } else {
            &self.state_var_mgr.state_vars
        };
        vars.get(slot).map(|(name, sort)| Expr::var(&**name, sort.clone()))
    }

    /// Build field constraints for flattened `Option<T>` destination of range `next()`.
    ///
    /// Encodes:
    /// - `fld0 = has_remaining` (`is_some`)
    /// - `fld1 = ite(has_remaining, current_item, old_fld1)` (payload)
    /// - any additional fields preserve prior value
    pub(in crate::codegen_ay::chc) fn build_flattened_range_next_fields(
        &mut self,
        dest_local: usize,
        has_remaining: Expr,
        current_item: Expr,
        modified_locals: &HashSet<usize>,
    ) -> Option<Vec<Option<Expr>>> {
        let field_count = self.flattened_field_count(dest_local);
        if field_count < 2 {
            return None;
        }

        let payload_sort = self
            .state_var_mgr
            .output_state_vars
            .get(self.try_state_idx_for_local(dest_local)? + 1)
            .map(|(_, sort)| sort.clone())?;
        let coerced_item = self.coerce_value_to_sort(current_item, &payload_sort, false)?;
        let old_payload = self.flattened_local_field_expr(dest_local, 1, modified_locals)?;
        let payload_update = Expr::ite(has_remaining.clone(), coerced_item, old_payload);

        let mut values = vec![Some(has_remaining), Some(payload_update)];
        for field_idx in 2..field_count {
            values.push(self.flattened_local_field_expr(dest_local, field_idx, modified_locals));
        }
        Some(values)
    }

    /// Determine whether a Range local's element type should use signed BV comparison.
    fn range_local_element_signedness(&self, iter_local: Option<usize>) -> Option<bool> {
        let local_idx = iter_local?;
        let local_decl = self.body.locals().get(local_idx)?;
        match local_decl.ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args)) if def.trimmed_name() == "Range" => {
                match args.0.first() {
                    Some(GenericArgKind::Type(elem_ty)) => super::super::ty_signedness(*elem_ty),
                    _ => None, // external enum: GenericArgKind
                }
            }
            TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "IndexRange" => {
                Some(false)
            }
            _ => None, // external enum: TyKind
        }
    }

    /// Advance a range iterator (`Range<T>::next`) for both datatype and flattened paths.
    ///
    /// Returns:
    /// - updated iterator state (datatype iterator value, or flattened `start` scalar)
    /// - `has_remaining` guard (`start < end`)
    /// - current item (pre-increment `start`) for `Option::Some`
    #[must_use]
    pub(in crate::codegen_ay::chc) fn advance_range_iterator_expr(
        &mut self,
        iter_expr: &Expr,
        iter_local: Option<usize>,
        modified_locals: &HashSet<usize>,
    ) -> Option<(Expr, Expr, Expr)> {
        let is_signed = self.range_local_element_signedness(iter_local).unwrap_or_else(|| {
            crate::codegen_ay::shared::signedness_fallback_for_arithmetic(
                "advance_range_iterator_expr",
            )
        });

        if let Some(dt) = iter_expr.sort().datatype_sort() {
            let ctor = dt.constructors.first()?;
            let start_field = ctor.field("fld_start")?;
            let end_field = ctor.field("fld_end")?;

            let start =
                iter_expr.clone().field_select(&*dt.name, "fld_start", start_field.sort.clone());
            let end = iter_expr.clone().field_select(&*dt.name, "fld_end", end_field.sort.clone());

            let (has_remaining, next_start) =
                Self::range_has_remaining_and_next_start(start.clone(), end, is_signed)?;
            let new_iter = self.rebuild_datatype_with_field(iter_expr, "fld_start", next_start)?;
            self.diagnostics.range_spec_next_datatype_path.inc();
            return Some((new_iter, has_remaining, start));
        }

        let local_idx = iter_local?;
        if !self.flatten.flattened_tuple_locals.contains(&local_idx)
            || self.flattened_field_count(local_idx) < 2
        {
            return None;
        }

        let start = self.flattened_local_field_expr(local_idx, 0, modified_locals)?;
        let end = self.flattened_local_field_expr(local_idx, 1, modified_locals)?;
        let (has_remaining, next_start) =
            Self::range_has_remaining_and_next_start(start.clone(), end, is_signed)?;
        self.diagnostics.range_spec_next_flattened_path.inc();
        Some((next_start, has_remaining, start))
    }

    /// Emit the post-advance range invariant used by `RangeIteratorImpl::spec_next`.
    ///
    /// This is deliberately guarded by `has_remaining`: reverse/empty ranges
    /// (`start >= end`) are legal Rust values and must remain modeled as empty
    /// rather than pruned. When a range does advance, though, `start + 1 <= end`
    /// is a semantic consequence of `start < end`; spelling it out gives the
    /// CHC solver a stable loop invariant for composed range-next transitions.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn range_advance_bound_constraint(
        &self,
        iter_expr: &Expr,
        iter_local: Option<usize>,
        advanced_iter: &Expr,
        has_remaining: &Expr,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let is_signed = self.range_local_element_signedness(iter_local).unwrap_or_else(|| {
            crate::codegen_ay::shared::signedness_fallback_for_arithmetic(
                "range_advance_bound_constraint",
            )
        });
        let end = self.range_end_expr(iter_expr, iter_local, modified_locals)?;
        let next_start = Self::range_start_expr(advanced_iter)?;
        Self::guarded_range_le(next_start, end, has_remaining.clone(), is_signed)
    }

    fn range_start_expr(range_expr: &Expr) -> Option<Expr> {
        if let Some(dt) = range_expr.sort().datatype_sort() {
            let ctor = dt.constructors.first()?;
            let start_field = ctor.field("fld_start")?;
            return Some(range_expr.clone().field_select(
                &*dt.name,
                "fld_start",
                start_field.sort.clone(),
            ));
        }
        Some(range_expr.clone())
    }

    fn range_end_expr(
        &self,
        range_expr: &Expr,
        iter_local: Option<usize>,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if let Some(dt) = range_expr.sort().datatype_sort() {
            let ctor = dt.constructors.first()?;
            let end_field = ctor.field("fld_end")?;
            return Some(range_expr.clone().field_select(
                &*dt.name,
                "fld_end",
                end_field.sort.clone(),
            ));
        }

        let local_idx = iter_local?;
        self.flattened_local_field_expr(local_idx, 1, modified_locals)
    }

    pub(in crate::codegen_ay::chc) fn guarded_range_le(
        lhs: Expr,
        rhs: Expr,
        has_remaining: Expr,
        signed: bool,
    ) -> Option<Expr> {
        if lhs.sort().is_bitvec() && rhs.sort().is_bitvec() {
            let lhs_width = lhs.sort().bitvec_width()?;
            let rhs_width = rhs.sort().bitvec_width()?;
            let width = lhs_width.max(rhs_width);
            let lhs_cmp = if lhs_width == width {
                lhs
            } else {
                coerce_bitvec_width_safe(lhs, width, SignExtension::for_signedness(signed))
            };
            let rhs_cmp = if rhs_width == width {
                rhs
            } else {
                coerce_bitvec_width_safe(rhs, width, SignExtension::for_signedness(signed))
            };
            let le = if signed { lhs_cmp.bvsle(rhs_cmp) } else { lhs_cmp.bvule(rhs_cmp) };
            return Some(Expr::ite(has_remaining, le, Expr::bool_const(true)));
        }

        if lhs.sort().is_int() && rhs.sort().is_int() {
            return Some(Expr::ite(has_remaining, lhs.int_le(rhs), Expr::bool_const(true)));
        }

        None
    }

    /// Compute `ExactSizeIterator::len` for `IndexRange`/`Range` from `(start, end)`.
    ///
    /// Supports both datatype and flattened local representations.
    /// Part of #3247: resolves signedness from the Range element type, matching
    /// `advance_range_iterator_expr`.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn index_range_len_expr(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let (iter_expr, iter_local) =
            self.iterator_receiver_expr_and_local(args, modified_locals)?;

        // Part of #3247: resolve signedness for range length comparison.
        // IndexRange is always unsigned; Range<T> inherits T's signedness.
        let is_signed = self.range_local_element_signedness(iter_local).unwrap_or(false);

        if let Some(dt) = iter_expr.sort().clone().datatype_sort() {
            let ctor = dt.constructors.first()?;
            // Direct IndexRange: has fld_start/fld_end
            if let (Some(start_field), Some(end_field)) =
                (ctor.field("fld_start"), ctor.field("fld_end"))
            {
                let start = iter_expr.clone().field_select(
                    &*dt.name,
                    "fld_start",
                    start_field.sort.clone(),
                );
                let end = iter_expr.field_select(&*dt.name, "fld_end", end_field.sort.clone());
                return Self::range_len_expr(start, end, is_signed);
            }
            // PolymorphicIter: extract fld_alive (IndexRange) then get start/end
            if let Some(alive_field) = ctor.field("fld_alive") {
                let alive_expr =
                    iter_expr.field_select(&*dt.name, "fld_alive", alive_field.sort.clone());
                if let Some(inner_dt) = alive_expr.sort().clone().datatype_sort() {
                    let inner_ctor = inner_dt.constructors.first()?;
                    if let (Some(start_f), Some(end_f)) =
                        (inner_ctor.field("fld_start"), inner_ctor.field("fld_end"))
                    {
                        let start = alive_expr.clone().field_select(
                            &*inner_dt.name,
                            "fld_start",
                            start_f.sort.clone(),
                        );
                        let end =
                            alive_expr.field_select(&*inner_dt.name, "fld_end", end_f.sort.clone());
                        return Self::range_len_expr(start, end, is_signed);
                    }
                }
            }
        }

        // Fallback: read start/end from state variable slots directly.
        // The receiver may not be in flattened_tuple_locals (e.g., IndexRange passed
        // by reference through ExactSizeIterator::len), but it still occupies two
        // consecutive state variable slots (start, end) that we can read.
        let local_idx = iter_local?;
        let start = self.flattened_local_field_expr(local_idx, 0, modified_locals)?;
        let end = self.flattened_local_field_expr(local_idx, 1, modified_locals)?;
        Self::range_len_expr(start, end, is_signed)
    }

    /// Compute non-negative range length from start/end.
    ///
    /// For bitvectors this emits `ite(end >= start, end - start, 0)` to avoid
    /// wraparound lengths on malformed states.
    ///
    /// Part of #3247: `signed` controls whether comparison uses `bvsge`/`bvsle`
    /// (signed) or `bvuge`/`bvule` (unsigned), matching `range_has_remaining_and_next_start`.
    pub(in crate::codegen_ay::chc) fn range_len_expr(
        start: Expr,
        end: Expr,
        signed: bool,
    ) -> Option<Expr> {
        if start.sort().is_bitvec() && end.sort().is_bitvec() {
            let start_width = start.sort().bitvec_width()?;
            let end_width = end.sort().bitvec_width()?;
            let width = start_width.max(end_width);
            let start_cmp = if start_width == width {
                start
            } else {
                coerce_bitvec_width_safe(start, width, SignExtension::for_signedness(signed))
            };
            let end_cmp = if end_width == width {
                end
            } else {
                coerce_bitvec_width_safe(end, width, SignExtension::for_signedness(signed))
            };
            let zero = Expr::bitvec_const(0u64, width);
            let len = end_cmp.clone().bvsub(start_cmp.clone());
            let ge = if signed { end_cmp.bvsge(start_cmp) } else { end_cmp.bvuge(start_cmp) };
            return Some(Expr::ite(ge, len, zero));
        }
        if start.sort().is_int() && end.sort().is_int() {
            let zero = Expr::int_const(0);
            let len = end.clone().int_sub(start.clone());
            return Some(Expr::ite(end.int_ge(start), len, zero));
        }
        None
    }

    /// Compute `has_remaining` and the next range start value.
    fn range_has_remaining_and_next_start(
        start: Expr,
        end: Expr,
        signed: bool,
    ) -> Option<(Expr, Expr)> {
        if start.sort().is_bitvec() && end.sort().is_bitvec() {
            let (has_remaining, start_cmp) =
                Self::adapter_pos_lt_len_with_signedness(start, end, signed)?;
            let width = start_cmp.sort().bitvec_width()?;
            let one = Expr::bitvec_const(1u64, width);
            let next = Expr::ite(has_remaining.clone(), start_cmp.clone().bvadd(one), start_cmp);
            Some((has_remaining, next))
        } else if start.sort().is_int() && end.sort().is_int() {
            let has_remaining = start.clone().int_lt(end);
            let next =
                Expr::ite(has_remaining.clone(), start.clone().int_add(Expr::int_const(1)), start);
            Some((has_remaining, next))
        } else {
            None
        }
    }

    /// Compare iterator position and length with width normalization.
    ///
    /// Uses unsigned comparison (default iterator semantics).
    pub(in crate::codegen_ay::chc) fn adapter_pos_lt_len(
        pos: Expr,
        len: Expr,
    ) -> Option<(Expr, Expr)> {
        Self::adapter_pos_lt_len_with_signedness(pos, len, false)
    }

    /// Compare iterator position and length with width normalization and signedness.
    pub(in crate::codegen_ay::chc) fn adapter_pos_lt_len_with_signedness(
        pos: Expr,
        len: Expr,
        signed: bool,
    ) -> Option<(Expr, Expr)> {
        let pos_width = pos.sort().bitvec_width()?;
        let len_width = len.sort().bitvec_width()?;
        let width = pos_width.max(len_width);
        let pos_cmp = if pos_width == width {
            pos
        } else {
            coerce_bitvec_width_safe(pos, width, SignExtension::for_signedness(signed))
        };
        let len_cmp = if len_width == width {
            len
        } else {
            coerce_bitvec_width_safe(len, width, SignExtension::for_signedness(signed))
        };
        let has_remaining =
            if signed { pos_cmp.clone().bvslt(len_cmp) } else { pos_cmp.clone().bvult(len_cmp) };
        Some((has_remaining, pos_cmp))
    }
}
use super::super::stubs_option_helpers::OptionHelpers;
