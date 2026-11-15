// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SliceRepeat — `<[T]>::repeat(&self, n) -> Vec<T>`.
//!
//! `str::repeat` is `String::from_utf8_unchecked(self.as_bytes().repeat(n))`,
//! and the slice method is abstracted at the reachability boundary, so the call used to
//! reach the tail's anonymous havoc: the result `Vec` was unconstrained and
//! `String::from("a").repeat(1).chars().nth(0)` could be anything
//! (`expected/string-repeat/2235.rs`).
//!
//! The model is exact or it declines:
//! - a constant `n == 0`, or an empty source, is an empty `Vec`;
//! - `n == 1` is the source itself (same bytes, same length);
//! - a constant `n` over a source of concrete length `L` with `L * n` at most
//!   [`SLICE_REPEAT_UNROLL_LIMIT`] is a store chain, element `i` being source
//!   element `i mod L`.
//!
//! Every other shape records its own fail-closed reason and havocs the
//! destination, which is what the tail did before. The buffer gets a fresh
//! heap object sized `len * size_of::<T>()`, as `StringFrom` does, so the
//! pointer cannot alias another allocation.

use crate::codegen_ay::chc::codegen_ctx::ExactVar;
use ay_bindings::{Expr, Sort};
use rustc_public::mir::{Operand, StatementKind, TerminatorKind};
use tracing::debug;

use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use crate::codegen_ay::names::vec_layout;
use crate::codegen_ay::types::{CtorFieldExt, POINTER_WIDTH};

use super::ChcCtx;
use super::chc_call_context::ChcCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_call_vec_ops::ProjectedVecState;
use super::codegen_ctx::globals::chc_fresh_name;
use super::codegen_ctx::types::CollectionProjectionKind;
use super::codegen_expr_heap::{obj_size_in, obj_size_out, obj_valid_in, obj_valid_out};
use super::codegen_rules::CodegenRules;
use crate::codegen_ay::stubs::StubKind;

/// Largest result, in elements, that is unrolled into a store chain.
pub(super) const SLICE_REPEAT_UNROLL_LIMIT: usize = 64;

/// Most call links followed from `repeat`'s argument back to the `String`.
const SOURCE_CHAIN_LIMIT: usize = 6;

/// A call whose result is its first argument re-typed, with the same bytes:
/// `str::as_bytes`, `String::as_str`, `<String as Deref>::deref`
/// (the registry's `StringAsStr`). `str::repeat` reaches `<[u8]>::repeat`
/// through exactly this chain.
pub(super) fn is_repeat_source_passthrough(callee_path: &str, stub: Option<StubKind>) -> bool {
    matches!(stub, Some(StubKind::StringAsStr))
        || (callee_path.ends_with("::as_bytes")
            && (callee_path.contains("<impl str>") || callee_path.contains("str::")))
        || (callee_path.ends_with("::as_str") && callee_path.contains("String"))
        || (callee_path.contains("String as") && callee_path.ends_with("Deref>::deref"))
}

/// The bytes of a resolved source, copied out of the string lanes' backing.
struct SourceBytes {
    data: Expr,
    len: Expr,
    offset: Expr,
}

/// What `repeat`'s source resolved to.
enum RepeatSource {
    /// Bytes and length the string lanes already resolve.
    Backing(SourceBytes),
    /// A `String::new()`: no bytes.
    Empty,
}

/// How a `repeat` result is built, decided from the source length and count.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RepeatShape {
    /// `n == 0` or an empty source: length zero.
    Empty,
    /// `n == 1`: the source itself.
    SameAsSource,
    /// `src_len * n == total` elements, each `src[i mod src_len]`.
    Unrolled { src_len: usize, total: usize },
}

/// Decide the exact shape, or the fail-closed reason the call is not modelled.
///
/// `src_len` and `n` are `Some` only when constant.
pub(super) fn plan_slice_repeat(
    src_len: Option<usize>,
    n: Option<usize>,
) -> Result<RepeatShape, &'static str> {
    let n = n.ok_or("slice_repeat_count_symbolic")?;
    if n == 0 || src_len == Some(0) {
        return Ok(RepeatShape::Empty);
    }
    if n == 1 {
        return Ok(RepeatShape::SameAsSource);
    }
    let src_len = src_len.ok_or("slice_repeat_source_len_symbolic")?;
    // `<[T]>::repeat` panics with "capacity overflow" when the product
    // overflows; that path is not modelled here.
    let total = src_len.checked_mul(n).ok_or("slice_repeat_capacity_overflow")?;
    if total > SLICE_REPEAT_UNROLL_LIMIT {
        return Err("slice_repeat_unroll_limit");
    }
    Ok(RepeatShape::Unrolled { src_len, total })
}

/// `data[i] = src[offset + i mod src_len]` for `i < total`, over a fresh base
/// array of the destination's sort. Element sorts must agree exactly.
fn unroll_repeat_data(
    src_data: &Expr,
    src_offset: usize,
    src_len: usize,
    total: usize,
    data_sort: &Sort,
) -> Result<Expr, &'static str> {
    let src_arr = src_data.sort().array_sort().ok_or("slice_repeat_source_not_array")?;
    let dest_arr = data_sort.array_sort().ok_or("slice_repeat_dest_layout_unknown")?;
    if src_arr.element_sort != dest_arr.element_sort {
        return Err("slice_repeat_element_sort_mismatch");
    }
    let src_idx_width = src_arr.index_sort.bitvec_width().ok_or("slice_repeat_source_not_array")?;
    let dest_idx_width =
        dest_arr.index_sort.bitvec_width().ok_or("slice_repeat_dest_layout_unknown")?;
    let mut data = ExactVar::nondet(chc_fresh_name("__slice_repeat_data"), data_sort.clone());
    for i in 0..total {
        let src_i = src_offset.checked_add(i % src_len).ok_or("slice_repeat_capacity_overflow")?;
        let elem = src_data.clone().select(Expr::bitvec_const(src_i as u128, src_idx_width));
        data = data.store(Expr::bitvec_const(i as u128, dest_idx_width), elem);
    }
    Ok(data)
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle `<[T]>::repeat(&self, n)`: an exact result `Vec`, or a recorded
    /// fail-closed havoc of the destination.
    pub(in crate::codegen_ay::chc) fn codegen_call_slice_repeat(&mut self, cx: &ChcCallContext<'_>) {
        let dest_local = cx.destination.local;
        match self.build_slice_repeat_constraints(cx) {
            Ok((extra_constraints, extra_dests)) => {
                debug!(dest_local, "CHC: slice_repeat modelled exactly");
                let out = self.build_output_args(cx.modified_locals, &extra_dests);
                self.emit_goto_rule_extra(
                    cx.from_app,
                    cx.target,
                    &out,
                    cx.stmt_constraints,
                    extra_constraints,
                );
            }
            Err(reason) => {
                debug!(dest_local, reason, "CHC: slice_repeat declined; destination havocked");
                self.record_sound_fallback_reason(reason);
                let out = self.build_output_args(cx.modified_locals, &[dest_local]);
                self.emit_goto_rule(cx.from_app, cx.target, &out, cx.stmt_constraints);
            }
        }
    }

    /// Resolve `repeat`'s source: the string lanes' own backing when they have
    /// one, else follow the single defining call through the re-typing chain
    /// (`as_bytes`, `as_str`, `Deref`) and the reference it borrows, back to a
    /// `String` whose bytes resolve — or to a `String::new()`, which has none.
    fn resolve_slice_repeat_source(
        &mut self,
        arg: &Operand,
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<RepeatSource> {
        let mut operand = arg.clone();
        for _ in 0..SOURCE_CHAIN_LIMIT {
            if let Some(backing) = self.resolve_string_backing(&operand, modified_locals) {
                return Some(RepeatSource::Backing(SourceBytes {
                    data: backing.data,
                    len: backing.len,
                    offset: backing.offset,
                }));
            }
            let (Operand::Copy(place) | Operand::Move(place)) = &operand else {
                return None;
            };
            if !place.projection.is_empty() {
                return None;
            }
            let local = self
                .ref_resolution
                .ref_targets
                .get(&place.local)
                .filter(|rt| rt.projections.is_empty())
                .map_or(place.local, |rt| rt.local);
            if self.local_has_multiple_whole_definitions(local) {
                return None;
            }
            let (func, args) = self.single_defining_call(local)?;
            if matches!(self.detect_stub(&func), Some(StubKind::StringNew)) {
                return Some(RepeatSource::Empty);
            }
            let path = self.resolve_callee_path(&func)?;
            if !is_repeat_source_passthrough(&path, self.detect_stub(&func)) {
                return None;
            }
            operand = args.first()?.clone();
        }
        None
    }

    /// The `(func, args)` of the one call terminator whose whole destination is
    /// `local`, when no statement also assigns it.
    fn single_defining_call(&self, local: usize) -> Option<(Operand, Vec<Operand>)> {
        let mut found = None;
        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                if let StatementKind::Assign(place, _) = &stmt.kind
                    && place.local == local
                {
                    return None;
                }
            }
            if let TerminatorKind::Call { func, args, destination, .. } = &bb.terminator.kind
                && destination.local == local
            {
                if found.is_some() || !destination.projection.is_empty() {
                    return None;
                }
                found = Some((func.clone(), args.clone()));
            }
        }
        found
    }

    fn build_slice_repeat_constraints(
        &mut self,
        cx: &ChcCallContext<'_>,
    ) -> Result<(Vec<Expr>, Vec<usize>), &'static str> {
        let dest_local = cx.destination.local;
        let [src_arg, count_arg] = cx.args else {
            return Err("slice_repeat_arity");
        };
        let dest_vec_idx =
            self.try_state_idx_for_local(dest_local).ok_or("slice_repeat_dest_not_in_state")?;

        // Everything fallible is decided before any context state is touched.
        let n = self
            .translate_operand_with_modified(count_arg, cx.modified_locals)
            .as_ref()
            .and_then(Self::extract_const_usize_from_expr_utf8);
        let (backing, shape) = match self
            .resolve_slice_repeat_source(src_arg, cx.modified_locals)
            .ok_or("slice_repeat_source_unresolved")?
        {
            RepeatSource::Empty => (None, plan_slice_repeat(Some(0), n)?),
            RepeatSource::Backing(backing) => {
                if backing.len.sort().bitvec_width() != Some(POINTER_WIDTH) {
                    return Err("slice_repeat_source_len_sort");
                }
                let src_len = Self::extract_const_usize_from_expr_utf8(&backing.len);
                let shape = plan_slice_repeat(src_len, n)?;
                (Some(backing), shape)
            }
        };
        let src_len = backing.as_ref().and_then(|b| Self::extract_const_usize_from_expr_utf8(&b.len));
        let src_offset =
            backing.as_ref().and_then(|b| Self::extract_const_usize_from_expr_utf8(&b.offset));

        let projected = self.collections.projection_locals.get(&dest_local).copied()
            == Some(CollectionProjectionKind::Vec);
        let data_sort = if projected {
            self.state_var_mgr
                .output_state_vars
                .get(dest_vec_idx + vec_layout::IDX_DATA)
                .map(|(_, sort)| sort.clone())
        } else {
            self.state_var_mgr.output_state_vars.get(dest_vec_idx).and_then(|(_, sort)| {
                sort.datatype_sort()?
                    .constructors
                    .first()?
                    .fields
                    .iter()
                    .find(|f| f.name == vec_layout::FLD_DATA)
                    .map(|f| f.sort.clone())
            })
        }
        .ok_or("slice_repeat_dest_layout_unknown")?;
        let elem_bits = data_sort
            .array_sort()
            .and_then(|arr| arr.element_sort.bitvec_width())
            .filter(|bits| *bits > 0 && bits % 8 == 0)
            .ok_or("slice_repeat_element_sort_unsupported")?;
        let elem_bytes = u64::from(elem_bits / 8);

        let (len, data) = match shape {
            RepeatShape::Empty => (
                Expr::bitvec_const(0u64, POINTER_WIDTH),
                ExactVar::nondet(chc_fresh_name("__slice_repeat_empty_data"), data_sort.clone()),
            ),
            RepeatShape::SameAsSource
                if src_offset == Some(0)
                    && backing.as_ref().is_some_and(|b| b.data.sort() == &data_sort) =>
            {
                let b = backing.as_ref().ok_or("slice_repeat_source_unresolved")?;
                (b.len.clone(), b.data.clone())
            }
            RepeatShape::SameAsSource => {
                let b = backing.as_ref().ok_or("slice_repeat_source_unresolved")?;
                let src_len = src_len.ok_or("slice_repeat_rebased_source_len_symbolic")?;
                if src_len > SLICE_REPEAT_UNROLL_LIMIT {
                    return Err("slice_repeat_unroll_limit");
                }
                let offset = src_offset.ok_or("slice_repeat_source_offset_symbolic")?;
                (
                    Expr::bitvec_const(src_len as u64, POINTER_WIDTH),
                    unroll_repeat_data(&b.data, offset, src_len, src_len, &data_sort)?,
                )
            }
            RepeatShape::Unrolled { src_len, total } => {
                let b = backing.as_ref().ok_or("slice_repeat_source_unresolved")?;
                let offset = src_offset.ok_or("slice_repeat_source_offset_symbolic")?;
                (
                    Expr::bitvec_const(total as u64, POINTER_WIDTH),
                    unroll_repeat_data(&b.data, offset, src_len, total, &data_sort)?,
                )
            }
        };
        let size_32 = self
            .coerce_to_heap_bv32(len.clone().bvmul(Expr::bitvec_const(elem_bytes, POINTER_WIDTH)))
            .ok_or("slice_repeat_alloc_size_sort")?;
        let obj_id = self.heap_state.next_heap_alloc_id().ok_or("slice_repeat_heap_ids_exhausted")?;
        let obj_id_expr = Expr::bitvec_const(obj_id as i128, 32);
        let ptr = Expr::bitvec_const(obj_id as i128, 32).concat(Expr::bitvec_const(0, 32));

        let mut extra_constraints: Vec<Expr> = Vec::new();
        let mut extra_dests: Vec<usize> = Vec::new();
        if let Some(len_var) = self.collections.len_state.get_len_var(dest_local).cloned() {
            self.collection_len_set(
                &len_var,
                len.clone(),
                &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
            );
        }
        if let Some(cap_var) = self.collections.len_state.get_cap_var(dest_local).cloned() {
            self.collection_cap_set(
                &cap_var,
                len.clone(),
                &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
            );
        }
        if projected {
            if !self.constrain_projected_vec_fields_for_call(
                dest_local,
                ProjectedVecState { ptr, len: len.clone(), cap: len.clone(), data },
                &mut extra_constraints,
                &mut extra_dests,
            ) {
                return Err("slice_repeat_vec_field_constraint_not_emitted");
            }
        } else {
            let (out_name, out_sort) = self
                .state_var_mgr
                .output_state_vars
                .get(dest_vec_idx)
                .cloned()
                .ok_or("slice_repeat_dest_layout_unknown")?;
            let is_vec_dt = out_sort
                .datatype_sort()
                .and_then(|dt| dt.constructors.first())
                .is_some_and(|ctor| ctor.has_field(vec_layout::FLD_CAP));
            let dt_name = out_sort.datatype_name().ok_or("slice_repeat_dest_layout_unknown")?;
            if !is_vec_dt {
                return Err("slice_repeat_dest_layout_unknown");
            }
            extra_constraints.push(Self::build_vec_datatype_eq(
                dt_name,
                vec![ptr, len.clone(), len.clone(), data],
                &out_name,
                &out_sort,
            ));
            extra_dests.push(dest_local);
        }

        self.record_known_heap_alloc_size_expr(obj_id, &size_32);
        extra_constraints.push(obj_size_out().eq(obj_size_in().store(obj_id_expr.clone(), size_32)));
        extra_constraints
            .push(obj_valid_out().eq(obj_valid_in().store(obj_id_expr, Expr::bool_const(true))));
        self.mark_heap_metadata_modified();
        Ok((extra_constraints, extra_dests))
    }
}

#[cfg(test)]
mod tests {
    use super::{
        RepeatShape, SLICE_REPEAT_UNROLL_LIMIT, is_repeat_source_passthrough, plan_slice_repeat,
        unroll_repeat_data,
    };
    use crate::codegen_ay::stubs::StubKind;
    use ay_bindings::{Expr, Sort};

    #[test]
    fn source_passthrough_is_the_str_repeat_retyping_chain() {
        assert!(is_repeat_source_passthrough("core::str::<impl str>::as_bytes", None));
        assert!(is_repeat_source_passthrough("alloc::string::String::as_str", None));
        assert!(is_repeat_source_passthrough(
            "<std::string::String as std::ops::Deref>::deref",
            None
        ));
        assert!(is_repeat_source_passthrough("anything", Some(StubKind::StringAsStr)));
        // Calls that change the bytes, or are not about strings, are not followed.
        assert!(!is_repeat_source_passthrough("core::str::<impl str>::trim", None));
        assert!(!is_repeat_source_passthrough("alloc::vec::Vec::<u8>::as_slice", None));
        assert!(!is_repeat_source_passthrough("my_crate::Thing::as_bytes", None));
        assert!(!is_repeat_source_passthrough("anything", Some(StubKind::StringNew)));
    }

    #[test]
    fn plan_zero_count_or_empty_source_is_empty() {
        assert_eq!(plan_slice_repeat(Some(3), Some(0)), Ok(RepeatShape::Empty));
        assert_eq!(plan_slice_repeat(None, Some(0)), Ok(RepeatShape::Empty));
        assert_eq!(plan_slice_repeat(Some(0), Some(7)), Ok(RepeatShape::Empty));
    }

    #[test]
    fn plan_count_one_is_the_source_whatever_its_length() {
        assert_eq!(plan_slice_repeat(Some(1), Some(1)), Ok(RepeatShape::SameAsSource));
        assert_eq!(plan_slice_repeat(None, Some(1)), Ok(RepeatShape::SameAsSource));
    }

    #[test]
    fn plan_concrete_product_unrolls_within_the_limit() {
        assert_eq!(
            plan_slice_repeat(Some(2), Some(3)),
            Ok(RepeatShape::Unrolled { src_len: 2, total: 6 })
        );
        assert_eq!(
            plan_slice_repeat(Some(SLICE_REPEAT_UNROLL_LIMIT), Some(2)),
            Err("slice_repeat_unroll_limit")
        );
    }

    #[test]
    fn plan_declines_symbolic_and_overflowing_shapes() {
        assert_eq!(plan_slice_repeat(Some(1), None), Err("slice_repeat_count_symbolic"));
        assert_eq!(plan_slice_repeat(None, Some(2)), Err("slice_repeat_source_len_symbolic"));
        assert_eq!(
            plan_slice_repeat(Some(usize::MAX), Some(2)),
            Err("slice_repeat_capacity_overflow")
        );
    }

    #[test]
    fn unroll_reads_source_element_i_mod_len_from_the_offset() {
        let arr_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
        let src = Expr::var("src", arr_sort.clone());
        let data = unroll_repeat_data(&src, 4, 2, 3, &arr_sort).expect("same element sort");
        // store(store(store(base, 0, src[4]), 1, src[5]), 2, src[4])
        let outer = format!("{data:?}");
        let last_store = Expr::bitvec_const(2u128, 64);
        assert!(outer.contains(&format!("{last_store:?}")), "{outer}");
        assert_eq!(data.sort(), &arr_sort);
    }

    #[test]
    fn unroll_refuses_an_element_sort_mismatch() {
        let src = Expr::var("src", Sort::array(Sort::bitvec(64), Sort::bitvec(8)));
        let dest = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
        assert_eq!(
            unroll_repeat_data(&src, 0, 1, 2, &dest),
            Err("slice_repeat_element_sort_mismatch")
        );
    }
}
