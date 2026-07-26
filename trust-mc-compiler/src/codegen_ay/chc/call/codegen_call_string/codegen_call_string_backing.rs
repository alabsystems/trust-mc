// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! String backing-array recovery helpers.
//!
//! Split from `codegen_call_string.rs` to keep the main string stub dispatcher
//! under the 500-line file limit. Raw-parts resolution and Result type helpers
//! are in `codegen_call_string_raw_parts.rs`.

use std::collections::HashSet;

use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::Operand;

use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};

use super::super::codegen_call_misc::CallMisc;
use super::super::{ChcCtx, chc_fresh_name};

pub(in crate::codegen_ay::chc) struct StringBacking {
    pub(in crate::codegen_ay::chc) data: Expr,
    pub(in crate::codegen_ay::chc) len: Expr,
    pub(in crate::codegen_ay::chc) offset: Expr,
}

const SMALL_STRING_EQ_UNROLL_LIMIT: usize = 8;

/// Part of #4087: when both string lengths are concrete, unroll element-wise
/// equality up to this limit. This avoids quantifier blow-up for const-evaluated
/// strings (e.g. type_name literals of 10-20 bytes).
const CONST_STRING_EQ_UNROLL_LIMIT: usize = 64;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn try_codegen_precise_string_eq(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let lhs = self.resolve_string_backing(&args[0], modified_locals)?;
        let rhs = self.resolve_string_backing(&args[1], modified_locals)?;
        let lhs_const_len = Self::extract_const_usize_from_expr(&lhs.len);
        let rhs_const_len = Self::extract_const_usize_from_expr(&rhs.len);
        // Fast path: when one side has a small concrete length, unroll directly.
        if let Some(len) =
            lhs_const_len.or(rhs_const_len).filter(|&len| len <= SMALL_STRING_EQ_UNROLL_LIMIT)
        {
            return Some(Self::build_unrolled_string_eq(&lhs, &rhs, len));
        }
        // Part of #4087: when both lengths are concrete, unroll up to the higher
        // limit. This covers const-evaluated strings like type_name output where
        // both operands have known lengths but exceed the small threshold.
        if let (Some(l), Some(r)) = (lhs_const_len, rhs_const_len) {
            if l == r && l <= CONST_STRING_EQ_UNROLL_LIMIT {
                return Some(Self::build_unrolled_string_eq(&lhs, &rhs, l));
            }
        }
        let idx_name = chc_fresh_name("string_cmp_idx");
        let idx_sort = ptr_sort();
        let idx = Expr::var(&idx_name, idx_sort.clone());
        let lhs_idx = lhs.offset.bvadd(idx.clone());
        let rhs_idx = rhs.offset.bvadd(idx.clone());
        let elems_eq = lhs.data.select(lhs_idx).eq(rhs.data.select(rhs_idx));
        let in_bounds = idx.bvult(lhs.len.clone());
        let content_eq = Expr::forall(vec![(idx_name, idx_sort)], in_bounds.implies(elems_eq));
        Some(lhs.len.eq(rhs.len).and(content_eq))
    }

    pub(in crate::codegen_ay::chc) fn resolve_string_backing(
        &mut self,
        arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<StringBacking> {
        if let Operand::Copy(place) | Operand::Move(place) = arg
            && place.projection.is_empty()
        {
            if let Some(backing) = self.resolve_string_backing_local(place.local, modified_locals) {
                return Some(backing);
            }

            let resolved = self.resolve_provenance_local(place.local);
            if resolved != place.local {
                if let Some(backing) = self.resolve_string_backing_with_metadata_local(
                    resolved,
                    place.local,
                    modified_locals,
                ) {
                    return Some(backing);
                }
                if let Some(backing) = self.resolve_string_backing_local(resolved, modified_locals)
                {
                    return Some(backing);
                }
            }

            // Part of #4118: Handle &str locals created from Ref to a str field
            // of a custom DST (e.g., `_X = &(*_3).data` where `data: str`).
            if let Some(backing) =
                self.resolve_string_backing_from_str_field_ref(place.local, modified_locals)
            {
                return Some(backing);
            }
        }

        let value = self.resolve_ref_or_const_referent(arg, modified_locals)?;
        self.backing_from_expr_with_static_bytes(
            value,
            None,
            Expr::bitvec_const(0u64, POINTER_WIDTH),
        )
    }

    pub(super) fn resolve_string_backing_local(
        &mut self,
        local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<StringBacking> {
        self.resolve_string_backing_with_metadata_local(local, local, modified_locals)
    }

    pub(in crate::codegen_ay::chc) fn propagate_str_as_bytes_metadata(
        &mut self,
        dest_local: usize,
        arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> bool {
        let Some(backing) = self.resolve_string_backing(arg, modified_locals) else {
            return false;
        };

        self.ref_resolution.const_ref_values.remove(&dest_local);
        self.ref_resolution.const_ref_slice_views.remove(&dest_local);
        self.ref_resolution.subslice_len.remove(&dest_local);
        self.ref_resolution.subslice_offset.remove(&dest_local);

        self.ref_resolution.const_ref_values.insert(dest_local, backing.data);
        self.ref_resolution.subslice_len.insert(dest_local, backing.len);
        if !Self::is_zero_pointer_width_bitvec(&backing.offset) {
            self.ref_resolution.subslice_offset.insert(dest_local, backing.offset);
        }
        true
    }

    pub(super) fn resolve_string_backing_with_metadata_local(
        &mut self,
        data_local: usize,
        metadata_local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<StringBacking> {
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        let (len_hint, metadata_offset) = self.string_backing_metadata_for_local(metadata_local);
        if let Some(value) = self.ref_resolution.const_ref_values.get(&data_local).cloned() {
            let offset = metadata_offset.clone().unwrap_or_else(|| zero.clone());
            if let Some(backing) =
                self.backing_from_expr_with_static_bytes(value, len_hint.clone(), offset)
            {
                return Some(backing);
            }
        }

        if let Some(backing) =
            self.resolve_string_backing_from_call_result(data_local, modified_locals)
        {
            // Part of #4099: prefer concrete lengths over symbolic.
            let len = match (&len_hint, Self::extract_const_usize_from_expr(&backing.len)) {
                (Some(hint), None) => hint.clone(),
                (_, Some(_)) => backing.len,
                (None, None) => backing.len,
            };
            return Some(StringBacking {
                data: backing.data,
                len,
                offset: metadata_offset.unwrap_or(backing.offset),
            });
        }

        if let Some(backing) =
            self.resolve_string_backing_from_aggregate_operands(data_local, modified_locals)
        {
            // Part of #4099: prefer concrete lengths over symbolic.
            let len = match (&len_hint, Self::extract_const_usize_from_expr(&backing.len)) {
                (Some(hint), None) => hint.clone(),
                (_, Some(_)) => backing.len,
                (None, None) => backing.len,
            };
            return Some(StringBacking {
                data: backing.data,
                len,
                offset: metadata_offset.unwrap_or(backing.offset),
            });
        }

        let value = self.try_resolve_local_expr(data_local, modified_locals)?;
        let offset = metadata_offset.unwrap_or(zero);
        self.backing_from_expr_with_static_bytes(value, len_hint, offset)
    }

    pub(in crate::codegen_ay::chc) fn string_backing_metadata_for_local(
        &self,
        local: usize,
    ) -> (Option<Expr>, Option<Expr>) {
        let len_hint = self.ref_resolution.subslice_len.get(&local).cloned().or_else(|| {
            self.collections
                .len_state
                .get_len_var(local)
                .cloned()
                .map(|name| self.collection_current_len(&name))
        });
        let offset = self.ref_resolution.subslice_offset.get(&local).cloned();
        (len_hint, offset)
    }

    /// Part of #4161: public wrapper for the inline walker to build a
    /// `StringBacking` from a pre-translated expression without needing
    /// operand resolution or MIR access.
    pub(in crate::codegen_ay::chc) fn string_backing_from_expr(
        value: Expr,
        len_hint: Option<Expr>,
        offset: Expr,
    ) -> Option<StringBacking> {
        Self::backing_from_expr(value, len_hint, offset)
    }

    pub(super) fn backing_from_expr(
        expr: Expr,
        len_hint: Option<Expr>,
        offset: Expr,
    ) -> Option<StringBacking> {
        if expr.sort().array_sort().is_some() {
            return Some(StringBacking { data: expr, len: len_hint?, offset });
        }

        let dt_name = expr.sort().datatype_name()?.to_owned();
        let data_sort = Self::get_dt_field_sort(&expr, "fld_data")?;
        let len = Self::chc_array_length(&expr).or(len_hint)?;
        let data = expr.field_select(&dt_name, "fld_data", data_sort);
        Some(StringBacking { data, len, offset })
    }

    fn backing_from_expr_with_static_bytes(
        &self,
        expr: Expr,
        len_hint: Option<Expr>,
        offset: Expr,
    ) -> Option<StringBacking> {
        if let Some(backing) =
            Self::backing_from_expr(expr.clone(), len_hint.clone(), offset.clone())
        {
            return Some(backing);
        }

        if expr.sort().bitvec_width() != Some(2 * POINTER_WIDTH) {
            return None;
        }
        let (data_ptr, len) = Self::split_fat_pointer_expr(&expr).unwrap_or_else(|| {
            (
                expr.clone().extract(POINTER_WIDTH - 1, 0),
                expr.extract(2 * POINTER_WIDTH - 1, POINTER_WIDTH),
            )
        });
        let effective_len = match len_hint {
            Some(hint) if Self::extract_const_usize_from_expr(&hint).is_some() => hint,
            _ => len.clone(),
        };
        let data = self.static_byte_backing_from_inits(data_ptr, &effective_len)?;
        Some(StringBacking { data, len: effective_len, offset })
    }

    fn split_fat_pointer_expr(expr: &Expr) -> Option<(Expr, Expr)> {
        let ExprValue::BvConcat(metadata, data_ptr) = expr.value() else {
            return None;
        };
        if metadata.sort().bitvec_width() == Some(POINTER_WIDTH)
            && data_ptr.sort().bitvec_width() == Some(POINTER_WIDTH)
        {
            Some((data_ptr.clone(), metadata.clone()))
        } else {
            None
        }
    }

    fn static_byte_backing_from_inits(&self, base_addr: Expr, len: &Expr) -> Option<Expr> {
        let len = Self::extract_const_usize_from_expr(len)?;
        if len == 0 || len > 64 {
            return None;
        }

        let elem_sort = ay_bindings::Sort::bitvec(8);
        let mut result = Expr::const_array(ptr_sort(), Expr::bitvec_const(0u64, 8));
        for idx in 0..len {
            let expected_addr = ChcCtx::static_addr_with_offset(base_addr.clone(), idx as u64);
            let expected_addr_text = expected_addr.to_string();
            let byte_expr = self
                .ref_resolution
                .static_memory_inits
                .iter()
                .find(|(type_key, stored_sort, _, addr_expr)| {
                    &**type_key == "u8"
                        && stored_sort == &elem_sort
                        && addr_expr.to_string() == expected_addr_text
                })
                .map(|(_, _, value, _)| value.clone())?;
            result = result.store(Expr::bitvec_const(idx as u128, POINTER_WIDTH), byte_expr);
        }
        Some(result)
    }

    fn extract_const_usize_from_expr(expr: &Expr) -> Option<usize> {
        if let ExprValue::BitVecConst { value, .. } = expr.value() {
            u64::try_from(value).ok().map(|v| v as usize)
        } else {
            None
        }
    }

    fn build_unrolled_string_eq(lhs: &StringBacking, rhs: &StringBacking, len: usize) -> Expr {
        let content_eq = (0..len)
            .map(|idx| {
                let idx_expr = Expr::bitvec_const(idx as u128, POINTER_WIDTH);
                let lhs_idx = lhs.offset.clone().bvadd(idx_expr.clone());
                let rhs_idx = rhs.offset.clone().bvadd(idx_expr);
                lhs.data.clone().select(lhs_idx).eq(rhs.data.clone().select(rhs_idx))
            })
            .reduce(Expr::and)
            .unwrap_or_else(|| Expr::bool_const(true));
        lhs.len.clone().eq(rhs.len.clone()).and(content_eq)
    }
}
