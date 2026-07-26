// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Iterator flatten/collect operations for AY codegen.
//!
//! Extracted from `iter_helpers.rs`. Handles:
//! - `codegen_iter_flatten_from_vec_iter`: Flatten nested Vec iterator
//! - `codegen_iter_collect_vec`: Collect iterator into Vec
//! - `make_vec_from_parts`: Construct Vec from parts
//! - `make_vec_into_iter`: Wrap Vec in VecIntoIter
//! - `make_flatten_iter`: Wrap iterator in Flatten
//!
//! Part of #2246: Large file decomposition.

use crate::codegen_ay::names::{self, struct_sort};
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};
use ay_bindings::{Expr, Sort};
use std::sync::atomic::Ordering;
use tracing::error;

use super::super::StatementCodegen;
use super::iter::BMC_ITERATOR_UNSOUND_SKIP_COUNT;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    #[must_use]
    pub(in crate::codegen_ay::statement) fn codegen_iter_collect_vec(
        &mut self,
        iter: &Expr,
    ) -> Option<Expr> {
        let sort_ref = iter.sort().clone();
        let iter_expr = if let Some((dt_name, _ctor, iter_sort)) =
            Self::datatype_field_info(&sort_ref, "fld_iter")
        {
            iter.clone().field_select(dt_name, "fld_iter", iter_sort)
        } else {
            iter.clone()
        };

        // Part of #1920: Explicit failure for non-datatype sort
        if !iter_expr.sort().is_datatype() {
            let count = BMC_ITERATOR_UNSOUND_SKIP_COUNT.fetch_add(1, Ordering::Relaxed) + 1;
            error!(
                "UNSOUND: codegen_iter_collect_vec has non-datatype sort {:?} (hit #{}) - forcing verification failure",
                iter_expr.sort(),
                count
            );
            self.record_violation_guarded(Expr::bool_const(true), "iterator_sort_mismatch_unsound");
            return None;
        }

        // Clone Sort (O(1) Arc) so dt borrows from sort_ref, not iter_expr.
        let sort_ref = iter_expr.sort().clone();
        let dt_name: &str = sort_ref.datatype_sort().map_or("VecIntoIter", |dt| &*dt.name);

        let vec_sort = self.infer_iter_vec_sort(&iter_expr);
        let vec = iter_expr.clone().field_select(dt_name, "fld_vec", vec_sort);
        // Last use of `iter_expr` — move instead of clone
        let pos = iter_expr.field_select(dt_name, "fld_pos", ptr_sort());
        let pos_zero = pos.eq(Expr::bitvec_const(0u64, POINTER_WIDTH));
        let sym_name = self.ctx.fresh_name("iter_collect_vec");
        let sym_vec = self.ctx.declare_var(&sym_name, vec.sort().clone());
        Some(Expr::ite(pos_zero, vec, sym_vec))
    }

    #[must_use]
    pub(in crate::codegen_ay::statement) fn codegen_iter_flatten_from_vec_iter(
        &mut self,
        iter: &Expr,
    ) -> Option<Expr> {
        // Part of #1920: Explicit failure for non-datatype sort
        if !iter.sort().is_datatype() {
            let count = BMC_ITERATOR_UNSOUND_SKIP_COUNT.fetch_add(1, Ordering::Relaxed) + 1;
            error!(
                "UNSOUND: codegen_iter_flatten_from_vec_iter has non-datatype sort {:?} (hit #{}) - forcing verification failure",
                iter.sort(),
                count
            );
            self.record_violation_guarded(Expr::bool_const(true), "iterator_sort_mismatch_unsound");
            return None;
        }
        // Clone Sort (O(1) Arc) so dt borrows from sort_ref, not iter.
        let sort_ref = iter.sort().clone();
        let iter_dt_name: &str = sort_ref.datatype_sort().map_or("VecIntoIter", |dt| &*dt.name);

        let outer_vec =
            iter.clone().field_select(iter_dt_name, "fld_vec", self.infer_iter_vec_sort(iter));
        let outer_len = self.vec_field_select_declared(&outer_vec, "fld_len", ptr_sort());
        let len_is_two = outer_len.eq(Expr::bitvec_const(2u64, POINTER_WIDTH));

        let outer_data = self.extract_vec_data(&outer_vec);
        let idx0 = Expr::bitvec_const(0u64, POINTER_WIDTH);
        let idx1 = Expr::bitvec_const(1u64, POINTER_WIDTH);
        let inner0 = outer_data.clone().select(idx0);
        let inner1 = outer_data.select(idx1);

        let len0 = self.vec_field_select_declared(&inner0, "fld_len", ptr_sort());
        let len1 = self.vec_field_select_declared(&inner1, "fld_len", ptr_sort());
        let len_out = len0.clone().bvadd(len1);

        let inner0_data = self.extract_vec_data(&inner0);
        let inner1_data = self.extract_vec_data(&inner1);
        let elem_sort =
            inner0_data.sort().array_sort().map_or_else(ptr_sort, |arr| arr.element_sort.clone());

        let data_sort = Sort::array(ptr_sort(), elem_sort.clone());
        let data_name = self.ctx.fresh_name("flatten_data");
        let data_out = self.ctx.declare_var(&data_name, data_sort);
        let default_name = self.ctx.fresh_name("flatten_default");
        let default_elem = self.ctx.declare_var(&default_name, elem_sort.clone());

        let idx_name = self.ctx.fresh_name("flatten_idx");
        let idx = Expr::var(idx_name.clone(), ptr_sort());
        let in_first = idx.clone().bvult(len0.clone());
        let in_range = idx.clone().bvult(len_out.clone());
        // Last use of `len0` — move instead of clone
        let idx_second = idx.clone().bvsub(len0);
        let elem_first = inner0_data.select(idx.clone());
        let elem_second = inner1_data.select(idx_second);
        let elem = Expr::ite(in_first, elem_first, elem_second);
        let elem = Expr::ite(in_range, elem, default_elem);
        let body = data_out.clone().select(idx).eq(elem);
        let forall = Expr::forall(vec![(idx_name, ptr_sort())], body);
        self.ctx.assert(forall);

        let vec_out = self.make_vec_from_parts(elem_sort, len_out, data_out);
        let sym_name = self.ctx.fresh_name("flatten_vec");
        let sym_vec = self.ctx.declare_var(&sym_name, vec_out.sort().clone());
        let result_vec = Expr::ite(len_is_two, vec_out, sym_vec);

        let iter_out = self.make_vec_into_iter(result_vec);
        Some(self.make_flatten_iter(iter_out))
    }

    #[must_use]
    pub(in crate::codegen_ay::statement) fn make_vec_from_parts(
        &mut self,
        elem_sort: Sort,
        len: Expr,
        data: Expr,
    ) -> Expr {
        let vec_sort_name = names::vec_sort_name(&names::sort_short_name(&elem_sort));
        let vec_sort = struct_sort(vec_sort_name.clone(), names::vec_fields(data.sort().clone()));
        let ptr_name = self.ctx.fresh_name("flatten_ptr");
        let ptr = self.ctx.declare_var(&ptr_name, ptr_sort());
        let ctor_name = names::resolve_ctor_name(&vec_sort, &vec_sort_name);
        Expr::datatype_constructor(
            vec_sort_name,
            ctor_name,
            vec![ptr, len.clone(), len, data],
            vec_sort,
        )
    }

    #[must_use]
    pub(in crate::codegen_ay::statement) fn make_vec_into_iter(&mut self, vec: Expr) -> Expr {
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        let vec_sort = vec.sort().clone();
        let iter_sort_name = names::vec_into_iter_sort_name(&names::sort_short_name(&vec_sort));
        let iter_sort =
            struct_sort(iter_sort_name.clone(), [("fld_vec", vec_sort), ("fld_pos", ptr_sort())]);
        let ctor_name = names::resolve_ctor_name(&iter_sort, &iter_sort_name);
        Expr::datatype_constructor(iter_sort_name, ctor_name, vec![vec, zero], iter_sort)
    }

    #[must_use]
    pub(in crate::codegen_ay::statement) fn make_flatten_iter(&mut self, inner_iter: Expr) -> Expr {
        let iter_sort = inner_iter.sort().clone();
        let flatten_sort_name = {
            let short = names::sort_short_name(&iter_sort);
            let mut s = String::with_capacity(8 + short.len());
            s.push_str("Flatten_");
            s.push_str(&short);
            s
        };
        let flatten_sort = struct_sort(flatten_sort_name.clone(), [("fld_iter", iter_sort)]);
        let ctor_name = names::resolve_ctor_name(&flatten_sort, &flatten_sort_name);
        Expr::datatype_constructor(flatten_sort_name, ctor_name, vec![inner_iter], flatten_sort)
    }
}
