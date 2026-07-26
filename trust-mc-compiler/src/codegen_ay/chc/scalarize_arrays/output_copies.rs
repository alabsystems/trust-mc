// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Rewriting helpers for scalarized output-array copies.

use std::collections::HashMap;

use ay_bindings::Expr;

use super::rewrite::RewriteMaps;
use super::{ConstIdx, ScalarInfo};

pub(super) fn build_scalar_copy_constraints(
    dst: &ScalarInfo,
    base: &str,
    infos: &[ScalarInfo],
    maps: &RewriteMaps,
) -> Vec<Expr> {
    dst.index_to_scalar
        .keys()
        .filter_map(|idx| {
            let base_scalar = scalar_expr_for_array_var(base, idx, infos, maps)?;
            let scalar_out = Expr::var(dst.scalar_output_name(idx), dst.elem_sort.clone());
            Some(scalar_out.eq(base_scalar))
        })
        .collect()
}

pub(super) fn build_scalar_store_constraints_from_base(
    dst: &ScalarInfo,
    base: &str,
    stores: &[(ConstIdx, Expr)],
    infos: &[ScalarInfo],
    maps: &RewriteMaps,
) -> Vec<Expr> {
    let stored_values: HashMap<&ConstIdx, &Expr> =
        stores.iter().map(|(idx, val)| (idx, val)).collect();

    dst.index_to_scalar
        .keys()
        .filter_map(|idx| {
            let scalar_out = Expr::var(dst.scalar_output_name(idx), dst.elem_sort.clone());
            if let Some(val) = stored_values.get(idx) {
                Some(scalar_out.eq((*val).clone()))
            } else {
                scalar_expr_for_array_var(base, idx, infos, maps)
                    .map(|base_scalar| scalar_out.eq(base_scalar))
            }
        })
        .collect()
}

pub(super) fn scalar_info_for_array_var(name: &str, maps: &RewriteMaps) -> Option<(usize, bool)> {
    if let Some(&info_idx) = maps.by_input.get(name) {
        return Some((info_idx, false));
    }
    maps.by_output.get(name).map(|&info_idx| (info_idx, true))
}

fn scalar_expr_for_array_var(
    name: &str,
    idx: &ConstIdx,
    infos: &[ScalarInfo],
    maps: &RewriteMaps,
) -> Option<Expr> {
    let (info_idx, is_output) = scalar_info_for_array_var(name, maps)?;
    let info = &infos[info_idx];
    if !info.index_to_scalar.contains_key(idx) {
        return None;
    }
    let scalar_name =
        if is_output { info.scalar_output_name(idx) } else { info.scalar_input_name(idx) };
    Some(Expr::var(scalar_name, info.elem_sort.clone()))
}
