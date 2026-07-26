// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Sort normalization helpers for projection field selection.

use ay_bindings::{Expr, Sort};

use crate::codegen_ay::chc::ChcCtx;
use crate::codegen_ay::types::{
    SignExtension, coerce_datatype_structural, flatten_datatype_to_bitvec,
    unflatten_bitvec_to_datatype,
};

pub(super) fn coerce_selected_field_value(value: Expr, target_sort: &Sort) -> Option<Expr> {
    if value.sort() == target_sort {
        return Some(value);
    }

    if let Some(src_dt) = value.sort().datatype_sort()
        && let Some(tgt_dt) = target_sort.datatype_sort()
        && let Some(coerced) = coerce_datatype_structural(
            value.clone(),
            src_dt,
            tgt_dt,
            target_sort.clone(),
            SignExtension::ZeroExtend,
        )
    {
        return Some(coerced);
    }

    if let Some(reinterpreted) = ChcCtx::reinterpret_fixed_layout_expr(&value, target_sort) {
        return Some(reinterpreted);
    }

    if value.sort().is_bitvec() && target_sort.is_datatype() {
        return unflatten_bitvec_to_datatype(&value, target_sort);
    }

    if value.sort().is_datatype() && target_sort.is_bitvec() {
        return flatten_datatype_to_bitvec(&value, target_sort.bitvec_width()?);
    }

    None
}
