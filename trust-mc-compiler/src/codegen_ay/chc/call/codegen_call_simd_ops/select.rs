// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::Expr;

/// Build an ITE chain: `idx == 0 ? elements[0] : idx == 1 ? ... : elements[last]`.
pub(super) fn build_ite_select(elements: &[Expr], idx: &Expr) -> Expr {
    let idx_width = idx.sort().bitvec_width().unwrap_or(POINTER_WIDTH);
    let mut result = elements.last().expect("non-empty elements").clone();
    for (i, elem) in elements.iter().enumerate().rev() {
        let i_const = Expr::bitvec_const(i as u64, idx_width);
        let cond = idx.clone().eq(i_const);
        result = Expr::ite(cond, elem.clone(), result);
    }
    result
}
