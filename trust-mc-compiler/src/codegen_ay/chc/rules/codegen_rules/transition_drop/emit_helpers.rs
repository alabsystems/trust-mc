// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::sync::Arc;

use ay_bindings::Expr;
use trust_mc_core::chc::RelationApp;

use crate::codegen_ay::chc::ChcCtx;

pub(super) fn emit_inline_guard_error(
    ctx: &mut ChcCtx<'_, '_>,
    from_app: &RelationApp,
    shared_constraints: &Arc<[Expr]>,
    bb_idx: usize,
    guard: Option<&Expr>,
) {
    if let Some(guard) = guard {
        ctx.emit_error_rule_for_condition_shared(
            from_app,
            guard.clone(),
            shared_constraints,
            bb_idx,
        );
    }
}

pub(super) fn vtable_guard(vtable_disc: &Expr, vtable_id: u64) -> Expr {
    vtable_disc
        .clone()
        .eq(Expr::bitvec_const(vtable_id as u128, crate::codegen_ay::types::POINTER_WIDTH))
}
