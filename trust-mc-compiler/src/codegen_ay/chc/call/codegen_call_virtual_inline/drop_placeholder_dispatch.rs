// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Dyn drop dispatch and MIR analysis helpers for drop placeholders.
//!
//! Extracted from drop_placeholders.rs for 500-line file-size compliance.
//! Part of #4206.

use super::super::ChcCtx;
use super::InlineReturn;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::Expr;
use std::collections::HashMap;

pub(super) fn try_inline_dyn_drop_dispatch_call(
    ctx: &mut ChcCtx<'_, '_>,
    drop_ty: rustc_public::ty::Ty,
    self_expr: Expr,
    vtable_disc: Option<Expr>,
    _outer_body: &rustc_public::mir::Body,
    _local_exprs: &HashMap<usize, Expr>,
    _inline_vtable_ids: &HashMap<usize, Expr>,
    _dropped_local: Option<usize>,
    inline_depth: usize,
) -> Option<InlineReturn> {
    super::super::native_dyn_drop::translate_bound_dyn_drop(
        ctx,
        drop_ty,
        self_expr,
        vtable_disc,
        0,
        inline_depth,
    )
}
