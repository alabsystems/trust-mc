// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! NonNull helper functions for pointer identity stubs.
//!
//! Extracted from codegen_call_ptr_identity.rs to stay under the 500-line limit.
//! Contains: nonnull_new_option_wrap (Option wrapping for NonNull::new)
//! and try_emit_nonnull_new_flattened (flattened Option<NonNull<T>> emission).

use ay_bindings::Expr;
use tracing::debug;

use super::ChcCtx;
use super::chc_call_context::ChcCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_rules::CodegenRules;
use super::stubs_option_helpers::OptionHelpers;
use crate::codegen_ay::stubs::StubKind;

/// When stub is NonNull::new and dest is Option-like datatype, wrap ptr in Some(ptr).
/// NonNull::new_unchecked returns NonNull<T> directly (identity — no wrapping).
pub(super) fn nonnull_new_option_wrap(
    ctx: &mut ChcCtx<'_, '_>,
    stub: StubKind,
    ptr: Expr,
    dest_sort: &ay_bindings::Sort,
    dest_local: usize,
) -> Expr {
    if matches!(stub, StubKind::NonNullNew) && dest_sort.datatype_name().is_some() {
        if let Some(some_expr) = ctx.make_some_expr_for_option(ptr.clone(), dest_sort) {
            debug!(dest_local, "nonnull_passthrough: wrapped ptr in Some for NonNull::new");
            return some_expr;
        }
    }
    ptr
}

/// Try to emit a flattened Option<NonNull<T>> destination for NonNull::new.
///
/// NonNull::new returns Option<NonNull<T>>. When the destination local is
/// flattened (field 0 = is_some Bool, field 1 = pointer BV), set both fields
/// directly rather than trying to construct a datatype expression.
/// Returns true if the flattened path was taken, false otherwise.
pub(super) fn try_emit_nonnull_new_flattened(
    ctx: &mut ChcCtx<'_, '_>,
    cx: &ChcCallContext<'_>,
    ptr: Expr,
    src_local: Option<usize>,
    ptr_obj_id: Option<u32>,
) -> bool {
    let dest_local = cx.destination.local;

    if !ctx.flatten.flattened_tuple_locals.contains(&dest_local)
        || ctx.flattened_field_count(dest_local) < 2
    {
        return false;
    }

    let Some(vec_idx) = ctx.try_state_idx_for_local(dest_local) else {
        return false;
    };
    let mut constraints = Vec::new();

    // Field 0: is_some = true (NonNull::new assumes non-null for verification).
    if let Some((out_name, out_sort)) = ctx.state_var_mgr.output_state_vars.get(vec_idx).cloned() {
        let is_some_var = Expr::var(&*out_name, out_sort.clone());
        let is_some_val = if out_sort.is_bool() {
            Expr::bool_const(true)
        } else {
            Expr::bitvec_const(1u64, out_sort.bitvec_width().unwrap_or(1))
        };
        ctx.encode.flattened_field_env.insert((dest_local, 0), is_some_val.clone());
        constraints.push(is_some_var.eq(is_some_val));
    }

    // Field 1: payload = ptr value.
    if let Some((out_name, out_sort)) =
        ctx.state_var_mgr.output_state_vars.get(vec_idx + 1).cloned()
    {
        let payload_var = Expr::var(&*out_name, out_sort.clone());
        let coerced_ptr = if ptr.sort() == &out_sort {
            ptr.clone()
        } else if let (Some(_ptr_w), Some(dest_w)) =
            (ptr.sort().bitvec_width(), out_sort.bitvec_width())
        {
            crate::codegen_ay::types::coerce_bitvec_width_safe(
                ptr.clone(),
                dest_w,
                crate::codegen_ay::types::SignExtension::ZeroExtend,
            )
        } else {
            ptr.clone()
        };
        ctx.encode.flattened_field_env.insert((dest_local, 1), coerced_ptr.clone());
        constraints.push(payload_var.eq(coerced_ptr));
    }

    if constraints.is_empty() {
        return false;
    }

    super::codegen_call_ptr_identity::propagate_alloc_id(ctx, dest_local, src_local);
    super::codegen_call_ptr_identity::propagate_ref_target(ctx, dest_local, src_local, ptr_obj_id);

    let new_output_args = ctx.build_output_args(cx.modified_locals, &[dest_local]);
    ctx.emit_goto_rule_extra(
        cx.from_app,
        cx.target,
        &new_output_args,
        cx.stmt_constraints,
        constraints,
    );
    true
}
