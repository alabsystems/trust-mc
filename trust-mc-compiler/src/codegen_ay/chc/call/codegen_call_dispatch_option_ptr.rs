// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Option/Result + pointer-family call dispatch helpers for CHC call terminators.
//!
//! Dispatches Option/Result predicates, unwrap variants, combinators,
//! pointer memory ops, and pointer/NonZero utility stubs to their handlers.
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use std::collections::{BTreeMap, HashMap};
use tracing::debug;

use crate::codegen_ay::chc::stub_codegen::stubs_option_helpers::OptionHelpers;
use crate::codegen_ay::stubs::StubKind;

use super::ChcCtx;
use super::chc_call_context::{ChcCallContext, DispatchCallContext};
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_call_misc::CallMisc;
use super::codegen_call_option_result::CallOptionResult;
use super::codegen_call_ptr::CallPtr;
use super::codegen_call_raw_ptr_as_ref::try_dispatch_raw_ptr_as_ref;
use super::codegen_call_vec::CallVec;
use super::codegen_call_virtual_inline::nested_option_state::shape_option_as_mut_result;
use super::codegen_call_virtual_inline::{
    InlineReturn, attach_spawn_task_slot_vtable, is_option_like_sort,
};
use super::codegen_rules::CodegenRules;
use super::codegen_types::CodegenTypes;
use super::inline_alias_writeback::pre_resolve_arg_target_locals;

/// Extension trait for Option/Result + pointer dispatch in call-terminator codegen.
pub(in crate::codegen_ay::chc) trait CallDispatchOptionPtr {
    fn try_dispatch_call_option_pointer(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchOptionPtr for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_option_pointer(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let func = dcx.func;

        if try_dispatch_option_state_fast_path(self, dcx) {
            return true;
        }

        if try_dispatch_raw_ptr_as_ref(self, dcx) {
            return true;
        }

        // Single callee-path resolve + registry lookup (Part of #2408 T3).
        let stub = match self.detect_stub(func) {
            Some(s) => s,
            None => return false,
        };

        // Part of #4086: OptionIsSomeAnd with Ordering predicates (is_gt/is_lt/is_ge/is_le).
        // fn_inline bails out on Ordering::is_gt closures, producing unconstrained
        // __nested_call_overapprox_0. Intercept here with direct Ordering BV encoding.
        if stub == StubKind::OptionIsSomeAnd {
            if let Some(target) = dcx.target {
                if try_codegen_is_some_and_ordering(self, dcx, *target) {
                    return true;
                }
            }
            return false;
        }

        // Part of #3984: Array-inner OptionMap pre-route. Intercept before the
        // generic combinator to produce precise Option<T> = Some(data[idx]) / None.
        if stub == StubKind::OptionMap && self.find_parent_array_into_iter_local().is_some() {
            if let Some(target) = dcx.target {
                let cx = ChcCallContext {
                    stub,
                    args: dcx.args,
                    destination: dcx.destination,
                    target: *target,
                    from_app: dcx.from_app,
                    stmt_constraints: dcx.stmt_constraints,
                    modified_locals: dcx.modified_locals,
                };
                if self.try_codegen_array_inner_option_map(&cx) {
                    return true;
                }
            }
        }

        dispatch_stub_via_route_table(self, dcx, stub)
    }
}

/// Handle structural `Option::{as_mut,take}` before stub lookup or MIR inlining.
///
/// The async spawn scheduler calls these on task slots in tight inline loops.
/// Falling through to the MIR body repeatedly produces a large amount of
/// `Option::as_mut` stub-lookup noise and can stall the exact spawn lane.
fn try_dispatch_option_state_fast_path(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) -> bool {
    let Some(target) = *dcx.target else {
        return false;
    };

    let fallback_callee_path;
    let callee_path = if let Some(path) = dcx.callee_path.as_deref() {
        path
    } else {
        fallback_callee_path =
            ctx.resolve_callee_path(dcx.func).or_else(|| ctx.resolve_fn_def_name(dcx.func));
        let Some(path) = fallback_callee_path.as_deref() else {
            return false;
        };
        path
    };

    let is_as_mut = callee_path.ends_with("::as_mut");
    let is_take = callee_path.ends_with("::take");
    if !callee_path.contains("Option") || (!is_as_mut && !is_take) || dcx.args.len() != 1 {
        return false;
    }

    let Some(receiver) = ctx
        .resolve_ref_or_const_referent(&dcx.args[0], dcx.modified_locals)
        .or_else(|| ctx.translate_operand_with_modified(&dcx.args[0], dcx.modified_locals))
    else {
        return false;
    };
    if !is_option_like_sort(receiver.sort()) {
        return false;
    }

    let Some(dest_sort) = dcx
        .destination
        .ty(ctx.body.locals())
        .ok()
        .map(|ty| ctx.resolve_body_ty(ty))
        .and_then(ChcCtx::translate_ty)
    else {
        return false;
    };

    let mut result = if is_take {
        if receiver.sort() != &dest_sort {
            return false;
        }
        let Some(none_expr) = ctx.make_none_expr_for_option(receiver.sort()) else {
            return false;
        };
        InlineReturn {
            value: receiver,
            vtable: None,
            alloc_id: None,
            alias_updates: BTreeMap::from([(1, none_expr)]),
            deferred_checks: Vec::new(),
        }
    } else {
        let Some(value) = shape_option_as_mut_result(ctx, receiver, &dest_sort) else {
            return false;
        };
        InlineReturn::value_only(value)
    };

    let body = ctx.body;
    attach_spawn_task_slot_vtable(ctx, Some(callee_path), dcx.destination, body, &mut result);
    let pre_resolved_args = pre_resolve_arg_target_locals(ctx, dcx);
    let caller_vtable_ids = HashMap::new();
    ctx.emit_translated_inline_call_result(
        dcx,
        target,
        result.value,
        result.vtable,
        result.alias_updates,
        result.deferred_checks,
        &pre_resolved_args,
        &caller_vtable_ids,
        Some(callee_path),
        "option_state_fast_path",
        "option_state_alias_update",
    )
}

/// Route a resolved stub through the ordered predicate→handler table.
fn dispatch_stub_via_route_table<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    dcx: &DispatchCallContext<'_>,
    stub: StubKind,
) -> bool {
    type Predicate = fn(StubKind) -> bool;
    type Handler<'ctx, 'mir> = fn(&mut ChcCtx<'ctx, 'mir>, &ChcCallContext<'_>);

    let routes: [(Predicate, Handler<'tcx, 'body>); 9] = [
        (StubKind::is_option_predicate, ChcCtx::codegen_call_option_predicate),
        (StubKind::is_result_predicate, ChcCtx::codegen_call_result_predicate),
        (StubKind::is_unwrap_or, ChcCtx::codegen_call_unwrap_or),
        (StubKind::is_unwrap_expect, ChcCtx::codegen_call_unwrap_expect),
        (StubKind::is_unwrap_or_else, ChcCtx::codegen_call_unwrap_or_else),
        (StubKind::is_option_copied, ChcCtx::codegen_call_option_copied),
        (StubKind::is_combinator, ChcCtx::codegen_call_combinator),
        (StubKind::is_ptr_memory, ChcCtx::codegen_call_ptr_memory),
        (StubKind::is_pointer_utility, ChcCtx::codegen_call_pointer_utility),
    ];
    let handler =
        routes.into_iter().find_map(|(predicate, handler)| predicate(stub).then_some(handler));

    if let Some(handler) = handler {
        if let Some(target) = dcx.target {
            let cx = ChcCallContext {
                stub,
                args: dcx.args,
                destination: dcx.destination,
                target: *target,
                from_app: dcx.from_app,
                stmt_constraints: dcx.stmt_constraints,
                modified_locals: dcx.modified_locals,
            };
            // SOUNDNESS: unwrap/expect survive fn_inline as Call terminators, so
            // the library body's panic edge never reaches codegen. Emit the
            // None/Err-panic obligation HERE (BMC twin: codegen_option_unwrap_impl).
            if stub.is_unwrap_expect() {
                ctx.emit_unwrap_expect_panic_obligation(&cx, dcx.bb_idx);
            }
            handler(ctx, &cx);
        } else {
            ctx.record_diverging_call_drop(
                dcx.func,
                Some(dcx.bb_idx),
                "option_ptr::route_table",
                Some(stub),
            );
        }
        return true;
    }

    false
}

/// Part of #4086: Handle `Option<Ordering>::is_some_and(Ordering::is_gt)` and similar.
///
/// The default `PartialOrd::gt()` desugars to `self.partial_cmp(other).is_some_and(Ordering::is_gt)`.
/// The inline walker bails out on the `Ordering::is_gt` closure, producing unconstrained
/// `__nested_call_overapprox_0`. This handler intercepts at the stub level and directly
/// encodes the Ordering predicate against the BV32 payload (Less=-1, Equal=0, Greater=1).
fn try_codegen_is_some_and_ordering(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: rustc_public::mir::BasicBlockIdx,
) -> bool {
    if dcx.args.len() < 2 {
        return false;
    }

    // Extract the Ordering method from is_some_and's generic closure/fn type arg.
    let func_ty = dcx.func.ty(ctx.body.locals()).ok();
    let ordering_method = func_ty.and_then(|ty| {
        let fn_args = match ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(_, substs)) => substs,
            _ => return None,
        };
        fn_args.0.iter().find_map(|arg| {
            if let GenericArgKind::Type(ty) = arg
                && let TyKind::RigidTy(RigidTy::FnDef(def, _)) = ty.kind()
            {
                let name = def.name();
                if name.contains("Ordering") {
                    return match name.rsplit("::").next()? {
                        "is_gt" => Some("gt"),
                        "is_ge" => Some("ge"),
                        "is_lt" => Some("lt"),
                        "is_le" => Some("le"),
                        "is_eq" => Some("eq"),
                        "is_ne" => Some("ne"),
                        _ => None,
                    };
                }
            }
            None
        })
    });
    let Some(method) = ordering_method else {
        return false;
    };

    debug!(
        method,
        bb_idx = dcx.bb_idx,
        "CHC: is_some_and(Ordering::{method}) intercepted (Part of #4086)"
    );

    // Resolve the Option<Ordering> receiver.
    let option_expr = ctx.resolve_ref_or_const_referent(&dcx.args[0], dcx.modified_locals);
    let Some(option_val) = option_expr else {
        return false;
    };

    // Extract is_some and ordering payload from the Option Datatype.
    let option_sort = option_val.sort().clone();
    let (is_some, payload) = if let Some(dt) = option_sort.datatype_sort() {
        let some_cons = dt.constructors.iter().find(|c| c.fields.len() == 1);
        let Some(some_cons) = some_cons else {
            return false;
        };
        let is_some = option_val.clone().is_constructor(&dt.name, &some_cons.name);
        let payload = option_val.field_select(
            &dt.name,
            &some_cons.fields[0].name,
            some_cons.fields[0].sort.clone(),
        );
        (is_some, payload)
    } else {
        return false;
    };

    // Compute predicate: Less=-1 (0xFFFFFFFF), Equal=0, Greater=1 in BV32.
    let pw = payload.sort().bitvec_width().unwrap_or(32);
    let less = Expr::bitvec_const(-1i128 as u128, pw);
    let equal = Expr::bitvec_const(0u128, pw);
    let greater = Expr::bitvec_const(1u128, pw);

    let result = match method {
        "gt" => is_some.and(payload.eq(greater)),
        "ge" => is_some.and(payload.clone().eq(greater).or(payload.eq(equal.clone()))),
        "lt" => is_some.and(payload.eq(less)),
        "le" => is_some.and(payload.clone().eq(less).or(payload.eq(equal.clone()))),
        "eq" => is_some.and(payload.eq(equal)),
        "ne" => is_some.and(payload.ne(equal)),
        _ => return false,
    };

    // Emit goto rule constraining destination to the computed boolean.
    let dest_local = dcx.destination.local;
    if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
        let eq_constraint = ctx.make_coerced_eq_constraint(
            &dest_var,
            result,
            dest_var.sort(),
            dest_local,
            "is_some_and_ordering",
        );
        let new_output_args = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule_extra(
            dcx.from_app,
            target,
            &new_output_args,
            dcx.stmt_constraints,
            eq_constraint,
        );
    } else {
        emit_sound_fallback_goto(
            ctx,
            dcx.from_app,
            target,
            dcx.modified_locals,
            &[dest_local],
            dcx.stmt_constraints,
        );
    }

    true
}
