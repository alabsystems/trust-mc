// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Precise nested-call fast paths for `Option::as_mut()` and `Option::take()`.
//!
//! Part of #4075: the async spawn scheduler hits these methods tens of
//! thousands of times while `Scheduler::run` is inlined. Short-circuiting the
//! nested calls keeps the task-slot path compact and lets vtable attachment
//! happen at the call site instead of inside the callee MIR body.

use std::collections::{BTreeMap, HashMap};

use super::super::ChcCtx;
use super::super::codegen_ctx::{chc_fresh_name, declare_pending_var};
use super::super::codegen_types::CodegenTypes;
use super::super::inline_shared::PlaceResolver;
use super::InlineReturn;
use super::pointer_wrapper::resolve_nested_ref_arg_referent;
use crate::codegen_ay::chc::stub_codegen::stubs_option_helpers::{
    OptionHelpers, option_value_sort,
};
use ay_bindings::{Expr, Sort, SortInner};
use rustc_public::mir::Operand;

pub(in crate::codegen_ay::chc) fn is_option_like_sort(sort: &Sort) -> bool {
    let SortInner::Datatype(dt) = sort.inner() else {
        return false;
    };

    let option_named =
        dt.name == "Option" || dt.name.starts_with("Option_") || dt.name.ends_with("::Option");
    if option_named {
        return true;
    }

    let has_empty = dt.constructors.iter().any(|ctor| ctor.fields.is_empty());
    let has_payload = dt.constructors.iter().any(|ctor| !ctor.fields.is_empty());
    if has_empty && has_payload {
        return true;
    }

    dt.constructors.len() == 1
        && dt.constructors[0].fields.len() == 2
        && dt.constructors[0].fields[0].sort.is_bool()
}

fn option_receiver_expr(
    ctx: &mut ChcCtx<'_, '_>,
    args: &[Operand],
    translated_args: &[Expr],
    outer_body: &rustc_public::mir::Body,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
) -> Option<Expr> {
    args.first()
        .and_then(|arg| {
            resolve_nested_ref_arg_referent(ctx, arg, outer_body, local_exprs, resolver)
        })
        .or_else(|| translated_args.first().cloned())
        .filter(|receiver| is_option_like_sort(receiver.sort()))
}

fn option_payload_sort_for_result(option_sort: &Sort) -> Option<Sort> {
    if let Some(payload_sort) = option_value_sort(option_sort) {
        return Some(payload_sort);
    }

    let SortInner::Datatype(dt) = option_sort.inner() else {
        return None;
    };
    let ctor = dt.constructors.first()?;
    (dt.constructors.len() == 1
        && ctor.fields.len() == 2
        && ctor.fields.first().is_some_and(|field| field.sort.is_bool()))
    .then(|| ctor.fields[1].sort.clone())
}

fn fresh_guarded_option_as_mut_payload(dest_sort: &Sort) -> Option<Expr> {
    let payload_sort = option_payload_sort_for_result(dest_sort)?;
    Some(declare_pending_var(chc_fresh_name("option_as_mut_ref"), payload_sort))
}

pub(in crate::codegen_ay::chc) fn shape_option_as_mut_result(
    ctx: &mut ChcCtx<'_, '_>,
    receiver: Expr,
    dest_sort: &Sort,
) -> Option<Expr> {
    if !is_option_like_sort(dest_sort) {
        return None;
    }

    // `Option<T>::as_mut` returns a mutable reference to the option payload slot,
    // not the stored `T` value. Without payload-slot address/provenance, reusing
    // the receiver payload is unsound even when both encode as BV64.
    let payload = fresh_guarded_option_as_mut_payload(dest_sort)?;
    let some_expr = ctx.make_some_expr_for_option(payload, dest_sort)?;
    let none_expr = ctx.make_none_expr_for_option(dest_sort)?;
    let is_some = ctx.option_is_some(receiver);
    ctx.record_aggregate_gap("option_as_mut_payload_unconstrained");
    Some(Expr::ite(is_some, some_expr, none_expr))
}

pub(in crate::codegen_ay::chc) fn try_inline_option_state_call(
    ctx: &mut ChcCtx<'_, '_>,
    callee_path: &str,
    args: &[Operand],
    translated_args: &[Expr],
    outer_body: &rustc_public::mir::Body,
    destination: &rustc_public::mir::Place,
    local_exprs: &HashMap<usize, Expr>,
    resolver: &PlaceResolver<'_>,
) -> Option<InlineReturn> {
    let is_option_state_call = callee_path.ends_with("::as_mut") || callee_path.ends_with("::take");
    if !callee_path.contains("Option") || !is_option_state_call {
        return None;
    }
    if args.len() != 1 && translated_args.len() != 1 {
        return None;
    }

    let receiver =
        option_receiver_expr(ctx, args, translated_args, outer_body, local_exprs, resolver)?;

    if callee_path.ends_with("::as_mut") {
        let dest_sort = destination
            .ty(outer_body.locals())
            .ok()
            .map(|ty| ctx.resolve_body_ty(ty))
            .and_then(ChcCtx::translate_ty)?;
        return Some(InlineReturn::value_only(shape_option_as_mut_result(
            ctx, receiver, &dest_sort,
        )?));
    }

    if callee_path.ends_with("::take") {
        let none_expr = ctx.make_none_expr_for_option(receiver.sort())?;
        let alias_updates = BTreeMap::from([(1usize, none_expr)]);
        return Some(InlineReturn {
            value: receiver,
            vtable: None,
            alloc_id: None,
            alias_updates,
            deferred_checks: Vec::new(),
        });
    }

    None
}

#[cfg(test)]
mod tests {
    #![allow(clippy::panic, clippy::unwrap_used)]

    use super::*;
    use crate::codegen_ay::chc::ChcConfig;
    use crate::codegen_ay::context::with_test_ay_ctx_for_source;
    use crate::codegen_ay::names::enum_sort;
    use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
    use crate::codegen_ay::types::POINTER_WIDTH;
    use ay_bindings::ExprValue;

    const OPTION_AS_MUT_SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_u64_as_mut(x: &mut Option<u64>) -> Option<&mut u64> {
            x.as_mut()
        }

        pub fn probe_option_ref_u64_as_mut<'a, 'slot>(
            x: &'slot mut Option<&'a u64>,
        ) -> Option<&'slot mut &'a u64> {
            x.as_mut()
        }

        pub fn probe_option_raw_ptr_u64_as_mut<'slot>(
            x: &'slot mut Option<*mut u64>,
        ) -> Option<&'slot mut *mut u64> {
            x.as_mut()
        }
    "#;

    fn reset_option_as_mut_aggregate_gap_metadata() {
        let _ = crate::codegen_ay::take_aggregate_encoding_gap_count();
        let _ = crate::codegen_ay::take_aggregate_encoding_gap_by_fn();
        let _ = crate::codegen_ay::chc::codegen_ctx::diagnostics::GLOBAL_COUNTERS
            .take_aggregate_gap_reasons_by_fn();
    }

    fn with_option_as_mut_ctx(
        fn_name: &'static str,
        test: impl FnOnce(&mut ChcCtx<'_, '_>, &rustc_public::mir::Body) + Send,
    ) {
        let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        reset_option_as_mut_aggregate_gap_metadata();
        with_test_ay_ctx_for_source(OPTION_AS_MUT_SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
            test(&mut chc_ctx, &body);
        });
        reset_option_as_mut_aggregate_gap_metadata();
    }

    fn option_ref_u64_sort() -> Sort {
        enum_sort(
            "LaneOptionAsMutRefU64",
            vec![("None", vec![]), ("Some", vec![("value", Sort::bitvec(POINTER_WIDTH))])],
        )
    }

    fn option_owned_u64_sort() -> Sort {
        enum_sort(
            "LaneOptionAsMutOwnedU64",
            vec![("None", vec![]), ("Some", vec![("value", Sort::bitvec(64))])],
        )
    }

    fn option_raw_ptr_sort() -> Sort {
        enum_sort(
            "LaneOptionAsMutRawPtr",
            vec![("None", vec![]), ("Some", vec![("value", Sort::bitvec(POINTER_WIDTH))])],
        )
    }

    fn option_constructor_payload(expr: &Expr) -> Option<&Expr> {
        match expr.value() {
            ExprValue::DatatypeConstructor { args, .. } if args.len() == 1 => args.first(),
            ExprValue::DatatypeConstructor { args, .. } if args.len() == 2 => args.get(1),
            _ => None,
        }
    }

    fn expr_var_name_starts_with(expr: &Expr, prefix: &str) -> bool {
        matches!(expr.value(), ExprValue::Var { name } if name.starts_with(prefix))
    }

    fn assert_guarded_as_mut_result<'a>(
        chc_ctx: &ChcCtx<'_, '_>,
        result: &'a Expr,
        receiver: &Expr,
    ) -> &'a Expr {
        match result.value() {
            ExprValue::Ite { cond, then_expr, else_expr } => {
                assert_eq!(
                    cond,
                    &chc_ctx.option_is_some(receiver.clone()),
                    "as_mut result should be guarded by the receiver discriminator"
                );
                assert!(
                    matches!(
                        else_expr.value(),
                        ExprValue::DatatypeConstructor { constructor_name, args, .. }
                            if crate::codegen_ay::names::is_none_constructor(constructor_name)
                                && args.is_empty()
                    ),
                    "as_mut None branch should construct destination None"
                );
                option_constructor_payload(then_expr)
                    .expect("as_mut Some branch should construct a payload")
            }
            other => panic!("expected guarded Option::as_mut ITE, got {other:?}"),
        }
    }

    fn assert_as_mut_uses_fresh_payload_for_receiver(
        chc_ctx: &mut ChcCtx<'_, '_>,
        option_sort: &Sort,
        receiver_payload: Expr,
    ) {
        let receiver = chc_ctx
            .make_some_expr_for_option(receiver_payload.clone(), option_sort)
            .expect("receiver Some should be constructible");
        let before_gap = chc_ctx.diagnostics.aggregate_encoding_gap.get();

        let result = shape_option_as_mut_result(chc_ctx, receiver.clone(), option_sort)
            .expect("Option::as_mut should shape an Option-like destination");

        assert_eq!(
            chc_ctx.diagnostics.aggregate_encoding_gap.get(),
            before_gap + 1,
            "as_mut must force the guarded fresh-reference fallback"
        );
        let actual_payload = assert_guarded_as_mut_result(chc_ctx, &result, &receiver);
        assert_eq!(actual_payload.sort(), receiver_payload.sort());
        assert!(
            expr_var_name_starts_with(actual_payload, "option_as_mut_ref"),
            "fresh fallback payload should be explicit, got {actual_payload}"
        );
        assert_ne!(
            actual_payload, &receiver_payload,
            "as_mut must not reuse the stored payload as the returned payload-slot reference"
        );
    }

    fn find_option_as_mut_destination(
        chc_ctx: &ChcCtx<'_, '_>,
        body: &rustc_public::mir::Body,
    ) -> (String, rustc_public::mir::Place) {
        let mut call_paths = Vec::new();
        for block in &body.blocks {
            let rustc_public::mir::TerminatorKind::Call { func, destination, .. } =
                &block.terminator.kind
            else {
                continue;
            };
            // `func` belongs to `body`, not `chc_ctx.body` (#chc-inline-operand-locals).
            let Some(callee_path) = chc_ctx
                .resolve_callee_path_with_locals(func, body.locals())
                .or_else(|| chc_ctx.resolve_fn_def_name_with_locals(func, body.locals()))
            else {
                continue;
            };
            call_paths.push(callee_path.clone());
            if callee_path.contains("Option") && callee_path.ends_with("::as_mut") {
                return (callee_path, destination.clone());
            }
        }
        panic!("expected Option::as_mut call in MIR, saw {call_paths:?}");
    }

    fn assert_real_mir_as_mut_uses_fresh_payload(
        fn_name: &'static str,
        receiver_sort: Sort,
        receiver_payload: Expr,
    ) {
        with_option_as_mut_ctx(fn_name, |chc_ctx, body| {
            let (callee_path, destination) = find_option_as_mut_destination(chc_ctx, body);
            let local_exprs = HashMap::new();
            let resolver_map = HashMap::new();
            let resolver = PlaceResolver::FieldMap(&resolver_map);
            let before_gap = chc_ctx.diagnostics.aggregate_encoding_gap.get();
            let receiver = chc_ctx
                .make_some_expr_for_option(receiver_payload.clone(), &receiver_sort)
                .expect("receiver Some should be constructible");

            let result = try_inline_option_state_call(
                chc_ctx,
                &callee_path,
                &[],
                std::slice::from_ref(&receiver),
                body,
                &destination,
                &local_exprs,
                &resolver,
            )
            .expect("real MIR Option::as_mut call should inline through the option-state path");

            assert_eq!(
                chc_ctx.diagnostics.aggregate_encoding_gap.get(),
                before_gap + 1,
                "real MIR as_mut must use the guarded fresh-reference fallback"
            );
            let actual_payload = assert_guarded_as_mut_result(chc_ctx, &result.value, &receiver);
            assert!(
                expr_var_name_starts_with(actual_payload, "option_as_mut_ref"),
                "real MIR as_mut payload should be fresh, got {actual_payload}"
            );
            assert_ne!(
                actual_payload, &receiver_payload,
                "real MIR as_mut must not reuse the stored payload as the payload-slot reference"
            );
        });
    }

    #[test]
    fn test_option_as_mut_u64_uses_fresh_guarded_payload_for_pointer_sized_scalar() {
        with_option_as_mut_ctx("probe_option_u64_as_mut", |chc_ctx, _body| {
            let dest_sort = option_ref_u64_sort();
            let receiver_sort = option_owned_u64_sort();
            let receiver_payload = Expr::var("owned_u64_payload", Sort::bitvec(64));
            let receiver = chc_ctx
                .make_some_expr_for_option(receiver_payload.clone(), &receiver_sort)
                .expect("receiver Some should be constructible");
            let before_gap = chc_ctx.diagnostics.aggregate_encoding_gap.get();

            let result = shape_option_as_mut_result(chc_ctx, receiver.clone(), &dest_sort)
                .expect("Option::as_mut should shape an Option-like destination");

            assert_eq!(
                chc_ctx.diagnostics.aggregate_encoding_gap.get(),
                before_gap + 1,
                "owned scalar payload must force the guarded fresh-reference fallback"
            );
            let actual_payload = assert_guarded_as_mut_result(chc_ctx, &result, &receiver);
            assert_eq!(actual_payload.sort(), &Sort::bitvec(POINTER_WIDTH));
            assert!(
                expr_var_name_starts_with(actual_payload, "option_as_mut_ref"),
                "fresh fallback payload should be explicit, got {actual_payload}"
            );
            assert_ne!(
                actual_payload, &receiver_payload,
                "owned u64 payload must not be reused as an &mut u64 payload"
            );
        });
    }

    #[test]
    fn test_option_as_mut_ref_payload_uses_fresh_guarded_payload() {
        with_option_as_mut_ctx("probe_option_u64_as_mut", |chc_ctx, _body| {
            assert_as_mut_uses_fresh_payload_for_receiver(
                chc_ctx,
                &option_ref_u64_sort(),
                Expr::var("stored_ref_payload", Sort::bitvec(POINTER_WIDTH)),
            );
        });
    }

    #[test]
    fn test_option_as_mut_raw_ptr_payload_uses_fresh_guarded_payload() {
        with_option_as_mut_ctx("probe_option_u64_as_mut", |chc_ctx, _body| {
            assert_as_mut_uses_fresh_payload_for_receiver(
                chc_ctx,
                &option_raw_ptr_sort(),
                Expr::var("stored_raw_ptr_payload", Sort::bitvec(POINTER_WIDTH)),
            );
        });
    }

    #[test]
    fn test_option_as_mut_real_mir_ref_payload_uses_fresh_guarded_payload() {
        assert_real_mir_as_mut_uses_fresh_payload(
            "probe_option_ref_u64_as_mut",
            option_ref_u64_sort(),
            Expr::var("real_mir_stored_ref_payload", Sort::bitvec(POINTER_WIDTH)),
        );
    }

    #[test]
    fn test_option_as_mut_real_mir_raw_ptr_payload_uses_fresh_guarded_payload() {
        assert_real_mir_as_mut_uses_fresh_payload(
            "probe_option_raw_ptr_u64_as_mut",
            option_raw_ptr_sort(),
            Expr::var("real_mir_stored_raw_ptr_payload", Sort::bitvec(POINTER_WIDTH)),
        );
    }
}
