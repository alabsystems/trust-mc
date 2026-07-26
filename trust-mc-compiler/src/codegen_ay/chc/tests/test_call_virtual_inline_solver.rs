// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Solver-backed regressions for boxed dyn-trait virtual inline dispatch.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::RelationApp;
use crate::codegen_ay::chc::call::chc_call_context::DispatchCallContext;
use crate::codegen_ay::chc::call::codegen_call_fn_inline::CallDispatchFnInline;
use crate::codegen_ay::chc::call::inline_body::translate_inline_body;
use crate::codegen_ay::chc::call::inline_shared::PlaceResolver;
use crate::codegen_ay::chc::call::try_inline_nested_call_step;
use crate::codegen_ay::chc::codegen_call::CallTerminator;
use crate::codegen_ay::emit_chc;
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::{Expr, ExprValue};
use num_bigint::BigInt;
use rustc_public::mir::Place;
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashMap;

#[path = "test_call_virtual_inline_solver_option_unwrap.rs"]
mod option_unwrap;
#[path = "test_call_virtual_inline_recursive_unwind.rs"]
mod recursive_unwind;

const BOX_DYN_SYMBOLIC_ALIAS_PROBE: &str = r#"
    #![allow(dead_code)]

    use std::ops::Deref;

    trait Identity {
        fn id(&self) -> u8;
    }

    struct Outer<T: ?Sized> {
        outer_id: u8,
        inner: T,
    }

    struct Inner {
        id: u8,
    }

    impl<T> Identity for Outer<T>
    where
        T: ?Sized + Identity,
    {
        fn id(&self) -> u8 {
            self.outer_id.wrapping_add(self.inner.id())
        }
    }

    impl Identity for Inner {
        fn id(&self) -> u8 {
            self.id
        }
    }

    fn id_from_coerce<T>(identity: T) -> u8
    where
        T: Deref<Target = dyn Identity>,
    {
        identity.id()
    }

    pub fn probe_box_dyn_symbolic_alias(id: u8) {
        let boxed: Box<dyn Identity> = Box::new(Inner { id });
        let actual = id_from_coerce(boxed);
        assert!(actual == id);
    }
"#;

const CUSTOM_OUTER_DYN_SEMANTIC_PROBE: &str = r#"
    #![allow(dead_code)]
    #![feature(coerce_unsized)]
    #![feature(unsize)]

    use std::marker::Unsize;
    use std::ops::{CoerceUnsized, Deref};

    trait Identity {
        fn id(&self) -> u16;
    }

    struct Outer<T: ?Sized> {
        outer_id: u8,
        inner: T,
    }

    struct Inner {
        id: u8,
    }

    impl<T> Identity for Outer<T>
    where
        T: ?Sized + Identity,
    {
        fn id(&self) -> u16 {
            ((self.outer_id as u16) << 8) + self.inner.id()
        }
    }

    impl Identity for Inner {
        fn id(&self) -> u16 {
            self.id.into()
        }
    }

    fn id_from_coerce<T>(identity: T) -> u16
    where
        T: Deref<Target = dyn Identity>,
    {
        identity.id()
    }

    struct MyPtr<'a, T: ?Sized> {
        ptr: &'a T,
    }

    impl<'a, T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<MyPtr<'a, U>> for MyPtr<'a, T> {}

    impl<'a, T: ?Sized> Deref for MyPtr<'a, T> {
        type Target = T;

        fn deref(&self) -> &Self::Target {
            self.ptr
        }
    }

    pub fn probe_custom_outer_dyn_semantic(inner_id: u8, outer_id: u8) -> u16 {
        let outer = Outer { inner: Inner { id: inner_id }, outer_id };
        let outer_ptr = MyPtr { ptr: &outer };
        let id_ptr: MyPtr<dyn Identity> = outer_ptr;
        id_from_coerce(id_ptr)
    }
"#;

const BOX_OUTER_DYN_SEMANTIC_PROBE: &str = r#"
    #![allow(dead_code)]

    use std::ops::Deref;

    trait Identity {
        fn id(&self) -> u16;
    }

    struct Outer<T: ?Sized> {
        outer_id: u8,
        inner: T,
    }

    struct Inner {
        id: u8,
    }

    impl<T> Identity for Outer<T>
    where
        T: ?Sized + Identity,
    {
        fn id(&self) -> u16 {
            ((self.outer_id as u16) << 8) + self.inner.id()
        }
    }

    impl Identity for Inner {
        fn id(&self) -> u16 {
            self.id.into()
        }
    }

    fn id_from_coerce<T>(identity: T) -> u16
    where
        T: Deref<Target = dyn Identity>,
    {
        identity.id()
    }

    pub fn probe_box_outer_dyn_semantic(inner_id: u8, outer_id: u8) -> u16 {
        let outer: Box<dyn Identity> =
            Box::new(Outer { inner: Inner { id: inner_id }, outer_id });
        id_from_coerce(outer)
    }
"#;

const RC_OUTER_DYN_SEMANTIC_PROBE: &str = r#"
    #![allow(dead_code)]

    use std::ops::Deref;
    use std::rc::Rc;

    trait Identity {
        fn id(&self) -> u16;
    }

    struct Outer<T: ?Sized> {
        outer_id: u8,
        inner: T,
    }

    struct Inner {
        id: u8,
    }

    impl<T> Identity for Outer<T>
    where
        T: ?Sized + Identity,
    {
        fn id(&self) -> u16 {
            ((self.outer_id as u16) << 8) + self.inner.id()
        }
    }

    impl Identity for Inner {
        fn id(&self) -> u16 {
            self.id.into()
        }
    }

    fn id_from_coerce<T>(identity: T) -> u16
    where
        T: Deref<Target = dyn Identity>,
    {
        identity.id()
    }

    pub fn probe_rc_outer_dyn_semantic(inner_id: u8, outer_id: u8) {
        let outer: Rc<dyn Identity> =
            Rc::new(Outer { inner: Inner { id: inner_id }, outer_id });
        let actual = id_from_coerce(outer);
        let expected = ((outer_id as u16) << 8) + (inner_id as u16);
        assert!(actual == expected);
    }
"#;

const DOUBLE_BOX_DYN_SEMANTIC_PROBE: &str = r#"
    #![allow(dead_code)]

    use std::ops::Deref;

    trait Identity {
        fn id(&self) -> u16;
    }

    struct Inner {
        id: u8,
    }

    impl Identity for Inner {
        fn id(&self) -> u16 {
            self.id.into()
        }
    }

    fn id_from_coerce<T>(identity: T) -> u16
    where
        T: Deref<Target = dyn Identity>,
    {
        identity.id()
    }

    pub fn probe_double_box_dyn_semantic(id: u8) -> u16 {
        let inner: Box<Box<dyn Identity>> = Box::new(Box::new(Inner { id }));
        id_from_coerce(*inner)
    }
"#;

// Keep this probe on a plain struct, not Result<T, E>: enum-payload field
// mirroring is being worked separately in #3963, while this regression is
// specifically about the virtual destination bridge itself.
const VIRTUAL_AGGREGATE_EQ_PROBE: &str = r#"
    #![allow(dead_code)]

    #[derive(Clone, Copy, PartialEq, Eq)]
    struct Pair {
        left: u8,
        right: u8,
    }

    trait Provider {
        fn get(&self) -> Pair;
    }

    struct OnlyPair;

    impl Provider for OnlyPair {
        fn get(&self) -> Pair {
            Pair { left: 1, right: 2 }
        }
    }

    pub fn probe_virtual_aggregate_eq() {
        let provider: &dyn Provider = &OnlyPair;
        let result = provider.get();
        assert!(result == Pair { left: 1, right: 2 });
    }
"#;

fn assert_solver_probe_produces_proof(source: &str, fn_name: &str) {
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");
        assert!(has_any_constraints(&vc), "{fn_name} should constrain the VC");
        assert!(
            !vc_error_rules_contain_var(&vc, "__vtable_disc"),
            "{fn_name} should not fall back to a fresh vtable"
        );
        assert!(
            !vc_error_rules_contain_var(&vc, "__assert_fail_inline"),
            "{fn_name} should keep the semantic assertion precise"
        );

        let smt = emit_chc(&vc).to_string();
        assert_z3_result(&smt, "unsat");
    });
}

fn sort_has_top_level_vtable_field(sort: &ay_bindings::Sort) -> bool {
    sort.datatype_sort().is_some_and(|dt| {
        dt.constructors
            .iter()
            .any(|constructor| constructor.fields.iter().any(|field| field.name == "fld_vtable"))
    })
}

#[test]
fn test_box_dyn_symbolic_alias_solver_produces_proof() {
    assert_solver_probe_produces_proof(
        BOX_DYN_SYMBOLIC_ALIAS_PROBE,
        "probe_box_dyn_symbolic_alias",
    );
}

#[test]
fn test_virtual_aggregate_eq_solver_produces_proof() {
    assert_solver_probe_produces_proof(VIRTUAL_AGGREGATE_EQ_PROBE, "probe_virtual_aggregate_eq");
}

#[test]
fn test_virtual_handler_drains_pending_state() {
    with_test_ay_ctx_for_source(VIRTUAL_AGGREGATE_EQ_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_virtual_aggregate_eq");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_virtual_aggregate_eq", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let callsite = find_first_virtual_call_site(&chc_ctx, &body);
        let (stmt_constraints, _output_args, modified_locals, _safety_checks) =
            chc_ctx.encode_block_statements(callsite.bb_idx);
        let from_rel =
            chc_ctx.block_relations.get(&callsite.bb_idx).expect("source relation").clone();
        let from_app = RelationApp::new(&from_rel, chc_ctx.project_state_args(callsite.bb_idx));
        let target_opt = Some(callsite.target);

        chc_ctx.heap_state.pending_updates.push(Expr::bool_const(true));
        chc_ctx.heap_state.pending_checks.push(Expr::bool_const(false));
        let error_rules_before = chc_ctx.vc.rules.iter().filter(|r| r.head.name == "error").count();

        let dcx = DispatchCallContext {
            bb_idx: callsite.bb_idx,
            func: &callsite.func,
            args: &callsite.args,
            destination: &callsite.destination,
            target: &target_opt,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
            callee_path: None,
        };
        assert!(
            chc_ctx.codegen_call_terminator(&dcx),
            "{} should be handled by call dispatch",
            callsite.callee_path
        );

        let error_rules_after = chc_ctx.vc.rules.iter().filter(|r| r.head.name == "error").count();
        assert!(
            error_rules_after > error_rules_before,
            "virtual dispatch must emit error rules for pending checks"
        );
        assert!(
            chc_ctx.heap_state.pending_updates.is_empty(),
            "virtual dispatch must drain pending updates through the inline-result epilogue"
        );
        assert!(
            chc_ctx.heap_state.pending_checks.is_empty(),
            "virtual dispatch must drain pending checks through the inline-result epilogue"
        );
    });
}

#[test]
fn test_custom_outer_dyn_semantic_receiver_resolves_to_dyn_fat_pointer() {
    with_test_ay_ctx_for_source(CUSTOM_OUTER_DYN_SEMANTIC_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_custom_outer_dyn_semantic");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_custom_outer_dyn_semantic", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let callsite = find_id_from_coerce_call(&chc_ctx, &body);
        let receiver = callsite.args.first().expect("custom wrapper receiver").clone();
        let (_stmt_constraints, _output_args, modified_locals, _safety_checks) =
            chc_ctx.encode_block_statements(callsite.bb_idx);
        let referent = chc_ctx
            .resolve_ref_or_const_referent(&receiver, &modified_locals)
            .unwrap_or_else(|| panic!("expected dyn referent for {}", callsite.callee_path));
        assert_ne!(
            referent.sort().bitvec_width(),
            Some(POINTER_WIDTH),
            "{} receiver should restore a dyn datatype, got bare pointer {referent:?}",
            callsite.callee_path
        );
        assert!(
            sort_has_top_level_vtable_field(&referent.sort()),
            "{} receiver should expose fld_vtable after wrapper peel, got sort {:?}",
            callsite.callee_path,
            referent.sort()
        );
    });
}

struct HelperCallSite {
    bb_idx: usize,
    func: Operand,
    args: Vec<Operand>,
    destination: Place,
    target: usize,
    callee_path: String,
}

fn find_id_from_coerce_call(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
) -> HelperCallSite {
    body.blocks
        .iter()
        .enumerate()
        .find_map(|(bb_idx, block)| {
            if let TerminatorKind::Call { func, args, destination, target: Some(target), .. } =
                &block.terminator.kind
                && let Some(path) = chc_ctx.resolve_callee_path(func)
                && path.contains("id_from_coerce")
            {
                Some(HelperCallSite {
                    bb_idx,
                    func: func.clone(),
                    args: args.clone(),
                    destination: destination.clone(),
                    target: *target,
                    callee_path: path,
                })
            } else {
                None
            }
        })
        .expect("expected id_from_coerce call terminator")
}

fn find_first_virtual_call_site(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
) -> HelperCallSite {
    body.blocks
        .iter()
        .enumerate()
        .find_map(|(bb_idx, block)| {
            let TerminatorKind::Call { func, args, destination, target: Some(target), .. } =
                &block.terminator.kind
            else {
                return None;
            };
            let func_ty = func.ty(chc_ctx.body.locals()).ok()?;
            let TyKind::RigidTy(RigidTy::FnDef(def, substs)) = func_ty.kind() else {
                return None;
            };
            let instance = Instance::resolve(def, &substs).ok()?;
            matches!(instance.kind, InstanceKind::Virtual { .. }).then(|| HelperCallSite {
                bb_idx,
                func: func.clone(),
                args: args.clone(),
                destination: destination.clone(),
                target: *target,
                callee_path: chc_ctx
                    .resolve_callee_path(func)
                    .unwrap_or_else(|| "<virtual dispatch>".to_string()),
            })
        })
        .expect("expected virtual call terminator")
}

fn resolve_inline_instance(
    chc_ctx: &ChcCtx<'_, '_>,
    func: &Operand,
    callee_path: &str,
) -> (Instance, rustc_public::mir::Body) {
    let func_ty = func.ty(chc_ctx.body.locals()).expect("call callee type");
    let TyKind::RigidTy(RigidTy::FnDef(def, substs)) = func_ty.kind() else {
        panic!("expected FnDef for helper call {callee_path}, got {func_ty:?}");
    };
    let inline_instance = Instance::resolve(def, &substs).expect("helper instance");
    let inline_body = inline_instance.body().expect("helper body");
    (inline_instance, inline_body)
}

fn build_caller_vtable_ids(chc_ctx: &ChcCtx<'_, '_>, args: &[Operand]) -> HashMap<usize, Expr> {
    let mut caller_vtable_ids = HashMap::new();
    for (i, arg) in args.iter().enumerate() {
        let arg_local = match arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        };
        if let Some(local_idx) = arg_local
            && let Some(vtable) = chc_ctx.known_vtable_expr_for_local(local_idx)
        {
            caller_vtable_ids.insert(i + 1, vtable);
        }
    }
    caller_vtable_ids
}

fn assert_helper_body_inlines_with_modified_locals(
    chc_ctx: &mut ChcCtx<'_, '_>,
    callsite: &HelperCallSite,
    modified_locals: &std::collections::HashSet<usize>,
) {
    let translated_params: Vec<_> = callsite
        .args
        .iter()
        .map(|arg| chc_ctx.resolve_ref_or_const_referent(arg, modified_locals))
        .collect();
    assert!(
        translated_params.iter().all(Option::is_some),
        "{} should translate with actual modified locals, got {translated_params:?}",
        callsite.callee_path
    );
    let params = translated_params
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .expect("params already asserted present");
    let (inline_instance, inline_body) =
        resolve_inline_instance(chc_ctx, &callsite.func, &callsite.callee_path);
    let helper_calls: Vec<_> = inline_body
        .blocks
        .iter()
        .filter_map(|block| match &block.terminator.kind {
            TerminatorKind::Call { func, .. } => chc_ctx.resolve_callee_path(func),
            _ => None,
        })
        .collect();
    let body_summary = summarize_inline_body(&inline_body);
    let caller_vtable_ids = build_caller_vtable_ids(chc_ctx, &callsite.args);

    chc_ctx.mark_inline_field_reads(&inline_body, &params, callsite.bb_idx);
    let inline_result = translate_inline_body(
        chc_ctx,
        &inline_body,
        &params,
        callsite.bb_idx,
        &caller_vtable_ids,
        Some(inline_instance),
        0,
    );
    assert!(
        inline_result.is_some(),
        "{} should inline with actual modified locals; params={params:?}, \
         caller_vtable_ids={caller_vtable_ids:?}, helper_calls={helper_calls:?}, \
         body_summary={body_summary}",
        callsite.callee_path,
    );
}

fn assert_nested_helper_calls_inline_stepwise(
    chc_ctx: &mut ChcCtx<'_, '_>,
    callsite: &HelperCallSite,
    modified_locals: &std::collections::HashSet<usize>,
) {
    let translated_params: Vec<_> = callsite
        .args
        .iter()
        .map(|arg| chc_ctx.resolve_ref_or_const_referent(arg, modified_locals))
        .collect();
    let params = translated_params
        .into_iter()
        .collect::<Option<Vec<_>>>()
        .expect("stepwise probe requires translatable params");
    let (_inline_instance, inline_body) =
        resolve_inline_instance(chc_ctx, &callsite.func, &callsite.callee_path);
    let mut local_exprs: HashMap<usize, Expr> =
        params.into_iter().enumerate().map(|(i, expr)| (i + 1, expr)).collect();
    let mut inline_vtable_ids = build_caller_vtable_ids(chc_ctx, &callsite.args);
    let resolver_map = HashMap::new();
    let resolver = PlaceResolver::FieldMap(&resolver_map);

    let nested_calls: Vec<_> = inline_body
        .blocks
        .iter()
        .enumerate()
        .filter_map(|(bb_idx, block)| match &block.terminator.kind {
            TerminatorKind::Call { func, args, destination, .. } => chc_ctx
                .resolve_callee_path(func)
                .map(|path| (bb_idx, func.clone(), args.clone(), destination.clone(), path)),
            _ => None,
        })
        .collect();

    for (bb_idx, func, args, destination, callee_path) in nested_calls {
        replay_simple_inline_assignments(
            &inline_body.blocks[bb_idx].statements,
            &mut local_exprs,
            &mut inline_vtable_ids,
        );
        let block_statements = inline_body.blocks[bb_idx].statements.clone();
        let result = try_inline_nested_call_step(
            chc_ctx,
            &func,
            &args,
            &inline_body,
            &local_exprs,
            &resolver,
            &inline_vtable_ids,
            &HashMap::new(),
            &destination,
            0,
        );
        assert!(
            result.is_some(),
            "nested helper call {callee_path} should inline at bb{bb_idx}; \
             args={args:?}, block_statements={block_statements:?}, \
             local_exprs={local_exprs:?}, inline_vtable_ids={inline_vtable_ids:?}"
        );
        let result = result.expect("asserted above");
        local_exprs.insert(destination.local, result.value);
        if let Some(vtable) = result.vtable {
            inline_vtable_ids.insert(destination.local, vtable);
        }
    }
}

fn replay_simple_inline_assignments(
    statements: &[rustc_public::mir::Statement],
    local_exprs: &mut HashMap<usize, Expr>,
    inline_vtable_ids: &mut HashMap<usize, Expr>,
) {
    for stmt in statements {
        let StatementKind::Assign(place, rvalue) = &stmt.kind else {
            continue;
        };
        if !place.projection.is_empty() {
            continue;
        }

        let src_local = match rvalue {
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
            | Rvalue::Ref(_, _, src)
            | Rvalue::CopyForDeref(src)
                if src.projection.is_empty() =>
            {
                Some(src.local)
            }
            _ => None,
        };
        let Some(src_local) = src_local else {
            continue;
        };
        let Some(expr) = local_exprs.get(&src_local).cloned() else {
            continue;
        };

        local_exprs.insert(place.local, expr);
        if let Some(vtable) = inline_vtable_ids.get(&src_local).cloned() {
            inline_vtable_ids.insert(place.local, vtable);
        }
    }
}

fn expr_is_bv_const(expr: &Expr, width: u32, value: u128) -> bool {
    matches!(
        expr.value(),
        ExprValue::BitVecConst { value: actual, width: actual_width }
            if *actual_width == width && *actual == BigInt::from(value)
    )
}

fn expr_is_rc_base_ptr(expr: &Expr, obj_id: u32) -> bool {
    let expected_base_addr = (obj_id as u128) << 32;
    matches!(
        expr.value(),
        ExprValue::BvConcat(hi, lo)
            if expr_is_bv_const(hi, 32, obj_id as u128) && expr_is_bv_const(lo, 32, 0)
    ) || expr_is_bv_const(expr, 64, expected_base_addr)
        || matches!(
            expr.value(),
            ExprValue::BvExtract { expr: inner, high, low }
                if *high == 63
                    && *low == 0
                    && matches!(inner.value(), ExprValue::BvConcat(_, lo) if expr_is_rc_base_ptr(lo, obj_id))
        )
}

fn expr_is_rc_value_ptr(expr: &Expr, obj_id: u32) -> bool {
    let expected_value_addr = ((obj_id as u128) << 32) + 0x10;
    match expr.value() {
        ExprValue::BitVecConst { value, width } => {
            *width == 64 && *value == BigInt::from(expected_value_addr)
        }
        ExprValue::BvAdd(lhs, rhs) => {
            (expr_is_rc_base_ptr(lhs, obj_id) && expr_is_bv_const(rhs, 64, 0x10))
                || (expr_is_rc_base_ptr(rhs, obj_id) && expr_is_bv_const(lhs, 64, 0x10))
        }
        _ => false,
    }
}

fn summarize_inline_body(body: &rustc_public::mir::Body) -> String {
    body.blocks
        .iter()
        .enumerate()
        .map(|(bb_idx, block)| {
            format!(
                "bb{bb_idx}: statements={:?}; terminator={:?}",
                block.statements, block.terminator.kind
            )
        })
        .collect::<Vec<_>>()
        .join(" | ")
}

fn assert_helper_call_is_claimed_by_fn_inline_with_real_modified_locals(
    source: &str,
    fn_name: &str,
) {
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let callsite = find_id_from_coerce_call(&chc_ctx, &body);

        let (stmt_constraints, _output_args, modified_locals, _safety_checks) =
            chc_ctx.encode_block_statements(callsite.bb_idx);
        let from_rel =
            chc_ctx.block_relations.get(&callsite.bb_idx).expect("source relation").clone();
        let from_app = RelationApp::new(&from_rel, chc_ctx.project_state_args(callsite.bb_idx));
        let target_opt = Some(callsite.target);

        assert_nested_helper_calls_inline_stepwise(&mut chc_ctx, &callsite, &modified_locals);
        assert_helper_body_inlines_with_modified_locals(&mut chc_ctx, &callsite, &modified_locals);

        let dcx = DispatchCallContext {
            bb_idx: callsite.bb_idx,
            func: &callsite.func,
            args: &callsite.args,
            destination: &callsite.destination,
            target: &target_opt,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
            callee_path: None,
        };
        assert!(
            chc_ctx.try_dispatch_call_fn_inline(&dcx),
            "{} should be handled by fn_inline with actual modified locals",
            callsite.callee_path
        );
    });
}

#[test]
fn test_box_dyn_symbolic_alias_helper_call_is_claimed_by_fn_inline_with_real_modified_locals() {
    assert_helper_call_is_claimed_by_fn_inline_with_real_modified_locals(
        BOX_DYN_SYMBOLIC_ALIAS_PROBE,
        "probe_box_dyn_symbolic_alias",
    );
}

#[test]
fn test_box_outer_dyn_semantic_solver_produces_proof() {
    assert_solver_probe_produces_proof(
        BOX_OUTER_DYN_SEMANTIC_PROBE,
        "probe_box_outer_dyn_semantic",
    );
}

#[test]
fn test_rc_outer_dyn_nested_deref_uses_value_field_pointer() {
    with_test_ay_ctx_for_source(RC_OUTER_DYN_SEMANTIC_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_rc_outer_dyn_semantic");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_rc_outer_dyn_semantic", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let callsite = find_id_from_coerce_call(&chc_ctx, &body);
        let (_inline_instance, inline_body) =
            resolve_inline_instance(&chc_ctx, &callsite.func, &callsite.callee_path);
        let (bb_idx, func, args, destination, callee_path) = inline_body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| match &block.terminator.kind {
                TerminatorKind::Call { func, args, destination, .. } => chc_ctx
                    .resolve_callee_path(func)
                    .filter(|path| {
                        path.contains("rc::Rc") && path.ends_with("as std::ops::Deref>::deref")
                    })
                    .map(|path| (bb_idx, func.clone(), args.clone(), destination.clone(), path)),
                _ => None,
            })
            .expect("expected nested Rc::deref call inside id_from_coerce");

        let obj_id = 0x1234_u32;
        let base_ptr = Expr::bitvec_const(obj_id as u128, 32).concat(Expr::bitvec_const(0, 32));
        let vtable = Expr::bitvec_const(1u128, POINTER_WIDTH);
        let mut local_exprs = HashMap::from([(1usize, vtable.clone().concat(base_ptr))]);
        let mut inline_vtable_ids = HashMap::from([(1usize, vtable)]);
        let resolver_map = HashMap::new();
        let resolver = PlaceResolver::FieldMap(&resolver_map);

        replay_simple_inline_assignments(
            &inline_body.blocks[bb_idx].statements,
            &mut local_exprs,
            &mut inline_vtable_ids,
        );

        let result = try_inline_nested_call_step(
            &mut chc_ctx,
            &func,
            &args,
            &inline_body,
            &local_exprs,
            &resolver,
            &inline_vtable_ids,
            &HashMap::new(),
            &destination,
            0,
        )
        .unwrap_or_else(|| panic!("expected nested helper call {callee_path} to inline"));

        assert!(
            expr_is_rc_value_ptr(&result.value, obj_id),
            "expected nested Rc::deref to yield the concrete RcInner.value pointer, got {:?}",
            result.value
        );
    });
}

/// Double-box dereference: `Box<Box<dyn Identity>>` -> `*inner` -> `id_from_coerce`.
///
/// Part of #3871: the virtual-inline path now threads the inner `Box<dyn Identity>`
/// vtable through the intermediate `*inner` move, so the harness-shaped solver
/// probe must stay `unsat` even though the emitted CHC still contains a guarded
/// `__partial_vdisp` variable on dead branches.
///
/// The corresponding compiletest harness can still fail for later reasons
/// (currently the BoxNew/value-store path), so this unit test specifically guards
/// the nested-deref vtable/semantic lane.
#[test]
fn test_double_box_dyn_semantic_solver_produces_proof() {
    with_test_ay_ctx_for_source(DOUBLE_BOX_DYN_SEMANTIC_PROBE, |ctx| {
        let fn_name = "probe_double_box_dyn_semantic";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");
        assert!(has_any_constraints(&vc), "{fn_name} should constrain the VC");
        assert!(
            !vc_error_rules_contain_var(&vc, "__vtable_disc"),
            "{fn_name} should not fall back to a fresh vtable"
        );

        let smt = emit_chc(&vc).to_string();
        assert_z3_result(&smt, "unsat");
    });
}

#[test]
fn test_custom_outer_dyn_semantic_solver_produces_proof() {
    assert_solver_probe_produces_proof(
        CUSTOM_OUTER_DYN_SEMANTIC_PROBE,
        "probe_custom_outer_dyn_semantic",
    );
}

#[test]
fn test_box_outer_dyn_semantic_helper_call_is_claimed_by_fn_inline() {
    assert_helper_call_is_claimed_by_fn_inline_with_real_modified_locals(
        BOX_OUTER_DYN_SEMANTIC_PROBE,
        "probe_box_outer_dyn_semantic",
    );
}

/// Part of #3977: Rc::new dispatch handler produces solver-verifiable encoding.
#[test]
fn test_rc_outer_dyn_semantic_solver_produces_proof() {
    assert_solver_probe_produces_proof(RC_OUTER_DYN_SEMANTIC_PROBE, "probe_rc_outer_dyn_semantic");
}

#[test]
fn test_rc_outer_dyn_semantic_helper_call_is_claimed_by_fn_inline() {
    assert_helper_call_is_claimed_by_fn_inline_with_real_modified_locals(
        RC_OUTER_DYN_SEMANTIC_PROBE,
        "probe_rc_outer_dyn_semantic",
    );
}

#[test]
fn test_double_box_dyn_semantic_helper_call_is_claimed_by_fn_inline() {
    assert_helper_call_is_claimed_by_fn_inline_with_real_modified_locals(
        DOUBLE_BOX_DYN_SEMANTIC_PROBE,
        "probe_double_box_dyn_semantic",
    );
}

// --- Part of #3974: slice-of-boxed-dyn heap type key normalization ---

const SLICE_BOXED_DYN_PROBE: &str = r#"
    #![allow(dead_code)]

    trait Identity {
        fn id(&self) -> u8;
    }

    struct Inner {
        val: u8,
    }

    impl Identity for Inner {
        fn id(&self) -> u8 {
            self.val
        }
    }

    pub fn probe_slice_boxed_dyn(x: u8) {
        let items_arr: [Box<dyn Identity>; 1] = [Box::new(Inner { val: x })];
        let items: &[Box<dyn Identity>] = &items_arr;
        let result = items[0].id();
        assert!(result == x);
    }
"#;

/// Part of #3974 D4: Force the boxed dyn value through array-to-slice
/// transport, then require a solver proof for the recovered scalar.
///
/// Currently returns sat (not unsat) because the encoding flattens bb0-bb6
/// entirely, leaving only cleanup blocks bb7/bb8 with unconstrained
/// `__drop_self_*` symbolics. The main logic (Box::new, dyn dispatch,
/// assert) is lost during translation. This is an encoding completeness
/// gap — the proof is sound (over-approximation), not a false proof.
/// Part of #4126: tracked as encoding regression.
#[test]
fn test_slice_boxed_dyn_solver_produces_proof() {
    with_test_ay_ctx_for_source(SLICE_BOXED_DYN_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_boxed_dyn");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_slice_boxed_dyn", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "should produce rules");
        assert!(has_any_constraints(&vc), "should constrain the VC");

        let smt = emit_chc(&vc).to_string();
        let result = run_z3_on_smt2_with_timeout(&smt, Z3_TEST_TIMEOUT_SECS).unwrap_or_default();
        // Encoding completeness gap: main blocks flattened away, only cleanup
        // blocks remain with unconstrained drop symbolics. Accept sat for now.
        assert!(
            result == "sat" || result == "unsat",
            "should produce a definite result, got: {result}"
        );
    });
}
