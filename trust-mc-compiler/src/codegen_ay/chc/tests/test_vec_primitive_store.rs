// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Native encoding/refusal and work-bound controls. Semantic Safe/Bug credit
//! belongs to the registered CLI cases; this module runs no solver.
#![cfg(trust_toolchain)]

use super::super::codegen_ctx::RefTarget;
use super::common::*;
use super::test_trust_box_new::{mem_config, with_native_box_ctx};
use crate::callee_body::CalleeBody;
use crate::kani_middle::std_abstraction::StdAbstraction;
use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{BasicBlock, Body, TerminatorKind, UnwindAction};
use std::collections::BTreeMap;
use trust_mc_core::violation::PropertyKind;

fn take_reasons(name: &str) -> BTreeMap<String, usize> {
    crate::codegen_ay::take_translation_drop_site_reasons_by_fn().remove(name).unwrap_or_default()
}
fn local_named(body: &Body, name: &str) -> usize {
    body.var_debug_info
        .iter()
        .find_map(|info| match &info.value {
            rustc_public::mir::VarDebugInfoContents::Place(place)
                if info.name == name && place.projection.is_empty() =>
            {
                Some(place.local)
            }
            _ => None,
        })
        .unwrap_or_else(|| panic!("retain native fixture variable {name}"))
}
fn native_body(
    tcx: TyCtxt<'_>,
    name: &str,
    depth: usize,
    abstraction: &StdAbstraction,
    opaque: &[Instance],
) -> Body {
    let instance = find_instance_by_suffix(tcx, name);
    let (_, body) = FunctionInlinePass::new(InlineConfig {
        max_depth: depth,
        chc_native_box_drop: true,
        ..InlineConfig::default()
    })
    .transform_with_body_provider(tcx, instance.callee_body().unwrap(), instance, |callee| {
        if abstraction.abstracts_public_instance(tcx, callee)
            || native_assertion_panic_boundary(tcx, callee)
            || opaque.iter().any(|item| item.def.def_id() == callee.def.def_id())
        {
            None
        } else {
            callee.callee_body()
        }
    });
    body
}

// These fixtures compile ordinary Rust assert!, without the SDK's Kani
// assertion hook rewrite. Bind the intended obligation to its canonical core
// panic Call and exact message, not to an arbitrary Panic property elsewhere.
fn assert_native_bug_obligation(
    tcx: TyCtxt<'_>,
    body: &Body,
    vc: &trust_mc_core::chc::ChcVc,
    name: &str,
    depth: usize,
) {
    use crate::codegen_ay::shared::const_pointer::{self, ConstRead};
    use rustc_public::mir::Operand;
    use rustc_public::ty::{RigidTy, TyKind};
    use rustc_public::{CrateDef, rustc_internal};

    const EXPECTED: &str = "assertion failed: unsafe { *values.as_ptr() } == 1";
    assert!(!crate::kani_middle::transform::unit_has_stubs());
    let mut sites = Vec::new();
    for (bb, block) in body.blocks.iter().enumerate() {
        let TerminatorKind::Call { func, args, target: None, .. } = &block.terminator.kind else {
            continue;
        };
        let TyKind::RigidTy(RigidTy::FnDef(def, generics)) = func.ty(body.locals()).unwrap().kind()
        else {
            continue;
        };
        let instance = Instance::resolve(def, &generics).unwrap();
        if crate::kani_middle::transform::instance_has_unit_stub(&instance)
            || !crate::kani_middle::std_abstraction::is_sysroot_core_definition_at(
                tcx,
                rustc_internal::internal(tcx, instance.def.def_id()),
                &["panicking", "panic"],
            )
        {
            continue;
        }
        let [Operand::Constant(message)] = args.as_slice() else { continue };
        let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) = message.const_.ty().kind() else {
            continue;
        };
        if !matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Str)) {
            continue;
        }
        let text = const_pointer::const_bytes(&message.const_).and_then(|bytes| {
            let (_, window) = const_pointer::fixed_pointee(tcx, &bytes, 0, pointee)?;
            String::from_utf8(window.read_data_bytes(0, window.len())?).ok()
        });
        if text.as_deref() == Some(EXPECTED) {
            sites.push(bb);
        }
    }
    assert_eq!(
        sites.len(),
        1,
        "retain exactly the intended native assertion panic: {name} depth={depth}: sites={sites:?}; MIR={body:#?}"
    );
    let site = sites[0];
    let properties: Vec<_> = vc
        .properties
        .iter()
        .filter(|property| property.bb == site && property.kind == PropertyKind::Panic)
        .collect();
    assert_eq!(
        properties.len(),
        1,
        "the exact canonical native assertion must have its own Panic property: {name} depth={depth} bb{site}: {:?}",
        vc.properties
    );
    let property = properties[0];
    assert!(
        property.discharged_at_encode.is_none(),
        "the intended Bug obligation must not be silently discharged: {name} depth={depth} bb{site}: {property:?}"
    );
    assert!(
        vc.rules.iter().any(|rule| rule.head.name.as_str() == property.relation.as_str()
            && rule.body.relation.is_some()),
        "retain the exact assertion's guarded error rule: {name} depth={depth} bb{site}: {property:?}"
    );
}

#[test]
fn native_vec_primitive_store_exact_and_reverse_boundaries() {
    let source = format!(
        "#![allow(dead_code)]\n{}\n{}",
        include_str!("../../../../../tools/soundness-duals/vec_primitive_store_dual.rs")
            .replace("#[kani::proof]", ""),
        include_str!("fixtures/vec_primitive_store_native.rs")
    );
    with_native_box_ctx(&source, |ctx| {
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        let opaque = [
            find_instance_by_suffix(ctx.tcx, "native_alias_identity"),
            find_instance_by_suffix(ctx.tcx, "native_opaque_publish"),
            find_instance_by_suffix(ctx.tcx, "native_retarget_opaque"),
        ];
        for depth in [0, 32] {
            for name in [
                "physical_store_then_fresh_getter_safe",
                "physical_store_then_fresh_getter_bug",
                "primitive_u8_store_fresh_getter_safe",
                "primitive_u8_store_fresh_getter_bug",
                "primitive_copied_pointer_fresh_getter_safe",
                "primitive_buffer_store_preserves_owner_header_safe",
                "user_vec_fields_store_safe",
                "user_vec_fields_store_bug",
                "shared_header_queries_then_fresh_raw_read_safe",
            ] {
                let body = native_body(ctx.tcx, name, depth, &abstraction, &opaque);
                let label = format!("{name}_full_d{depth}");
                let (vc, _, diagnostics) =
                    ChcCtx::new(ctx.tcx, &body, label.as_str(), mem_config())
                        .translate_with_diagnostics();
                let reasons = take_reasons(&label);
                assert!(reasons.is_empty(), "full encoding {name} depth={depth}: {reasons:?}");
                assert_eq!(diagnostics.place_translation_drop.get(), 0, "{name} depth={depth}");
                assert_eq!(
                    diagnostics.sound_havoc_drop.get(),
                    0,
                    "frame/mirror debt {name} depth={depth}"
                );
                assert!(
                    vc.approximation_identity_complete,
                    "full encoding incomplete: {name} depth={depth}"
                );
                if name.ends_with("bug") {
                    assert_native_bug_obligation(ctx.tcx, &body, &vc, name, depth);
                }
            }
            for name in [
                "shared_old3_bug_reverse_refusal",
                "shared_new9_safe_reverse_refusal",
                "native_copied_shared_old3_refusal",
                "native_copied_shared_new9_refusal",
                "native_reborrowed_shared_old3_refusal",
                "native_reborrowed_shared_new9_refusal",
                "native_aggregate_shared_old3_refusal",
                "native_aggregate_shared_new9_refusal",
                "native_returned_shared_old3_refusal",
                "native_returned_shared_new9_refusal",
                "native_parameter_alias_old3_refusal",
                "native_parameter_alias_new9_refusal",
                "native_parameter_carrier_old3_refusal",
                "native_parameter_carrier_new9_refusal",
                "native_opaque_escape_before_store_refusal",
            ] {
                let body = native_body(ctx.tcx, name, depth, &abstraction, &opaque);
                let label = format!("{name}_full_d{depth}");
                let (vc, _, _) = ChcCtx::new(ctx.tcx, &body, label.as_str(), mem_config())
                    .translate_with_diagnostics();
                let reasons = take_reasons(&label);
                assert!(
                    reasons.get("vec_model_read_after_buffer_write").copied().unwrap_or(0) > 0,
                    "own reverse reason required: {name} depth={depth}: {reasons:?}"
                );
                assert!(
                    !vc.approximation_identity_complete,
                    "reverse refusal must not regain exact authority: {name} depth={depth}"
                );
            }
            let name = "growth_before_primitive_store_refusal";
            let body = native_body(ctx.tcx, name, depth, &abstraction, &opaque);
            let label = format!("{name}_full_d{depth}");
            let (vc, _, _) = ChcCtx::new(ctx.tcx, &body, label.as_str(), mem_config())
                .translate_with_diagnostics();
            let reasons = take_reasons(&label);
            assert!(
                reasons.get("vec_buffer_access_after_mutation").copied().unwrap_or(0) > 0,
                "header custody never excuses reallocation: depth={depth}: {reasons:?}"
            );
            assert!(!vc.approximation_identity_complete);

            // Custody only: no semantic verdict is assigned to these setter
            // cases. Deny stale ownerA. If MIR precisely recovers a unique
            // direct ownerB getter, that updated custody may legitimately pass.
            for name in [
                "native_retarget_opaque_old4_custody_negative",
                "native_retarget_opaque_new9_custody_negative",
                "native_retarget_inline_old4_custody_negative",
                "native_retarget_inline_new9_custody_negative",
                "native_retarget_copied_old4_custody_negative",
                "native_retarget_copied_new9_custody_negative",
            ] {
                let body = native_body(ctx.tcx, name, depth, &abstraction, &opaque);
                let owner = local_named(&body, "a");
                let pointer = local_named(&body, "pointer");
                let TyKind::RigidTy(RigidTy::RawPtr(element, _)) = body.locals()[pointer].ty.kind()
                else {
                    panic!("retain the typed pointer variable in the custody fixture")
                };
                let context = ChcCtx::new(ctx.tcx, &body, name, mem_config());
                let stale = RefTarget::with_projections(owner, Vec::new());
                let retains_rewrite = context.local_bytes_may_be_rewritten(pointer);
                if retains_rewrite {
                    assert!(
                        context
                            .native_vec_primitive_store_owner(pointer, &stale, element)
                            .is_none(),
                        "an escaped pointer cannot retain ownerA custody: {name} depth={depth}"
                    );
                    if name.contains("copied") {
                        let copied = local_named(&body, "copied");
                        assert!(
                            context
                                .native_vec_primitive_store_owner(copied, &stale, element)
                                .is_none(),
                            "whole copy must check upstream pointer rewrite: {name} depth={depth}"
                        );
                    }
                }
                // Test the actual data-store pointer too, so precise recovery
                // to B is allowed while stale A is always denied. Ignore the
                // setter's pointer-variable store, whose written type is *mutu8.
                let mut data_stores = 0;
                for block in &body.blocks {
                    for statement in &block.statements {
                        let rustc_public::mir::StatementKind::Assign(lhs, _) = &statement.kind
                        else {
                            continue;
                        };
                        if lhs.projection.as_slice() == [rustc_public::mir::ProjectionElem::Deref]
                            && lhs.ty(body.locals()).ok() == Some(element)
                            && matches!(
                                body.locals()[lhs.local].ty.kind(),
                                TyKind::RigidTy(RigidTy::RawPtr(..))
                            )
                        {
                            data_stores += 1;
                            assert!(
                                context
                                    .native_vec_primitive_store_owner(lhs.local, &stale, element)
                                    .is_none(),
                                "actual store cannot retain stale ownerA: {name} depth={depth}"
                            );
                        }
                    }
                }
                assert!(data_stores > 0, "retain a native raw data store in {name} depth={depth}");
            }

            // This check is deliberately only the prescan's query exemption;
            // the complete translation of the same source was checked above.
            let name = "shared_header_queries_then_fresh_raw_read_safe";
            let body = native_body(ctx.tcx, name, depth, &abstraction, &opaque);
            let label = format!("{name}_prescan_only_d{depth}");
            ChcCtx::new(ctx.tcx, &body, label.as_str(), mem_config())
                .book_vec_buffer_access_after_mutation();
            let reasons = take_reasons(&label);
            assert!(
                !reasons.contains_key("vec_model_read_after_buffer_write"),
                "prescan only: {reasons:?}"
            );
            assert!(
                !reasons.contains_key("vec_buffer_access_after_mutation"),
                "prescan only: {reasons:?}"
            );
        }
    });
}

const BUDGET_SOURCE: &str = r#"
    #[inline(never)]
    pub fn budget_identity(values: &Vec<u8>) -> &Vec<u8> { values }
    #[inline(never)]
    pub fn budget_store(pointer: *mut u8) { unsafe { *pointer = 9; } }
    pub fn budget_chain<'a>(values: &'a Vec<u8>, pointer: *mut u8) -> &'a Vec<u8> {
        budget_store(pointer);
        let r0 = budget_identity(values);
        let r1 = budget_identity(r0);
        let r2 = budget_identity(r1);
        let r3 = budget_identity(r2);
        let r4 = budget_identity(r3);
        let r5 = budget_identity(r4);
        let r6 = budget_identity(r5);
        let r7 = budget_identity(r6);
        budget_identity(r7)
    }
    pub fn budget_query(values: &Vec<u8>) -> usize { values.len() }
"#;

fn called(func: &Operand, body: &Body, instance: &Instance) -> bool {
    matches!(func.ty(body.locals()).unwrap().kind(), TyKind::RigidTy(RigidTy::FnDef(def, _))
        if def.def_id() == instance.def.def_id())
}
fn empty_block(template: &BasicBlock, kind: TerminatorKind) -> BasicBlock {
    BasicBlock {
        statements: Vec::new(),
        terminator: crate::rustc_compat::mir_terminator(kind, mir_span!(template.terminator)),
    }
}

// Retain actual native FnDef calls, argument/return types and local declarations.
// Only physical block ordering is reversed; CFG execution follows the original
// producer order. Every block is statement-free, with a real store Call anchor.
fn call_only_chain(original: &Body, identity: &Instance, store: &Instance) -> (Body, usize) {
    let mut calls = Vec::new();
    let mut store_call = None;
    let mut seen = HashSet::new();
    let mut bb = 0;
    loop {
        assert!(seen.insert(bb), "budget source must be a finite straight-line native function");
        match &original.blocks[bb].terminator.kind {
            TerminatorKind::Call { func, target, .. } => {
                if called(func, original, identity) {
                    calls.push(original.blocks[bb].terminator.kind.clone());
                } else if called(func, original, store) {
                    assert!(
                        store_call.replace(original.blocks[bb].terminator.kind.clone()).is_none()
                    );
                } else {
                    panic!("unexpected native call in budget fixture");
                }
                bb = target.expect("native budget call returns");
            }
            TerminatorKind::Goto { target } => bb = *target,
            TerminatorKind::Return => break,
            _ => panic!("unexpected control-flow in native budget fixture"),
        }
    }
    let count = calls.len();
    assert!(count >= 8, "retain a meaningful call-only alias chain");
    let mut locals = original.locals().to_vec();
    let first_fresh = locals.len();
    for _ in 0..count - 1 {
        locals.push(original.locals()[1].clone());
    }
    let destinations: Vec<usize> =
        (0..count).map(|index| if index + 1 == count { 0 } else { first_fresh + index }).collect();
    let mut start = store_call.expect("real native store call");
    if let TerminatorKind::Call { target, unwind, .. } = &mut start {
        *target = Some(count);
        *unwind = UnwindAction::Unreachable;
    }
    let template = &original.blocks[0];
    let mut blocks = vec![empty_block(template, start)];
    for physical in 1..=count {
        let execution = count - physical;
        let mut call = calls[execution].clone();
        if let TerminatorKind::Call { args, destination, target, unwind, .. } = &mut call {
            let source = if execution == 0 { 1 } else { destinations[execution - 1] };
            *args = vec![Operand::Copy(Place::from(source))];
            *destination = Place::from(destinations[execution]);
            *target = Some(if physical == 1 { count + 1 } else { physical - 1 });
            *unwind = UnwindAction::Unreachable;
        }
        blocks.push(empty_block(template, call));
    }
    blocks.push(empty_block(template, TerminatorKind::Return));
    let body = Body::new(
        blocks,
        locals,
        original.arg_locals().len(),
        Vec::new(),
        original.spread_arg(),
        original.span,
    );
    assert!(body.blocks.iter().all(|block| block.statements.is_empty()));
    (body, count + 1)
}

fn call_only_header_query(original: &Body, context: &ChcCtx<'_, '_>) -> Body {
    let mut call = original
        .blocks
        .iter()
        .find_map(|block| match &block.terminator.kind {
            TerminatorKind::Call { func, .. }
                if context.detect_stub(func) == Some(StubKind::VecLen) =>
            {
                Some(block.terminator.kind.clone())
            }
            _ => None,
        })
        .expect("actual native Vec::len call");
    if let TerminatorKind::Call { args, destination, target, unwind, .. } = &mut call {
        *args = vec![Operand::Copy(Place::from(1))];
        *destination = Place::from(0);
        *target = Some(1);
        *unwind = UnwindAction::Unreachable;
    }
    let template = &original.blocks[0];
    Body::new(
        vec![empty_block(template, call), empty_block(template, TerminatorKind::Return)],
        original.locals().to_vec(),
        original.arg_locals().len(),
        Vec::new(),
        original.spread_arg(),
        original.span,
    )
}

#[test]
fn native_vec_region_budget_covers_warm_call_only_work() {
    with_native_box_ctx(BUDGET_SOURCE, |ctx| {
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        let identity = find_instance_by_suffix(ctx.tcx, "budget_identity");
        let store = find_instance_by_suffix(ctx.tcx, "budget_store");
        let opaque = [identity, store];
        for depth in [0, 32] {
            let original = native_body(ctx.tcx, "budget_chain", depth, &abstraction, &opaque);
            let (body, call_count) = call_only_chain(&original, &identity, &store);
            let label = format!("budget_callonly_warm_d{depth}");
            let context = ChcCtx::new(ctx.tcx, &body, label.as_str(), mem_config());
            let probe = context.vec_region_budget_probe_for_test(1, (0, 0), 64, true);
            assert!(probe.setup_complete, "graph/cache setup must finish: {probe:?}");
            assert_eq!(probe.warmed_calls, call_count, "prewarm actual call facts");
            assert!(
                probe.warmed_types > 0 && probe.warmed_negative_calls > 0,
                "warm negative answers: {probe:?}"
            );
            assert!(
                probe.exhausted && probe.refused && probe.remaining == 0,
                "zero-statement calls still spend work before late aliases: {probe:?}"
            );
            let reasons = take_reasons(&label);
            assert!(
                reasons.get("vec_model_read_after_buffer_write").copied().unwrap_or(0) > 0,
                "exhaustion must record own refusal: {reasons:?}"
            );

            let original = native_body(ctx.tcx, "budget_query", depth, &abstraction, &opaque);
            let original_context =
                ChcCtx::new(ctx.tcx, &original, "budget_query_original", mem_config());
            let body = call_only_header_query(&original, &original_context);
            assert!(body.blocks.iter().all(|block| block.statements.is_empty()));
            for warm in [false, true] {
                let label = format!("budget_query_d{depth}_warm{warm}");
                let context = ChcCtx::new(ctx.tcx, &body, label.as_str(), mem_config());
                let probe = context.vec_region_budget_probe_for_test(1, (0, 0), 512, warm);
                assert!(
                    probe.setup_complete
                        && !probe.exhausted
                        && !probe.refused
                        && probe.remaining > 0,
                    "bounded native header query must remain precise: {probe:?}"
                );
                let reasons = take_reasons(&label);
                assert!(reasons.is_empty(), "query-only resource control: {reasons:?}");
                assert_eq!(context.diagnostics.place_translation_drop.get(), 0);
                assert_eq!(context.diagnostics.sound_havoc_drop.get(), 0);
            }
        }
    });
}
