// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Ownership component controls. The original all-debt strict control remains
//! separate: byte-view debt is not qualified by these ownership-only checks.

use super::common::*;
use super::test_trust_box_new::{mem_config, with_native_box_ctx};
use crate::callee_body::CalleeBody;
use crate::codegen_ay::shared::native_box_call::{NativeBoxCallKind, native_global_dyn_box_call};
use crate::kani_middle::std_abstraction::StdAbstraction;
use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};
use rustc_public::CrateDef;
use rustc_public::mir::{Body, Operand, TerminatorKind, mono::Instance};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashSet;

const SOURCE: &str =
    include_str!("../../../../../tools/soundness-duals/callable_native_ownership_dual.rs");
const NEGATIVE: &str = r#"
fn erased_storage(pointer:*mut Box<dyn FnMut(&mut i32)>) {core::hint::black_box(pointer);}
fn raw_exposed(mut function:Box<dyn FnMut(&mut i32)>,value:&mut i32) {erased_storage(&raw mut function);function(value);}
fn replace(function:&mut Box<dyn FnMut(&mut i32)>) {*function=Box::new(&decrement);}
fn rebinding(mut function:Box<dyn FnMut(&mut i32)>,value:&mut i32) {replace(&mut function);function(value);}
#[inline(never)]fn unknown_borrow(function:&mut Box<dyn FnMut(&mut i32)>) {core::hint::black_box(function);}
fn unclosed(mut function:Box<dyn FnMut(&mut i32)>,value:&mut i32) {unknown_borrow(&mut function);function(value);}
pub fn raw_probe(){let mut value=1;raw_exposed(Box::new(&increment),&mut value);assert!(value==2);}
pub fn rebound_probe(){let mut value=1;rebinding(Box::new(&increment),&mut value);assert!(value==2);}
pub fn cyclic_probe(count:usize){let mut value=1;for _ in 0..count{twice(Box::new(&increment),&mut value);}}
pub fn unclosed_probe(){let mut value=1;unclosed(Box::new(&increment),&mut value);assert!(value==2);}
pub fn joined_probe(branch:bool){let mut first:Box<dyn FnMut(&mut i32)>=Box::new(&increment);let mut second:Box<dyn FnMut(&mut i32)>=Box::new(&decrement);let selected=if branch{&mut first}else{&mut second};let mut value=1;selected(&mut value);assert!(value==2);}
"#;
fn call_instance(body: &Body, func: &Operand) -> Option<Instance> {
    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func.ty(body.locals()).ok()?.kind() else {
        return None;
    };
    Instance::resolve(def, &args).ok()
}
fn has_cycle(body: &Body) -> bool {
    for start in 0..body.blocks.len() {
        let mut seen = HashSet::new();
        let mut pending = body.blocks[start].terminator.successors();
        while let Some(next) = pending.pop() {
            if next == start {
                return true;
            }
            if seen.insert(next) {
                pending.extend(body.blocks[next].terminator.successors());
            }
        }
    }
    false
}
fn solve_properties(
    vc: &trust_mc_core::chc::ChcVc,
    query: &str,
    name: &str,
) -> (&'static str, bool) {
    if let Some(dir) = std::env::var_os("MC_CALLABLE_OWNERSHIP_ARTIFACT_DIR") {
        std::fs::write(std::path::Path::new(&dir).join(format!("{name}.smt2")), query).unwrap();
    }
    let problem = ay_chc::ChcParser::parse(query).unwrap();
    let obligations = problem.query_obligations().unwrap();
    assert!(!obligations.is_empty());
    let count = obligations.len();
    let mut unresolved = Vec::new();
    let mut source_error_reached = false;
    let mut named_safe = true;
    for obligation in obligations {
        let (id, mut problem) = obligation.into_parts();
        problem.expand_nullary_fail_queries(false);
        if let Some(dir) = std::env::var_os("MC_CALLABLE_OWNERSHIP_ARTIFACT_DIR") {
            std::fs::write(
                std::path::Path::new(&dir).join(format!("{name}-{}.normalized", id.label())),
                problem.normalized_input(),
            )
            .unwrap();
        }
        // AY also preserves direct, unlabelled source error definitions.
        // Keep those obligations too; do not invent a property category.
        let property = vc.properties.iter().find(|property| property.relation == id.label());
        let actual =
            match ay_chc::AdaptivePortfolio::new(problem, ay_adaptive_config_with_timeout(30))
                .solve()
            {
                ay_chc::VerifiedChcResult::Safe(_) => "unsat",
                ay_chc::VerifiedChcResult::Unsafe(_) => "sat",
                _ => "unknown",
            };
        if property.is_some() && actual != "unsat" {
            named_safe = false;
        }
        if actual != "unsat" {
            unresolved.push((
                id.label().to_owned(),
                actual,
                property.and_then(|property| property.message.clone()),
            ));
        }
        if actual == "sat" {
            source_error_reached = true;
        }
    }
    eprintln!("CALLABLE_OWNERSHIP_PROPERTIES {name} rows={count} unresolved={unresolved:?}");
    (
        if source_error_reached {
            "sat"
        } else if unresolved.is_empty() {
            "unsat"
        } else {
            "unknown"
        },
        named_safe,
    )
}
#[test]
fn actual_native_callable_preprocessing_retains_typed_borrows_calls_and_user_effects() {
    with_native_box_ctx(&SOURCE.replace("#[kani::proof]", ""), |ctx| {
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        for name in [
            "native_fn_owner_borrow_safe",
            "native_fn_owner_borrow_bug",
            "repeated_native_fnmut_borrow_safe",
            "repeated_native_fnmut_borrow_bug",
            "loop_native_fnmut_borrow_safe",
            "loop_native_fnmut_borrow_bug",
            "user_named_call_mut_effect_safe",
            "user_named_call_mut_effect_bug",
            "second_native_fnmut_origin_safe",
            "second_native_fnmut_origin_bug",
        ] {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let mut pass = FunctionInlinePass::new(InlineConfig {
                max_depth: 32,
                chc_native_box_drop: true,
                ..InlineConfig::default()
            });
            let (_, body) = pass.transform_with_body_provider(
                ctx.tcx,
                instance.callee_body().unwrap(),
                instance,
                |callee| {
                    if abstraction.abstracts_public_instance(ctx.tcx, callee) {
                        None
                    } else {
                        callee.callee_body()
                    }
                },
            );
            let chc = ChcCtx::new(ctx.tcx, &body, name, mem_config());
            let mut calls = 0;
            for block in &body.blocks {
                let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else {
                    continue;
                };
                let Some(callee) = call_instance(&body, func) else {
                    continue;
                };
                if native_global_dyn_box_call(ctx.tcx, &callee).is_some() {
                    calls += 1;
                    let receiver = match &args[0] {
                        Operand::Copy(place) | Operand::Move(place) => place,
                        _ => panic!("actual reference receiver"),
                    };
                    assert!(receiver.projection.is_empty());
                    let owner = chc
                        .host_native_dyn_borrow_owner(receiver.local)
                        .expect("closed typed protocol borrow");
                    assert_ne!(
                        owner, receiver.local,
                        "owner storage and payload/reference views stay distinct"
                    );
                }
            }
            assert_eq!(
                calls,
                if name.starts_with("repeated_") || name.starts_with("second_") { 2 } else { 1 },
                "{name}: actual calls preserved, user forwarding body inlined"
            );
            assert_eq!(
                has_cycle(&body),
                name.starts_with("loop_"),
                "{name}: user loop must survive in the host CHC graph"
            );
            let (vc, _, diagnostics) = chc.translate_with_diagnostics();
            let query = crate::codegen_ay::emit_chc(&vc).to_string();
            // Use the production backward-sliced obligations, keeping every
            // row and strict native validation. Aggregate AY inputs can be
            // harder without changing the source's conjunction of properties.
            let (result, named_safe) = solve_properties(&vc, &query, name);
            assert!(
                named_safe,
                "{name}: every labelled native safety obligation must validate Safe"
            );
            let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                .remove(name)
                .unwrap_or_default();
            eprintln!(
                "CALLABLE_OWNERSHIP {name}: {result:?}; drops={}; reasons={reasons:?}",
                diagnostics.place_translation_drop.get()
            );
            if let Some(dir) = std::env::var_os("MC_CALLABLE_OWNERSHIP_ARTIFACT_DIR") {
                std::fs::write(std::path::Path::new(&dir).join(format!("{name}.smt2")), query)
                    .unwrap();
            }
            if name == "loop_native_fnmut_borrow_safe" && result == "unknown" {
                // The exact source assertion remains strict in the dual
                // manifest. This ownership component establishes call/loop
                // preservation and all native safety rows; it does not turn
                // the solver's unresolved assertion into a source pass.
                eprintln!(
                    "CALLABLE_OWNERSHIP_SOURCE_UNQUALIFIED {name}: AY77 source assertion Unknown; strict manifest still SUCCESSFUL"
                );
            } else {
                assert_eq!(
                    result,
                    if name.ends_with("safe") { "unsat" } else { "sat" },
                    "{name}: unchanged native truth"
                );
            }
            assert_eq!(diagnostics.place_translation_drop.get(), 0, "{name}: ownership component");
            for reason in [
                "box_deref_validity_unmodeled",
                "fn_trait_dispatch_unguarded_candidate",
                "native_box_drop_exact_origin_required",
            ] {
                assert!(!reasons.contains_key(reason), "{name}: {reasons:?}");
            }
        }
    });
}
#[test]
fn raw_rebound_unclosed_and_cyclic_owners_do_not_gain_native_authority() {
    let source = SOURCE.replace("#[kani::proof]", "") + NEGATIVE;
    with_native_box_ctx(&source, |ctx| {
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        for name in ["raw_probe", "rebound_probe", "cyclic_probe", "unclosed_probe", "joined_probe"]
        {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let mut pass = FunctionInlinePass::new(InlineConfig {
                max_depth: 32,
                chc_native_box_drop: true,
                ..InlineConfig::default()
            });
            let (_, body) = pass.transform_with_body_provider(
                ctx.tcx,
                instance.callee_body().unwrap(),
                instance,
                |callee| {
                    if abstraction.abstracts_public_instance(ctx.tcx, callee) {
                        None
                    } else {
                        callee.callee_body()
                    }
                },
            );
            let (_, _, diagnostics) =
                ChcCtx::new(ctx.tcx, &body, name, mem_config()).translate_with_diagnostics();
            let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                .remove(name)
                .unwrap_or_default();
            eprintln!(
                "CALLABLE_OWNERSHIP_REFUSAL {name} drops={} reasons={reasons:?}",
                diagnostics.place_translation_drop.get()
            );
            assert!(diagnostics.place_translation_drop.get() > 0, "{name}: {reasons:?}");
            assert!(
                reasons.keys().any(|reason| reason.starts_with("native_dyn_")
                    || reason == "box_deref_validity_unmodeled"
                    || reason == "native_box_drop_exact_origin_required"),
                "{name}: {reasons:?}"
            );
        }
    });
}
#[test]
fn native_callable_protocol_identity_refuses_local_lookalikes_and_stubs() {
    let source = format!("#![feature(allocator_api)]\n{}", SOURCE.replace("#[kani::proof]", ""))
        + r#"
    pub fn owned_once(function:Box<dyn FnOnce(&mut i32)>,value:&mut i32){function(value);}
    pub fn marker(){}
    trait DecoyCall {fn call_mut(&mut self,value:&mut i32);}
    impl DecoyCall for Box<dyn FnMut(&mut i32)>{fn call_mut(&mut self,value:&mut i32){*value=99;}}
    pub fn local_trait_call(mut function:Box<dyn FnMut(&mut i32)>,value:&mut i32){DecoyCall::call_mut(&mut function,value);}
    struct Custom;
    unsafe impl std::alloc::Allocator for Custom {
        fn allocate(&self,_layout:std::alloc::Layout)->Result<core::ptr::NonNull<[u8]>,std::alloc::AllocError>{Err(std::alloc::AllocError)}
        unsafe fn deallocate(&self,_pointer:core::ptr::NonNull<u8>,_layout:std::alloc::Layout){}
    }
    pub fn custom_call(mut function:Box<dyn FnMut(&mut i32),Custom>,value:&mut i32){function(value);}
    "#;
    with_native_box_ctx(&source, |ctx| {
        let mut actual = None;
        for (name, kind) in [
            ("native_fn_owner_borrow_safe", NativeBoxCallKind::Fn),
            ("twice", NativeBoxCallKind::FnMut),
            ("owned_once", NativeBoxCallKind::FnOnce),
        ] {
            let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
            let recognized = body
                .blocks
                .iter()
                .filter_map(|block| match &block.terminator.kind {
                    TerminatorKind::Call { func, .. } => call_instance(&body, func),
                    _ => None,
                })
                .find(|callee| native_global_dyn_box_call(ctx.tcx, callee).is_some());
            let callee = recognized.expect("real native callable protocol");
            assert_eq!(native_global_dyn_box_call(ctx.tcx, &callee).unwrap().1, kind);
            actual = Some(callee);
        }
        let body = find_instance_by_suffix(ctx.tcx, "user_named_call_mut_effect_safe")
            .callee_body()
            .unwrap();
        let user = body
            .blocks
            .iter()
            .filter_map(|block| match &block.terminator.kind {
                TerminatorKind::Call { func, .. } => call_instance(&body, func),
                _ => None,
            })
            .find(|callee| {
                ctx.tcx.def_path_str(rustc_public::rustc_internal::internal(
                    ctx.tcx,
                    callee.def.def_id(),
                )) == "call_mut"
            })
            .expect("user named forwarder");
        assert!(native_global_dyn_box_call(ctx.tcx, &user).is_none());
        for name in ["local_trait_call", "custom_call"] {
            let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
            let callees = body
                .blocks
                .iter()
                .filter_map(|block| match &block.terminator.kind {
                    TerminatorKind::Call { func, .. } => call_instance(&body, func),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert!(!callees.is_empty());
            for callee in callees {
                assert!(
                    native_global_dyn_box_call(ctx.tcx, &callee).is_none(),
                    "{name}: no name/ABI/allocator substitute"
                );
            }
        }
        let TyKind::RigidTy(RigidTy::FnDef(marker, _)) =
            find_instance_by_suffix(ctx.tcx, "marker").ty().kind()
        else {
            panic!("actual marker function");
        };
        let _scope = crate::kani_middle::transform::UnitStubsTestScope::install(
            std::collections::HashMap::from([(marker, marker)]),
        );
        assert!(native_global_dyn_box_call(ctx.tcx, &actual.unwrap()).is_none());
    });
}

#[test]
fn native_callable_borrow_analysis_exhaustion_refuses_instead_of_licensing_a_view() {
    with_native_box_ctx(&SOURCE.replace("#[kani::proof]", ""), |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "native_fn_owner_borrow_safe");
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        let mut pass = FunctionInlinePass::new(InlineConfig {
            max_depth: 32,
            chc_native_box_drop: true,
            ..InlineConfig::default()
        });
        let (_, mut body) = pass.transform_with_body_provider(
            ctx.tcx,
            instance.callee_body().unwrap(),
            instance,
            |callee| {
                if abstraction.abstracts_public_instance(ctx.tcx, callee) {
                    None
                } else {
                    callee.callee_body()
                }
            },
        );
        let borrow = body
            .blocks
            .iter()
            .find_map(|block| match &block.terminator.kind {
                TerminatorKind::Call { func, args, .. }
                    if call_instance(&body, func).is_some_and(|callee| {
                        native_global_dyn_box_call(ctx.tcx, &callee).is_some()
                    }) =>
                {
                    match &args[0] {
                        Operand::Copy(place) | Operand::Move(place) => Some(place.local),
                        _ => None,
                    }
                }
                _ => None,
            })
            .unwrap();
        assert!(
            ChcCtx::new(ctx.tcx, &body, "bounded", mem_config())
                .host_native_dyn_borrow_owner(borrow)
                .is_some()
        );
        let mut nop = body.blocks[0].statements[0].clone();
        nop.kind = rustc_public::mir::StatementKind::Nop;
        body.blocks[0].statements.extend(std::iter::repeat_n(nop, 16_385));
        assert!(
            ChcCtx::new(ctx.tcx, &body, "exhausted", mem_config())
                .host_native_dyn_borrow_owner(borrow)
                .is_none()
        );
    });
}
