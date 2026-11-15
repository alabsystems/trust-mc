// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Allocation identity, rather than a coincidentally equal local index, owns
//! BMC storage liveness. These tests exercise the actual predicate/deref paths.

use super::*;
use crate::codegen_ay::statement::dispatch::InlineArgValue;
use crate::codegen_ay::stubs::StubKind;
use std::collections::BTreeMap;

#[test]
fn test_stack_owner_preserves_frames_and_pointer_slot_storage() {
    let mut refs = BTreeMap::<Arc<str>, Arc<str>>::new();
    refs.insert(Arc::from("outer#1::local_3"), Arc::from("inner#2::local_3"));
    let slot = StatementCodegen::resolve_stack_storage_owner(&refs, "outer#1::local_3")
        .expect("bounded resolution")
        .expect("plain pointer slot owns its own storage");
    assert_eq!(slot.base.as_ref(), "outer#1::local_3");
    let pointee = StatementCodegen::resolve_stack_storage_owner(&refs, "outer#1::local_3_deref")
        .expect("bounded resolution")
        .expect("explicit dereference follows its allocation");
    assert_eq!(pointee.base.as_ref(), "inner#2::local_3");
    assert_eq!(pointee.local, slot.local);
    assert_ne!(pointee.frame, slot.frame);
    let nested = StatementCodegen::resolve_stack_storage_owner(
        &refs,
        "function::local_91::nested#4::local_3_field_0",
    )
    .expect("bounded resolution")
    .expect("the final local separator owns the allocation");
    assert_eq!(nested.frame.as_ref(), "function::local_91::nested#4");
    assert!(nested.has_field_projection);
}

#[test]
fn test_stack_owner_refuses_heap_aliases_cycles_and_unbounded_names() {
    let mut refs = BTreeMap::<Arc<str>, Arc<str>>::new();
    assert!(
        StatementCodegen::resolve_stack_storage_owner(&refs, "f::local_22_deref")
            .unwrap()
            .is_none()
    );
    refs.insert(Arc::from("f::local_22"), Arc::from("heap_allocation_4"));
    assert!(
        StatementCodegen::resolve_stack_storage_owner(&refs, "f::local_22_deref")
            .unwrap()
            .is_none()
    );
    refs.insert(Arc::from("f::local_22"), Arc::from("f::local_22_deref"));
    assert!(StatementCodegen::resolve_stack_storage_owner(&refs, "f::local_22_deref").is_err());
    assert!(
        StatementCodegen::resolve_stack_storage_owner(&refs, &"x".repeat(1024 * 1024 + 1)).is_err()
    );
    for malformed in ["f::local_bad", "f::local_3not_a_field", "f::local_03"] {
        assert!(StatementCodegen::resolve_stack_storage_owner(&refs, malformed).is_err());
    }
    for n in 0..33 {
        refs.insert(
            Arc::from(format!("f::local_{n}")),
            Arc::from(format!("f::local_{}_deref", n + 1)),
        );
    }
    assert!(StatementCodegen::resolve_stack_storage_owner(&refs, "f::local_0_deref").is_err());
    let indexed =
        StatementCodegen::resolve_stack_storage_owner(&refs, "f::local_5_cidx_0").unwrap().unwrap();
    assert!(!indexed.has_field_projection, "preserve existing field-only extent guard");
}

const POINTER_SOURCE: &str =
    "pub fn pointer_probe(p: *const u32, holder: *const u32) -> bool { p.is_null() }";

#[test]
fn test_stack_owner_foreign_facts_do_not_alias_current_local_indices() {
    with_test_ay_ctx_for_source(POINTER_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "pointer_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let mut cg = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        let current = format!("{}::local_1", cg.ctx.current_fn_name());
        let own = StatementCodegen::resolve_stack_storage_owner(&cg.ref_pointees, &current)
            .unwrap()
            .unwrap();
        let other =
            StatementCodegen::resolve_stack_storage_owner(&cg.ref_pointees, "other#9::local_1")
                .unwrap()
                .unwrap();
        cg.dead_locals.insert(1);
        cg.maybe_dead_locals.insert(1);
        assert_eq!(cg.stack_owner_is_live(&own), Some(false));
        assert_eq!(cg.stack_owner_is_live(&other), None);
        cg.qualified_storage_lifetimes.insert(Arc::clone(&other.base), Some(true));
        assert_eq!(cg.stack_owner_is_live(&other), Some(true));
        cg.dead_locals.remove(&1);
        cg.maybe_dead_locals.remove(&1);
        cg.qualified_storage_lifetimes.insert(Arc::clone(&other.base), Some(false));
        assert_eq!(cg.stack_owner_is_live(&own), Some(true));
        assert_eq!(cg.stack_owner_is_live(&other), Some(false));
        cg.qualified_storage_lifetimes.insert(Arc::clone(&other.base), None);
        assert_eq!(cg.stack_owner_is_live(&other), None);
    });
}

fn assert_bool_polarities(
    ctx: &crate::codegen_ay::context::AYCtx<'_, '_>,
    result: &Expr,
    expected: Option<bool>,
) {
    for polarity in [false, true] {
        let mut program = ctx.program.clone();
        program.assert(result.clone().eq(Expr::bool_const(polarity)));
        program.check_sat();
        let wanted = if expected.is_none_or(|value| value == polarity) { "sat" } else { "unsat" };
        assert_eq!(
            run_ay_on_smt2_with_timeout(&program.to_string(), AY_TEST_TIMEOUT_SECS)
                .expect("AY result"),
            wanted,
            "expected {expected:?}, asserted {polarity}"
        );
    }
}

#[test]
fn test_stack_owner_resolution_refusal_cannot_certify_either_polarity() {
    for cycle in [false, true] {
        for stub in [StubKind::KaniMemCanDereference, StubKind::KaniMemSameAllocation] {
            with_test_ay_ctx_for_source(POINTER_SOURCE, |mut ctx| {
                let instance = find_instance_by_suffix(&ctx, "pointer_probe");
                let body = instance.body().expect("body");
                ctx.set_current_fn(instance);
                let mut cg = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
                let pointer = cg.ssa_base_name(&local_place(1));
                let heap = cg.ctx.heap_alloc(
                    Expr::bitvec_const(4u128, POINTER_WIDTH),
                    Expr::bitvec_const(4u128, POINTER_WIDTH),
                );
                cg.current_env.insert(Arc::from(pointer.as_str()), heap);
                cg.ref_pointees
                    .insert(Arc::from(pointer.as_str()), Arc::from("alias::local_0_deref"));
                for local in 0..33 {
                    cg.ref_pointees.insert(
                        Arc::from(format!("alias::local_{local}")),
                        Arc::from(format!(
                            "alias::local_{}_deref",
                            if cycle { 0 } else { local + 1 }
                        )),
                    );
                }
                let args = if matches!(stub, StubKind::KaniMemSameAllocation) {
                    vec![local_operand(1), local_operand(1)]
                } else {
                    vec![local_operand(1)]
                };
                cg.try_codegen_simple_stub(stub, &args, &local_place(0), Some(1), "kani::mem");
                let destination = cg.ssa_base_name(&local_place(0));
                let result = cg.current_env.get(destination.as_str()).unwrap();
                assert_bool_polarities(cg.ctx, result, None);
                assert!(
                    cg.ctx.unsupported_constructs.contains_key("kani_mem_stack_lifetime_unknown")
                );
                cg.emit_raw_ptr_deref_checks(&Place {
                    local: 1,
                    projection: vec![ProjectionElem::Deref],
                });
                assert!(
                    cg.ctx.unsupported_constructs.contains_key("raw_ptr_stack_lifetime_unknown")
                );
            });
        }
    }
}

#[test]
fn test_kani_mem_heap_alias_retains_heap_evidence_under_both_polarities() {
    for stub in [StubKind::KaniMemCanDereference, StubKind::KaniMemSameAllocation] {
        with_test_ay_ctx_for_source(POINTER_SOURCE, |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "pointer_probe");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let mut cg = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
            let pointer = cg.ssa_base_name(&local_place(1));
            let heap = cg.ctx.heap_alloc(
                Expr::bitvec_const(4u128, POINTER_WIDTH),
                Expr::bitvec_const(4u128, POINTER_WIDTH),
            );
            cg.current_env.insert(Arc::from(pointer.as_str()), heap);
            // Box::into_raw's tracked leaf: the heap payload is not the
            // pointer holder's stack allocation, even after that holder dies.
            let alias = format!("{}::local_2_deref", cg.ctx.current_fn_name());
            cg.ref_pointees.insert(Arc::from(pointer.as_str()), Arc::from(alias));
            cg.dead_locals.insert(2);
            cg.maybe_dead_locals.insert(2);
            let before = cg.ctx.program.commands().len();
            let args = if matches!(stub, StubKind::KaniMemSameAllocation) {
                vec![local_operand(1), local_operand(1)]
            } else {
                vec![local_operand(1)]
            };
            assert_eq!(
                cg.try_codegen_simple_stub(stub, &args, &local_place(0), Some(1), "kani::mem"),
                Some(Some(1))
            );
            let destination_base = cg.ssa_base_name(&local_place(0));
            let dest = cg.current_env.get(destination_base.as_str()).unwrap();
            let rhs = extract_ssa_rhs(&cg.ctx.program.commands()[before..], dest).unwrap();
            assert!(
                !matches!(rhs.value(), ExprValue::BoolConst(_)),
                "heap predicate must retain allocation evidence: {rhs:?}"
            );
            assert!(!cg.ctx.unsupported_constructs.contains_key("kani_mem_stack_lifetime_unknown"));
            assert_bool_polarities(cg.ctx, dest, Some(true));
        });
    }
}

#[test]
fn test_kani_mem_foreign_owner_is_unknown_or_uses_qualified_fact() {
    for (known, current_dead) in [(None, true), (Some(true), true), (Some(false), false)] {
        for stub in [StubKind::KaniMemCanDereference, StubKind::KaniMemSameAllocation] {
            with_test_ay_ctx_for_source(POINTER_SOURCE, |mut ctx| {
                let instance = find_instance_by_suffix(&ctx, "pointer_probe");
                let body = instance.body().expect("body");
                ctx.set_current_fn(instance);
                let mut cg = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
                let pointer = cg.ssa_base_name(&local_place(1));
                let heap = cg.ctx.heap_alloc(
                    Expr::bitvec_const(4u128, POINTER_WIDTH),
                    Expr::bitvec_const(4u128, POINTER_WIDTH),
                );
                cg.current_env.insert(Arc::from(pointer.as_str()), heap);
                cg.ref_pointees.insert(Arc::from(pointer.as_str()), Arc::from("caller#7::local_1"));
                if current_dead {
                    cg.dead_locals.insert(1);
                    cg.maybe_dead_locals.insert(1);
                }
                if let Some(value) = known {
                    cg.qualified_storage_lifetimes
                        .insert(Arc::from("caller#7::local_1"), Some(value));
                }
                let before = cg.ctx.program.commands().len();
                let args = if matches!(stub, StubKind::KaniMemSameAllocation) {
                    vec![local_operand(1), local_operand(1)]
                } else {
                    vec![local_operand(1)]
                };
                cg.try_codegen_simple_stub(stub, &args, &local_place(0), Some(1), "kani::mem");
                let destination_base = cg.ssa_base_name(&local_place(0));
                let dest = cg.current_env.get(destination_base.as_str()).unwrap();
                let rhs = extract_ssa_rhs(&cg.ctx.program.commands()[before..], dest).unwrap();
                assert_eq!(
                    matches!(rhs.value(), ExprValue::BoolConst(false)),
                    known == Some(false)
                );
                if known.is_none() {
                    assert!(
                        matches!(rhs.value(), ExprValue::Var { .. }),
                        "missing foreign evidence must yield a fresh Bool"
                    );
                    assert!(
                        cg.ctx
                            .unsupported_constructs
                            .contains_key("kani_mem_stack_lifetime_unknown")
                    );
                }
                assert_bool_polarities(cg.ctx, dest, known);
            });
        }
    }
}

#[test]
fn test_raw_deref_foreign_owner_never_uses_current_extent_or_lifetime() {
    with_test_ay_ctx_for_source(
        "pub unsafe fn raw_probe(p: *const u128) -> u128 { unsafe { *p } }",
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "raw_probe");
            let body = instance.body().expect("body");
            for fact in [None, Some(true), Some(false)] {
                ctx.set_current_fn(instance);
                let mut cg = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
                let pointer = cg.ssa_base_name(&local_place(1));
                cg.current_env.insert(
                    Arc::from(pointer.as_str()),
                    Expr::bitvec_const(4096u128, POINTER_WIDTH),
                );
                cg.ref_pointees.insert(Arc::from(pointer.as_str()), Arc::from("caller#7::local_1"));
                cg.dead_locals.insert(1);
                cg.maybe_dead_locals.insert(1);
                if let Some(value) = fact {
                    cg.qualified_storage_lifetimes
                        .insert(Arc::from("caller#7::local_1"), Some(value));
                }
                let before = cg.ctx.bmc_vc.violations.len();
                cg.emit_raw_ptr_deref_checks(&Place {
                    local: 1,
                    projection: vec![ProjectionElem::Deref],
                });
                let names: Vec<_> = cg.ctx.bmc_vc.violations[before..]
                    .iter()
                    .filter_map(|v| v.smt_var.as_deref())
                    .collect();
                assert_eq!(names.iter().any(|n| n.contains("dead_object")), fact == Some(false));
                assert!(
                    !names.iter().any(|n| n.contains("pointer_invalid")),
                    "foreign u128 allocation must not use current pointer-slot's 8-byte extent"
                );
                assert!(
                    names.iter().any(|n| n.contains("use_after_free_check")),
                    "heap checks remain present"
                );
                if fact.is_none() {
                    assert!(
                        cg.ctx
                            .unsupported_constructs
                            .contains_key("raw_ptr_stack_lifetime_unknown")
                    );
                }
            }
        },
    );
}

#[test]
fn test_mini_inline_keeps_caller_storage_live_and_expires_own_frame() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn caller(first: u32, second: u32) -> u32 { first + second }
        pub unsafe fn callee(p: *const u32) -> u32 { unsafe { *p } }
    "#,
        |mut ctx| {
            let caller = find_instance_by_suffix(&ctx, "caller");
            let callee = find_instance_by_suffix(&ctx, "callee");
            let body = caller.body().expect("body");
            ctx.set_current_fn(caller);
            let mut cg = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
            let caller_base: Arc<str> = Arc::from(format!("{}::local_2", cg.ctx.current_fn_name()));
            let parameter = InlineArgValue {
                expr: Expr::bitvec_const(4096u128, POINTER_WIDTH),
                pointee_base: Some(Arc::clone(&caller_base)),
                flattened_entries: vec![],
                nested_ref_pointees: vec![],
            };
            for _ in 0..2 {
                assert!(
                    cg.inline_instance_value(callee, std::slice::from_ref(&parameter)).is_some()
                );
            }
            assert_eq!(cg.qualified_storage_lifetimes.get(&caller_base), Some(&Some(true)));
            let expired: Vec<_> = cg
                .qualified_storage_lifetimes
                .iter()
                .filter(|(base, _)| !base.starts_with(cg.ctx.current_fn_name()))
                .collect();
            assert!(
                expired.len() >= 4,
                "distinct frame identities and their return slots must survive both calls"
            );
            assert!(expired.iter().all(|(_, live)| **live == Some(false)));
            assert!(!cg.ctx.unsupported_constructs.contains_key("raw_ptr_stack_lifetime_unknown"));
            assert!(
                !cg.ctx
                    .bmc_vc
                    .violations
                    .iter()
                    .any(|v| v.smt_var.as_deref().is_some_and(|n| n.contains("dead_object")))
            );
        },
    );
}

#[test]
fn test_raw_deref_heap_alias_does_not_use_dead_pointer_holder() {
    with_test_ay_ctx_for_source(
        "pub unsafe fn heap_alias_probe(p: *const u128, holder: *const u8) -> u128 { unsafe { *p } }",
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "heap_alias_probe");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let mut cg = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
            let pointer = cg.ssa_base_name(&local_place(1));
            cg.current_env
                .insert(Arc::from(pointer.as_str()), Expr::bitvec_const(4096u128, POINTER_WIDTH));
            cg.ref_pointees.insert(
                Arc::from(pointer.as_str()),
                Arc::from(format!("{}::local_2_deref", cg.ctx.current_fn_name())),
            );
            cg.dead_locals.insert(2);
            cg.maybe_dead_locals.insert(2);
            cg.emit_raw_ptr_deref_checks(&Place {
                local: 1,
                projection: vec![ProjectionElem::Deref],
            });
            let names: Vec<_> =
                cg.ctx.bmc_vc.violations.iter().filter_map(|v| v.smt_var.as_deref()).collect();
            assert!(names.iter().any(|n| n.contains("use_after_free_check")));
            assert!(
                !names.iter().any(|n| n.contains("dead_object") || n.contains("pointer_invalid"))
            );
            assert!(!cg.ctx.unsupported_constructs.contains_key("raw_ptr_stack_lifetime_unknown"));
        },
    );
}

#[test]
fn test_kani_mem_zst_does_not_require_stack_lifetime_evidence() {
    with_test_ay_ctx_for_source(
        "pub fn zst_probe(p: *const ()) -> bool { p.is_null() }",
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "zst_probe");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let mut cg = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
            let pointer = cg.ssa_base_name(&local_place(1));
            cg.current_env
                .insert(Arc::from(pointer.as_str()), Expr::bitvec_const(4096u128, POINTER_WIDTH));
            cg.ref_pointees.insert(Arc::from(pointer.as_str()), Arc::from("unknown#7::local_1"));
            cg.dead_locals.insert(1);
            cg.maybe_dead_locals.insert(1);
            cg.try_codegen_simple_stub(
                StubKind::KaniMemCanDereference,
                &[local_operand(1)],
                &local_place(0),
                Some(1),
                "kani::mem",
            );
            assert!(!cg.ctx.unsupported_constructs.contains_key("kani_mem_stack_lifetime_unknown"));
        },
    );
}
