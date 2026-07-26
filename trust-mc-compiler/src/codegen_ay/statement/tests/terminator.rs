// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven unit tests for terminator.rs — terminator translation paths.
//!
//! Trivial tests that only constructed AY Expr/Sort values (SwitchInt bool/bv
//! expression-level, signed discriminant masking arithmetic, otherwise branch
//! condition construction, Int sort case constants) were removed per rule #2312
//! and #2482 because they did not exercise production codegen paths.
//!
//! Part of #2016: test coverage for untested codegen_ay modules.

use super::*;
use crate::codegen_ay::get_unsupported_construct_fallback_count;
use crate::codegen_ay::set_unsupported_construct_fallback_count_for_test;
use crate::codegen_ay::statement::dispatch::CallDispatchOutcome;

const POSIX_MEMALIGN_TERMINATOR_SOURCE: &str = r#"
    #![feature(rustc_private)]

    extern crate libc;
    use core::ptr;

    pub fn probe_posix_memalign_invalid() -> i32 {
        let mut out = ptr::null_mut();
        unsafe { libc::posix_memalign(&mut out, 13, 4) }
    }

    pub fn probe_posix_memalign_success() -> i32 {
        let mut out = ptr::null_mut();
        let _ret = unsafe { libc::posix_memalign(&mut out, 16, 4) };
        if out.is_null() { 1 } else { 0 }
    }
"#;

const SYSCONF_TERMINATOR_SOURCE: &str = r#"
    #![feature(rustc_private)]

    extern crate libc;

    pub fn probe_sysconf_bmc() -> libc::c_long {
        unsafe { libc::sysconf(libc::_SC_PAGESIZE) }
    }
"#;

const CALL_OUTCOME_PROBE: &str = r#"
pub fn call_outcome_probe(x: Option<u32>) -> u32 {
    x.unwrap()
}
"#;

fn with_call_terminator_probe<F>(callback: F)
where
    F: FnOnce(
            &mut StatementCodegen<'_, '_, '_>,
            &Operand,
            Option<rustc_public::mir::BasicBlockIdx>,
            &Terminator,
        ) + Send,
{
    with_test_ay_ctx_for_source(CALL_OUTCOME_PROBE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "call_outcome_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
            }
        }

        let call_terminator = body
            .blocks
            .iter()
            .find_map(|bb| match &bb.terminator.kind {
                TerminatorKind::Call { func, target, .. } => Some((func, *target, &bb.terminator)),
                _ => None,
            })
            .expect("probe should produce a Call terminator");
        callback(&mut codegen, call_terminator.0, call_terminator.1, call_terminator.2);
    });
}

// ─── Full terminator codegen via MIR ────────────────────────────────

#[test]
fn test_goto_terminator_in_mir() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn goto_test(flag: bool) -> u32 {
            let mid = if flag { 10 } else { 20 };
            mid + 1
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "goto_test");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let mut found_goto = false;
            for bb in &body.blocks {
                if matches!(bb.terminator.kind, TerminatorKind::Goto { .. }) {
                    let successors = codegen.codegen_terminator_with_successors(&bb.terminator);
                    assert_eq!(successors.len(), 1, "Goto should have exactly one successor");
                    let (target, edge_cond) = &successors[0];
                    assert!(*target < body.blocks.len(), "Goto target {} out of range", target);
                    assert!(edge_cond.is_none(), "Goto successor should be unconditional");
                    found_goto = true;
                }
            }
            assert!(found_goto, "expected at least one Goto terminator in MIR");
        },
    );
}

#[test]
fn test_switchint_terminator_in_mir() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn switch_test(x: bool) -> u32 {
            if x { 1 } else { 0 }
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "switch_test");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Find the SwitchInt terminator
            let mut found_switch = false;
            for bb in &body.blocks {
                if matches!(bb.terminator.kind, TerminatorKind::SwitchInt { .. }) {
                    let successors = codegen.codegen_terminator_with_successors(&bb.terminator);
                    // Bool switch: should have 2 successors (true case + otherwise)
                    assert!(
                        successors.len() >= 2,
                        "bool SwitchInt should have at least 2 successors, got {}",
                        successors.len()
                    );
                    // At least one successor should have a path condition
                    let has_condition = successors.iter().any(|(_, cond)| cond.is_some());
                    assert!(has_condition, "SwitchInt should produce path conditions");
                    found_switch = true;
                }
            }
            assert!(found_switch, "expected SwitchInt terminator in bool branch MIR");
        },
    );
}

#[test]
fn test_return_terminator_in_mir() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn return_test() -> u32 { 42 }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "return_test");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Find the Return terminator
            let mut found_return = false;
            for bb in &body.blocks {
                if matches!(bb.terminator.kind, TerminatorKind::Return) {
                    let successors = codegen.codegen_terminator_with_successors(&bb.terminator);
                    assert!(successors.is_empty(), "Return should have no successors");
                    found_return = true;
                }
            }
            assert!(found_return, "expected Return terminator in MIR");
        },
    );
}

#[test]
fn test_handled_call_successors_continue_returns_one_successor() {
    with_call_terminator_probe(|codegen, func, target, term| {
        let successors = codegen
            .handled_call_successors(CallDispatchOutcome::Continue(3), func, target, term)
            .expect("continue outcome should produce successors");
        assert_eq!(successors, vec![(3, None)]);
    });
}

#[test]
fn test_handled_call_successors_diverge_returns_empty_successors() {
    with_call_terminator_probe(|codegen, func, target, term| {
        let successors = codegen
            .handled_call_successors(CallDispatchOutcome::Diverge, func, target, term)
            .expect("diverge outcome should be handled");
        assert!(successors.is_empty(), "diverge outcome should produce no successors");
    });
}

#[test]
fn test_handled_call_successors_fallthrough_routes_to_unsupported_footer() {
    with_call_terminator_probe(|codegen, func, target, term| {
        set_unsupported_construct_fallback_count_for_test(0);
        let fallback_target = target.expect("probe call should have a normal successor");
        let successors = codegen
            .handled_call_successors(
                CallDispatchOutcome::FallthroughToUnsupported,
                func,
                target,
                term,
            )
            .expect("fallthrough outcome should reuse unsupported footer");
        assert_eq!(successors, vec![(fallback_target, None)]);
        assert!(
            get_unsupported_construct_fallback_count() >= 1,
            "fallthrough outcome should record unsupported fallback telemetry"
        );
    });
}

#[test]
fn test_drop_terminator_in_mir() {
    with_test_ay_ctx_for_source(
        r#"
        pub struct NeedsDrop(pub u8);
        impl Drop for NeedsDrop {
            fn drop(&mut self) {}
        }

        pub fn drop_test(flag: bool) -> u8 {
            let value = if flag { NeedsDrop(1) } else { NeedsDrop(2) };
            value.0
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "drop_test");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            let mut found_drop = false;
            for bb in &body.blocks {
                if matches!(bb.terminator.kind, TerminatorKind::Drop { .. }) {
                    let successors = codegen.codegen_terminator_with_successors(&bb.terminator);
                    assert_eq!(successors.len(), 1, "Drop should have exactly one successor");
                    let (target, edge_cond) = &successors[0];
                    assert!(*target < body.blocks.len(), "Drop target {} out of range", target);
                    assert!(edge_cond.is_none(), "Drop successor should be unconditional");
                    found_drop = true;
                }
            }
            assert!(found_drop, "expected at least one Drop terminator in MIR");
        },
    );
}

#[test]
fn test_integer_switchint_in_mir() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn int_switch_test(x: u32) -> u32 {
            match x {
                0 => 10,
                1 => 20,
                2 => 30,
                _ => 99,
            }
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "int_switch_test");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Find the SwitchInt terminator
            let mut found_switch = false;
            for bb in &body.blocks {
                if matches!(bb.terminator.kind, TerminatorKind::SwitchInt { .. }) {
                    let successors = codegen.codegen_terminator_with_successors(&bb.terminator);
                    // 3 explicit cases + otherwise = 4 successors
                    assert!(
                        successors.len() >= 4,
                        "u32 match with 3 arms + default should have >=4 successors, got {}",
                        successors.len()
                    );
                    found_switch = true;
                }
            }
            assert!(found_switch, "expected SwitchInt terminator for match expression");
        },
    );
}

// ─── Assert edge condition propagation (#762) ────────────────────────

/// Test Assert(Overflow) terminator propagates assertion as edge condition (Some(cond)).
/// MIR-driven: compiles a function with overflow checks (`x + y` for u32),
/// finds the Assert terminator, and verifies the successor has `Some(cond)`.
/// Covers terminator.rs:120-125 — the Overflow-specific edge condition propagation (#762).
#[test]
fn test_assert_terminator_propagates_edge_condition() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn add_with_overflow(x: u32, y: u32) -> u32 {
            x + y
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "add_with_overflow");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Process all statements first to populate operand environment
            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            // Find and process the Assert terminator
            let mut found_assert = false;
            for bb in &body.blocks {
                if matches!(bb.terminator.kind, TerminatorKind::Assert { .. }) {
                    let successors = codegen.codegen_terminator_with_successors(&bb.terminator);
                    // Assert should produce exactly one successor
                    assert_eq!(
                        successors.len(),
                        1,
                        "Assert terminator should have exactly one successor"
                    );
                    let (target, edge_cond) = &successors[0];
                    // Target block should be valid
                    assert!(*target < body.blocks.len(), "Assert target {} out of range", target);
                    // Edge condition should be Some — this is the key property (#762).
                    // Before the fix, this was None; now it propagates the assertion
                    // to enable dead_object detection in post-Assert blocks.
                    assert!(
                        edge_cond.is_some(),
                        "Assert terminator should propagate edge condition (Some), not None"
                    );
                    // The edge condition should be a bool expression
                    let cond_expr = edge_cond.as_ref().unwrap();
                    assert!(
                        cond_expr.sort().is_bool(),
                        "Assert edge condition should be Bool sort"
                    );
                    found_assert = true;
                }
            }
            assert!(found_assert, "expected Assert terminator in u32 addition MIR");
        },
    );
}

/// Test Assert(Overflow) terminator records violation AND propagates edge condition.
/// Verifies that codegen_terminator_with_successors both:
/// 1. Records a violation via emit_overflow_check (Overflow-specific path, terminator.rs:115)
/// 2. Returns a non-None edge condition in the successor (terminator.rs:124-125)
///
/// Exercises the AssertMessage::Overflow early-return path (lines 105-126),
/// not the general Assert path (lines 128-144) which uses record_violation_guarded.
#[test]
fn test_assert_overflow_records_violation_and_propagates_edge() {
    with_test_ay_ctx_for_source(
        r#"
        pub fn sub_with_overflow(x: u32, y: u32) -> u32 {
            x - y
        }
        "#,
        |mut ctx| {
            let instance = find_instance_by_suffix(&ctx, "sub_with_overflow");
            let body = instance.body().expect("body");
            ctx.set_current_fn(instance);
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

            // Process statements to populate operand environment
            for bb in &body.blocks {
                for stmt in &bb.statements {
                    codegen.codegen_statement(stmt);
                }
            }

            let violations_before = codegen.ctx.bmc_vc.violations.len();

            // Process Assert terminators
            let mut found_assert = false;
            for bb in &body.blocks {
                if matches!(bb.terminator.kind, TerminatorKind::Assert { .. }) {
                    let successors = codegen.codegen_terminator_with_successors(&bb.terminator);
                    // Verify violation was recorded via emit_overflow_check
                    assert!(
                        codegen.ctx.bmc_vc.violations.len() > violations_before,
                        "Assert(Overflow) should record overflow violation"
                    );
                    // Verify edge condition propagated
                    assert_eq!(successors.len(), 1);
                    assert!(
                        successors[0].1.is_some(),
                        "Assert(Overflow) should propagate edge condition"
                    );
                    found_assert = true;
                }
            }
            assert!(found_assert, "expected Assert terminator in u32 subtraction MIR");
        },
    );
}

#[test]
fn test_posix_memalign_invalid_avoids_unsupported_foreign_violation() {
    with_test_ay_ctx_for_source(POSIX_MEMALIGN_TERMINATOR_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_posix_memalign_invalid");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
            }
        }

        let violations_before = codegen.ctx.bmc_vc.violations.len();
        let commands_before = codegen.ctx.program.commands().len();
        let mut found_call = false;

        for bb in &body.blocks {
            let TerminatorKind::Call { func, destination, .. } = &bb.terminator.kind else {
                continue;
            };
            let Some(path) = codegen.resolve_callee_path(func) else {
                continue;
            };
            if path != "libc::posix_memalign" {
                continue;
            }
            found_call = true;

            let successors = codegen.codegen_terminator_with_successors(&bb.terminator);
            assert_eq!(successors.len(), 1, "posix_memalign should keep a normal successor");
            assert_eq!(
                codegen.ctx.bmc_vc.violations.len(),
                violations_before,
                "invalid-alignment posix_memalign should not record unsupported foreign function"
            );

            let dest_base = codegen.ssa_base_name(destination);
            let dest_expr =
                codegen.current_env.get(dest_base.as_str()).expect("destination assigned");
            let added = &codegen.ctx.program.commands()[commands_before..];
            let rhs = extract_ssa_rhs(added, dest_expr)
                .expect("missing SSA rhs for posix_memalign result");
            assert!(
                matches!(
                    rhs.value(),
                    ExprValue::BitVecConst { value, width }
                        if *width == 32 && u64::try_from(value).ok() == Some(22)
                ) || matches!(rhs.value(), ExprValue::Ite { .. }),
                "invalid alignment should produce an EINVAL-shaped result, got {:?}",
                rhs.value()
            );
            break;
        }

        assert!(found_call, "expected direct libc::posix_memalign call in MIR");
    });
}

#[test]
fn test_sysconf_avoids_unsupported_foreign_violation_and_assigns_symbolic_return() {
    with_test_ay_ctx_for_source(SYSCONF_TERMINATOR_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_sysconf_bmc");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
            }
        }

        let violations_before = codegen.ctx.bmc_vc.violations.len();
        let mut found_call = false;

        for bb in &body.blocks {
            let TerminatorKind::Call { func, destination, .. } = &bb.terminator.kind else {
                continue;
            };
            let Some(path) = codegen.resolve_callee_path(func) else {
                continue;
            };
            if path != "libc::sysconf" {
                continue;
            }
            found_call = true;

            let commands_before = codegen.ctx.program.commands().len();
            let successors = codegen.codegen_terminator_with_successors(&bb.terminator);
            assert_eq!(successors.len(), 1, "sysconf should keep a normal successor");
            assert_eq!(
                codegen.ctx.bmc_vc.violations.len(),
                violations_before,
                "sysconf should not record unsupported foreign function"
            );

            let dest_base = codegen.ssa_base_name(destination);
            let dest_expr =
                codegen.current_env.get(dest_base.as_str()).expect("destination assigned");
            let added = &codegen.ctx.program.commands()[commands_before..];
            let rhs = extract_ssa_rhs(added, dest_expr).expect("missing SSA rhs for sysconf");
            assert!(
                matches!(rhs.value(), ExprValue::Var { name } if name.starts_with("sysconf_result")),
                "sysconf return should be a fresh symbolic value, got {:?}",
                rhs.value()
            );
            break;
        }

        assert!(found_call, "expected direct libc::sysconf call in MIR");
    });
}

#[test]
fn test_posix_memalign_success_updates_out_pointer() {
    with_test_ay_ctx_for_source(POSIX_MEMALIGN_TERMINATOR_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "probe_posix_memalign_success");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        for bb in &body.blocks {
            for stmt in &bb.statements {
                codegen.codegen_statement(stmt);
            }
        }

        let violations_before = codegen.ctx.bmc_vc.violations.len();
        let mut found_call = false;

        for bb in &body.blocks {
            let TerminatorKind::Call { func, args, .. } = &bb.terminator.kind else {
                continue;
            };
            let Some(path) = codegen.resolve_callee_path(func) else {
                continue;
            };
            if path != "libc::posix_memalign" {
                continue;
            }
            found_call = true;

            let out_local = match args.first().expect("memptr arg") {
                Operand::Copy(place) | Operand::Move(place) => {
                    let ref_base = codegen.ssa_base_name(place);
                    let pointee_base = codegen
                        .ref_pointees
                        .get(ref_base.as_str())
                        .cloned()
                        .or_else(|| codegen.ensure_ref_pointee_for_place(place))
                        .expect("out local should resolve through ref_pointees");
                    StatementCodegen::resolve_ref_chain_target(&codegen.ref_pointees, &pointee_base)
                }
                _ => panic!("memptr arg should be a local reference"),
            };
            let out_place = local_place(out_local);
            let out_before = codegen
                .codegen_place(&out_place)
                .expect("out pointer should be available before call");

            let commands_before = codegen.ctx.program.commands().len();
            let successors = codegen.codegen_terminator_with_successors(&bb.terminator);
            assert_eq!(successors.len(), 1, "posix_memalign should keep a normal successor");
            assert_eq!(
                codegen.ctx.bmc_vc.violations.len(),
                violations_before,
                "success-path posix_memalign should not record unsupported foreign function"
            );

            let out_base = codegen.ssa_base_name(&out_place);
            let out_expr =
                codegen.current_env.get(out_base.as_str()).expect("out pointer assigned");
            let added = &codegen.ctx.program.commands()[commands_before..];
            let rhs = extract_ssa_rhs(added, out_expr).expect("missing SSA rhs for out pointer");
            assert_ne!(
                rhs, out_before,
                "success path should overwrite the out-pointer slot with a fresh pointer"
            );
            break;
        }

        assert!(found_call, "expected direct libc::posix_memalign call in MIR");
    });
}
