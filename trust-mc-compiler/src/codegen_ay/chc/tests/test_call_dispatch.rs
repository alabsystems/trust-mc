// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC call dispatch spine (codegen_call.rs) and call family handlers
//! (codegen_call_kani.rs, codegen_call_numeric.rs, codegen_call_misc.rs).
//!
//! Part of #2188 — coverage for untested call terminator dispatch logic.
//! These files have 0 dedicated tests despite being central to CHC codegen.

#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::chc::dyn_coercion;
use crate::codegen_ay::emit_chc;
use crate::codegen_ay::shared::is_pointer_wrapper_adt;
use rustc_public::mir::mono::{Instance, InstanceKind};

// build_output_args coverage is in test_call_coerce.rs (5 tests) and
// test_stmt_output.rs (4 tests). Three vacuous tests removed here — they
// always produced zero state_vars at Reg level, making all assertions skip.

// =============================================================================
// Kani hook detection tests (codegen_call_kani.rs)
// Uses local `mod kani` stubs since the kani crate isn't linked in test mode.
// =============================================================================

/// Tests that kani::assert-like path is detected.
/// Uses a local mod kani stub that mimics the kani API surface.
#[test]
fn test_kani_assert_like_detection() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        mod kani {
            pub fn assert(_cond: bool, _msg: &str) {}
            pub fn assume(_cond: bool) {}
        }

        pub fn probe_assert(x: u32) {
            kani::assert(x > 0, "x must be positive");
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_assert");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_assert", ChcConfig::default());

        // Exercise the call dispatch path: every Call terminator gets classified
        let mut call_count = 0;
        let mut all_hooks_none = true;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                // detect_kani_hook requires actual kani functions resolved by KaniFunction table,
                // so local stubs won't match — should return None.
                let hook = chc_ctx.detect_kani_hook(func);
                if hook.is_some() {
                    all_hooks_none = false;
                }
                call_count += 1;
            }
        }
        assert!(call_count >= 1, "should find at least one Call terminator");
        // Local mod kani stubs don't match the real KaniFunction table
        assert!(
            all_hooks_none,
            "detect_kani_hook should return None for local kani stubs (not in KaniFunction table)"
        );
    });
}

/// Tests that kani::assume-like calls exercise the detection path.
#[test]
fn test_kani_assume_like_detection() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        mod kani {
            pub fn assume(_cond: bool) {}
        }

        pub fn probe_assume(x: u32) {
            kani::assume(x < 100);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_assume");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_assume", ChcConfig::default());

        let mut call_count = 0;
        let mut all_hooks_none = true;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                let hook = chc_ctx.detect_kani_hook(func);
                if hook.is_some() {
                    all_hooks_none = false;
                }
                call_count += 1;
            }
        }
        assert!(call_count >= 1, "should find at least one Call terminator");
        assert!(
            all_hooks_none,
            "detect_kani_hook should return None for local kani stubs (not in KaniFunction table)"
        );
    });
}

// =============================================================================
// Full translate() integration tests — call dispatch spine
// =============================================================================

/// Tests that translate() produces non-empty VC with rules for a function with calls.
#[test]
fn test_translate_produces_rules_for_calls() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn helper(x: u32) -> u32 { x + 1 }

        pub fn probe_call_vc(x: u32) -> u32 {
            helper(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_call_vc");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_call_vc", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(!smt.is_empty(), "VC for function with calls should produce non-empty SMT output");
        assert!(!vc.rules.is_empty(), "VC should have at least one rule for the function body");
    });
}

/// Tests that translate() produces multiple rules for a branching function.
#[test]
fn test_translate_branching_produces_multiple_rules() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_branch(x: u32) -> u32 {
            if x > 10 { x + 1 } else { x - 1 }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_branch");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_branch", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();

        // Branching function should produce at least 2 rules (then + else edges)
        assert!(
            vc.rules.len() >= 2,
            "Branching function should produce at least 2 rules, got {}",
            vc.rules.len()
        );
    });
}

/// Tests that the VC emits an error relation for assertion-like patterns.
#[test]
fn test_translate_with_assert_macro() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_assert_macro(x: u32) {
            assert!(x > 0, "x must be positive");
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_assert_macro");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_assert_macro", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        // The Rust assert!() macro generates panic paths that CHC should handle
        assert!(
            !smt.is_empty(),
            "VC for assert-containing function should produce non-empty output"
        );
        assert!(
            vc.relations.iter().any(|r| r.name == "error"),
            "translate() must declare the error relation"
        );
        // Part of #2252: verify that at least one rule targets the error relation.
        // Without this, the panic path falls through to emit_goto_rule and
        // the assert!() macro produces false proofs.
        let has_error_rule = vc.rules.iter().any(|r| r.head.name == "error");
        assert!(
            has_error_rule,
            "translate() must emit at least one rule targeting error() for assert!() panic paths"
        );
    });
}

// =============================================================================
// primitive_cmp_method edge case tests (codegen_call_misc.rs)
// =============================================================================

/// Tests edge cases for primitive_cmp_method classification.
#[test]
fn test_primitive_cmp_method_edge_cases() {
    // Empty string
    assert_eq!(ChcCtx::primitive_cmp_method(""), None);

    // Only trait name, no method
    assert_eq!(ChcCtx::primitive_cmp_method("std::cmp::Ord"), None);

    // Double-colon suffix but wrong trait
    assert_eq!(ChcCtx::primitive_cmp_method("std::ops::Add::add"), None);

    // PartialEq comparisons are now handled as primitive_cmp (Part of #2196)
    assert_eq!(ChcCtx::primitive_cmp_method("std::cmp::PartialEq::eq"), Some("eq"));
    assert_eq!(ChcCtx::primitive_cmp_method("std::cmp::PartialEq::ne"), Some("ne"));

    // Full qualifying path with extra modules should still work
    assert_eq!(ChcCtx::primitive_cmp_method("std::cmp::Ord::cmp"), Some("cmp"));
    assert_eq!(ChcCtx::primitive_cmp_method("std::cmp::Ord::min"), Some("min"));
    assert_eq!(ChcCtx::primitive_cmp_method("std::cmp::Ord::max"), Some("max"));
    assert_eq!(ChcCtx::primitive_cmp_method("std::cmp::Ord::clamp"), Some("clamp"));
    assert_eq!(ChcCtx::primitive_cmp_method("core::cmp::PartialOrd::lt"), Some("lt"));
}

/// Tests step_unchecked_method edge cases.
#[test]
fn test_step_unchecked_edge_cases() {
    // Empty string
    assert_eq!(ChcCtx::step_unchecked_method(""), None);

    // Non-step method
    assert_eq!(ChcCtx::step_unchecked_method("std::cmp::Ord::cmp"), None);

    // Valid forward (returns true)
    assert_eq!(
        ChcCtx::step_unchecked_method("<u32 as std::iter::Step>::forward_unchecked"),
        Some(true)
    );

    // Valid backward (returns false)
    assert_eq!(
        ChcCtx::step_unchecked_method("<i64 as core::iter::Step>::backward_unchecked"),
        Some(false)
    );
}

/// Tests wrapping_arithmetic_method classification.
#[test]
fn test_wrapping_arithmetic_method() {
    use rustc_public::mir::BinOp;

    // Standard wrapping methods — is_unchecked = false
    assert_eq!(
        ChcCtx::wrapping_arithmetic_method("core::num::<impl u8>::wrapping_add"),
        Some((BinOp::Add, false))
    );
    assert_eq!(
        ChcCtx::wrapping_arithmetic_method("core::num::<impl u32>::wrapping_sub"),
        Some((BinOp::Sub, false))
    );
    assert_eq!(
        ChcCtx::wrapping_arithmetic_method("core::num::<impl i64>::wrapping_mul"),
        Some((BinOp::Mul, false))
    );

    // Unchecked methods — same BinOp, is_unchecked = true (Part of #3299).
    assert_eq!(
        ChcCtx::wrapping_arithmetic_method("core::num::<impl u32>::unchecked_add"),
        Some((BinOp::Add, true))
    );
    assert_eq!(
        ChcCtx::wrapping_arithmetic_method("core::num::<impl u32>::unchecked_sub"),
        Some((BinOp::Sub, true))
    );
    assert_eq!(
        ChcCtx::wrapping_arithmetic_method("core::num::<impl u32>::unchecked_mul"),
        Some((BinOp::Mul, true))
    );
    // Part of #3970: unchecked_div/rem must be recognized so fn_inline bypass works.
    assert_eq!(
        ChcCtx::wrapping_arithmetic_method("core::num::<impl u32>::unchecked_div"),
        Some((BinOp::Div, true))
    );
    assert_eq!(
        ChcCtx::wrapping_arithmetic_method("core::num::<impl u32>::unchecked_rem"),
        Some((BinOp::Rem, true))
    );

    // Non-wrapping methods
    assert_eq!(ChcCtx::wrapping_arithmetic_method("core::num::<impl u32>::checked_add"), None);
    assert_eq!(ChcCtx::wrapping_arithmetic_method("core::num::<impl u32>::saturating_add"), None);
    assert_eq!(ChcCtx::wrapping_arithmetic_method("std::ops::Add::add"), None);
    assert_eq!(ChcCtx::wrapping_arithmetic_method(""), None);
}

// =============================================================================
// is_pointer_wrapper_adt tests (codegen_expr_signedness.rs)
// =============================================================================

/// Tests the is_pointer_wrapper_adt classification.
#[test]
fn test_pointer_wrapper_adt_classification() {
    assert!(is_pointer_wrapper_adt("std::boxed::Box"));
    assert!(is_pointer_wrapper_adt("alloc::boxed::Box"));
    assert!(is_pointer_wrapper_adt("Box"));

    assert!(is_pointer_wrapper_adt("std::ptr::Unique"));
    assert!(is_pointer_wrapper_adt("Unique"));

    assert!(is_pointer_wrapper_adt("std::ptr::NonNull"));
    assert!(is_pointer_wrapper_adt("NonNull"));

    // Not pointer wrappers
    assert!(!is_pointer_wrapper_adt("Vec"));
    assert!(!is_pointer_wrapper_adt("String"));
    assert!(!is_pointer_wrapper_adt("HashMap"));
    assert!(!is_pointer_wrapper_adt(""));
}

// =============================================================================
// codegen_call_kani.rs — assertion and safety-check pipeline tests (Part of #2198)
// =============================================================================

/// Test that overflow-checked arithmetic generates an error rule via MIR Assert terminator.
/// MIR Assert terminators (from overflow checks) produce error rules directly.
#[test]
fn test_overflow_check_generates_error_rule() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_overflow(x: u32) -> u32 {
            x + 1
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_overflow");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_overflow", ChcConfig::default());

        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "overflow check VC must have an 'error' relation");

        // In debug mode, u32 + 1 generates a MIR Assert terminator for overflow
        assert!(
            vc.rules.iter().any(|r| r.head.name == "error"),
            "overflow check should generate at least one error rule"
        );
    });
}

/// Test that array bounds checks (MIR Assert terminator) produce error rules.
#[test]
fn test_bounds_check_generates_error_rule() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_bounds_check(arr: [u32; 4], idx: usize) -> u32 {
            arr[idx]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_bounds_check");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_bounds_check", ChcConfig::default());

        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "Array bounds check should produce an 'error' relation");
    });
}

/// Test that assert!() macro produces a non-trivial VC with branching.
/// Rust assert!() compiles to if !cond { panic!() } producing multiple BBs.
#[test]
fn test_assert_macro_produces_branching_vc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_assert_branching(x: u32) {
            assert!(x > 0);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_assert_branching");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_assert_branching", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert!(bb_count >= 2, "assert!() should generate at least 2 BBs, got {}", bb_count);

        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "assert!() VC must have an 'error' relation");

        // SwitchInt on the condition produces constrained transition rules
        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some() && !r.body.constraints.is_empty()),
            "assert!() should produce constrained transition rules for the branch"
        );
    });
}

/// Test that conditional panic path produces branching with guard constraints.
#[test]
fn test_conditional_panic_produces_guarded_transitions() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_cond_panic(x: u32) -> u32 {
            if x == 0 {
                panic!("zero!");
            }
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cond_panic");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_cond_panic", ChcConfig::default());

        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "conditional panic!() VC must have an 'error' relation");

        // if/else with panic produces multiple BBs with transitions
        let transition_rules: Vec<_> =
            vc.rules.iter().filter(|r| r.body.relation.is_some()).collect();
        assert!(
            transition_rules.len() >= 2,
            "if/panic path should produce >= 2 transition rules, got {}",
            transition_rules.len()
        );
    });
}

/// Test that multiple overflow-checked operations produce multiple error rules.
#[test]
fn test_multiple_overflow_checks() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_multi_overflow(x: u32, y: u32) -> u32 {
            let a = x + 1;
            let b = y + 1;
            a + b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_multi_overflow");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_multi_overflow", ChcConfig::default());

        let error_rules: Vec<_> = vc.rules.iter().filter(|r| r.head.name == "error").collect();
        assert!(
            error_rules.len() >= 2,
            "Three checked additions should produce at least 2 error rules, got {}",
            error_rules.len()
        );
    });
}

/// Part of #2303/#1739: kani::any at Mem level must mirror the nondet destination
/// into memory so a subsequent raw-pointer dereference can read a coupled value.
#[test]
fn test_kani_any_mem_level_mirrors_value_to_memory_load() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "AnyModel"]
            pub fn any<T>() -> T {
                panic!("model-only marker function")
            }
        }

        pub fn probe_kani_any_mem_mirror() -> u32 {
            let x: u32 = kani::any();
            let p = &x as *const u32;
            unsafe { *p }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_kani_any_mem_mirror");
        let body = instance.body().expect("function body");

        let reg_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_kani_any_mem_mirror", ChcConfig::default());
        let mut any_dest_local = None;
        let has_any_model = body.blocks.iter().any(|block| {
            if let rustc_public::mir::TerminatorKind::Call { func, destination, .. } =
                &block.terminator.kind
            {
                if matches!(reg_ctx.detect_kani_model(func), Some(KaniModel::Any)) {
                    any_dest_local = Some(destination.local);
                    return true;
                }
                false
            } else {
                false
            }
        });
        assert!(has_any_model, "expected at least one KaniModel::Any call in MIR");
        let any_dest_local = any_dest_local.expect("kani::any destination local");
        let any_dest_output = format!("_probe_kani_any_mem_mirror_{}__out", any_dest_local);

        let mem_vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_kani_any_mem_mirror",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let reg_vc = mir_to_chc(ctx.tcx, &body, "probe_kani_any_mem_mirror", ChcConfig::default());
        assert_vc_structure(&mem_vc, "probe_kani_any_mem_mirror_mem", body.blocks.len());
        assert_vc_structure(&reg_vc, "probe_kani_any_mem_mirror_reg", body.blocks.len());

        // After ay bump (free-variable encoding), constraints are encoded via
        // declare-var and appear in the serialized SMT-LIB2 output from emit_chc
        // rather than in the rule data structures (which have 0-arity relations).
        // Check the full SMT output for store/select patterns.
        let mem_smt_full = emit_chc(&mem_vc).to_string();
        // After ay bump (free-variable encoding), mem-level encoding uses scalar
        // at-address declare-vars (_mem_<ty>_at_<addr>) instead of Array (store ...)
        // operations. Verify mem-level encoding is distinct by checking for either:
        // - Traditional Array store: (store ...)
        // - Scalar mem at-address vars: _mem_ pattern in declare-var
        // - Memory select for obj_valid: (select obj_valid ...)
        let has_store = mem_smt_full.contains("(store ");
        let has_mem_at_addr = mem_smt_full.contains("_mem_");
        let has_select_obj_valid = mem_smt_full.contains("(select obj_valid");
        assert!(
            has_store || has_mem_at_addr || has_select_obj_valid,
            "Mem-level kani::any path should emit memory-level encoding \
             (store/at-address vars/obj_valid select) in SMT output"
        );

        assert!(
            mem_smt_full.contains(&any_dest_output),
            "Mem-level CHC encoding should reference kani::any destination output {any_dest_output}"
        );

        assert!(
            mem_smt_full.contains("(select"),
            "Mem-level dereference path should include select() reads after kani::any"
        );
    });
}

// =============================================================================
// Diverging call dispatch tests (#2587)
// =============================================================================

/// Test that a custom diverging function call (target=None, not recognized by
/// any dispatcher) emits an error() rule instead of being silently dropped.
/// This exercises the final fallback path in codegen_call.rs.
#[test]
fn test_unrecognized_diverging_call_emits_error_rule() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn custom_diverge() -> ! {
            loop {}
        }

        pub fn probe_diverging_call(x: u32) -> u32 {
            if x == 0 {
                custom_diverge();
            }
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_diverging_call");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_diverging_call", ChcConfig::default());

        assert_vc_structure(&vc, "probe_diverging_call", body.blocks.len());

        // The diverging call path should produce at least one error-headed rule.
        // Before #2587 fix, this path was silently dropped (no rule emitted).
        let has_error_rule = vc.rules.iter().any(|r| r.head.name == "error");
        assert!(
            has_error_rule,
            "diverging call path must produce error() rule — silent drop is unsound (#2587)"
        );
    });
}

/// Test that conditional panic!() (a recognized diverging call) still produces
/// error() rules as before — regression guard for the #2587 fix.
#[test]
fn test_panic_diverging_still_produces_error_rule() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_panic_diverge(x: u32) -> u32 {
            if x == 0 {
                panic!("zero not allowed");
            }
            x + 1
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_panic_diverge");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_panic_diverge", ChcConfig::default());

        assert_vc_structure(&vc, "probe_panic_diverge", body.blocks.len());

        // panic!() is a recognized diverging call — PanicError emits error() rules.
        assert!(
            vc.rules.iter().any(|r| r.head.name == "error"),
            "panic!() must emit error-headed rules (PanicError path)"
        );

        // The non-panic path should also have transition rules (x + 1 path)
        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some() && r.head.name != "error"),
            "non-panic path should produce transition rules"
        );
    });
}

#[test]
fn test_resolve_dispatch_bodies_preserve_candidate_vtable_ids() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

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
                ((self.outer_id as u16) << 8) + (self.inner.id() as u16)
            }
        }

        impl Identity for Inner {
            fn id(&self) -> u16 {
                self.id.into()
            }
        }

        pub fn probe_vtable_ids(outer_id: u8, inner_id: u8) -> u16 {
            let outer = Outer { outer_id, inner: Inner { id: inner_id } };
            let dyn_ref: &dyn Identity = &outer;
            dyn_ref.id()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vtable_ids");
        let body = instance.body().expect("probe body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vtable_ids", ChcConfig::default());

        let (fn_def, fn_args) = body
            .blocks
            .iter()
            .find_map(|block| match &block.terminator.kind {
                rustc_public::mir::TerminatorKind::Call { func, .. } => {
                    let func_ty = func.ty(body.locals()).ok()?;
                    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func_ty.kind() else {
                        return None;
                    };
                    let Ok(instance) = Instance::resolve(def, &args) else {
                        return None;
                    };
                    matches!(instance.kind, InstanceKind::Virtual { .. }).then_some((def, args))
                }
                _ => None,
            })
            .expect("probe should contain a virtual trait call");

        let trait_def_id = chc_ctx
            .resolve_parent_trait_def_id(fn_def)
            .expect("virtual call should resolve to parent trait");

        let candidates = dyn_coercion::collect_dyn_trait_candidates(&chc_ctx, trait_def_id);
        let candidate_vtable_ids: Vec<_> = candidates.iter().map(|c| c.vtable_id).collect();
        assert_eq!(
            candidate_vtable_ids,
            vec![0, 1],
            "expected merged candidates for Inner then Outer<Inner>"
        );

        let (dispatch_bodies, _dropped_resolved_candidate) =
            dyn_coercion::resolve_dispatch_bodies(&chc_ctx, &candidates, fn_def, &fn_args);
        let dispatch_vtable_ids: Vec<_> =
            dispatch_bodies.iter().map(|body| body.vtable_id).collect();
        assert_eq!(
            dispatch_vtable_ids,
            vec![0, 1],
            "dispatch resolution should preserve merged candidate vtable IDs"
        );
    });
}
