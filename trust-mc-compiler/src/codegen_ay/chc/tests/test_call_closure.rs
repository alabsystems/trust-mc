// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for codegen_call_closure.rs — closure call dispatch and inline translation.
//!
//! Part of #2303: Zero-coverage production file test addition.
//!
//! Covers:
//! - try_dispatch_call_closure: Fn::call, FnMut::call_mut, FnOnce::call_once
//! - extract_closure_env_captures: captured variable resolution
//! - extract_closure_call_args: argument tuple extraction
//! - translate_closure_body_multi_arg: inline closure body translation
//! - closure_rvalue_to_expr_inline: rvalue to AY expr in closure context
//! - ty_signedness_shallow (from trust_mc-codegen-shared): type signedness helper

#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::emit_chc;

// ═══════════════════════════════════════════════════════════════════════
// Probe sources for closure tests
// ═══════════════════════════════════════════════════════════════════════

/// Simple closure with single capture and single arg.
const SIMPLE_CLOSURE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_simple_closure(x: u32) -> u32 {
        let offset = 10u32;
        let f = |n: u32| -> u32 { n.wrapping_add(offset) };
        f(x)
    }
"#;

/// Closure with no captures (pure function).
const PURE_CLOSURE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_pure_closure(x: u32) -> u32 {
        let f = |n: u32| -> u32 { n.wrapping_mul(2) };
        f(x)
    }
"#;

/// Closure with multiple captures.
const MULTI_CAPTURE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_multi_capture(a: u32, b: u32) -> u32 {
        let x = a;
        let y = b;
        let f = |n: u32| -> u32 { n.wrapping_add(x).wrapping_add(y) };
        f(1)
    }
"#;

/// Closure used with iterator (map).
const CLOSURE_MAP_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_closure_map(x: u32) -> u32 {
        let vals = [1u32, 2, 3];
        let doubled: u32 = vals.iter().map(|v| v.wrapping_mul(2)).sum();
        doubled.wrapping_add(x)
    }
"#;

/// Closure with two arguments.
const TWO_ARG_CLOSURE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_two_arg_closure(x: u32, y: u32) -> u32 {
        let f = |a: u32, b: u32| -> u32 { a.wrapping_add(b) };
        f(x, y)
    }
"#;

/// Exact strict-boundary shape from tests/ay/test_closure_vec_len.rs.
const CLOSURE_CAPTURED_VEC_LEN_ASSUME_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            panic!("model-only marker function")
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(_cond: bool) {}
    }

    pub fn probe_closure_captured_vec_len_assume() {
        let v = vec![1u32, 2, 3];
        let check = |idx: &usize| *idx < v.len();
        let idx: usize = kani::any();
        kani::assume(check(&idx));
        assert!(idx < 3);
    }
"#;

/// Non-capturing closure coerced to a fn pointer with address-taken ZST params.
/// The fn-ptr call must be in the probe's own body (not behind an `invoke`
/// wrapper) so that `mir_to_chc` on the probe function sees the FnPtr call
/// and triggers the ZST address hint path.
const FN_PTR_ZST_PARAM_SOURCE: &str = r#"
    #![allow(dead_code)]

    struct Void;

    pub fn probe_fn_ptr_zst_param_addrs(input: usize) -> usize {
        let closure = |a: Void, out: usize, b: Void| -> usize {
            assert!(&a as *const Void != std::ptr::null::<Void>());
            assert!(&b as *const Void != std::ptr::null::<Void>());
            out
        };
        let f: fn(Void, usize, Void) -> usize = closure;
        f(Void, input, Void)
    }
"#;

/// Full-harness-style fn-pointer closure source matching the real compiletest
/// shape more closely: kani any/cover markers, messageful assertions, and the
/// outer assert_eq! on the returned value.
const FN_PTR_ZST_PARAM_FULL_HARNESS_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            panic!("model-only marker function")
        }

        #[kanitool::fn_marker = "CoverHook"]
        pub fn cover(_cond: bool, _msg: &'static str) {}
    }

    struct Void;

    #[inline(never)]
    fn invoke(input: usize, f: fn(Void, usize, Void) -> usize) -> usize {
        kani::cover(true, "cover location");
        f(Void, input, Void)
    }

    pub fn probe_fn_ptr_zst_param_full_harness() {
        let input: usize = kani::any();
        let closure = |a: Void, out: usize, b: Void| -> usize {
            kani::cover(true, "cover location");
            assert!(&a as *const Void != std::ptr::null(), "Should succeed");
            assert!(&b as *const Void != std::ptr::null(), "Should succeed");
            out
        };
        let output = invoke(input, closure);
        assert_eq!(output, input);
    }
"#;

/// No closure — control case to verify dispatch returns false.
const NO_CLOSURE_SOURCE: &str = r#"
    #![allow(dead_code)]

    fn helper(x: u32) -> u32 { x.wrapping_add(1) }

    pub fn probe_no_closure(x: u32) -> u32 {
        helper(x)
    }
"#;

fn assert_inline_zst_addr_is_concrete(vc: &trust_mc_core::chc::ChcVc, fn_name: &str) {
    let smt = emit_chc(vc).to_string();
    assert!(
        !smt.contains("__inline_zst_addr"),
        "{fn_name}: inline ZST parameter addresses should be concrete constants, not symbolic vars"
    );
    assert!(
        !smt.contains("(bvor (bvand"),
        "{fn_name}: inline ZST parameter addresses should not require HORN BV non-null reasoning"
    );
}

/// Closure that lowers to CheckedBinaryOp + Assert in debug MIR.
const CHECKED_BINOP_CLOSURE_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[inline(never)]
    fn call_closure_indirect<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
        f(x)
    }

    pub fn probe_checked_binop_closure(x: i32) -> i32 {
        let offset = 7i32;
        let add_offset = |n: i32| -> i32 { n + offset };
        call_closure_indirect(add_offset, x)
    }
"#;

/// Boxed dyn FnOnce call that previously missed the closure lane and fell into
/// Box/layout inline fallback paths.
const BOXED_DYN_FN_ONCE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_boxed_dyn_fn_once() {
        let f: Box<dyn FnOnce(f32, i32)> = Box::new(|x, y| {
            assert!(x == 1.0);
            assert!(y == 2);
        });
        f(1.0, 2);
    }
"#;

/// Multiple dyn-callable closures with distinct signatures, mirroring the
/// `nested_closures` regression shape. The closure lane should resolve each
/// call without falling through to virtual dispatch.
const MULTI_SIGNATURE_DYN_CALLABLE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_multi_signature_dyn_callable() {
        let f: Box<Box<dyn FnOnce(i32)>> = Box::new(Box::new(|x| assert!(x == 1)));
        f(1);

        let g = |x: f32, y: i32| {
            assert!(x == 1.0);
            assert!(y == 2);
        };
        let p: &dyn Fn(f32, i32) = &g;
        p(1.0, 2);

        let r: Box<&dyn Fn(f32, i32, bool)> = Box::new(&|x: f32, y: i32, z: bool| {
            assert!(x == 1.0);
            assert!(y == 2);
            assert!(z);
        });
        r(1.0, 2, true);
    }
"#;

/// Direct `kani_register_contract(closure)` call: CHC should treat this as an
/// immediate zero-arg closure invocation instead of falling through to
/// inferable summaries.
const REGISTER_CONTRACT_DIRECT_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    #[inline(never)]
    #[kanitool::fn_marker = "kani_register_contract"]
    const fn kani_register_contract<T, F: FnOnce() -> T>(_f: F) -> T {
        unreachable!()
    }

    pub fn probe_register_contract_direct(x: u32) -> u32 {
        let bias = 1u32;
        let closure = || -> u32 { x.wrapping_add(bias) };
        kani_register_contract(closure)
    }
"#;

/// Nested `kani_register_contract(closure)` inside a helper body. This matches
/// the remaining `#1836` contract-shim path more closely: CHC fn-inline must
/// inline the helper, then the nested walker must inline the register-contract
/// closure without producing inferable summaries.
const REGISTER_CONTRACT_NESTED_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    #[inline(never)]
    #[kanitool::fn_marker = "kani_register_contract"]
    const fn kani_register_contract<T, F: FnOnce() -> T>(_f: F) -> T {
        unreachable!()
    }

    #[inline(never)]
    fn helper(x: u32) -> u32 {
        let bias = 1u32;
        let closure = || -> u32 { x.wrapping_add(bias) };
        kani_register_contract(closure)
    }

    pub fn probe_register_contract_nested(x: u32) -> u32 {
        helper(x)
    }
"#;

// ═══════════════════════════════════════════════════════════════════════
// Full pipeline tests (mir_to_chc)
// ═══════════════════════════════════════════════════════════════════════

/// Verify that a simple closure call generates a valid VC.
#[test]
fn test_closure_simple_generates_vc() {
    with_test_ay_ctx_for_source(SIMPLE_CLOSURE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple_closure");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_simple_closure", ChcConfig::default());

        assert_vc_structure(&vc, "probe_simple_closure", body.blocks.len());
        assert!(!vc.rules.is_empty(), "closure call should produce CHC rules");
    });
}

/// Verify that a pure closure (no captures) generates a valid VC.
#[test]
fn test_closure_pure_generates_vc() {
    with_test_ay_ctx_for_source(PURE_CLOSURE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_pure_closure");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_pure_closure", ChcConfig::default());

        assert_vc_structure(&vc, "probe_pure_closure", body.blocks.len());

        // Pure closure with wrapping_mul on u32 should have bv32 sorts
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "pure closure over u32 should have bv32 sort");
    });
}

/// Verify that multi-capture closure generates a valid VC.
#[test]
fn test_closure_multi_capture_generates_vc() {
    with_test_ay_ctx_for_source(MULTI_CAPTURE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_multi_capture");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_multi_capture", ChcConfig::default());

        assert_vc_structure(&vc, "probe_multi_capture", body.blocks.len());

        // Multi-capture closure with u32 args should have bv32 sorts
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "multi-capture closure over u32 should have bv32 sort");
    });
}

#[test]
fn test_register_contract_direct_avoids_inferable_predicates() {
    with_test_ay_ctx_for_source(REGISTER_CONTRACT_DIRECT_SOURCE, |ctx| {
        let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let _ = crate::codegen_ay::take_inferable_predicate_count();

        let instance = find_instance_by_suffix(ctx.tcx, "probe_register_contract_direct");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc_with_instance(
            ctx.tcx,
            &body,
            instance,
            "probe_register_contract_direct",
            ChcConfig::default(),
        );

        let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
        assert_eq!(
            inferable_count, 0,
            "kani_register_contract direct call should not emit inferable summaries"
        );
        assert!(
            !vc.rules.is_empty(),
            "direct register-contract probe should still produce CHC rules"
        );
    });
}

#[test]
fn test_register_contract_nested_inline_avoids_inferable_predicates() {
    with_test_ay_ctx_for_source(REGISTER_CONTRACT_NESTED_SOURCE, |ctx| {
        let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let _ = crate::codegen_ay::take_inferable_predicate_count();

        let instance = find_instance_by_suffix(ctx.tcx, "probe_register_contract_nested");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc_with_instance(
            ctx.tcx,
            &body,
            instance,
            "probe_register_contract_nested",
            ChcConfig::default(),
        );

        let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
        assert_eq!(
            inferable_count, 0,
            "nested register-contract inline should not emit inferable summaries"
        );
        assert!(
            !vc.rules.is_empty(),
            "nested register-contract probe should still produce CHC rules"
        );
    });
}

/// Verify that closure with iterator (map) generates a valid VC.
#[test]
fn test_closure_map_generates_vc() {
    with_test_ay_ctx_for_source(CLOSURE_MAP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_closure_map");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_closure_map", ChcConfig::default());

        assert_vc_structure(&vc, "probe_closure_map", body.blocks.len());

        // Closure with iterator map on u32 values should have bv32 sorts
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "closure map over u32 should have bv32 sort");
    });
}

/// Verify two-argument closure generates a valid VC.
#[test]
fn test_closure_two_arg_generates_vc() {
    with_test_ay_ctx_for_source(TWO_ARG_CLOSURE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_two_arg_closure");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_two_arg_closure", ChcConfig::default());

        assert_vc_structure(&vc, "probe_two_arg_closure", body.blocks.len());

        // Two-arg closure with u32 should have bv32 sorts
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "two-arg closure over u32 should have bv32 sort");
    });
}

#[test]
fn test_closure_captured_vec_len_assume_emits_strict_unsigned_bound() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();

    with_test_ay_ctx_for_source(CLOSURE_CAPTURED_VEC_LEN_ASSUME_SOURCE, |ctx| {
        let fn_name = "probe_closure_captured_vec_len_assume";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert!(has_any_constraints(&vc), "{fn_name} should constrain the VC");

        let inferable_decls: Vec<_> = vc
            .vars()
            .iter()
            .filter(|decl| decl.name.contains("P_inf"))
            .map(|decl| decl.name.clone())
            .collect();
        assert!(
            inferable_decls.is_empty(),
            "{fn_name} should inline captured closure refs without inferable summaries: {inferable_decls:?}"
        );

        let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "{fn_name} should avoid CHC fallback while lowering captured closure refs"
        );

        let has_strict_unsigned_bound = vc.rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|constraint| {
                constraint_tree_contains(constraint, &|expr| {
                    matches!(expr.value(), ExprValue::BvULt(_, _))
                })
            }) || rule.head.args.iter().any(|arg| {
                constraint_tree_contains(arg, &|expr| {
                    matches!(expr.value(), ExprValue::BvULt(_, _))
                })
            })
        });
        assert!(
            has_strict_unsigned_bound,
            "{fn_name} should emit a strict unsigned bound for the closure predicate"
        );

        let smt = emit_chc(&vc).to_string();
        assert!(smt.contains("bvult"), "{fn_name} SMT should contain strict unsigned comparison");
    });

    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
}

/// fn-pointer closure inline must preserve address identity for address-taken
/// ZST params instead of reusing the raw parameter value expression.
#[test]
fn test_fn_ptr_closure_zst_param_addresses_use_pointer_hints() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = crate::codegen_ay::take_place_translation_drop_count();
    let _ = crate::codegen_ay::take_unhandled_call_by_fn();

    with_test_ay_ctx_for_source(FN_PTR_ZST_PARAM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_fn_ptr_zst_param_addrs");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_fn_ptr_zst_param_addrs", ChcConfig::default());

        assert!(
            vc.relations.iter().any(|relation| relation.name.contains("__bb0")),
            "fn-pointer ZST closure should declare an entry relation"
        );
        assert!(!vc.rules.is_empty(), "fn-pointer ZST closure should produce CHC rules");
        assert_inline_zst_addr_is_concrete(&vc, "probe_fn_ptr_zst_param_addrs");

        let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
        assert_eq!(
            unhandled_calls.get("probe_fn_ptr_zst_param_addrs").copied().unwrap_or(0),
            0,
            "fn-pointer ZST closure should not increment unhandled-call counters, map={unhandled_calls:?}"
        );

        // Global place_translation_drop_count is racy under parallel test
        // execution — drain but don't assert on the global counter (#3960).
        let _ = crate::codegen_ay::take_place_translation_drop_count();
    });
}

/// The full compiletest-style fn-pointer harness must not fall through to
/// unhandled inline calls once ZST address identity is modeled.
#[test]
fn test_fn_ptr_closure_zst_param_full_harness_has_no_unhandled_calls() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = crate::codegen_ay::take_place_translation_drop_count();
    let _ = crate::codegen_ay::take_unhandled_call_by_fn();

    with_test_ay_ctx_for_source(FN_PTR_ZST_PARAM_FULL_HARNESS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_fn_ptr_zst_param_full_harness");
        let body = instance.body().expect("function body");

        let vc =
            mir_to_chc(ctx.tcx, &body, "probe_fn_ptr_zst_param_full_harness", ChcConfig::default());

        assert_vc_structure(&vc, "probe_fn_ptr_zst_param_full_harness", body.blocks.len());
        assert!(!vc.rules.is_empty(), "full fn-pointer ZST harness should produce CHC rules");
        assert_inline_zst_addr_is_concrete(&vc, "probe_fn_ptr_zst_param_full_harness");

        let unhandled_calls = crate::codegen_ay::take_unhandled_call_by_fn();
        assert_eq!(
            unhandled_calls.get("probe_fn_ptr_zst_param_full_harness").copied().unwrap_or(0),
            0,
            "full fn-pointer ZST harness should have zero unhandled calls, map={unhandled_calls:?}"
        );

        let place_drop_count = crate::codegen_ay::take_place_translation_drop_count();
        assert_eq!(
            place_drop_count, 0,
            "full fn-pointer ZST harness should translate without sound fallbacks, got {place_drop_count}",
        );
    });
}

/// Verify no-closure source works (control case — dispatch fallthrough).
#[test]
fn test_no_closure_dispatch_fallthrough() {
    with_test_ay_ctx_for_source(NO_CLOSURE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_no_closure");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_no_closure", ChcConfig::default());

        assert_vc_structure(&vc, "probe_no_closure", body.blocks.len());

        // No-closure control case with u32 should still have bv32 sorts
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "no-closure function with u32 should have bv32 sort");
    });
}

/// CheckedBinaryOp closure source should compile through CHC pipeline without
/// fail-closed `false` transition constraints.
#[test]
fn test_checked_binop_closure_generates_vc_without_fail_closed_constraints() {
    with_test_ay_ctx_for_source(CHECKED_BINOP_CLOSURE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_binop_closure");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_checked_binop_closure", ChcConfig::default());

        assert_vc_structure(&vc, "probe_checked_binop_closure", body.blocks.len());

        let fail_closed_constraints = vc
            .rules
            .iter()
            .flat_map(|r| &r.body.constraints)
            .filter(|c| matches!(c.value(), ExprValue::BoolConst(false)))
            .count();
        assert_eq!(
            fail_closed_constraints, 0,
            "checked-binop closure should not emit fail-closed false constraints"
        );
    });
}

/// Box<dyn FnOnce(... )> should stay in the closure dispatch lane and avoid the
/// fail-closed `false` constraints emitted when inline translation misses.
#[test]
fn test_boxed_dyn_fn_once_generates_vc_without_fail_closed_constraints() {
    with_test_ay_ctx_for_source(BOXED_DYN_FN_ONCE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_boxed_dyn_fn_once");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_boxed_dyn_fn_once", ChcConfig::default());

        assert_vc_structure(&vc, "probe_boxed_dyn_fn_once", body.blocks.len());
        assert!(!vc.rules.is_empty(), "boxed dyn FnOnce call should produce CHC rules");

        let fail_closed_constraints = vc
            .rules
            .iter()
            .flat_map(|r| &r.body.constraints)
            .filter(|c| matches!(c.value(), ExprValue::BoolConst(false)))
            .count();
        assert_eq!(
            fail_closed_constraints, 0,
            "boxed dyn FnOnce call should not emit fail-closed false constraints"
        );
    });
}

/// A mixed-signature dyn-callable body should still go through the closure lane
/// and build CHC rules instead of panicking during virtual dispatch candidate
/// resolution.
#[test]
fn test_multi_signature_dyn_callable_generates_vc_without_fail_closed_constraints() {
    with_test_ay_ctx_for_source(MULTI_SIGNATURE_DYN_CALLABLE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_multi_signature_dyn_callable");
        let body = instance.body().expect("function body");

        let vc =
            mir_to_chc(ctx.tcx, &body, "probe_multi_signature_dyn_callable", ChcConfig::default());

        assert_vc_structure(&vc, "probe_multi_signature_dyn_callable", body.blocks.len());
        assert!(!vc.rules.is_empty(), "mixed dyn-callable source should produce CHC rules");

        let fail_closed_constraints = vc
            .rules
            .iter()
            .flat_map(|r| &r.body.constraints)
            .filter(|c| matches!(c.value(), ExprValue::BoolConst(false)))
            .count();
        assert_eq!(
            fail_closed_constraints, 0,
            "mixed dyn-callable source should stay on the closure lane without fail-closed fallbacks"
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// ChcCtx-level tests: closure detection and MIR structure
// ═══════════════════════════════════════════════════════════════════════

/// Verify MIR for simple closure contains a Closure-type aggregate.
#[test]
fn test_closure_mir_has_closure_aggregate() {
    with_test_ay_ctx_for_source(SIMPLE_CLOSURE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple_closure");
        let body = instance.body().expect("function body");

        let mut found_closure_aggregate = false;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let rustc_public::mir::StatementKind::Assign(
                    _,
                    rustc_public::mir::Rvalue::Aggregate(
                        rustc_public::mir::AggregateKind::Closure(_, _),
                        _,
                    ),
                ) = &stmt.kind
                {
                    found_closure_aggregate = true;
                }
            }
        }
        assert!(
            found_closure_aggregate,
            "simple closure should produce a Closure aggregate in MIR"
        );
    });
}

/// Verify multi-capture closure has multiple fields in the Closure aggregate.
#[test]
fn test_multi_capture_closure_fields() {
    with_test_ay_ctx_for_source(MULTI_CAPTURE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_multi_capture");
        let body = instance.body().expect("function body");

        let mut max_capture_fields = 0;
        for block in &body.blocks {
            for stmt in &block.statements {
                if let rustc_public::mir::StatementKind::Assign(
                    _,
                    rustc_public::mir::Rvalue::Aggregate(
                        rustc_public::mir::AggregateKind::Closure(_, _),
                        fields,
                    ),
                ) = &stmt.kind
                {
                    max_capture_fields = max_capture_fields.max(fields.len());
                }
            }
        }
        assert!(
            max_capture_fields >= 2,
            "multi-capture closure should have at least 2 fields, found {}",
            max_capture_fields
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Mem track level tests
// ═══════════════════════════════════════════════════════════════════════

/// Verify closure handling at Mem track level.
#[test]
fn test_closure_mem_track_level() {
    with_test_ay_ctx_for_source(SIMPLE_CLOSURE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple_closure");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_simple_closure",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_simple_closure", body.blocks.len());

        // Closure at Mem track level should still have bv32 sorts for u32
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "closure at Mem level should have bv32 sort for u32");
    });
}

/// Verify closure handling with wide memory model.
#[test]
fn test_closure_wide_mem() {
    with_test_ay_ctx_for_source(SIMPLE_CLOSURE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_simple_closure");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_simple_closure",
            ChcConfig { wide_mem: WideMemMode::On, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_simple_closure", body.blocks.len());

        // Closure with wide memory should still have bv32 sorts for u32
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "closure with wide mem should have bv32 sort for u32");
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Error-path tests: closure translation failure / fail-closed paths
// ═══════════════════════════════════════════════════════════════════════
//
// Part of #2627: error-path test coverage gaps.
// Closures that are too complex for inline translation hit None-return
// paths in translate_closure_body_multi_arg. The pipeline handles this
// gracefully (fail-closed), but we verify it doesn't panic.

/// Closure with branching (if/else) generates SwitchInt in MIR, which is an
/// unsupported terminator for inline closure translation (line 395).
/// Pipeline should still produce a valid VC via fail-closed path.
const BRANCHING_CLOSURE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_branching_closure(x: u32) -> u32 {
        let threshold = 10u32;
        let f = |n: u32| -> u32 {
            if n > threshold { n.wrapping_sub(threshold) } else { 0 }
        };
        f(x)
    }
"#;

#[test]
fn test_closure_with_branch_does_not_panic() {
    with_test_ay_ctx_for_source(BRANCHING_CLOSURE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_branching_closure");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_branching_closure", ChcConfig::default());

        // Pipeline should produce rules even when closure inline translation fails
        assert!(!vc.rules.is_empty(), "branching closure should produce VC rules (fail-closed)");
        assert!(!vc.relations.is_empty(), "branching closure should produce relations");
    });
}

/// Closure with a loop generates cyclic CFG that exhausts the block-walk
/// visitor (line 352). Pipeline should handle gracefully.
const LOOP_CLOSURE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_loop_closure(x: u32) -> u32 {
        let f = |mut n: u32| -> u32 {
            let mut acc = 0u32;
            while n > 0 {
                acc = acc.wrapping_add(n);
                n = n.wrapping_sub(1);
            }
            acc
        };
        f(x)
    }
"#;

#[test]
fn test_closure_with_loop_does_not_panic() {
    with_test_ay_ctx_for_source(LOOP_CLOSURE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_loop_closure");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_loop_closure", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "loop closure should produce VC rules (fail-closed)");
        assert!(!vc.relations.is_empty(), "loop closure should produce relations");
    });
}

/// Closure that calls a multi-block helper function triggers inline failure
/// at try_inline_closure_call (line 445: >1 block). Pipeline should handle.
const MULTI_BLOCK_CALL_CLOSURE_SOURCE: &str = r#"
    #![allow(dead_code)]

    fn complex_helper(n: u32) -> u32 {
        if n > 5 { n.wrapping_mul(2) } else { n.wrapping_add(1) }
    }

    pub fn probe_complex_call_closure(x: u32) -> u32 {
        let f = |n: u32| -> u32 { complex_helper(n) };
        f(x)
    }
"#;

#[test]
fn test_closure_calling_multi_block_fn_does_not_panic() {
    with_test_ay_ctx_for_source(MULTI_BLOCK_CALL_CLOSURE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_complex_call_closure");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_complex_call_closure", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "closure calling multi-block fn should produce rules");
        assert!(!vc.relations.is_empty(), "multi-block closure should produce relations");
    });
}
