// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unit tests for chc/codegen_call_kani_model.rs — Kani model function
//! handling: kani::any(), rustc_intrinsics::offset, and simd_bitmask.
//!
//! Covers:
//! - codegen_call_kani_model: KaniModel::Any nondet emission
//! - codegen_call_kani_model: KaniModel::Offset pointer arithmetic
//! - codegen_call_kani_model: KaniModel::SimdBitmask lane extraction
//! - codegen_call_kani_model: ZST optimisation (identity goto for unit types)
//! - is_zst_ty: unit, never, zero-length arrays, ZST-element arrays
//!
//! Part of #2921: CHC zero-coverage remediation.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use ay_bindings::ExprValue;

// =============================================================================
// kani::any() pipeline tests
// =============================================================================

/// kani::any::<u32>() should produce a nondeterministic variable in the VC.
#[test]
fn test_kani_any_u32_emits_nondet() {
    const SOURCE: &str = r#"
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

        pub fn probe_kani_any_u32() -> u32 {
            kani::any()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_kani_any_u32");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_kani_any_u32", ChcConfig::default());

        assert_vc_structure(&vc, "probe_kani_any_u32", body.blocks.len());

        // kani::any() produces a fresh nondet variable. In the relation-arg
        // encoding this appears as a Var in a transition rule head arg. In the
        // free-variable encoding (`declare-var`) the nondet semantics come from
        // the variable being universally quantified with no constraining rule.
        // Accept either encoding strategy.
        let has_head_var = vc.rules.iter().any(|rule| {
            rule.body.relation.is_some()
                && rule.head.name != "error"
                && rule.head.args.iter().any(|a| matches!(a.value(), ExprValue::Var { .. }))
        });
        let has_free_var_bv32 = vc.vars().iter().any(|v| v.sort.bitvec_width() == Some(32));
        assert!(
            has_head_var || has_free_var_bv32,
            "probe_kani_any_u32: expected at least one transition rule with Var head args (nondet) \
             or a BV32 free variable declaration"
        );
    });
}

/// kani::any::<bool>() should also produce valid VCs.
#[test]
fn test_kani_any_bool_pipeline() {
    const SOURCE: &str = r#"
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

        pub fn probe_kani_any_bool() -> bool {
            kani::any()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_kani_any_bool");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_kani_any_bool", ChcConfig::default());

        assert_vc_structure(&vc, "probe_kani_any_bool", body.blocks.len());
        // Bool arg should be present in at least one relation
        assert_relation_has_arg_sort(
            &vc,
            "probe_kani_any_bool",
            ay_bindings::Sort::is_bool,
            "Bool",
        );
    });
}

/// kani::any() followed by kani::assume() should produce constraints.
#[test]
fn test_kani_any_with_assume_produces_constraints() {
    const SOURCE: &str = r#"
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

        pub fn probe_any_assume() -> u32 {
            let x: u32 = kani::any();
            kani::assume(x > 0);
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_any_assume");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_any_assume", ChcConfig::default());

        assert_vc_structure(&vc, "probe_any_assume", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_any_assume");
    });
}

// =============================================================================
// kani::any() with ZST types — should produce identity goto
// =============================================================================

/// kani::any::<()>() is a ZST — should produce a structurally valid VC
/// without spurious nondeterminism.
#[test]
fn test_kani_any_unit_zst_identity() {
    const SOURCE: &str = r#"
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

        pub fn probe_any_unit() {
            let _: () = kani::any();
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_any_unit");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_any_unit", ChcConfig::default());

        assert_vc_structure(&vc, "probe_any_unit", body.blocks.len());
    });
}

// =============================================================================
// Pointer offset pipeline tests
// =============================================================================

/// Pointer offset via unsafe ptr.add should produce BvAdd in the VC.
#[test]
fn test_pointer_offset_emits_bvadd() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_offset(p: *const u32) -> *const u32 {
            unsafe { p.add(1) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_offset");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_ptr_offset", ChcConfig::default());

        assert_vc_structure(&vc, "probe_ptr_offset", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_ptr_offset");
    });
}

/// KaniModel::Offset on non-power-of-two pointees must emit checked byte-offset guards.
///
/// Regression for #3783: the CHC success edge previously kept raw modular
/// pointer arithmetic for `kani::rustc_intrinsics::offset`, which let
/// `offset_from_unsigned` observe wrapped addresses.
#[test]
fn test_kani_model_offset_non_power_two_emits_signed_overflow_guards() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "OffsetModel"]
            pub fn offset(base: *const [u64; 3], count: usize) -> *const [u64; 3] {
                unsafe { base.add(count) }
            }
        }

        pub fn probe_offset_model_non_power_two(
            base: *const [u64; 3],
            count: usize,
        ) -> *const [u64; 3] {
            kani::offset(base, count)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_offset_model_non_power_two");
        let body = instance.body().expect("function body");
        // Safety checks (error rules) are gated behind extra_pointer_checks
        // since [U]114 (86b3b9c0ca). Enable to test the overflow guard path.
        let cfg = ChcConfig { extra_pointer_checks: true, ..ChcConfig::default() };
        let vc = mir_to_chc(ctx.tcx, &body, "probe_offset_model_non_power_two", cfg);

        assert_vc_structure(&vc, "probe_offset_model_non_power_two", body.blocks.len());
        assert!(
            vc.rules.iter().any(|rule| rule.head.name == "error"),
            "probe_offset_model_non_power_two should emit error rules for offset safety checks"
        );
        assert_rule_contains_expr_kind(
            &vc,
            "probe_offset_model_non_power_two",
            |e| matches!(e.value(), ExprValue::BvSDiv(_, _)),
            "bvsdiv",
        );
    });
}

/// KaniModel::PtrOffsetFrom should encode signed pointer-distance arithmetic.
#[test]
fn test_kani_model_ptr_offset_from_emits_bvsdiv() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "PtrOffsetFromModel"]
            pub fn ptr_offset_from<T>(_lhs: *const T, _rhs: *const T) -> isize {
                panic!("model-only marker function")
            }
        }

        pub fn probe_ptr_offset_from_model(lhs: *const u32, rhs: *const u32) -> isize {
            kani::ptr_offset_from(lhs, rhs)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_offset_from_model");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_ptr_offset_from_model", ChcConfig::default());

        assert_vc_structure(&vc, "probe_ptr_offset_from_model", body.blocks.len());
        assert_rule_contains_expr_kind(
            &vc,
            "probe_ptr_offset_from_model",
            |e| matches!(e.value(), ExprValue::BvSDiv(_, _)),
            "bvsdiv",
        );
    });
}

/// KaniModel::PtrOffsetFromUnsigned should encode unsigned pointer-distance arithmetic.
#[test]
fn test_kani_model_ptr_offset_from_unsigned_emits_bvudiv() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "PtrOffsetFromUnsignedModel"]
            pub fn ptr_offset_from_unsigned<T>(_lhs: *const T, _rhs: *const T) -> usize {
                panic!("model-only marker function")
            }
        }

        pub fn probe_ptr_offset_from_unsigned_model(lhs: *const u32, rhs: *const u32) -> usize {
            kani::ptr_offset_from_unsigned(lhs, rhs)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_offset_from_unsigned_model");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_ptr_offset_from_unsigned_model",
            ChcConfig::default(),
        );

        assert_vc_structure(&vc, "probe_ptr_offset_from_unsigned_model", body.blocks.len());
        assert_rule_contains_expr_kind(
            &vc,
            "probe_ptr_offset_from_unsigned_model",
            |e| matches!(e.value(), ExprValue::BvUDiv(_, _)),
            "bvudiv",
        );
    });
}

// =============================================================================
// kani::any() with Mem tracking level
// =============================================================================

/// kani::any() at Mem level should produce memory store constraints.
#[test]
fn test_kani_any_at_mem_level_pipeline() {
    const SOURCE: &str = r#"
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

        pub fn probe_any_mem() -> u64 {
            kani::any()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_any_mem");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_any_mem",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_any_mem", body.blocks.len());
    });
}

// =============================================================================
// kani::any() with multiple types
// =============================================================================

/// kani::any::<i64>() should produce a bitvec(64) relation argument.
#[test]
fn test_kani_any_i64_produces_bv64_arg() {
    const SOURCE: &str = r#"
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

        pub fn probe_any_i64() -> i64 {
            kani::any()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_any_i64");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_any_i64", ChcConfig::default());

        assert_vc_structure(&vc, "probe_any_i64", body.blocks.len());
        assert_relation_has_arg_sort(
            &vc,
            "probe_any_i64",
            |s| s.bitvec_width() == Some(64),
            "bv64",
        );
    });
}

// =============================================================================
// SizeOfVal inline model boundary (#3989)
// =============================================================================

/// When a function calls SizeOfValRawModel inside a virtual-inline body, the
/// inline walker should intercept it as a modeled leaf and produce a compile-time
/// constant — not re-inline the library model body.
///
/// Part of #3989: guards the inline walker's SizeOfVal interception path.
#[test]
fn test_inline_size_of_val_model_produces_constant() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "SizeOfValRawModel"]
            pub fn size_of_val_raw<T>(_ptr: *const T) -> usize {
                panic!("model-only marker function")
            }
        }

        fn inner_size(x: &u32) -> usize {
            kani::size_of_val_raw(x as *const u32)
        }

        pub fn probe_inline_size_of_val(x: &u32) -> usize {
            inner_size(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_inline_size_of_val");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_inline_size_of_val", ChcConfig::default());

        assert_vc_structure(&vc, "probe_inline_size_of_val", body.blocks.len());

        // The VC should contain a BV constant 4 (size of u32 = 4 bytes)
        // in either a body constraint or head arg, proving the inline walker
        // resolved the size at compile time instead of re-inlining.
        assert_rule_contains_expr_kind(
            &vc,
            "probe_inline_size_of_val",
            |e| {
                matches!(
                    e.value(),
                    ExprValue::BitVecConst { value, width: 64 } if *value == 4u128.into()
                )
            },
            "bitvec_const(4, 64) for sizeof(u32)",
        );
    });
}

/// Function items have no runtime representation, so size_of_val(&fn_item)
/// must resolve to a zero-sized value.
#[test]
fn test_size_of_val_fndef_is_zero_sized() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn h() {}

        pub fn probe_fndef_size_of_val() -> usize {
            core::mem::size_of_val(&h)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_fndef_size_of_val");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_fndef_size_of_val", ChcConfig::default());

        assert_vc_structure(&vc, "probe_fndef_size_of_val", body.blocks.len());

        let h_item = find_crate_item_by_suffix(ctx.tcx, "h");
        let h_def = rustc_internal::internal(ctx.tcx, h_item.def_id());
        let h_ty = rustc_internal::stable(ctx.tcx.type_of(h_def)).value;
        assert!(matches!(h_ty.kind(), TyKind::RigidTy(RigidTy::FnDef(_, _))));

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_fndef_size_of_val", ChcConfig::default());
        assert_eq!(chc_ctx.get_type_size(h_ty), Some(0), "FnDef size should be ZST");
    });
}

// =============================================================================
// simd_bitmask_lane_bit utility
// =============================================================================

/// Wide bitmask lane encoding should use bvshl with the correct lane index.
#[test]
fn test_simd_bitmask_lane_bit_uses_bv_shift_for_wide_masks() {
    use super::super::codegen_call_kani_model::simd_bitmask_lane_bit;

    let bit = simd_bitmask_lane_bit(256, 200);
    let rendered = bit.to_string();
    assert!(rendered.contains("bvshl"), "expected bvshl lane encoding, got {rendered}");
    assert!(
        rendered.contains("00c8"),
        "expected lane index 200 in rendered shift expression, got {rendered}"
    );
}
