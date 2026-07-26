// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// =============================================================================
// codegen_call_misc.rs — Option/Result predicate and unwrap coverage (Part of #2188)
// =============================================================================

#[test]
fn test_mir_to_chc_option_is_some_predicate() {
    // (#2188) Exercise codegen_call_option_predicate: Option::is_some generates
    // a discriminant check constraint in the CHC output.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_is_some(opt: Option<u32>) -> bool {
            opt.is_some()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_is_some");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_is_some", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_option_is_some", bb_count);

        // After flattening (#2214), Option<u32> is encoded as (Bool, BV32) scalar
        // state vars — no Datatype sorts should remain.
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(
            has_bool,
            "Option::is_some VC should have Bool state vars from flattened Option discriminant"
        );

        // After flattening, no relation argument should have Datatype sort.
        // Note: `declare-datatype` may still appear in the SMT output as infrastructure
        // for translate_place Datatype reconstruction (#2970), but the state variables
        // themselves must be scalar.
        let has_datatype_arg =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_datatype));
        assert!(
            !has_datatype_arg,
            "flattened Option relations should not have Datatype-sorted arguments"
        );
    });
}

#[test]
fn test_mir_to_chc_option_is_none_predicate() {
    // (#2188) Exercise codegen_call_option_predicate for is_none (negation of is_some).
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_is_none(opt: Option<u32>) -> bool {
            opt.is_none()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_is_none");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_is_none", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_option_is_none", bb_count);

        // After flattening (#2214), Option<u32> is (Bool, BV32) — Bool for discriminant
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(
            has_bool,
            "Option::is_none VC should have Bool state vars from flattened Option discriminant"
        );

        // After flattening, no relation argument should have Datatype sort.
        // Note: `declare-datatype` may still appear in SMT output as infrastructure
        // for translate_place Datatype reconstruction (#2970).
        let has_datatype_arg =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_datatype));
        assert!(
            !has_datatype_arg,
            "flattened Option relations should not have Datatype-sorted arguments"
        );
    });
}

#[test]
fn test_mir_to_chc_option_unwrap_or() {
    // (#2188) Exercise codegen_call_unwrap_or for Option::unwrap_or.
    // Translates unwrap_or(self, default) to ITE(is_some, inner, default).
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_unwrap_or(opt: Option<u32>) -> u32 {
            opt.unwrap_or(42)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unwrap_or");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_unwrap_or", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_unwrap_or", bb_count);

        // unwrap_or returns u32 → should have BV32 state vars
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "Option::unwrap_or VC should have BV32 state vars for u32 return");

        // After flattening, no relation argument should have Datatype sort.
        let has_datatype_arg =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_datatype));
        assert!(
            !has_datatype_arg,
            "flattened Option relations should not have Datatype-sorted arguments"
        );
    });
}

#[test]
fn test_mir_to_chc_result_is_ok_predicate() {
    // (#2188) Exercise codegen_call_result_predicate for Result::is_ok.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_result_is_ok(res: Result<u32, u32>) -> bool {
            res.is_ok()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_is_ok");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_result_is_ok", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_result_is_ok", bb_count);

        // After flattening (#2214), Result<u32,u32> is (Bool, BV32) — Bool for
        // discriminant (is_ok), BV32 for shared payload
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(
            has_bool,
            "Result::is_ok VC should have Bool state vars from flattened Result discriminant"
        );

        // After flattening, no relation argument should have Datatype sort.
        let has_datatype_arg =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_datatype));
        assert!(
            !has_datatype_arg,
            "flattened Result relations should not have Datatype-sorted arguments"
        );
    });
}

#[test]
fn test_mir_to_chc_result_is_err_predicate() {
    // (#2188) Exercise codegen_call_result_predicate for Result::is_err.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_result_is_err(res: Result<u32, u32>) -> bool {
            res.is_err()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_result_is_err");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_result_is_err", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_result_is_err", bb_count);

        // After flattening (#2214), Result<u32,u32> is (Bool, BV32) — Bool for
        // discriminant, BV32 for shared payload
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(
            has_bool,
            "Result::is_err VC should have Bool state vars from flattened Result discriminant"
        );

        // After flattening, no relation argument should have Datatype sort.
        let has_datatype_arg =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_datatype));
        assert!(
            !has_datatype_arg,
            "flattened Result relations should not have Datatype-sorted arguments"
        );
    });
}

#[test]
fn test_mir_to_chc_option_unwrap_expect() {
    // (#2188) Exercise codegen_call_unwrap_expect for Option::expect.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_expect(opt: Option<u32>) -> u32 {
            opt.expect("value must be present")
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_expect");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_option_expect", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_option_expect", bb_count);

        // Option::expect returns u32 → should have BV32 state vars
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "Option::expect VC should have BV32 state vars for u32 return");

        // After flattening, no relation argument should have Datatype sort.
        let has_datatype_arg =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_datatype));
        assert!(
            !has_datatype_arg,
            "flattened Option relations should not have Datatype-sorted arguments"
        );
    });
}
