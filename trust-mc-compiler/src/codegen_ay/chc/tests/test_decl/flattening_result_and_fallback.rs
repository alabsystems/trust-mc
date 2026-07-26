// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ═══════════════════════════════════════════════════════════════════════
// Result<T, E> flattening tests (Part of #2214)
// ═══════════════════════════════════════════════════════════════════════

const RESULT_PROBE_SOURCE: &str = r#"
pub fn result_ok_local(x: u32) -> u32 {
    let res: Result<u32, u32> = Ok(x);
    match res {
        Ok(v) => v,
        Err(e) => e,
    }
}

pub fn result_err_local(x: u32) -> u32 {
    let res: Result<u32, u32> = Err(x);
    match res {
        Ok(v) => v,
        Err(e) => e,
    }
}
"#;

/// Verify that Result<u32, u32> locals are flattened (no Datatype sort in relations).
#[test]
fn test_result_flattened_no_datatype_sort() {
    with_test_ay_ctx_for_source(RESULT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "result_ok_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "result_ok_local", ChcConfig::default());
        chc_ctx.declare_block_relations();

        for rel in &chc_ctx.vc.relations {
            for sort in &rel.arg_sorts {
                assert!(
                    !sort.is_datatype(),
                    "Result<u32, u32> should be flattened, but relation {} has Datatype sort: {:?}",
                    rel.name,
                    sort
                );
            }
        }
    });
}

/// Verify that flattened Result locals appear in flattened_tuple_locals set.
#[test]
fn test_result_local_in_flattened_set() {
    with_test_ay_ctx_for_source(RESULT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "result_ok_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "result_ok_local", ChcConfig::default());
        chc_ctx.declare_block_relations();

        assert!(
            !chc_ctx.flatten.flattened_tuple_locals.is_empty(),
            "result_ok_local should have at least one flattened local (Result<u32, u32>)"
        );
    });
}

/// Verify that flattened Result<u32, u32> produces Bool + bv32 state vars.
#[test]
fn test_result_flattened_produces_bool_and_bv32_state_vars() {
    with_test_ay_ctx_for_source(RESULT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "result_ok_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "result_ok_local", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut found_result_local = false;
        for &local_idx in &chc_ctx.flatten.flattened_tuple_locals {
            if let Some(&vec_idx) = chc_ctx.state_var_mgr.local_to_state_idx.get(&local_idx) {
                let fld0 = &chc_ctx.state_var_mgr.state_vars[vec_idx];
                let fld1 = &chc_ctx.state_var_mgr.state_vars[vec_idx + 1];
                if fld0.1.is_bool() && fld1.1.bitvec_width() == Some(32) {
                    found_result_local = true;
                }
            }
        }

        assert!(
            found_result_local,
            "should find at least one flattened Result with Bool + bv32 fields"
        );
    });
}

/// Verify that flattened Result locals have correct discriminant mapping.
#[test]
fn test_result_flattened_enum_discr_mapping() {
    with_test_ay_ctx_for_source(RESULT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "result_ok_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "result_ok_local", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Result: (0, 1) — true=Ok(discr 0), false=Err(discr 1)
        let has_result_discr = chc_ctx
            .flatten
            .flattened_enum_discr
            .values()
            .any(|&(true_val, false_val)| true_val == 0 && false_val == 1);

        assert!(
            has_result_discr,
            "should have Result discriminant mapping (0, 1), found: {:?}",
            chc_ctx.flatten.flattened_enum_discr
        );
    });
}

/// Verify that mir_to_chc on Result-using function produces valid VC structure.
#[test]
fn test_result_mir_to_chc_valid_vc() {
    with_test_ay_ctx_for_source(RESULT_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "result_ok_local");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "result_ok_local", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "result_ok_local", bb_count);

        for rel in &vc.relations {
            for sort in &rel.arg_sorts {
                assert!(
                    !sort.is_datatype(),
                    "result_ok_local VC should have no Datatype sorts, found {:?} in {}",
                    sort,
                    rel.name
                );
            }
        }
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Fallback counter tests (Part of #2234)
// ═══════════════════════════════════════════════════════════════════════

const FALLBACK_METRIC_SOURCE: &str = r#"
pub async fn async_probe() -> u32 {
    7
}

pub fn use_async_probe() -> impl core::future::Future<Output = u32> {
    async_probe()
}
"#;

const CLOSURE_DECL_SOURCE: &str = r#"
pub fn closure_capture(seed: u32) -> u32 {
    let add_seed = |x: u32| x.wrapping_add(seed);
    add_seed(7)
}
"#;

/// A function with only primitive types should produce zero fallbacks.
#[test]
fn test_fallback_count_zero_for_primitive_types() {
    with_test_ay_ctx_for_source(DECL_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "simple_fn");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "simple_fn", ChcConfig::default());

        chc_ctx.declare_block_relations();

        assert_eq!(
            chc_ctx.fallback_count, 0,
            "primitive-only function should trigger zero type fallbacks"
        );
    });
}

/// Async opaque return type is now handled by the type translation system
/// (via BV fallback), so mir_to_chc completes without CHC fallback entries.
/// Updated in #3785 — previously expected fallback_count > 0.
#[test]
fn test_fallback_metric_records_untranslatable_async_opaque_type() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    with_test_ay_ctx_for_source(FALLBACK_METRIC_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "use_async_probe");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "use_async_probe", ChcConfig::default());

        // Key property: VC is produced (relations + rules exist).
        assert!(!vc.relations.is_empty(), "async probe should produce relations");
        assert!(!vc.rules.is_empty(), "async probe should produce rules");
    });
    clear_chc_fallback_counts();
}

/// A function with mixed types (including bools, ints) should still produce zero fallbacks
/// when all types are translatable.
#[test]
fn test_fallback_count_zero_for_multi_local() {
    with_test_ay_ctx_for_source(DECL_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "multi_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "multi_local", ChcConfig::default());

        chc_ctx.declare_block_relations();

        assert_eq!(
            chc_ctx.fallback_count, 0,
            "multi_local with i32/u64/bool should trigger zero type fallbacks"
        );
    });
}

/// Capturing closure locals must translate without unknown-type bv32 fallback.
#[test]
fn test_fallback_count_zero_for_closure_local_decl() {
    with_test_ay_ctx_for_source(CLOSURE_DECL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "closure_capture");
        let body = instance.body().expect("function body");
        let has_closure_local = body
            .local_decls()
            .any(|(_idx, decl)| matches!(decl.ty.kind(), TyKind::RigidTy(RigidTy::Closure(..))));
        assert!(has_closure_local, "probe should contain a closure local declaration");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "closure_capture", ChcConfig::default());

        chc_ctx.declare_block_relations();

        assert_eq!(
            chc_ctx.fallback_count, 0,
            "capturing closure local declaration should not trigger unknown-type fallback"
        );
    });
}
