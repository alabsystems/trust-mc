// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::common::*;

const SOURCE: &str = r#"
    #![allow(dead_code, unused_assignments)]
    fn call(mut f: Box<dyn FnMut(&mut i32)>, value: &mut i32) { f(value) }
    fn increment(value: &mut i32) { *value = value.wrapping_add(1) }

    pub fn projected_safe() {
        let mut pair = (1i32, 9u8);
        let mut unrelated = 41i32;
        let keep_live = &mut unrelated;
        *keep_live = keep_live.wrapping_add(0);
        call(Box::new(&increment), &mut pair.0);
        assert!(pair.0 == 2 && unrelated == 41);
    }
    pub fn projected_bug() {
        let mut pair = (1i32, 9u8);
        let mut unrelated = 41i32;
        let keep_live = &mut unrelated;
        *keep_live = keep_live.wrapping_add(0);
        call(Box::new(&increment), &mut pair.0);
        assert!(pair.0 == 1);
    }
    pub fn same_sort_safe() {
        let mut x = 1i32;
        let mut y = 41i32;
        let keep_live = &mut y;
        *keep_live = keep_live.wrapping_add(0);
        call(Box::new(&increment), &mut x);
        assert!(x == 2 && y == 41);
    }
    pub fn same_sort_bug() {
        let mut x = 1i32;
        let mut y = 41i32;
        let keep_live = &mut y;
        *keep_live = keep_live.wrapping_add(0);
        call(Box::new(&increment), &mut x);
        assert!(x == 1);
    }
    fn reassigned(original: &mut i32) -> i32 {
        let mut pair = (1i32, 9u8);
        let mut current = original;
        current = &mut pair.0;
        call(Box::new(&increment), current);
        pair.0
    }
    pub fn reassigned_safe() {
        let mut unrelated = 41i32;
        let result = reassigned(&mut unrelated);
        assert!(result == 2 && unrelated == 41);
    }
    pub fn reassigned_bug() {
        let mut unrelated = 41i32;
        let result = reassigned(&mut unrelated);
        assert!(result == 1);
    }
    fn twice(mut f: Box<dyn FnMut(&mut i32)>, value: &mut i32) { f(value); f(value); }
    pub fn stale_safe() {
        let mut x = 1i32;
        twice(Box::new(&increment), &mut x);
        assert!(x == 3);
    }
    pub fn stale_bug() {
        let mut x = 1i32;
        twice(Box::new(&increment), &mut x);
        assert!(x == 2);
    }
"#;

#[test]
fn mutable_reference_native_twins_keep_exact_owners_or_fail_closed() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in [
            "projected_safe",
            "projected_bug",
            "same_sort_safe",
            "same_sort_bug",
            "reassigned_safe",
            "reassigned_bug",
            "stale_safe",
            "stale_bug",
        ] {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.body().expect("body");
            let chc = ChcCtx::new(
                ctx.tcx,
                &body,
                name,
                ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
            );
            let (vc, _, diagnostics) = chc.translate_with_diagnostics();
            let smt = crate::codegen_ay::emit_chc(&vc).to_string();
            let result = run_z3_on_smt2_with_timeout(&smt, 30);
            let all_reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
            let reasons = all_reasons.get(name).cloned().unwrap_or_default();
            eprintln!(
                "OWNER_CONTROL {name}: {result:?}; fail_closed={}; reasons={reasons:?}",
                diagnostics.place_translation_drop.get()
            );
            if name.starts_with("same_sort") {
                let expected = if name.ends_with("safe") { "unsat" } else { "sat" };
                assert_eq!(
                    result.as_deref(),
                    Ok(expected),
                    "{name}: the passed borrow, rather than a same-sort decoy, must receive the update"
                );
            } else {
                let refusal = reasons.iter().any(|(reason, count)| {
                    *count > 0 && reason.starts_with("fn_trait_mut_ref_owner_")
                });
                assert!(
                    refusal && diagnostics.place_translation_drop.get() > 0,
                    "{name}: unsupported ownership or stale value authority requires explicit fail-closed debt: {reasons:?}"
                );
                // Driver qualification demotes any proof with this category.
                // Raw UNSAT alone is deliberately insufficient for a certificate.
                assert!(
                    result.as_deref() != Ok("unsat")
                        || diagnostics.place_translation_drop.get() > 0
                );
            }
            for reason in
                reasons.keys().filter(|reason| reason.starts_with("fn_trait_mut_ref_owner_"))
            {
                assert_eq!(
                    super::super::codegen_ctx::fallback_soundness(reason),
                    super::super::codegen_ctx::FallbackSoundness::FailClose
                );
            }
        }
    });
}
