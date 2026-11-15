// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Metadata must follow a replaced wide pointer, while prior copies keep theirs.

use super::common::*;
use std::sync::atomic::{AtomicBool, Ordering};

const SOURCE: &str = r#"
    pub fn unchanged_literal() {
        let text = "ab";
        assert!(text.len() == 2);
    }
    pub fn indirect_rebind_safe() {
        let mut text = "ab";
        let snapshot = text;
        { let slot = &mut text; *slot = "é🙂"; }
        assert!(text.len() == 6);
        assert!(snapshot.len() == 2);
    }
    pub fn indirect_rebind_bug() {
        let mut text = "ab";
        { let slot = &mut text; *slot = "é🙂"; }
        assert!(text.len() == 2);
    }
    pub fn snapshot_rebind_bug() {
        let mut text = "ab";
        let snapshot = text;
        let replacement = "é🙂";
        { let slot = &mut text; *slot = replacement; }
        assert!(snapshot == replacement);
    }
    pub fn copied_rebind_safe() {
        let mut text = "ab";
        { let slot = &mut text; *slot = "é🙂"; }
        let current = text;
        assert!(current.len() == 6);
    }
    pub fn copied_rebind_bug() {
        let mut text = "ab";
        { let slot = &mut text; *slot = "é🙂"; }
        let current = text;
        assert!(current.len() == 2);
    }
    pub fn nested_rebind_safe() {
        let mut text = "ab";
        {
            let mut slot = &mut text;
            let outer = &mut slot;
            **outer = "é🙂";
        }
        assert!(text.len() == 6);
    }
    pub fn conditional_rebind_safe(replace: bool) {
        let mut text = "ab";
        if replace { let slot = &mut text; *slot = "é🙂"; }
        assert!(text.len() == if replace { 6 } else { 2 });
    }
    pub fn conditional_rebind_bug(replace: bool) {
        let mut text = "ab";
        if replace { let slot = &mut text; *slot = "é🙂"; }
        assert!(text.len() == 2);
    }
"#;

#[test]
fn test_string_metadata_follows_indirect_rebinding() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let ran = AtomicBool::new(false);
    with_test_ay_ctx_for_source(SOURCE, |context| {
        let mut outcomes = Vec::new();
        for (name, expected, rebind) in [
            ("unchanged_literal", "unsat", false),
            ("indirect_rebind_safe", "unsat", true),
            ("indirect_rebind_bug", "sat", true),
            ("snapshot_rebind_bug", "sat", true),
            ("copied_rebind_safe", "unsat", true),
            ("copied_rebind_bug", "sat", true),
            ("nested_rebind_safe", "unsat", true),
            ("conditional_rebind_safe", "unsat", true),
            ("conditional_rebind_bug", "sat", true),
        ] {
            let instance = find_instance_by_suffix(context.tcx, name);
            let body = instance.body().expect("string metadata regression body");
            let vc =
                mir_to_chc_with_instance(context.tcx, &body, instance, name, ChcConfig::default());
            let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                .remove(name)
                .unwrap_or_default();
            let smt = crate::codegen_ay::emit_chc(&vc).to_string();
            // Retain the exact native compiler output for independent replay.
            eprintln!("STRING_METADATA_SMT_BEGIN {name}\n{smt}\nSTRING_METADATA_SMT_END {name}");
            let result =
                run_z3_on_smt2_capture_output_with_timeout(&smt, z3_test_timeout_secs_or(30))
                    .expect("AY must execute the emitted query");
            let refusal_preserved = !rebind
                || reasons
                    .get("pointer_stored_through_deref_rebinds_target")
                    .is_some_and(|count| *count > 0);
            let correct = result.status_success && result.verdict == expected && refusal_preserved;
            outcomes.push((name, correct, result.verdict, reasons));
        }
        assert!(outcomes.iter().all(|(_, correct, _, _)| *correct), "{outcomes:#?}");
        ran.store(true, Ordering::SeqCst);
    });
    assert!(ran.load(Ordering::SeqCst), "the native Rust source must compile and run");
}
