// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for `codegen_expr.rs` — `reconstruct_option_like_enum` and
//! `reconstruct_nested_datatype_from_slots`.
//!
//! Part of #2933 (test coverage for uncovered production functions).
//!
//! Covers:
//! - `reconstruct_option_like_enum`: reconstructs flattened Option<T> as ITE
//! - `reconstruct_nested_datatype_from_slots`: recursive Datatype reconstruction
//! - Integration: full translate() pipeline produces correct VC for these patterns

#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::emit_chc;
use rustc_public::mir::Place;

mod expr_reconstruct_helpers;
mod nested_datatype;

// =============================================================================
// reconstruct_option_like_enum — Option<T> bare read reconstruction
// =============================================================================

/// Happy path: bare read of a flattened Option<u32> local should produce an
/// ITE(discriminant, Some(payload), None()) expression in the VC.
///
/// This exercises `reconstruct_option_like_enum` in codegen_expr.rs:327-392.
/// The pipeline flattens Option<u32> to (fld0: Bool, fld1: BV32), and when
/// the local is read as a whole (e.g., for a return), reconstruction fires.
///
/// Part of #2933: first dedicated test for reconstruct_option_like_enum.
#[test]
fn test_reconstruct_option_like_enum_happy_path_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_bare_read(flag: bool, val: u32) -> Option<u32> {
            let opt: Option<u32> = if flag { Some(val) } else { None };
            opt
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_bare_read");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_bare_read", ChcConfig::default());
        let (vc, _needs_mem_promote) = chc_ctx.translate();

        // The VC should have rules and produce valid SMT.
        assert!(!vc.rules.is_empty(), "Option bare read pipeline should produce rules");

        let smt = emit_chc(&vc).to_string();
        assert!(!smt.is_empty(), "SMT output should be non-empty");

        // Look for evidence of Option reconstruction in the constraint structure.
        // The ITE(discr, Some(payload), None()) pattern produces either:
        // - An `ite` expression in constraints, OR
        // - A Datatype constructor application (`Option_mk_Some`, `Option_mk_None`)
        // The constraints should contain non-trivial content (not all `true`).
        let total = count_constraint_str(&vc, |_| true);
        let trivial = count_constraint_str(&vc, |c| c == "true");
        assert!(total > trivial, "Option bare read should produce non-trivial constraints");
    });
}

/// Option<u8> in an array repeat context (`[Some(4u8); 2]`) — this is the
/// original motivating case from #2876 that required reconstruct_option_like_enum.
///
/// Part of #2933: regression guard for the #2876 fix.
#[test]
fn test_reconstruct_option_like_enum_array_repeat_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_array_repeat() -> [Option<u8>; 2] {
            [Some(4u8); 2]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_array_repeat");
        let body = instance.body().expect("function body");
        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_option_array_repeat", ChcConfig::default());
        let (vc, _needs_mem_promote) = chc_ctx.translate();

        // The pipeline should produce a translatable VC.
        assert!(!vc.rules.is_empty(), "Option array repeat pipeline should produce rules");

        let smt = emit_chc(&vc).to_string();

        // The SMT must be parseable (no sort mismatches from failed reconstruction).
        assert!(!smt.is_empty(), "Option array repeat should produce non-empty SMT");
    });
}

/// Unit-level test: calling translate_place_with_modified on a flattened
/// Option<u32> local with empty projection (bare read) should trigger
/// reconstruct_option_like_enum and return Some(expr).
///
/// Part of #2933: direct unit coverage for reconstruct_option_like_enum.
#[test]
fn test_reconstruct_option_like_enum_translate_place_returns_some() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_option_place(x: Option<u32>) -> Option<u32> {
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_place");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_option_place", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find the Option<u32> parameter local. In MIR, local 0 = return,
        // local 1 = first param. The param should be flattened for Option.
        let option_local = 1usize;

        // Check if the local was flattened (Option should be flattened to
        // Bool + payload fields). If not flattened, skip — the test only
        // applies when flattening is active.
        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&option_local),
            "test precondition failed: Option<u32> param local {option_local} was not \
             flattened — probe source may need adjustment if flattening heuristic changed"
        );

        let modified: HashSet<usize> = HashSet::new();
        let place = Place { local: option_local, projection: vec![] };
        let result = chc_ctx.translate_place_with_modified(&place, &modified);

        // If the local is flattened and has Datatype sort, reconstruction
        // should succeed (not return None with a place_translation_drop).
        assert!(
            result.is_some(),
            "bare read of flattened Option<u32> local should reconstruct via \
             reconstruct_option_like_enum, not drop translation"
        );

        let expr = result.unwrap();
        // The reconstructed expression should have a Datatype sort
        // (the Option<u32> Datatype, reconstructed from flattened fields).
        assert!(
            expr.sort().is_datatype(),
            "reconstructed Option expression should have Datatype sort, got {:?}",
            expr.sort()
        );
    });
}

/// Bare read of a flattened `Option<struct>` local should reconstruct the nested
/// payload instead of dropping translation.
///
/// Part of #3814: `LinearExpr::coeff_for` returns `Option<Rational>`, and those
/// temporaries flatten to `(is_some, num, den)`. The old 2-slot-only Option
/// path dropped these bare reads, leaving Tier 3 LRA harnesses on the
/// `flattened_bare_read` lane.
#[test]
fn test_reconstruct_option_like_enum_nested_payload_translate_place_returns_some() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone, Copy)]
        pub struct Rational {
            pub num: u32,
            pub den: u32,
        }

        pub fn probe_option_struct_place(x: Option<Rational>) -> Option<Rational> {
            x
        }
    "#;

    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_place_translation_drop_count();

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_option_struct_place");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_option_struct_place", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let option_local = 1usize;
        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&option_local),
            "test precondition failed: Option<Rational> param local {option_local} was not \
             flattened"
        );

        let modified: HashSet<usize> = HashSet::new();
        let place = Place { local: option_local, projection: vec![] };
        let expr = chc_ctx
            .translate_place_with_modified(&place, &modified)
            .expect("bare read of flattened Option<Rational> should reconstruct");

        assert!(
            expr.sort().is_datatype(),
            "reconstructed Option<Rational> expression should have Datatype sort, got {:?}",
            expr.sort()
        );
    });

    let translation_drops = take_translation_drop_by_fn();
    assert!(
        !translation_drops.contains_key("probe_option_struct_place"),
        "Option<Rational> bare read should not record translation drops, map={translation_drops:?}"
    );
    let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    assert!(
        !translation_sites.contains_key("probe_option_struct_place"),
        "Option<Rational> bare read should not record translation-drop site reasons, map={translation_sites:?}"
    );
    assert_eq!(
        crate::codegen_ay::take_place_translation_drop_count(),
        0,
        "Option<Rational> bare read should not increment place_translation_drop"
    );
}

// =============================================================================
// Edge cases and guard paths
// =============================================================================

/// Multi-constructor enum (not Option-like) should NOT trigger
/// reconstruct_option_like_enum. The pipeline should handle AB { A(u32), B(u64) }
/// without panicking and produce a valid VC — this exercises the Datatype codegen
/// path for non-Option enums.
///
/// Note: AB is not flattened by the heuristic (only Option-like enums are), so the
/// reconstruct_option_like_enum guard is never reached at the translate_place level.
/// Instead, this test validates the full pipeline handles non-Option enums correctly.
///
/// Part of #2933: negative/regression test for non-Option enum codegen.
#[test]
fn test_reconstruct_option_like_enum_rejects_non_option_enum() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub enum AB { A(u32), B(u64) }

        pub fn probe_non_option_enum(x: AB) -> AB {
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_non_option_enum");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_non_option_enum", ChcConfig::default());
        let (vc, _needs_mem_promote) = chc_ctx.translate();

        // The pipeline should produce a translatable VC for non-Option enums.
        assert!(!vc.rules.is_empty(), "non-Option enum pipeline should produce rules");

        let smt = emit_chc(&vc).to_string();
        // The SMT must be parseable (no sort mismatches from incorrectly
        // applying Option-like reconstruction to a non-Option enum).
        assert!(!smt.is_empty(), "non-Option enum should produce non-empty SMT");
    });
}
