// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Nested Datatype reconstruction coverage for `reconstruct_nested_datatype_from_slots`.

#![allow(clippy::unwrap_used)]

use super::expr_reconstruct_helpers::find_field_index_place;
use super::*;

// =============================================================================
// reconstruct_nested_datatype_from_slots — nested struct reconstruction
// =============================================================================

/// Happy path: bare read of a recursively flattened nested struct should
/// reconstruct the Datatype from leaf state var slots.
///
/// Pattern: `Outer { inner: Inner { x: i32, y: i32 }, value: i32 }` is
/// flattened to 3 leaf state vars. Bare read reconstructs as
/// `Outer_mk(Inner_mk(slot0, slot1), slot2)`.
///
/// Part of #2933: first dedicated test for reconstruct_nested_datatype_from_slots.
#[test]
fn test_reconstruct_nested_datatype_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone, Copy)]
        pub struct Inner {
            pub x: u32,
            pub y: u32,
        }

        #[derive(Clone, Copy)]
        pub struct Outer {
            pub inner: Inner,
            pub value: u32,
        }

        pub fn probe_nested_struct_return(a: u32, b: u32, c: u32) -> Outer {
            let s = Outer { inner: Inner { x: a, y: b }, value: c };
            s
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nested_struct_return");
        let body = instance.body().expect("function body");
        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_nested_struct_return", ChcConfig::default());
        let (vc, _needs_mem_promote) = chc_ctx.translate();

        assert!(!vc.rules.is_empty(), "nested struct pipeline should produce rules");

        let smt = emit_chc(&vc).to_string();
        assert!(!smt.is_empty(), "nested struct return should produce non-empty SMT");
    });
}

/// Whole-struct deref store with nested structs exercises both decomposition
/// and reconstruction paths. The RHS `*ptr = outer_val` requires reading
/// `outer_val` as a whole Datatype (reconstruct_nested_datatype_from_slots)
/// and then decomposing it for the store (try_decompose_struct_store).
///
/// Part of #2933: integration test covering the reconstruction→store path.
#[test]
fn test_reconstruct_nested_datatype_deref_store_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Point {
            pub x: u32,
            pub y: u32,
        }

        pub fn probe_nested_deref_store(ptr: &mut Point, a: u32, b: u32) {
            *ptr = Point { x: a, y: b };
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nested_deref_store");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_nested_deref_store",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _needs_mem_promote) = chc_ctx.translate();

        assert!(!vc.rules.is_empty(), "nested deref store pipeline should produce rules");
        assert!(
            any_constraint_str(&vc, |c| c.contains("store")),
            "nested struct deref store should emit store constraints"
        );
    });
}

/// Unit-level test: translate_place_with_modified on a recursively flattened
/// nested struct should return Some(expr) with Datatype sort.
///
/// Part of #2933: direct unit coverage for reconstruct_nested_datatype_from_slots.
#[test]
fn test_reconstruct_nested_datatype_translate_place_returns_some() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Inner { pub x: u32, pub y: u32 }
        pub struct Outer { pub inner: Inner, pub z: u32 }

        pub fn probe_nested_place(s: Outer) -> Outer {
            s
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nested_place");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_nested_place", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let outer_local = 1usize;
        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&outer_local),
            "test precondition failed: Outer struct param local {outer_local} was not \
             flattened — probe source may need adjustment if flattening heuristic changed"
        );

        let n_fields = chc_ctx.flattened_field_count(outer_local);
        assert!(n_fields >= 2, "Outer should have at least 2 flattened fields, got {n_fields}");

        let modified: HashSet<usize> = HashSet::new();
        let place = Place { local: outer_local, projection: vec![] };
        let result = chc_ctx.translate_place_with_modified(&place, &modified);

        assert!(
            result.is_some(),
            "bare read of flattened Outer struct should reconstruct via \
             reconstruct_nested_datatype_from_slots, not drop translation"
        );

        let expr = result.unwrap();
        assert!(
            expr.sort().is_datatype(),
            "reconstructed Outer expression should have Datatype sort, got {:?}",
            expr.sort()
        );
    });
}

/// Deep recursive flattening stops at `MAX_FLATTEN_DEPTH`, leaving the deepest
/// subtree as a single opaque Datatype slot. Bare-read reconstruction must
/// treat that slot as a leaf instead of recursing past the flatten boundary.
///
/// Part of #4075: async spawn cleanup drops whole-read a deeply nested
/// coroutine temp, and reconstruction must match the flattening granularity.
#[test]
fn test_reconstruct_nested_datatype_depth_limited_leaf_returns_some() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone, Copy)]
        pub struct Level5 {
            pub x: u32,
            pub y: u32,
        }

        #[derive(Clone, Copy)]
        pub struct Level4 {
            pub inner: Level5,
            pub ay: u32,
        }

        #[derive(Clone, Copy)]
        pub struct Level3 {
            pub inner: Level4,
            pub z3: u32,
        }

        #[derive(Clone, Copy)]
        pub struct Level2 {
            pub inner: Level3,
            pub z2: u32,
        }

        #[derive(Clone, Copy)]
        pub struct Level1 {
            pub inner: Level2,
            pub z1: u32,
        }

        pub fn probe_depth_limited_place(s: Level1) -> Level1 {
            s
        }
    "#;

    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_place_translation_drop_count();

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_depth_limited_place");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_depth_limited_place", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let root_local = 1usize;
        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&root_local),
            "test precondition failed: Level1 param local {root_local} was not flattened"
        );
        assert_eq!(
            chc_ctx.flattened_field_count(root_local),
            5,
            "depth-limited flattening should keep Level5 as one opaque leaf plus ay..z1"
        );

        let expr = chc_ctx
            .translate_place_with_modified(
                &Place { local: root_local, projection: vec![] },
                &HashSet::new(),
            )
            .expect("bare read of depth-limited nested struct should reconstruct");

        assert!(
            expr.sort().is_datatype(),
            "reconstructed Level1 expression should have Datatype sort, got {:?}",
            expr.sort()
        );
    });

    let translation_drops = take_translation_drop_by_fn();
    assert!(
        !translation_drops.contains_key("probe_depth_limited_place"),
        "depth-limited bare read should not record translation drops, map={translation_drops:?}"
    );
    let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    assert!(
        !translation_sites.contains_key("probe_depth_limited_place"),
        "depth-limited bare read should not record translation-drop site reasons, map={translation_sites:?}"
    );
    assert_eq!(
        crate::codegen_ay::take_place_translation_drop_count(),
        0,
        "depth-limited bare read should not increment place_translation_drop"
    );
}

/// Mixed `Field+Index` reads on recursively flattened locals should rebuild the
/// root Datatype first, then continue the projection chain against that root.
///
/// Part of #3829: regression guard for `reconstruct_flattened_root(...)`
/// delegating to recursive slot-based reconstruction.
#[test]
fn test_reconstruct_flattened_root_field_index_nested_array_returns_some() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone, Copy)]
        pub struct RationalLike {
            pub num: i64,
            pub den: i64,
        }

        #[derive(Clone, Copy)]
        pub struct LinearExprNested {
            pub vars: [u32; 4],
            pub coeffs: [RationalLike; 4],
            pub len: usize,
            pub constant: RationalLike,
        }

        pub fn probe_field_index(expr: LinearExprNested, idx: usize) -> i64 {
            let lane = if expr.len == 0 { 0 } else { idx % expr.len };
            expr.coeffs[lane].num + expr.constant.den
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_field_index");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_field_index", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let expr_local = 1usize;
        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&expr_local),
            "test precondition failed: LinearExprNested param local {expr_local} was not flattened"
        );

        let place = find_field_index_place(&body, expr_local)
            .expect("MIR should contain a Field+Index place rooted at the flattened expr local");
        let result = chc_ctx.translate_place_with_modified(&place, &HashSet::new());

        assert!(
            result.is_some(),
            "Field+Index read on flattened LinearExprNested should reconstruct the root Datatype"
        );
    });
}

/// Triple-nested struct exercises the recursive depth of
/// reconstruct_nested_datatype_from_slots with 3 levels.
///
/// Part of #2933: deep recursion test.
#[test]
fn test_reconstruct_nested_datatype_three_levels_deep_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[derive(Clone, Copy)]
        pub struct V2 { pub x: u32, pub y: u32 }

        #[derive(Clone, Copy)]
        pub struct Segment { pub start: V2, pub end: V2 }

        #[derive(Clone, Copy)]
        pub struct Line { pub seg: Segment, pub width: u32 }

        pub fn probe_triple_nested(a: u32, b: u32, c: u32, d: u32, w: u32) -> Line {
            Line {
                seg: Segment {
                    start: V2 { x: a, y: b },
                    end: V2 { x: c, y: d },
                },
                width: w,
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_triple_nested");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_triple_nested", ChcConfig::default());
        let (vc, _needs_mem_promote) = chc_ctx.translate();

        assert!(!vc.rules.is_empty(), "triple-nested struct pipeline should produce rules");

        let smt = emit_chc(&vc).to_string();
        assert!(!smt.is_empty(), "triple-nested struct should produce non-empty SMT");
    });
}
