// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for Box<str> drop-glue DST pointer extraction in
//! `emit_box_dealloc_transition`.
//!
//! Part of #3655: Box<str> is represented as a Datatype (Slice_bv8) rather
//! than a flat BV64 pointer. Before the fix, `split_pointer()` returned None
//! for Datatype expressions, causing the Box dealloc to fall through to a
//! plain skip — losing double-free/UAF detection. The fix extracts `fld_ptr`
//! from the Datatype before splitting.

#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// Box<str> drop at Ptr track level
// =============================================================================

const BOXED_STR_DROP_SOURCE: &str = r#"
    #![allow(dead_code, unused_variables)]

    pub fn probe_boxed_str_drop() {
        let s = String::from("hello");
        let _b: Box<str> = s.into_boxed_str();
    }
"#;

/// Box<str> drop at Ptr level should emit obj_valid dealloc constraints.
///
/// Before #3655 fix, Box<str> (represented as Slice_bv8 Datatype) caused
/// `split_pointer()` to return None, falling through to plain skip.
/// After the fix, `extract_pointer_expr()` peels `fld_ptr` from the Datatype,
/// enabling the full dealloc transition with obj_valid checks.
#[test]
fn test_boxed_str_drop_emits_dealloc_constraints() {
    with_test_ay_ctx_for_source(BOXED_STR_DROP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_boxed_str_drop");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_boxed_str_drop",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_boxed_str_drop", body.blocks.len());

        // The VC should contain obj_valid__out constraints from the Box dealloc
        // transition. If this fails, emit_box_dealloc_transition is not handling
        // the Datatype pointer extraction correctly.
        assert!(
            vc_rules_contain_var(&vc, "obj_valid__out"),
            "Box<str> drop at Ptr level should emit obj_valid__out dealloc constraints \
             (fld_ptr extraction from Slice_bv8 Datatype)"
        );
    });
}

/// Box<str> drop at Reg level should produce a valid VC without panics.
///
/// Even at Reg level (no heap model), the codegen should not panic when
/// encountering a Datatype expression in the drop path.
#[test]
fn test_boxed_str_drop_reg_level_no_panic() {
    with_test_ay_ctx_for_source(BOXED_STR_DROP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_boxed_str_drop");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_boxed_str_drop", ChcConfig::default());

        assert_vc_structure(&vc, "probe_boxed_str_drop", body.blocks.len());

        // At Reg level, Box drop is a no-op (no heap model), but it should
        // still produce valid transition rules without panicking.
        assert!(
            vc.rules.iter().any(|r| r.body.relation.is_some()),
            "Box<str> drop at Reg level should produce transition rules"
        );
    });
}

// =============================================================================
// extract_pointer_expr unit test for Slice Datatype
// =============================================================================

/// Verify that extract_pointer_expr handles Slice_bv8 Datatype correctly.
///
/// This is the core mechanism enabling Box<str> dealloc: peel the fld_ptr
/// field from the Datatype to get a BV64 that split_pointer() can handle.
#[test]
fn test_extract_pointer_expr_from_slice_datatype() {
    use super::super::dyn_coercion::extract_pointer_expr;
    use ay_bindings::{Expr, Sort};

    // Construct a Slice_bv8-like Datatype sort using Sort::struct_type
    let dt_sort = Sort::struct_type(
        "Slice_bv8",
        [
            ("fld_ptr", Sort::bitvec(64)),
            ("fld_len", Sort::bitvec(64)),
            ("fld_data", Sort::array(Sort::bitvec(64), Sort::bitvec(8))),
        ],
    );
    let dt_expr = Expr::var("box_str_local", dt_sort);

    let result = extract_pointer_expr(&dt_expr);
    assert!(result.is_some(), "extract_pointer_expr should handle Slice_bv8 Datatype");

    let ptr = result.unwrap();
    assert!(ptr.sort().is_bitvec(), "extracted pointer should be BV64, got {:?}", ptr.sort());
    assert_eq!(ptr.sort().bitvec_width(), Some(64), "extracted pointer should be 64-bit");
}

/// BV64 expressions should pass through extract_pointer_expr unchanged.
#[test]
fn test_extract_pointer_expr_bv64_passthrough() {
    use super::super::dyn_coercion::extract_pointer_expr;
    use ay_bindings::{Expr, Sort};

    let bv_expr = Expr::var("ptr", Sort::bitvec(64));
    let result = extract_pointer_expr(&bv_expr);
    assert!(result.is_some(), "BV64 should pass through extract_pointer_expr");
    assert_eq!(result.unwrap().sort().bitvec_width(), Some(64));
}

// =============================================================================
// D2: Mem-level diagnostic counter test (Part of #3655)
// =============================================================================

/// Box<str> drop at Mem level should produce zero place_translation_drop events.
///
/// Part of #3655: After fixing MemSizeOf<str> (no longer classified as sound
/// fallback), emit_box_dealloc_transition (Slice_bv8 fld_ptr extraction), and
/// is_array_to_slice_unsize (Box<[u8]> -> Box<str>), the boxed_str probe
/// should have zero remaining translation drops. This test isolates the
/// counter to verify the full Mem-level pipeline.
#[test]
fn test_boxed_str_drop_mem_level_zero_translation_drops() {
    with_test_ay_ctx_for_source(BOXED_STR_DROP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_boxed_str_drop");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_boxed_str_drop",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();

        assert_vc_structure(&vc, "probe_boxed_str_drop", body.blocks.len());

        let translation_drop_count = diagnostics.place_translation_drop.get();
        assert_eq!(
            translation_drop_count, 0,
            "Box<str> probe at Mem level should have 0 place_translation_drop events, \
             got {translation_drop_count}. Remaining drops indicate an unhandled \
             encoding path in the boxed_str pipeline."
        );
    });
}
