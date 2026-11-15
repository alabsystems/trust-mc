// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Design 4 (docs/chc-hole-fix-designs-2026-09-24.md): a wide slice pointer's
//! length reaches its slot exactly, or as a counted fresh value.
//!
//! * A: the unsize cast `&[u8; 10] -> &[u8]` packs `concat(10, addr)`;
//! * C: the subslice borrow `&(*bytes)[1..]` of a loop-carried slice packs the
//!   base slice's CURRENT length minus one;
//! * D: the write boundary replaces the high half of a widened thin leaf with a
//!   fresh length (booked fail-closed) and leaves carried lengths alone.
//!
//! tools/soundness-duals/chc_slice_pattern_loop_dead_dual.rs and
//! chc_slice_len_join_dual.rs are the end-to-end twins.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::ptr_repr::PtrRepr;
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::Sort;
use rustc_public::mir::{CastKind, PointerCoercion, ProjectionElem, Rvalue, StatementKind};

const SLICE_LOOP_SOURCE: &str = r#"
pub fn probe_slice_loop(a: [u8; 10]) -> u32 {
    let mut bytes: &[u8] = &a;
    let mut n: u32 = 0;
    while let [_first, rest @ ..] = bytes {
        bytes = rest;
        n += 1;
    }
    n
}
"#;

fn mem_ctx<'tcx, 'body>(
    tcx: TyCtxt<'tcx>,
    body: &'body rustc_public::mir::Body,
) -> ChcCtx<'tcx, 'body> {
    let mut chc_ctx = ChcCtx::new(
        tcx,
        body,
        "probe_slice_loop",
        ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
    );
    chc_ctx.declare_block_relations();
    chc_ctx
}

/// The `(dest, rvalue)` of the first assignment whose rvalue matches.
fn find_assign(body: &rustc_public::mir::Body, pred: impl Fn(&Rvalue) -> bool) -> (usize, Rvalue) {
    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(place, rvalue) = &stmt.kind
                && place.projection.is_empty()
                && pred(rvalue)
            {
                return (place.local, rvalue.clone());
            }
        }
    }
    panic!("expected a matching assignment in the MIR body");
}

fn is_unsize(rvalue: &Rvalue) -> bool {
    matches!(rvalue, Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), _, _))
}

fn is_subslice_borrow(rvalue: &Rvalue) -> bool {
    matches!(
        rvalue,
        Rvalue::Ref(_, _, place)
            if place.projection.iter().any(|p| matches!(p, ProjectionElem::Subslice { .. }))
    )
}

fn const_value(expr: &Expr) -> Option<String> {
    match expr.value() {
        ExprValue::BitVecConst { value, .. } => Some(value.to_string()),
        _ => None,
    }
}

#[test]
fn array_to_slice_unsize_packs_the_array_length() {
    with_test_ay_ctx_for_source(SLICE_LOOP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_loop");
        let body = instance.body().expect("function body");
        let mut chc_ctx = mem_ctx(ctx.tcx, &body);
        let (dest, rvalue) = find_assign(&body, is_unsize);

        let drops_before = chc_ctx.diagnostics.place_translation_drop.get();
        let value = chc_ctx
            .translate_rvalue_with_modified(&rvalue, &HashSet::new(), Some(dest))
            .expect("unsize translates");

        let Some(PtrRepr::Fat { meta, .. }) = PtrRepr::classify(&value) else {
            panic!("the unsize result must be a structural wide pointer, got {value:?}");
        };
        assert_eq!(const_value(meta.as_expr()).as_deref(), Some("10"), "length is the array's N");
        assert_eq!(
            chc_ctx.diagnostics.place_translation_drop.get(),
            drops_before,
            "an exact length books no fail-close reason"
        );
    });
}

#[test]
fn subslice_borrow_of_a_loop_carried_slice_reads_its_current_length() {
    with_test_ay_ctx_for_source(SLICE_LOOP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_loop");
        let body = instance.body().expect("function body");
        let mut chc_ctx = mem_ctx(ctx.tcx, &body);
        let (dest, rvalue) = find_assign(&body, is_subslice_borrow);
        let Rvalue::Ref(_, _, ref_place) = &rvalue else { unreachable!() };
        let base = ref_place.local;
        assert!(
            chc_ctx.local_has_multiple_whole_definitions(base),
            "the loop-carried slice has two producers (the unsize and `bytes = rest`)"
        );

        let drops_before = chc_ctx.diagnostics.place_translation_drop.get();
        let value = chc_ctx
            .translate_rvalue_with_modified(&rvalue, &HashSet::new(), Some(dest))
            .expect("subslice borrow translates");

        let Some(PtrRepr::Fat { meta, .. }) = PtrRepr::classify(&value) else {
            panic!("the subslice borrow must carry a length, got {value:?}");
        };
        let meta = meta.as_expr().to_string();
        let base_var = format!("probe_slice_loop_{base}");
        assert!(
            meta.contains("extract") && meta.contains(&base_var) && meta.contains("bvsub"),
            "length is the base slice's own high half minus one: {meta}"
        );
        assert_eq!(
            chc_ctx.diagnostics.place_translation_drop.get(),
            drops_before,
            "a carried length books no fail-close reason"
        );
    });
}

#[test]
fn write_boundary_gives_a_widened_leaf_a_fresh_length_and_keeps_carried_ones() {
    with_test_ay_ctx_for_source(SLICE_LOOP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_slice_loop");
        let body = instance.body().expect("function body");
        let mut chc_ctx = mem_ctx(ctx.tcx, &body);
        let (slice_local, _) = find_assign(&body, is_unsize);
        let slice_ty = body.locals()[slice_local].ty;
        let addr = |name: &str| Expr::var(name, Sort::bitvec(POINTER_WIDTH));

        // A widened thin pointer: the fabricated-zero shape.
        let drops_before = chc_ctx.diagnostics.place_translation_drop.get();
        let guarded = chc_ctx.guard_slice_len_slot_write(
            slice_ty,
            addr("_p").zero_extend(POINTER_WIDTH),
            "test",
        );
        let Some(PtrRepr::Fat { data, meta }) = PtrRepr::classify(&guarded) else {
            panic!("guarded value is a structural wide pointer, got {guarded:?}");
        };
        assert_eq!(data.as_expr(), &addr("_p"), "the data address is kept");
        assert!(
            meta.as_expr().to_string().contains("__slice_len_unresolved"),
            "the length is fresh, never the zero padding: {meta:?}"
        );
        assert_eq!(chc_ctx.diagnostics.place_translation_drop.get(), drops_before + 1);

        // A thin pointer is widened first, then guarded the same way.
        let thin = chc_ctx.guard_slice_len_slot_write(slice_ty, addr("_q"), "test");
        assert!(thin.to_string().contains("__slice_len_unresolved"));

        // A join: only the widened branch gets a fresh length.
        let carried = Expr::bitvec_const(3u64, POINTER_WIDTH).concat(addr("_a"));
        let joined = Expr::ite(
            Expr::var("_c", Sort::bool()),
            carried.clone(),
            addr("_b").zero_extend(POINTER_WIDTH),
        );
        let guarded_join = chc_ctx.guard_slice_len_slot_write(slice_ty, joined, "test");
        let ExprValue::Ite { then_expr, else_expr, .. } = guarded_join.value() else {
            panic!("the join keeps its shape, got {guarded_join:?}");
        };
        assert_eq!(then_expr, &carried, "a carried length is untouched");
        assert!(else_expr.to_string().contains("__slice_len_unresolved"));

        // Carried and opaque values pass unchanged and book nothing.
        let drops_mid = chc_ctx.diagnostics.place_translation_drop.get();
        let opaque = Expr::var("_s", Sort::bitvec(2 * POINTER_WIDTH));
        assert_eq!(chc_ctx.guard_slice_len_slot_write(slice_ty, carried.clone(), "t"), carried);
        assert_eq!(chc_ctx.guard_slice_len_slot_write(slice_ty, opaque.clone(), "t"), opaque);
        assert_eq!(chc_ctx.diagnostics.place_translation_drop.get(), drops_mid);

        // A non-slice destination is never touched.
        let counter_ty = body.locals()[0].ty;
        let narrow = Expr::bitvec_const(0u64, 32);
        assert_eq!(chc_ctx.guard_slice_len_slot_write(counter_ty, narrow.clone(), "t"), narrow);
    });
}
