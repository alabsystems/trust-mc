// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! The conditions under which a payload VALUE fact survives duplicated
//! producers (`stmt::codegen_stmt_payload_value_fact`), and the checked inline
//! constructor that declines a field-sort mismatch instead of panicking.
//!
//! Identical producers of one local only arise from loop unwinding, which a
//! unit probe cannot produce, so each condition is exercised on its own and the
//! combination is covered by tools/soundness-duals/slice_iter_agreeing_payload_fact_dual.rs.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::call::inline_shared::checked_inline_variant_constructor;
use crate::codegen_ay::context::with_test_ay_ctx_for_source_with_rustc_flags;
use ay_bindings::Sort;
use rustc_public::mir::{Body, ProjectionElem, Rvalue, StatementKind, TerminatorKind};

const PROBE_SOURCE: &str = r#"
#![allow(dead_code, unused_assignments, unused_variables, unused_mut)]
pub fn dead_before_call(it: &mut core::slice::Iter<'_, u32>) -> u32 {
    let first = match it.next() {
        Some(r) => *r,
        None => 0,
    };
    let later = it.next();
    first
}
pub fn live_across_call(it: &mut core::slice::Iter<'_, u32>) -> u32 {
    match it.next() {
        Some(r) => {
            let later = it.next();
            *r
        }
        None => 0,
    }
}
pub fn overwritten(it: &mut core::slice::Iter<'_, u32>) -> u32 {
    let mut o = it.next();
    o = None;
    match o {
        Some(r) => *r,
        None => 0,
    }
}
pub fn for_by_pattern(xs: &[u32]) -> u32 {
    let mut s: u32 = 0;
    for &e in xs {
        s = s.wrapping_add(e);
    }
    s
}
pub fn copy_live_across_call(it: &mut core::slice::Iter<'_, u32>) -> u32 {
    let zero = 0u32;
    let mut kept = &zero;
    if let Some(q) = it.next() {
        kept = q;
    }
    let later = it.next();
    *kept
}
pub fn borrowed_source(it: &mut core::slice::Iter<'_, u32>) -> u32 {
    let mut o = it.next();
    let p = &mut o;
    *p = None;
    match o {
        Some(r) => *r,
        None => 0,
    }
}
"#;

/// `(dest, src)` of the first `dest = copy ((src as Some).0)`.
fn first_payload_copy(body: &Body) -> (usize, usize) {
    for stmt in body.blocks.iter().flat_map(|block| &block.statements) {
        if let StatementKind::Assign(lhs, Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)) =
            &stmt.kind
            && lhs.projection.is_empty()
            && matches!(
                src.projection.as_slice(),
                [ProjectionElem::Downcast(_), ProjectionElem::Field(0, _)]
            )
        {
            return (lhs.local, src.local);
        }
    }
    panic!("probe has no payload copy");
}

/// Blocks whose `Call` terminator writes a local other than `src`.
fn other_call_blocks(body: &Body, src: usize) -> Vec<usize> {
    body.blocks
        .iter()
        .enumerate()
        .filter_map(|(bb, block)| match &block.terminator.kind {
            TerminatorKind::Call { destination, .. } if destination.local != src => Some(bb),
            _ => None,
        })
        .collect()
}

fn mem_config() -> ChcConfig {
    ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() }
}

/// Kani's pipeline keeps `StorageLive`/`StorageDead`; the default test context
/// (`-C opt-level=0`, MIR opt level 1) strips them, which would hide the kill the
/// analysis relies on.
const KEEP_STORAGE_MARKERS: &[&str] = &["-Zmir-opt-level=0"];

#[test]
fn payload_copy_dead_before_the_next_call_keeps_the_source_stable() {
    with_test_ay_ctx_for_source_with_rustc_flags(PROBE_SOURCE, KEEP_STORAGE_MARKERS, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "dead_before_call");
        let body = instance.body().expect("function body");
        let (dest, src) = first_payload_copy(&body);
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "dead_before_call", mem_config());

        assert!(chc_ctx.whole_definitions_all_same_payload_copy_of(dest, src));
        assert!(!chc_ctx.whole_definitions_all_same_payload_copy_of(dest, dest));
        let sites = chc_ctx
            .source_call_producer_sites(src, dest)
            .expect("the scrutinee is written only by its `next` call");
        assert_eq!(sites.len(), 1);
        assert!(!chc_ctx.payload_copy_may_outlive_source(src, dest, &sites));

        let later = other_call_blocks(&body, src);
        assert!(!later.is_empty(), "probe has a second call");
        assert!(
            !chc_ctx.payload_copy_may_outlive_source(src, dest, &later),
            "the copy is StorageDead before the later call"
        );
    });
}

#[test]
fn payload_copy_without_storage_markers_is_decided_by_liveness() {
    // Same probe with the markers stripped. The copy is still read before the
    // later call and never after it, so LIVENESS settles it: storage markers
    // are debug-info shape, not the program (see
    // `codegen_stmt_payload_value_liveness`).
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "dead_before_call");
        let body = instance.body().expect("function body");
        let (dest, src) = first_payload_copy(&body);
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "dead_before_call", mem_config());
        let later = other_call_blocks(&body, src);
        assert!(!later.is_empty(), "probe has a second call");
        assert!(!chc_ctx.payload_copy_may_outlive_source(src, dest, &later));
    });
}

/// The regression that motivated the liveness rewrite: `for &e in a` reads the
/// payload through a temp rustc brackets NOWHERE, so the storage-marker form of
/// condition 4 refused every such loop (`expected/loop-backedge/test.rs`,
/// `slice_iter_unwound_payload_deref_dual.rs`).
#[test]
fn for_by_pattern_payload_temp_is_dead_at_the_next_call() {
    with_test_ay_ctx_for_source_with_rustc_flags(PROBE_SOURCE, KEEP_STORAGE_MARKERS, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "for_by_pattern");
        let body = instance.body().expect("function body");
        let (dest, src) = first_payload_copy(&body);
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "for_by_pattern", mem_config());

        // The temp carries no storage marker at all.
        assert!(
            !body.blocks.iter().flat_map(|block| &block.statements).any(|stmt| matches!(
                &stmt.kind,
                StatementKind::StorageLive(local) | StatementKind::StorageDead(local)
                    if *local == dest
            )),
            "probe's payload copy is a bare temp"
        );
        assert!(chc_ctx.whole_definitions_all_same_payload_copy_of(dest, src));
        let sites = chc_ctx
            .source_call_producer_sites(src, dest)
            .expect("the scrutinee is written only by its `next` call");
        // The loop backedge reaches that same `next` call again, and the copy is
        // dead there: the fact survives.
        assert!(!chc_ctx.payload_copy_may_outlive_source(src, dest, &sites));
        assert_eq!(chc_ctx.payload_fact_carriers(dest), vec![dest]);
    });
}

/// A local that INHERITS the fact keeps the guard closed even after the copy
/// itself is dead: `propagate_ref_metadata` hands `const_ref_values` across a
/// whole-local copy, so the inheriting local's liveness counts too.
#[test]
fn a_local_that_inherits_the_fact_is_a_carrier() {
    with_test_ay_ctx_for_source_with_rustc_flags(PROBE_SOURCE, KEEP_STORAGE_MARKERS, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "copy_live_across_call");
        let body = instance.body().expect("function body");
        let (dest, src) = first_payload_copy(&body);
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "copy_live_across_call", mem_config());

        let carriers = chc_ctx.payload_fact_carriers(dest);
        assert!(carriers.len() > 1, "the copy is handed on: {carriers:?}");
        let later = other_call_blocks(&body, src);
        assert!(!later.is_empty(), "probe has a second call");
        assert!(
            chc_ctx.payload_copy_may_outlive_source(src, dest, &later),
            "a carrier is read after the later call, so the fact is refused"
        );
    });
}

#[test]
fn payload_copy_live_across_a_source_producer_is_refused() {
    with_test_ay_ctx_for_source_with_rustc_flags(PROBE_SOURCE, KEEP_STORAGE_MARKERS, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "live_across_call");
        let body = instance.body().expect("function body");
        let (dest, src) = first_payload_copy(&body);
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "live_across_call", mem_config());

        let later = other_call_blocks(&body, src);
        assert!(!later.is_empty(), "probe has a second call");
        assert!(
            chc_ctx.payload_copy_may_outlive_source(src, dest, &later),
            "a producer at the later call would run while the copy is still live"
        );
    });
}

#[test]
fn source_written_by_a_statement_or_borrowed_is_refused() {
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        for name in ["overwritten", "borrowed_source"] {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.body().expect("function body");
            let (dest, src) = first_payload_copy(&body);
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, name, mem_config());
            assert!(
                chc_ctx.source_call_producer_sites(src, dest).is_none(),
                "{name}: a write outside the call producers refuses the fact"
            );
        }
    });
}

#[test]
fn only_the_payload_slot_variable_is_a_producer_independent_fact() {
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "dead_before_call");
        let body = instance.body().expect("function body");
        let (_, src) = first_payload_copy(&body);
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "dead_before_call", mem_config());
        chc_ctx.declare_block_relations();
        let base = chc_ctx.try_state_idx_for_local(src).expect("scrutinee has a state slot");
        let (slot_name, slot_sort) =
            chc_ctx.state_var_mgr.state_vars.get(base + 1).cloned().expect("payload slot");
        let (base_name, base_sort) = chc_ctx.state_var_mgr.state_vars[base].clone();

        chc_ctx.ref_resolution.const_ref_values.insert(src, Expr::bitvec_const(7u64, 32));
        assert!(chc_ctx.source_payload_slot_fact(src).is_none(), "a decoded value is per producer");

        chc_ctx.ref_resolution.const_ref_values.insert(src, Expr::var(&*base_name, base_sort));
        assert!(chc_ctx.source_payload_slot_fact(src).is_none(), "not the payload slot");

        chc_ctx.ref_resolution.const_ref_values.insert(src, Expr::var(&*slot_name, slot_sort));
        assert!(chc_ctx.source_payload_slot_fact(src).is_some());
    });
}

#[test]
fn kept_fact_without_a_recorded_stub_site_fails_closed() {
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "dead_before_call");
        let body = instance.body().expect("function body");
        let (dest, src) = first_payload_copy(&body);
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "dead_before_call", mem_config());
        let sites = chc_ctx.source_call_producer_sites(src, dest).unwrap();
        let before = chc_ctx.diagnostics.place_translation_drop.get();

        chc_ctx.ref_resolution.kept_payload_value_facts.insert((src, dest), sites.clone());
        chc_ctx.verify_kept_payload_value_facts();
        assert_eq!(
            chc_ctx.diagnostics.place_translation_drop.get(),
            before + 1,
            "an unverified producer records a fail-closed drop"
        );

        // A producer block the transition loop skipped reaches no derivation.
        chc_ctx.ref_resolution.untranslated_transition_blocks.extend(sites.iter().copied());
        chc_ctx.verify_kept_payload_value_facts();
        assert_eq!(chc_ctx.diagnostics.place_translation_drop.get(), before + 1);
        chc_ctx.ref_resolution.untranslated_transition_blocks.clear();

        chc_ctx.ref_resolution.payload_slot_fact_sites.entry(src).or_default().extend(sites);
        chc_ctx.verify_kept_payload_value_facts();
        assert_eq!(chc_ctx.diagnostics.place_translation_drop.get(), before + 1);
    });
}

#[test]
fn checked_inline_variant_constructor_declines_a_field_sort_mismatch() {
    let sort = Sort::struct_type("P", [("x", Sort::bv32()), ("y", Sort::bv32())]);
    let matching = checked_inline_variant_constructor(
        "P",
        "P_mk",
        vec![Expr::bitvec_const(1u64, 32), Expr::bitvec_const(2u64, 32)],
        sort.clone(),
    );
    assert!(matching.is_some());
    let mismatched = checked_inline_variant_constructor(
        "P",
        "P_mk",
        vec![Expr::bitvec_const(1u64, 64), Expr::bitvec_const(2u64, 32)],
        sort,
    );
    assert!(mismatched.is_none(), "a BitVec 64 field value is not a BitVec 32 field");
}
