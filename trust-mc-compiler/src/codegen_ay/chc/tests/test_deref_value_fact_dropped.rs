// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! A deref through a reference whose VALUE fact an ambiguous producer dropped.
//!
//! The slice `Iterator::next` stub stores the element in the `Option<&T>`
//! payload slot and records it in `const_ref_values`, so `*payload` resolves to
//! the element. Loop unwinding gives the payload copy one producer per unwound
//! body, `propagate_ref_metadata` drops the fact, and the Mem-level load then
//! selected memory at an "address" equal to the element's value. The CHC
//! counterexample over that free cell was certified Genuine on a safe program
//! (expected/loop-backedge/test.rs). The deref must fail closed instead.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use rustc_public::mir::{Body, Operand, Place, ProjectionElem, Rvalue, StatementKind};

const PROBE_SOURCE: &str = r#"
#![allow(dead_code, unused_assignments, unused_variables)]
pub fn different_borrows(x: u32, y: u32, b: bool) -> u32 {
    let mut r = &x;
    if b {
        r = &y;
    }
    *r
}
"#;

/// `(r, t)`: the reassigned reference `r` (producers `r = &x` and `r = copy t`)
/// and the temp `t` it copies.
fn reference_and_copied_temp(body: &Body) -> (usize, usize) {
    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(lhs, Rvalue::Use(Operand::Copy(src), ..)) = &stmt.kind
                && lhs.projection.is_empty()
                && src.projection.is_empty()
                && body.blocks.iter().flat_map(|b| &b.statements).any(|s| {
                    matches!(&s.kind, StatementKind::Assign(l, Rvalue::Ref(..)) if l.local == lhs.local)
                })
            {
                return (lhs.local, src.local);
            }
        }
    }
    panic!("probe has no `r = copy t` reassignment of a borrowed reference");
}

fn deref_is_bail(
    chc_ctx: &mut ChcCtx<'_, '_>,
    r: usize,
) -> bool {
    use super::super::expr::codegen_expr_deref_resolve::DerefCascadeResult;
    let place = Place { local: r, projection: vec![ProjectionElem::Deref] };
    matches!(
        chc_ctx.try_resolve_deref_cascade(&place, r, &HashSet::new()),
        DerefCascadeResult::Bail
    )
}

#[test]
fn dropped_value_fact_makes_the_deref_fail_closed() {
    use super::super::stmt::codegen_stmt_slice_metadata::RefMetadataOffsetMode;
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "different_borrows");
        let body = instance.body().expect("function body");
        let (r, t) = reference_and_copied_temp(&body);
        let config =
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() };

        // Control: no value fact on `t`, nothing to drop, the deref is not refused
        // by this rule.
        let mut control = ChcCtx::new(ctx.tcx, &body, "different_borrows", config);
        control.declare_block_relations();
        control.propagate_ref_metadata(t, r, 0, "test", false, RefMetadataOffsetMode::Copy);
        assert!(!control.ref_resolution.deref_value_fact_dropped.contains(&r));
        assert!(!deref_is_bail(&mut control, r), "control deref is not refused");

        // `t` carries a value fact standing in for its referent. `r` has two
        // producers, so the copy cannot carry it.
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "different_borrows", config);
        chc_ctx.declare_block_relations();
        chc_ctx.ref_resolution.const_ref_values.insert(t, Expr::bitvec_const(0u64, 32));
        chc_ctx.propagate_ref_metadata(t, r, 0, "test", false, RefMetadataOffsetMode::Copy);
        assert!(
            !chc_ctx.ref_resolution.const_ref_values.contains_key(&r),
            "ambiguous producer: the value fact is not copied"
        );
        assert!(
            chc_ctx.ref_resolution.deref_value_fact_dropped.contains(&r),
            "the dropped value fact is recorded"
        );
        // Clearing path-insensitive metadata (a later producer) keeps the record.
        chc_ctx.clear_path_insensitive_ref_metadata(r);
        assert!(chc_ctx.ref_resolution.deref_value_fact_dropped.contains(&r));
        assert!(deref_is_bail(&mut chc_ctx, r), "the deref fails closed");
    });
}
