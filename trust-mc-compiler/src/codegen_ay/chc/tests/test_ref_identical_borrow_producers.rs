// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Pass 1 points-at edges for a reference with several producers.
//!
//! Loop unwinding duplicates a `for` body, so the iterator re-borrow
//! (`_14 = &mut _12`) is assigned in every copy. Pass 1 used to refuse the
//! points-at edge for any reference with more than one whole definition, which
//! left `Iterator::next` reading the reference's raw pointer and failing closed
//! ("Vec iter stub requested fail-closed error"). The edge is sound when every
//! producer is the same borrow of the same fixed place, and only then.
//!
//! Plain rustc MIR never re-borrows into the same local (a reassignment goes
//! through a temp: `_4 = &_1; _3 = copy _4`), so these tests compile a probe and
//! then rewrite the `copy` producer into the borrow shape unwinding produces.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use rustc_public::mir::{Body, Rvalue, StatementKind};
use super::super::codegen_ctx::RefTarget;

const PROBE_SOURCE: &str = r#"
#![allow(dead_code, unused_assignments, unused_variables)]
pub fn same_borrow_twice(x: u32, b: bool) -> u32 {
    let mut r = &x;
    if b {
        r = &x;
    }
    *r
}
pub fn different_borrows(x: u32, y: u32, b: bool) -> u32 {
    let mut r = &x;
    if b {
        r = &y;
    }
    *r
}
pub fn indexed_borrows(a: [u32; 4], i: usize, j: usize, b: bool) -> u32 {
    let mut r = &a[i];
    if b {
        r = &a[j];
    }
    *r
}
"#;

/// Locate the reassigned reference local: the one whose whole definitions are
/// a borrow and a `copy` of a temp that holds a borrow. Returns
/// `(ref_local, (block, stmt) of the copy producer, temp's borrow rvalue)`.
fn reassigned_reference(body: &Body) -> (usize, (usize, usize), Rvalue) {
    let mut borrows: std::collections::HashMap<usize, Rvalue> = std::collections::HashMap::new();
    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(lhs, rhs @ Rvalue::Ref(..)) = &stmt.kind
                && lhs.projection.is_empty()
            {
                borrows.insert(lhs.local, rhs.clone());
            }
        }
    }
    for (bi, block) in body.blocks.iter().enumerate() {
        for (si, stmt) in block.statements.iter().enumerate() {
            if let StatementKind::Assign(lhs, Rvalue::Use(Operand::Copy(src), ..)) = &stmt.kind
                && lhs.projection.is_empty()
                && src.projection.is_empty()
                && borrows.contains_key(&lhs.local)
                && let Some(temp_borrow) = borrows.get(&src.local)
            {
                return (lhs.local, (bi, si), temp_borrow.clone());
            }
        }
    }
    panic!("probe has no `r = copy tmp` reassignment of a borrowed reference");
}

/// Rewrite the `copy` producer of the reassigned reference into `rvalue`.
fn with_producer(body: &Body, at: (usize, usize), ref_local: usize, rvalue: Rvalue) -> Body {
    let mut body = body.clone();
    let stmt = &mut body.blocks[at.0].statements[at.1];
    let StatementKind::Assign(lhs, _) = &stmt.kind else { unreachable!() };
    assert_eq!(lhs.local, ref_local);
    stmt.kind = StatementKind::Assign(lhs.clone(), rvalue);
    body
}

/// The original borrow producer of `ref_local` (not the copy).
fn first_borrow_of(body: &Body, ref_local: usize) -> Rvalue {
    body.blocks
        .iter()
        .flat_map(|b| &b.statements)
        .find_map(|s| match &s.kind {
            StatementKind::Assign(lhs, rhs @ Rvalue::Ref(..)) if lhs.local == ref_local => {
                Some(rhs.clone())
            }
            _ => None,
        })
        .expect("reference has a borrow producer")
}

fn ref_target_after_pass1(tcx: TyCtxt<'_>, body: &Body, name: &str, local: usize) -> Option<(usize, usize)> {
    let mut chc_ctx = ChcCtx::new(tcx, body, name, ChcConfig::default());
    chc_ctx.declare_block_relations();
    chc_ctx.ref_resolution.ref_targets.get(&local).map(|t| (t.local, t.projections.len()))
}

#[test]
fn identical_borrow_producers_keep_the_points_at_edge() {
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "same_borrow_twice");
        let body = instance.body().expect("function body");
        let (r, copy_at, _temp_borrow) = reassigned_reference(&body);
        let borrow = first_borrow_of(&body, r);
        let Rvalue::Ref(_, _, place) = &borrow else { unreachable!() };
        let pointee = place.local;

        // Unedited MIR: `r` has a borrow and a copy producer -> no edge.
        assert_eq!(ref_target_after_pass1(ctx.tcx, &body, "same_borrow_twice", r), None);

        // Both producers are `&x` -> the edge holds on every path.
        let unwound = with_producer(&body, copy_at, r, borrow.clone());
        assert_eq!(
            ref_target_after_pass1(ctx.tcx, &unwound, "same_borrow_twice", r),
            Some((pointee, 0)),
            "identical borrows of one fixed place must keep the points-at edge"
        );
    });
}

#[test]
fn borrows_of_different_places_get_no_edge() {
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "different_borrows");
        let body = instance.body().expect("function body");
        let (r, copy_at, temp_borrow) = reassigned_reference(&body);
        // Producers `&x` and `&y`: a single edge would be wrong on one path.
        let edited = with_producer(&body, copy_at, r, temp_borrow);
        assert_eq!(
            ref_target_after_pass1(ctx.tcx, &edited, "different_borrows", r),
            None,
            "borrows of different places must not collapse into one edge"
        );
    });
}

#[test]
fn identical_indexed_borrows_get_no_edge() {
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "indexed_borrows");
        let body = instance.body().expect("function body");
        let (r, copy_at, _temp_borrow) = reassigned_reference(&body);
        // Both producers are literally `&a[i]`, but `i` can change between
        // them, so the address is not fixed: no edge.
        let borrow = first_borrow_of(&body, r);
        let edited = with_producer(&body, copy_at, r, borrow);
        assert_eq!(
            ref_target_after_pass1(ctx.tcx, &edited, "indexed_borrows", r),
            None,
            "an Index projection is not a fixed location"
        );
    });
}

/// Statement translation re-visits every producer and calls
/// `clear_borrow_metadata_keeping_exact_edge`. It used to keep the exact edge
/// only for a single-producer reference, so the edge Pass 1 now records was
/// erased again at the first duplicated borrow.
fn edge_after_statement_clear(
    tcx: TyCtxt<'_>,
    body: &Body,
    name: &str,
    ref_local: usize,
    borrow: &Rvalue,
) -> Option<usize> {
    let Rvalue::Ref(_, _, place) = borrow else { unreachable!() };
    let mut chc_ctx = ChcCtx::new(tcx, body, name, ChcConfig::default());
    chc_ctx.declare_block_relations();
    chc_ctx.ref_resolution.ref_targets.insert(
        ref_local,
        RefTarget::with_projections(place.local, place.projection.clone()),
    );
    chc_ctx.clear_borrow_metadata_keeping_exact_edge(ref_local, place);
    chc_ctx.ref_resolution.ref_targets.get(&ref_local).map(|t| t.local)
}

#[test]
fn statement_clear_keeps_the_edge_for_identical_borrow_producers() {
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "same_borrow_twice");
        let body = instance.body().expect("function body");
        let (r, copy_at, _temp_borrow) = reassigned_reference(&body);
        let borrow = first_borrow_of(&body, r);
        let Rvalue::Ref(_, _, place) = &borrow else { unreachable!() };
        let pointee = place.local;
        let unwound = with_producer(&body, copy_at, r, borrow.clone());
        assert_eq!(
            edge_after_statement_clear(ctx.tcx, &unwound, "same_borrow_twice", r, &borrow),
            Some(pointee),
            "every producer borrows the same place: the exact edge must survive"
        );
    });
}

#[test]
fn statement_clear_drops_the_edge_for_different_borrow_producers() {
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "different_borrows");
        let body = instance.body().expect("function body");
        let (r, copy_at, temp_borrow) = reassigned_reference(&body);
        let first = first_borrow_of(&body, r);
        let edited = with_producer(&body, copy_at, r, temp_borrow);
        assert_eq!(
            edge_after_statement_clear(ctx.tcx, &edited, "different_borrows", r, &first),
            None,
            "producers borrow different places: no single edge holds on every path"
        );
    });
}

/// Loop unwinding also duplicates the COPY of a reference
/// (`_21 = copy _15` before `spec_next(move _21)`), so a destination whose every
/// producer is the same copy of a source with a path-insensitive edge must
/// inherit that edge — at collection time (Pass 1.5) and at statement time.
fn body_with_every_producer_of(body: &Body, local: usize, rvalue: &Rvalue) -> Body {
    let mut body = body.clone();
    for block in &mut body.blocks {
        for stmt in &mut block.statements {
            if let StatementKind::Assign(lhs, _) = &stmt.kind
                && lhs.local == local
                && lhs.projection.is_empty()
            {
                stmt.kind = StatementKind::Assign(lhs.clone(), rvalue.clone());
            }
        }
    }
    body
}

#[test]
fn identical_copy_producers_inherit_the_edge_at_collection_and_statement_time() {
    use super::super::stmt::codegen_stmt_slice_metadata::RefMetadataOffsetMode;
    use rustc_public::mir::{Operand, Place};
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "same_borrow_twice");
        let body = instance.body().expect("function body");
        // `r` (the reassigned reference) and its temp `t` with `t = &x`.
        let (r, _copy_at, temp_borrow) = reassigned_reference(&body);
        let Rvalue::Ref(_, _, pointee_place) = &temp_borrow else { unreachable!() };
        let pointee = pointee_place.local;
        let t = body
            .blocks
            .iter()
            .flat_map(|b| &b.statements)
            .find_map(|s| match &s.kind {
                StatementKind::Assign(lhs, rhs) if *rhs == temp_borrow && lhs.local != r => {
                    Some(lhs.local)
                }
                _ => None,
            })
            .expect("temp borrow local");
        let copy_t = rvalue_use!(Rvalue::Use(Operand::Copy(Place { local: t, projection: vec![] })));
        let unwound = body_with_every_producer_of(&body, r, &copy_t);

        // Collection time: Pass 1 gives t -> x, Pass 1.5 must carry it to r.
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &unwound, "same_borrow_twice", ChcConfig::default());
        chc_ctx.declare_block_relations();
        assert!(chc_ctx.whole_definitions_all_same_copy_of(r, t));
        assert_eq!(
            chc_ctx.ref_resolution.ref_targets.get(&t).map(|e| e.local),
            Some(pointee),
            "the copied borrow itself has its edge"
        );
        assert_eq!(
            chc_ctx.ref_resolution.ref_targets.get(&r).map(|e| e.local),
            Some(pointee),
            "Pass 1.5: identical copies of t inherit t's edge"
        );

        // Statement time: the same edge is restored by propagate_ref_metadata.
        chc_ctx.ref_resolution.ref_targets.remove(&r);
        chc_ctx.propagate_ref_metadata(t, r, 0, "test", false, RefMetadataOffsetMode::Copy);
        assert_eq!(
            chc_ctx.ref_resolution.ref_targets.get(&r).map(|e| e.local),
            Some(pointee),
            "statement lane: identical copies keep the exact edge"
        );
    });
}

#[test]
fn mixed_borrow_and_copy_producers_get_no_edge() {
    use super::super::stmt::codegen_stmt_slice_metadata::RefMetadataOffsetMode;
    with_test_ay_ctx_for_source(PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "different_borrows");
        let body = instance.body().expect("function body");
        // Unedited: r = &x; t = &y; r = copy t. Producers of r are mixed.
        let (r, _copy_at, temp_borrow) = reassigned_reference(&body);
        let t = body
            .blocks
            .iter()
            .flat_map(|b| &b.statements)
            .find_map(|s| match &s.kind {
                StatementKind::Assign(lhs, rhs) if *rhs == temp_borrow && lhs.local != r => {
                    Some(lhs.local)
                }
                _ => None,
            })
            .expect("temp borrow local");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "different_borrows", ChcConfig::default());
        chc_ctx.declare_block_relations();
        assert!(!chc_ctx.whole_definitions_all_same_copy_of(r, t));
        assert_eq!(
            chc_ctx.ref_resolution.ref_targets.get(&r).map(|e| e.local),
            None,
            "Pass 1.5: no edge for r"
        );
        chc_ctx.propagate_ref_metadata(t, r, 0, "test", false, RefMetadataOffsetMode::Copy);
        assert_eq!(
            chc_ctx.ref_resolution.ref_targets.get(&r).map(|e| e.local),
            None,
            "statement lane: mixed producers keep no edge"
        );
    });
}
