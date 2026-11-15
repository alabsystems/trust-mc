// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! FC-06 frame net around a call: the call's own argument check is not an
//! effect the net cannot see.
//!
//! `modifies_frame_call_check` emits "the pointee this `&mut` argument may write
//! is assignable" and tags that error rule `modifies_frame_call_arg_overapprox`
//! (SoundHavoc). `frame_net_after_call` used to read that tag as an unseen call
//! effect and record a DEMOTING fallback, so a harness whose every row proved
//! was reported `[chc_fallback=N]` (`interior-mutability/api/cell.rs`,
//! `whole-struct/cell.rs`, ledger row 72). These tests run the real check and
//! the real net on a real call terminator: the check alone must not demote, and
//! any other record inside the same call window still must.

#![allow(clippy::unwrap_used)]

use std::collections::{HashMap, HashSet};

use super::common::*;
use crate::codegen_ay::chc::chc_call_context::DispatchCallContext;
use crate::codegen_ay::chc::modifies_frame::ModifiesFrame;
use rustc_public::mir::TerminatorKind;

const FRAME_CALL_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::Cell;
    pub struct S {
        a: u32,
    }

    #[inline(never)]
    pub fn touch(s: &mut S) {
        s.a = 1;
    }

    pub fn frame_net_probe(s: &mut S) {
        touch(s);
    }

    #[inline(never)]
    pub fn touch_vec(v: &mut Vec<u8>) {
        v.push(7);
    }

    pub fn frame_net_probe_vec(v: &mut Vec<u8>) {
        touch_vec(v);
    }

    pub struct CH<'a> {
        c: Cell<u32>,
        r: &'a Cell<u32>,
    }

    #[inline(never)]
    pub fn touch_cell(c: &Cell<u32>) {
        c.set(5);
    }

    pub fn frame_net_probe_own_cell(h: &CH) {
        touch_cell(&h.c);
    }

    pub fn frame_net_probe_loaded_cell(h: &CH) {
        touch_cell(h.r);
    }

    pub fn frame_net_probe_tuple_cell(h: &CH) {
        let t = (h, 0u8);
        touch_cell(&t.0.c);
    }
"#;

/// Put every block of the probe inside one resolved, footprint-free frame and
/// run `between` between the FC-06 call check and the net's after-call test on
/// the `touch` call. Returns `(demoting fallbacks recorded, FC-06 records)`.
fn run_net_around_touch_call(between: impl Fn(&mut ChcCtx<'_, '_>) + Sync) -> (usize, usize) {
    run_net_around_call("frame_net_probe", "touch", between)
}

/// [`run_net_around_touch_call`] for the call to `callee_suffix` in `fn_name`.
fn run_net_around_call(
    fn_name: &'static str,
    callee_suffix: &'static str,
    between: impl Fn(&mut ChcCtx<'_, '_>) + Sync,
) -> (usize, usize) {
    let mut out = (usize::MAX, usize::MAX);
    let out_ref = &mut out;
    with_test_ay_ctx_for_source(FRAME_CALL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let blocks: HashSet<usize> = (0..body.blocks.len()).collect();
        chc_ctx.modifies_frames = vec![ModifiesFrame {
            enter_bb: 0,
            blocks: blocks.clone(),
            footprint: Vec::new(),
            resolved: true,
            watched: Vec::new(),
            static_footprint: Vec::new(),
            frame_locals: HashSet::new(),
        }];
        chc_ctx.modifies_frame_by_bb =
            blocks.iter().map(|bb| (*bb, 0usize)).collect::<HashMap<_, _>>();

        let mut calls = 0usize;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            let TerminatorKind::Call { func, args, destination, target, .. } =
                &block.terminator.kind
            else {
                continue;
            };
            let callee = chc_ctx.resolve_callee_path(func).unwrap_or_default();
            if callee.rsplit("::").next() != Some(callee_suffix) {
                continue;
            }
            calls += 1;
            let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
            let state_args: Vec<_> = chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .map(|(name, sort)| ay_bindings::Expr::var(name.to_string(), sort.clone()))
                .collect();
            let from_app = RelationApp::new(&from_rel, state_args);
            let stmt_constraints = [ay_bindings::Expr::bool_const(true)];
            let modified_locals = HashSet::new();
            let dcx = DispatchCallContext {
                bb_idx,
                func,
                args,
                destination,
                target,
                from_app: &from_app,
                stmt_constraints: &stmt_constraints,
                modified_locals: &modified_locals,
                callee_path: Some(callee),
            };

            chc_ctx.current_encode_bb = bb_idx;
            let before = chc_ctx.fallback_count;
            let snapshot = chc_ctx.frame_net_call_snapshot();
            assert!(snapshot.is_some(), "the call block is inside the frame's extent");
            chc_ctx.modifies_frame_call_check(&dcx);
            between(&mut chc_ctx);
            chc_ctx.frame_net_after_call(&dcx, true, snapshot);
            *out_ref = (
                chc_ctx.fallback_count - before,
                chc_ctx.modifies_frame_net.call_arg_check_records,
            );
        }
        assert_eq!(calls, 1, "expected exactly one call to `{callee_suffix}` in `{fn_name}`");
    });
    out
}

/// The FC-06 check's own over-approximation tag does not demote the harness.
#[test]
fn frame_net_does_not_demote_on_the_calls_own_arg_check() {
    let (demoted, own_records) = run_net_around_touch_call(|_| {});
    assert_eq!(own_records, 1, "the `&mut S` argument must go through the over-approximated check");
    assert_eq!(
        demoted, 0,
        "the net demoted the harness on the tag of the check it exists to insist on"
    );
}

/// Any other sound-fallback record inside the call window still demotes.
#[test]
fn frame_net_still_demotes_on_any_other_record_in_the_call() {
    for reason in ["nested_call_overapprox", "modifies_frame_call_store_untranslatable"] {
        let (demoted, own_records) = run_net_around_touch_call(|c| {
            c.record_sound_fallback_reason(reason);
        });
        assert_eq!(own_records, 1);
        assert_eq!(demoted, 1, "a `{reason}` record in the call window must still demote");
    }
}

/// A pointee that holds a pointer is NOT covered by the check: through a
/// `&mut Vec<u8>` the call writes the pre-existing heap buffer, which the
/// check's `size_of::<Vec<u8>>()` bytes do not include (T2 review,
/// 2026-09-24: `modifies(v); v.push(7)` into spare capacity was proved clean).
/// The check's tag stays foreign and the net demotes.
#[test]
fn frame_net_demotes_when_the_pointee_holds_a_pointer() {
    let (demoted, own_records) = run_net_around_call("frame_net_probe_vec", "touch_vec", |_| {});
    assert_eq!(own_records, 0, "a Vec pointee must not be booked as covered");
    assert_eq!(demoted, 1, "the call can write the Vec's buffer: the net must demote");
}

/// A pointer-free pointee whose address is a borrow of a field of a function
/// argument's pointee is covered: the check's address is the pointee's.
#[test]
fn frame_net_does_not_demote_on_a_direct_interior_mutable_field() {
    let (demoted, own_records) =
        run_net_around_call("frame_net_probe_own_cell", "touch_cell", |_| {});
    assert_eq!(own_records, 1, "`&h.c` is a direct borrow of a pointer-free Cell");
    assert_eq!(demoted, 0);
}

/// The same pointee reached through a reference LOADED from a struct field is
/// not covered: the check resolved that address inside the containing struct,
/// not at the referent (T2 review, 2026-09-24: `h.r.set(5)` with `r` pointing
/// at a heap Cell was proved clean). The net demotes.
#[test]
fn frame_net_demotes_when_the_argument_is_loaded_from_memory() {
    let (demoted, own_records) =
        run_net_around_call("frame_net_probe_loaded_cell", "touch_cell", |_| {});
    assert_eq!(own_records, 0, "a reference loaded from `h.r` must not be booked as covered");
    assert_eq!(demoted, 1, "the net must demote a call through a loaded reference");
}

/// A direct pointer carried through a local tuple (how Kani's contract wrapper
/// passes the function's arguments) stays direct: the tuple's single
/// definition put the argument in that field and nothing else writes it.
#[test]
fn frame_net_does_not_demote_on_a_pointer_carried_in_a_local_tuple() {
    let (demoted, own_records) =
        run_net_around_call("frame_net_probe_tuple_cell", "touch_cell", |_| {});
    assert_eq!(own_records, 1, "`&t.0.c` with `t = (h, 0)` is a direct borrow of a Cell");
    assert_eq!(demoted, 0);
}
