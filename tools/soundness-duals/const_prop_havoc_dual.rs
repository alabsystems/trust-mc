// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a slot the encoder HAVOCS must stay havocked through the
//! emit-time folding passes, even when its input is a constant.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, Kani 0.67.0, measured
//! 2026-09-25; see the manifest entry):
//!   bug_invariant_fixup_stale_cell           -> FAILED ('assertion failed: a[3] == 4')
//!   safe_invariant_fixup_written_cell        -> SUCCESSFUL
//!   safe_invariant_fixup_untouched_cell      -> SUCCESSFUL
//!   bug_fail_closed_store_then_call          -> FAILED ('assertion failed: o.inner.arr[0] == 0')
//!   safe_fail_closed_store_then_call         -> SUCCESSFUL
//!   bug_fail_closed_store_symbolic_index     -> FAILED ('assertion failed: o.inner.arr[i] == 0')
//!   safe_constants_through_unchanged_frames  -> SUCCESSFUL
//!   safe_scalar_constant_through_calls       -> SUCCESSFUL
//!
//! MECHANISM. A clause variable is universally quantified over its clause, so
//! a head argument `X__out` that no constraint of the rule binds is a HAVOC of
//! the slot. The encoder uses exactly that on purpose: the
//! constraint-or-unchanged fix-up (#3138, `constraint_invariant_fixup`) for a
//! local it marked modified without a constraint, `havoc_local_fail_closed`
//! for every flattened slot of an owner whose store it could not place, and
//! every audited `SoundHavoc` site. Two emit-time passes read such an unbound
//! `X__out` as the identity `X__out = X` instead:
//! - constant propagation (trust-mc-core `chc_const_prop_eval.rs`,
//!   `propagate_to_unconstrained_out_vars`) copied a known constant from `X`
//!   onto `X__out`;
//! - the scalarizer's read-only array fold (`scalarize_arrays/const_fold.rs`)
//!   counted an array whose output no transition CONSTRAINT mentions as never
//!   written, so it folded the reads of a havocked array to its entry values.
//! Either one put the stale value back before the solver ran. The
//! `invariant_fixup` rows lose the callee's write to the last cell of a slice
//! pattern, and the fix-up havocs the caller's array: constant propagation
//! re-bound its four scalarized lanes to 1, 2, 3, 4. The `fail_closed` rows
//! store into an array inside a single-field wrapper through a reference, which
//! the flattened owner cannot place (`flat_field_index_store_unresolved`, a
//! FailClose havoc of every slot): constant propagation re-bound the lanes of
//! `o.inner.arr`, and the array fold also counted the havocked array as
//! read-only.
//!
//! On the main bundle bdacee559 (driver 63a39f679181, ay 4378d73a4, chc, 30s)
//! every bug_ row was PROVED by the encoding: `bug_invariant_fixup_stale_cell`
//! proved the false `a[3] == 4` from a false error obligation and reached
//! FAILED only because an unrelated counter (`store_dropped_transition`)
//! demoted the proof; the two `fail_closed` bug rows reached FAILED only
//! through the FailClose demotion. Each pinned check read SUCCESS. With both
//! passes fixed each bug_ row FAILS on Kani's check from a solver
//! counterexample, tagged `OverApproximation` or `EncodingGap` because the
//! value it reads is a havoc.
//!
//! The safe rows keep the precision gap honest: Kani verifies them, and the
//! havoc makes them FAILED without a Genuine certificate (NOT_GENUINE). The
//! two constant rows guard the other direction: a constant carried through
//! unchanged frames (the INPUT variable in the head) still folds, and those
//! rows stay SUCCESSFUL clean.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s const_prop_havoc_dual.rs

// The slice pattern `[.., x]` behind a `&mut [i64]` parameter: the write the
// callee makes to the last cell is not mirrored into the caller's array.
fn set_last(a: &mut [i64]) {
    match a {
        [.., x] => *x = 99,
        _ => {}
    }
}

#[kani::proof]
fn bug_invariant_fixup_stale_cell() {
    let mut a: [i64; 4] = [1, 2, 3, 4];
    set_last(&mut a);
    assert!(a[3] == 4);
}

#[kani::proof]
fn safe_invariant_fixup_written_cell() {
    let mut a: [i64; 4] = [1, 2, 3, 4];
    set_last(&mut a);
    assert!(a[3] == 99);
}

#[kani::proof]
fn safe_invariant_fixup_untouched_cell() {
    let mut a: [i64; 4] = [1, 2, 3, 4];
    set_last(&mut a);
    assert!(a[0] == 1);
}

// A single-field array wrapper: `translate_ty(AQ)` is the array's sort, so a
// store through `&mut o.inner` into `arr[k]` has no flattened slot and fails
// closed.
pub struct A2 {
    x: [u8; 2],
    y: [u8; 2],
}
pub struct AQ {
    arr: [u8; 2],
}
pub struct PA {
    pre: A2,
    inner: AQ,
    c: u8,
}
fn mk_pa() -> PA {
    PA { pre: A2 { x: [0; 2], y: [0; 2] }, inner: AQ { arr: [0; 2] }, c: 0 }
}
#[inline(never)]
fn nop(v: u8) -> u8 {
    v
}

#[kani::proof]
fn bug_fail_closed_store_then_call() {
    let mut o = mk_pa();
    let v: u8 = kani::any();
    kani::assume(v != 0);
    let r = &mut o.inner;
    r.arr[0] = v;
    nop(v);
    assert!(o.inner.arr[0] == 0);
}

#[kani::proof]
fn safe_fail_closed_store_then_call() {
    let mut o = mk_pa();
    let v: u8 = kani::any();
    let r = &mut o.inner;
    r.arr[0] = v;
    nop(v);
    assert!(o.inner.arr[0] == v);
}

#[kani::proof]
fn bug_fail_closed_store_symbolic_index() {
    let mut o = mk_pa();
    let i: usize = kani::any();
    kani::assume(i < 2);
    let v: u8 = kani::any();
    kani::assume(v != 0);
    let r = &mut o.inner;
    r.arr[i] = v;
    assert!(o.inner.arr[i] == 0);
}

// Precision controls: constants carried through unchanged frames still fold.
#[kani::proof]
fn safe_constants_through_unchanged_frames() {
    let mut o = mk_pa();
    let v: u8 = kani::any();
    nop(v);
    o.c = 3;
    nop(v);
    assert!(o.inner.arr[0] == 0 && o.pre.x[1] == 0 && o.c == 3);
}

#[kani::proof]
fn safe_scalar_constant_through_calls() {
    let mut x: u8 = 5;
    let v: u8 = kani::any();
    nop(v);
    x += 1;
    nop(v);
    assert!(x == 6);
}
