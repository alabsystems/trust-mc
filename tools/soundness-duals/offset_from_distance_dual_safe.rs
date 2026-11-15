// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle: MUST be SUCCESSFUL.
//
// The non-vacuity twin of `offset_from_distance_dual.rs`. Same shape, byte
// distances that ARE exact multiples of `size_of::<u16>()`, so the
// exact-multiple obligation the CHC lane gained in S12 must hold.
//
// It is the witness that the twin's FAILURE comes from the distance check
// firing on a genuinely misaligned distance, and NOT from `offset_from` having
// become unconditionally refutable — which would trade one missed bug for a
// wall of false positives on every legitimate pointer-distance computation.
//
// LANE NOTE — a SECOND defect, which this pair found. Measured 2026-09-14 on
// the frozen dev-cli lane, on the pre-rebase engine and on the rebased one,
// BEFORE and AFTER the S12 CHC fix: the CHC lane proves all three; the **BMC
// lane reports a FALSE CERTIFICATE on all three**. Every harness comes back
//
//     [AY:CTREX_CAT:Genuine]
//     Failed Checks: pointer arithmetic overflow
//     Failed Checks: Offset result and original pointer should point to the
//                    same allocation
//     VERIFICATION:- FAILED
//
// on a `&buf[0]`-derived `*const u8` that never leaves its own 8-byte object.
// `Genuine` means "a real counterexample, no encoding doubt" — so this is a
// CONFIDENT WRONG BUG REPORT, not a demoted false failure, and
// `scripts/soundness-dual-gate.py` classes it `false-certificate` and gates it
// by default.
//
// It is NOT caused by the S12 fix, which touches only
// `chc/call/ptr_offset_common.rs`: the BMC verdicts are identical across it and
// across the rebase onto main, and the same three false certificates appear on
// the **trustc** route as on dev-cli, so it is the engine's, not a route's. Nothing unsound PASSES because of it — no missed
// bug — but a certified counterexample on a safe program is the certification
// channel failing the way a missed bug's proof channel fails, and it is worth
// its own fix. The manifest keeps the expectation `SUCCESSFUL`, so a BMC fix
// flips these green on its own, and marks the BMC rows
// `known_red_class = "false-certificate"` so the defect is reported with its
// evidence rather than hidden by scoping this file to the CHC lane.

/// Two `*const u16` two bytes apart: `2 % 2 == 0`, distance 1 element.
#[kani::proof]
fn safe_offset_from_aligned_distance() {
    let buf: [u8; 8] = [0; 8];
    let base: *const u8 = &buf[0] as *const u8;
    unsafe {
        let lo = base as *const u16;
        let hi = base.add(2) as *const u16;
        assert!(hi.offset_from(lo) == 1);
    }
}

/// A nondeterministically CHOSEN multiple of the element size stays provable.
/// Mirrors `bug_offset_from_symbolic_odd_distance`'s branch shape exactly, so
/// the pair differs in nothing but the parity of the byte distance.
#[kani::proof]
fn safe_offset_from_branch_aligned_distance() {
    let buf: [u8; 8] = [0; 8];
    let base: *const u8 = &buf[0] as *const u8;
    let first: bool = kani::any();
    unsafe {
        let lo = base as *const u16;
        let hi = if first { base.add(2) } else { base.add(4) } as *const u16;
        let d = hi.offset_from(lo);
        assert!(d == 1 || d == 2);
    }
}

/// `size_of::<T>() == 1` has no distance precondition at all: every byte
/// distance is a multiple of 1. This pins the `pointee_size > 1` guard, so a
/// future edit cannot turn the check on for `u8` and false-fail it.
#[kani::proof]
fn safe_offset_from_byte_pointee_any_distance() {
    let buf: [u8; 8] = [0; 8];
    let base: *const u8 = &buf[0] as *const u8;
    unsafe {
        assert!(base.add(3).offset_from(base) == 3);
    }
}
