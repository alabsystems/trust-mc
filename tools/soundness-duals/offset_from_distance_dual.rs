// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Oracle: MUST FAIL — on BOTH lanes, on BOTH compiler routes.
//
// WHY THIS FILE EXISTS — it was a FALSE PROOF with a CLEAN qualifier.
//
// `offset_from` is UB unless the byte distance between the two pointers is an
// EXACT multiple of `size_of::<T>()` (kani_core `models.rs`, `ptr_offset_from`:
// `safety_check(offset_bytes % t_size == 0, "Expected the distance between the
// pointers, in bytes, to be a multiple of the size of `T`")`).
//
// The BMC lane has emitted that obligation since #72
// (`statement/dispatch/ptr_arithmetic.rs`, `ptr_offset_from_exact_multiple`).
// The CHC lane intercepts the same call in `chc/call/ptr_offset_common.rs` and
// replaces the model body wholesale — and it emitted only the
// same-allocation and (unsigned) non-negative halves. The exact-multiple
// obligation existed NOWHERE on the CHC lane, so a harness whose entire
// purpose is this UB came back:
//
//     VERIFICATION:- SUCCESSFUL          0 of 11 failed
//     [AY:PROOF_QUALIFIERS:clean]
//
// Measured 2026-09-14 on `expected/offset-from-distance-check/main.rs`,
// all three counted Trustc CHC runs of Kani-domination ledger row 63. It is
// the ONE `missed_bug` that row carries. The dev-cli route reported FAILED on
// the same source, but for an UNRELATED reason — an over-approximated
// `copy_nonoverlapping::precondition_check` inside the pointer generator — so
// the gap was the ENGINE's on both routes and dev-cli merely masked it.
//
// The harnesses below are concrete on purpose: nothing here depends on the
// pointer generator, on `-Z mem-predicates`, or on which route compiled the
// crate, so a SUCCESSFUL verdict can only mean the exact-multiple obligation
// is missing again.
//
// If either harness ever reports SUCCESSFUL, that false-proof channel is back.

/// One odd byte of distance between two `*const u16`. `1 % 2 != 0`, so
/// `offset_from` is UB and the check must be refuted.
#[kani::proof]
fn bug_offset_from_odd_byte_distance() {
    let buf: [u8; 8] = [0; 8];
    let base: *const u8 = &buf[0] as *const u8;
    unsafe {
        let lo = base as *const u16;
        let hi = base.add(1) as *const u16;
        let _distance = hi.offset_from(lo);
    }
}

/// The same UB reached through a nondeterministically CHOSEN odd offset, so the
/// refutation cannot come from constant-folding one arithmetic expression. Both
/// branches are odd, so every path is UB and the check must be refuted on both.
///
/// The offset is picked by a branch rather than computed from a symbolic
/// `usize`: `base.add(<symbolic>)` leaves the engine's provenance walk
/// unresolved (`[AY:DEMOTION_REASONS:offset_provenance_unresolved=1]`), which
/// demotes a PROOF to FAILED and would let this harness pass the gate
/// VACUOUSLY — FAILED for want of a certificate rather than because the
/// distance check fired. Keeping both offsets concrete per path keeps the
/// tripwire honest.
#[kani::proof]
fn bug_offset_from_symbolic_odd_distance() {
    let buf: [u8; 8] = [0; 8];
    let base: *const u8 = &buf[0] as *const u8;
    let first: bool = kani::any();
    unsafe {
        let lo = base as *const u16;
        let hi = if first { base.add(1) } else { base.add(3) } as *const u16;
        let _distance = hi.offset_from(lo);
    }
}
