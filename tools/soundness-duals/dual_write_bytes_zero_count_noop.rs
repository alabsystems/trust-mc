// Oracle (per harness) — both are SAFE (the no-op must preserve the value):
//   zero_count_preserves_value -> VERIFICATION:- SUCCESSFUL
//   zero_count_niche_noop      -> VERIFICATION:- SUCCESSFUL
//
// WRITE_BYTES_ZERO_COUNT_NOOP dual — soundness net for the zero-count
// `write_bytes` no-op fix (codegen_call_cmp_string/misc_intrinsics_write_bytes.rs,
// marker `WRITE_BYTES_ZERO_COUNT_NOOP`).
//
// A `write_bytes(ptr, val, 0)` writes ZERO bytes and provably changes no memory.
// The precise-fill lanes require `total_write != 0`, so before the fix a
// zero-count write fell into the generic over-approximation path, which havocs
// the referent AND records a `write_bytes_overapprox` translation-drop that
// demoted the SMT PROOF to a tainted OverApproximation. The fix emits a plain
// identity transition, so the original value must survive the call.
//
// Oracle: BOTH harnesses MUST be SUCCESSFUL. If either FAILS, the "no-op" is not
// actually preserving memory (or is spuriously havocking) — fix or revert.
//
// kani-flags: -Z valid-value-checks
#![feature(core_intrinsics)]

use std::num::NonZeroU8;

/// A zero-count write must leave the original scalar value untouched.
#[kani::proof]
fn zero_count_preserves_value() {
    let mut val: u64 = 0xDEAD_BEEF_CAFE_F00D;
    let ptr = &mut val as *mut u64;
    // count == 0: total no-op.
    unsafe { std::intrinsics::write_bytes(ptr, 0xFF, 0) };
    assert_eq!(val, 0xDEAD_BEEF_CAFE_F00D, "zero-count write must not change memory");
}

/// Mirror of the fixed harness: a zero-count write into a niche `Option` is a
/// no-op, so `None` survives and the value stays valid.
#[kani::proof]
fn zero_count_niche_noop() {
    let mut val: Option<NonZeroU8> = None;
    let ptr = &mut val as *mut _;
    unsafe { std::intrinsics::write_bytes(ptr, 0, 0) };
    assert!(val.is_none(), "zero-count write must preserve the None niche");
}
