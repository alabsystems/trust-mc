// WRITE_BYTES_ZERO_COUNT_NOOP dual (companion) — proves the no-op is COUNT-GATED.
//
// The zero-count no-op fix in misc_intrinsics_write_bytes.rs must fire ONLY when
// the const-folded count is 0. A count > 0 write must still take full effect:
// it must overwrite memory and, for a value-validity violation, be detected.
//
// Oracle: BOTH harnesses MUST be FAILED. If either SUCCEEDS, the zero-count
// no-op leaked into the count > 0 path (a real over-relaxation / missed bug) —
// fix or revert.
//
// kani-flags: -Z valid-value-checks
#![feature(core_intrinsics)]

/// Direct-observation twin (clean, Genuine): a count == 1 write of an all-ones
/// byte pattern overwrites the value, so asserting the original survived FAILS.
/// Reads the local directly (no raw-pointer deref-load), so the failure is a
/// plain counterexample independent of the value-validity net.
#[kani::proof]
fn nonzero_count_overwrites_value() {
    let mut val: u64 = 0;
    let ptr = &mut val as *mut u64;
    unsafe { std::intrinsics::write_bytes(ptr, 0xFF, 1) };
    assert_eq!(val, 0, "count>0 write must have overwritten val (no-op leaked)");
}

/// Value-validity twin: a count == 1 write of 0xFF bytes into a `char` yields
/// 0xFFFFFFFF, an invalid Unicode scalar. With `-Z valid-value-checks` this is
/// UB and MUST be detected as a failure.
#[kani::proof]
fn nonzero_count_invalid_char() {
    let mut val = 'a';
    let ptr = &mut val as *mut char;
    unsafe { std::intrinsics::write_bytes(ptr, 0xFF, 1) };
    std::hint::black_box(val);
}
