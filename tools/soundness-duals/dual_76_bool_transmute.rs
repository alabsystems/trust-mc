// Task #76 dual: bool-transmute validity under `-Z valid-value-checks`.
//
// Run:
//   trust-mc-driver --ay-chc -Z unstable-options -Z valid-value-checks \
//     --harness-timeout=45s dual_76_bool_transmute.rs
//
// Expected: VERIFICATION:- FAILED.
//
// `transmute::<u8, bool>(2)` produces an invalid `bool` (immediate UB in real
// Rust; Kani-with-flag reports the invalid-value failure). trust-mc's backend
// lowers the u8->bool transmute value-normalizing (`x != 0`), so a validity
// check that reads back the materialized destination can never observe the
// invalid byte — the pre-fix false-Safe. The fixed ValidValuePass checks the
// SOURCE operand's bytes (2 is outside 0..=1), which must fail regardless of
// the destination lowering. The branch keeps the transmuted value live.
#[kani::proof]
fn dual_76_bool_invalid_transmute_must_fail() {
    let x: u8 = 2; // neither 0 nor 1 -> invalid bool bitpattern
    let b: bool = unsafe { core::mem::transmute::<u8, bool>(x) };
    // Branch on the transmuted value. In trust-mc's normalized lowering this
    // takes the `true` arm; the verdict must come from the validity check,
    // not from either arm's reachability.
    if b {
        core::hint::black_box(1u8);
    } else {
        core::hint::black_box(0u8);
    }
}
