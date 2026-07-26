// Task #76 valid twin: `transmute::<u8, bool>(1)` is a VALID bool.
//
// Run:
//   trust-mc-driver --ay-chc -Z unstable-options -Z valid-value-checks \
//     --harness-timeout=45s dual_76_bool_valid_twin.rs
//
// Expected: VERIFICATION:- SUCCESSFUL (byte 1 is inside bool's 0..=1 valid
// range; no UB). This twin pins the validity check as PRECISE, not a blanket
// fail-close: before the #76 fix this harness spuriously FAILED ("memory
// safety") because the destination read-back punned `*const bool` as
// `*const u8`; the source-byte check reads the u8 operand directly.
#[kani::proof]
fn dual_76_bool_valid_transmute_must_pass() {
    let x: u8 = 1;
    let b: bool = unsafe { core::mem::transmute::<u8, bool>(x) };
    if b {
        core::hint::black_box(1u8);
    } else {
        core::hint::black_box(0u8);
    }
}
