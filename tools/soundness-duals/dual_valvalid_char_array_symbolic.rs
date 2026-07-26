// VALVALID_PUNNED_ARRAY_DUAL — adversarial symbolic net.
//
// A fully symbolic `[u32; 2]` read as `[char; 2]`: some assignment makes an
// element an invalid `char`, so a BIT-FAITHFUL punned validity read cannot
// prove SUCCESS — it MUST be able to FAIL with a genuine counterexample. (If
// the read havoced the value into an unconstrained result the failure would be
// a spurious `chc_fallback`/EncodingGap instead of Genuine.)
//
// Oracle: MUST be FAILED (a Genuine counterexample exists).
// kani-flags: -Z valid-value-checks
#[kani::proof]
fn symbolic_char_array() {
    let val: [u32; 2] = [kani::any(), kani::any()];
    let _c = unsafe { *(&val as *const [u32; 2] as *const [char; 2]) };
}
