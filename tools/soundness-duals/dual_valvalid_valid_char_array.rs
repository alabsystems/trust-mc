// VALVALID_PUNNED_ARRAY_DUAL — the valid twin of the `[char; N]` punned-read
// fix. `[65, 66]` are `'A'`, `'B'`: both valid Unicode scalars, so the
// type-punned array-index validity read must PROVE SUCCESS with no false
// positive and no `chc_fallback` demotion.
//
// Oracle: MUST be SUCCESSFUL (clean proof).
// kani-flags: -Z valid-value-checks
#[kani::proof]
fn valid_char_array() {
    let val = [65u32, 66u32];
    let _c = unsafe { *(&val as *const [u32; 2] as *const [char; 2]) };
}
