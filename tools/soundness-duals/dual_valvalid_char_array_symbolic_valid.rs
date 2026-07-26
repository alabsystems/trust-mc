// VALVALID_PUNNED_ARRAY_DUAL — the constrained (not-over-conservative) twin.
//
// Symbolic `[u32; 2]` elements each ASSUMED into the low valid-`char` range
// `0..=0xD7FF` must PROVE SUCCESS: the array-index punned read is a clean
// bit-faithful proof, not a fallback and not a conservative always-fail. This
// guards against the fix regressing into "sound but spuriously FAILs every
// valid punned read".
//
// (The range is asserted directly rather than via `char::from_u32().is_some()`
// so the oracle isolates the array-read fix from the separate, pre-existing
// imprecision in modeling `char::from_u32` inside an assume.)
//
// Oracle: MUST be SUCCESSFUL.
// kani-flags: -Z valid-value-checks
#[kani::proof]
fn symbolic_char_array_valid() {
    let a = kani::any::<u32>();
    let b = kani::any::<u32>();
    kani::assume(a <= 0xD7FF);
    kani::assume(b <= 0xD7FF);
    let val = [a, b];
    let _c = unsafe { *(&val as *const [u32; 2] as *const [char; 2]) };
}
