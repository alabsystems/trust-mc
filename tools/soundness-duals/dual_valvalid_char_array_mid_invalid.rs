// VALVALID_PUNNED_ARRAY_DUAL — offset->index mapping net.
//
// A `[char; 3]` whose MIDDLE element (index 1, byte offset 4) is a lone
// surrogate `0xD800` (an invalid `char`) MUST FAIL. This proves the per-element
// decomposition (`req.offset / elem_stride`) checks EVERY position, not just
// index 0: a wrong offset/stride map, or a check that only reads element 0,
// would falsely prove SUCCESS here.
//
// Oracle: MUST be FAILED — "Invalid value of type `[char; 3]`".
// kani-flags: -Z valid-value-checks
#[kani::proof]
fn char_array_mid_invalid() {
    // 0xD800 is a lone high surrogate: outside 0..=0xD7FF and 0xE000..=0x10FFFF.
    let val = [65u32, 0xD800u32, 66u32];
    let _c = unsafe { *(&val as *const [u32; 3] as *const [char; 3]) };
}
