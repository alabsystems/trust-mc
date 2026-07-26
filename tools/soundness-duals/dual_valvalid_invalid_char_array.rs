// VALVALID_PUNNED_ARRAY_DUAL — soundness net for the `[char; N]` type-punned
// read bit-faithful validity fix (check_values array-index decomposition,
// `build_array_elem_limit` / `valvalid_punned_array_elem_check`).
//
// A `[u32; 2]` holding `u32::MAX` (not a valid Unicode scalar) read through a
// `*const [char; 2]` pun MUST be detected as invalid — the bit-faithful
// array-index read must NEVER swallow the invalid element into a false SUCCESS.
//
// Oracle: MUST be FAILED — "Invalid value of type `[char; 2]`".
// kani-flags: -Z valid-value-checks
#[kani::proof]
fn invalid_char_array_max() {
    let val = [100u32, u32::MAX];
    let _c = unsafe { *(&val as *const [u32; 2] as *const [char; 2]) };
}
