// Oracle: MUST FAIL.
//
// A raw SLICE pointer moved with `byte_add` / `wrapping_byte_add` keeps its
// metadata (`with_metadata_of(self)`), so the slice it describes still claims
// `len` elements but now starts inside the allocation. Turning it back into a
// reference (`&*ptr`) asserts validity for the whole
// `data .. data + len * size_of::<T>()` extent, which runs past the end of the
// array. Kani: "dereference failure: pointer invalid" on every harness.
//
// WHY THIS FILE EXISTS: tests/expected/ptr_to_ref_cast/slice/test.rs
// (`check_with_byte_add_fail`) scored a MISSED BUG on the CHC lane — the
// reference check at `&*raw` only knew SIZED pointees, and `[T]` has no static
// size, so the obligation was silently absent and the harness proved clean.
//
// If any harness here reports SUCCESSFUL, the slice-extent obligation at the
// raw-to-reference cast is gone again.

#[kani::proof]
fn bug_byte_add_u8_slice_deref() {
    let data = [5u8; 5];
    let ptr = &data as *const [u8];
    let val = unsafe { &*ptr.byte_add(1) };
    assert_eq!(val.len(), data.len());
}

#[kani::proof]
fn bug_byte_add_u32_slice_deref() {
    let data = [7u32; 3];
    let ptr = &data as *const [u32];
    // In bounds for `byte_add` itself (one element), out of bounds for the
    // 3-element extent the unchanged metadata still claims.
    let val = unsafe { &*ptr.byte_add(4) };
    assert_eq!(val.len(), 3);
}

#[kani::proof]
fn bug_wrapping_byte_add_slice_deref() {
    let data = [5u8; 5];
    let ptr = &data as *const [u8];
    let val = unsafe { &*ptr.wrapping_byte_add(1) };
    assert_eq!(val.len(), data.len());
}

// The byte-step stubs used to zero-pad the length of a wide pointer whose
// bit value came from an array unsizing, and `len()` of the result read the
// padding as 0. This FALSE assertion then proved clean: the round-trip keeps
// the original length, so `val.len() != data.len()` must be refuted.
#[kani::proof]
fn bug_wrapping_roundtrip_len_is_not_fabricated() {
    let data = [5u8; 5];
    let ptr = &data as *const [u8];
    let offset: usize = kani::any_where(|i| *i < 100);
    let val = unsafe { &*ptr.wrapping_byte_add(offset).wrapping_byte_sub(offset) };
    assert!(val.len() != data.len());
}
