// Oracle: MUST be SUCCESSFUL.
//
// The non-vacuity twin of slice_ptr_byte_add_deref_dual.rs. A raw slice
// pointer moved forward and back by the same byte count resolves to the
// original pointer WITH ITS METADATA, so `&*ptr` is valid and the slice still
// has the original length. And a slice pointer whose length is shortened by
// exactly the bytes it was moved still fits the allocation.
//
// WHY THIS FILE EXISTS: tests/expected/ptr_to_ref_cast/slice/test.rs
// (`check_with_byte_add_sub_pass`) was a FALSE POSITIVE on the CHC lane — the
// `wrapping_byte_add` / `wrapping_byte_sub` stubs truncated the fat pointer to
// its data word, dropping the length, so `val.len() == data.len()` failed.
// These harnesses also witness that the slice-extent obligation in the twin
// reads the pointer's OWN metadata (not the allocation size, not a havoc).

#[kani::proof]
fn safe_wrapping_byte_add_sub_roundtrip() {
    let data = [5u8; 5];
    let ptr = &data as *const [u8];
    let offset: usize = kani::any_where(|i| *i < 100);
    let val = unsafe { &*ptr.wrapping_byte_add(offset).wrapping_byte_sub(offset) };
    assert_eq!(val.len(), data.len());
}

#[kani::proof]
fn safe_byte_add_sub_roundtrip() {
    let data = [5u8; 5];
    let ptr = &data as *const [u8];
    let val = unsafe { &*ptr.byte_add(1).byte_sub(1) };
    assert_eq!(val.len(), data.len());
    assert_eq!(val[4], 5);
}

#[kani::proof]
fn safe_byte_add_shortened_slice_fits() {
    let data = [5u8; 5];
    let short = std::ptr::slice_from_raw_parts(data.as_ptr(), 4);
    let val = unsafe { &*short.byte_add(1) };
    assert_eq!(val.len(), 4);
}
