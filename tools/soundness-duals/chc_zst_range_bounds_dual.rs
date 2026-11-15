// Oracle: corpus-rev Kani 4c0fce8c3, measured 2026-09-26: every `bug_` harness
// FAILS and every `safe_` harness is SUCCESSFUL.
//
// WHY THIS FILE EXISTS: a range index of a zero-sized-element slice (`&z[..n]`
// with `z: [(); 8]`) is answered by emit_slice_index_zst, which writes a
// canonical zero and emits no range bounds check at all. On main 25905b622 (ay
// 643b2851f, chc) both past-the-end bug_ rows PROVED (SUCCESSFUL, clean): the
// panic Kani reports ("range end index 10 out of range for slice of length 8")
// was never modelled. On fix/chc-slice-length the design 4 write boundary gives
// the zero it writes into the wide `&[()]` slot a fresh length, booked
// fail-closed, so the proof is demoted and the bug_ rows FAIL
// (OverApproximation). That is the only thing standing between them and a
// clean proof: giving the ZST sub-range an exact length (the review's optional
// precision fix) without adding the range bounds check re-opens both missed
// bugs. The u8 control has the check and FAILS Genuine on both bundles.

#[kani::proof]
fn bug_zst_range_to_past_end() {
    let z = [(); 8];
    let n: usize = kani::any();
    kani::assume(n <= 10);
    let _s = &z[..n];
}

#[kani::proof]
fn bug_zst_range_from_past_end() {
    let z = [(); 8];
    let n: usize = kani::any();
    kani::assume(n <= 10);
    let _s = &z[n..];
}

#[kani::proof]
fn safe_zst_range_to_in_bounds() {
    let z = [(); 8];
    let n: usize = kani::any();
    kani::assume(n <= 8);
    let _s = &z[..n];
}

#[kani::proof]
fn bug_u8_range_to_past_end() {
    let z = [0u8; 8];
    let n: usize = kani::any();
    kani::assume(n <= 10);
    let _s = &z[..n];
}
