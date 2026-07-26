// SOUNDNESS DUAL — offset in-bounds provenance net (THE CRITICAL ONE).
//
// Marker: offset_isize_overflow_precise_dual (grep-anchor for the fix).
//
// A non-ZST offset whose count (100) fits isize AND whose byte product
// (100 * 1 = 100) fits isize — so obligation (1) (isize-overflow) is
// SATISFIED — but which steps a 4-byte stack allocation out of bounds
// (byte 100 >> one-past-end at 4). This is caught ONLY by obligation (2),
// the in-bounds / allocation-size provenance net (offset-site alloc bound
// and/or the deref-site strict bound).
//
// MUST be FAILED. If this flips to SUCCESSFUL, the fix wrongly gated off
// the provenance/in-bounds net (marked the site "resolved", or dropped the
// bound) — a false-Safe (missed bug). Verify FAILED both BEFORE and AFTER
// the change: the fix must be strictly a ZST/obligation-1 refinement and
// leave this untouched.
#[kani::proof]
fn dual_offset_inbounds_net() {
    let a = [0u8; 4];
    let p = a.as_ptr();
    unsafe {
        let q = p.add(100); // in isize, but OOB of the 4-byte allocation
        let v = *q; // OOB deref
        std::hint::black_box(v);
    }
}
