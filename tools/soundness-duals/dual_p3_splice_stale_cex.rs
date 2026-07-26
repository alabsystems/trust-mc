// P3-uninit dual (b): partial copy + assert(dst == stale) must CEX —
// the splice must actually CHANGE the low bytes (no self-loop identity).
// Oracle: FAIL with a genuine counterexample.
// kani-flags: -Z uninit-checks

#[repr(C)]
struct S(u32, u8); // 5 bytes of data + 3 bytes of padding.

#[kani::proof]
unsafe fn splice_stale_cex() {
    let from = S(0x1122_3344, 0x55);
    let mut to: u64 = 0xAABB_CCDD_EEFF_0011;

    std::ptr::copy(&from as *const S as *const u8, &mut to as *mut u64 as *mut u8, 4);

    // The splice overwrote bytes 0..4 with fld0 (0x11223344) — asserting the
    // STALE pre-copy value must CEX. (A buggy identity/self-loop encoding
    // would keep `to` stale and PROVE this — which is what this dual guards.)
    assert!(to == 0xAABB_CCDD_EEFF_0011);
}
