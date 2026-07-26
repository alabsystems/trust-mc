// P3-uninit dual (c): correct-value twin — the byte-splice must place the
// copied bytes at the RIGHT byte offsets (LE) and preserve the rest.
// Oracle: PASS (1 successfully verified harness), with NO demotions.
// kani-flags: -Z uninit-checks

#[repr(C)]
struct S(u32, u8); // 5 bytes of data + 3 bytes of padding.

#[kani::proof]
unsafe fn splice_value_pass() {
    let from = S(0x1122_3344, 0x55);
    let mut to: u64 = 0xAABB_CCDD_EEFF_0011;

    // Copy the first 4 bytes (fld0, LE) into the low 4 bytes of `to`.
    std::ptr::copy(&from as *const S as *const u8, &mut to as *mut u64 as *mut u8, 4);

    // LE byte order: low 32 bits = fld0; high 32 bits preserved.
    assert!(to & 0xFFFF_FFFF == 0x1122_3344);
    assert!(to >> 32 == 0xAABB_CCDD);
}
