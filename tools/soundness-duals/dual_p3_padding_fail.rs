// P3-uninit dual (a): a copy crossing into padding, then reading the
// padding bytes, must still FAIL under -Z uninit-checks (the splice must
// not bless the copied padding's init state).
// Oracle: FAIL (uninit read via the shadow-memory Is-check).
// kani-flags: -Z uninit-checks

#[repr(C)]
#[derive(kani::Arbitrary)]
struct S(u32, u8); // 5 bytes of data + 3 bytes of padding.

#[kani::proof]
unsafe fn padding_fail() {
    let from: S = kani::any();
    let mut to: u64 = kani::any();
    let from_ptr = &from as *const S;
    let to_ptr = &mut to as *mut u64;

    // Copies all 8 bytes, including the 3 uninitialized padding bytes.
    std::ptr::copy(from_ptr as *const u8, to_ptr as *mut u8, 8);

    // Reads the copied-uninit padding bytes through the RAW pointer — UB,
    // must FAIL. (A fresh safe borrow `&to` would BLESS the referent per the
    // Kani mem-init model — safe references assert initialization — so the
    // read must go through the raw pointer, as in the Kani suite tests.)
    let _v: u64 = std::ptr::read(to_ptr);
}
