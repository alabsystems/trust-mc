// KEYSTONE #52 DUAL (e) — one-past-end WRITE through an offset-derived stack
// pointer. The store-side strict bound (deref_mem) must catch it. MUST FAIL.

#[kani::proof]
fn dual_e_oob_write() {
    let mut arr: [i32; 4] = [1, 2, 3, 4];
    let p: *mut i32 = arr.as_mut_ptr();
    unsafe {
        *p.add(4) = 9; // one-past-end write: UB — MUST FAIL
    }
    std::hint::black_box(arr[0]);
}
