// KEYSTONE #52 DUAL (d) — offset strictly beyond one-past-end on a stack
// array. `p.add(5)` on [i32;4] (16 bytes) lands at byte 20 > 16: the
// OFFSET-site alloc bound itself (result_offset <= 16) must catch it,
// independent of any deref. MUST FAIL.

#[kani::proof]
fn dual_d_offset_beyond_end() {
    let arr: [i32; 4] = [1, 2, 3, 4];
    let p: *const i32 = arr.as_ptr();
    unsafe {
        let q = p.add(5); // beyond one-past-end: UB at the offset itself
        std::hint::black_box(q);
    }
}
