// KEYSTONE #52 DUAL (f) — chained offsets netting BELOW the allocation base.
// p.add(1).sub(2) lands at byte -4: UB at the second offset. MUST FAIL.
#[kani::proof]
fn dual_f_chain_underflow() {
    let arr: [i32; 4] = [1, 2, 3, 4];
    let p: *const i32 = arr.as_ptr();
    unsafe {
        let q = p.add(1).sub(2); // net -1 element: below base — UB
        std::hint::black_box(q);
    }
}
