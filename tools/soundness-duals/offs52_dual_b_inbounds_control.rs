// KEYSTONE #52 DUAL (b) — in-bounds offset+deref control on a stack array.
// MUST PASS (SUCCESSFUL, no demotion): with the stack-provenance lane the
// offset site resolves (obj = arr, size 16), the real bound `12 <= 16`
// discharges, and the deref of arr[3] is in-bounds.

#[kani::proof]
fn dual_b_offset_inbounds_stack() {
    let arr: [i32; 4] = [1, 2, 3, 4];
    let p: *const i32 = arr.as_ptr();
    unsafe {
        let x = *p.add(3); // last element: legal
        assert_eq!(x, 4);
    }
}
