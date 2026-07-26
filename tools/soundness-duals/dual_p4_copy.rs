// Dual for P4 fix 1 (overlap-legal `copy` precise encoding).
// BOTH harnesses must FAIL:
//  - dual_copy_count_exceeds_dst_room: the dst room check must survive the
//    disjointness suppression (count 4 > dst room 2).
//  - dual_copy_overlap_wrong_value: the overlap value model must be memmove
//    semantics, not havoc/anything-goes (arr[2] is 1 after the copy, not 0).
#![feature(core_intrinsics)]

#[kani::proof]
fn dual_copy_count_exceeds_dst_room() {
    let src: [i32; 4] = [1, 2, 3, 4];
    let mut dst: [i32; 2] = [0, 0];
    unsafe {
        core::intrinsics::copy(src.as_ptr(), dst.as_mut_ptr(), 4);
    }
    assert!(dst[0] == 1);
}

#[kani::proof]
fn dual_copy_overlap_wrong_value() {
    let arr: [i32; 3] = [0, 1, 0];
    let src: *const i32 = arr.as_ptr();
    unsafe {
        let dst = src.add(1) as *mut i32;
        core::intrinsics::copy(src, dst, 2);
        // Real result: arr == [0, 0, 1]; this assert is WRONG and must FAIL.
        assert!(arr[2] == 0);
    }
}
