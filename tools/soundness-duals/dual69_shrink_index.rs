// Task #69 adversarial dual: Vec shrunk (truncate / resize-smaller) then
// indexed at the OLD length. Real execution panics (index out of bounds), so
// these harnesses must NOT report VERIFICATION:- SUCCESSFUL. A FAILED or a
// demoted-FAILED (OverApproximation/Unknown) verdict are both acceptable; a
// clean SUCCESSFUL is the fail-open bug this task closes.

#[kani::proof]
fn dual69_shrink_index_truncate() {
    let mut v = vec![10u32, 20, 30, 40, 50];
    v.truncate(2);
    // Index at the old length - 1 (4), which is OOB after the shrink to len 2.
    let x = v[4];
    kani::assert(x < 1000, "read after shrink");
}

#[kani::proof]
fn dual69_shrink_index_resize() {
    let mut v = vec![7u32; 6];
    v.resize(2, 0);
    // OOB after resize-smaller: len is 2, index 5 must panic.
    let x = v[5];
    kani::assert(x < 1000, "read after resize-shrink");
}
