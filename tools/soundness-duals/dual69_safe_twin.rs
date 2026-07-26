// Task #69 safe twin: same shrink-then-index shape as dual69_shrink_index.rs
// but the index is IN BOUNDS after the shrink. Must NOT regress to a
// FAILED-Genuine verdict (clean SUCCESSFUL preferred; demoted-Unknown
// acceptable and itemized).

#[kani::proof]
fn dual69_safe_twin_truncate() {
    let mut v = vec![10u32, 20, 30, 40, 50];
    v.truncate(2);
    // In-bounds after shrink: len is 2, index 1 is valid.
    let x = v[1];
    kani::assert(x == 20, "in-bounds read after shrink");
}

#[kani::proof]
fn dual69_safe_twin_resize() {
    let mut v = vec![7u32; 6];
    v.resize(2, 0);
    let x = v[1];
    kani::assert(x == 7, "in-bounds read after resize-shrink");
}
