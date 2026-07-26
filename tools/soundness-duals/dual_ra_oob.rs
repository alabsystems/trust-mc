// Raw-alloc OOB read past size via from_raw_parts+index — must FAIL.
use std::alloc::{Layout, alloc};
use std::slice::from_raw_parts;

#[kani::proof]
fn dual_ra_oob() {
    let layout = Layout::from_size_align(4, 1).unwrap();
    unsafe {
        let ptr = alloc(layout);
        *ptr = 1;
        *ptr.add(1) = 2;
        *ptr.add(2) = 3;
        *ptr.add(3) = 4;
        // Read at offset 8 — well past the 4-byte allocation. UB.
        let v = *ptr.add(8); // ~ERROR: out of bounds
        assert!(v == v);
    }
}
