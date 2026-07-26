// Raw-alloc in-bounds read — must PASS or demote honestly.
use std::alloc::{Layout, alloc};

#[kani::proof]
fn dual_ra_inbounds() {
    let layout = Layout::from_size_align(8, 1).unwrap();
    unsafe {
        let ptr = alloc(layout);
        *ptr = 0x41;
        *ptr.add(1) = 0x42;
        let v = *ptr.add(1); // previously initialized, in bounds
        assert!(v == 0x42);
    }
}
