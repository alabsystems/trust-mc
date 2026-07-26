// alloc_zeroed then assert a byte is nonzero — must FAIL (bytes are zero).
use std::alloc::{Layout, alloc_zeroed};

#[kani::proof]
fn dual_ra_zeroed_nonzero() {
    let layout = Layout::from_size_align(8, 1).unwrap();
    unsafe {
        let ptr = alloc_zeroed(layout);
        let v = *ptr.add(2); // reads an initialized zero byte
        assert!(v != 0); // ~ERROR: alloc_zeroed byte is 0
    }
}
