// Diagnostic: set->get through a struct-field-ref in a PLAIN body (no contract,
// no ensures closure). If this FAILS for x=99 (99+2=101, not <101), then
// field-ref set->get agrees and the dual_a vacuity is the ensures-closure
// boundary. If it PASSES, the address recovery differs between set and get.
use std::cell::Cell;

struct IM {
    x: Cell<u32>,
}

fn helper(im: &IM) {
    im.x.set(im.x.get() + 2);
    assert!(im.x.get() < 101);
}

#[kani::proof]
fn dual_d() {
    let im = IM { x: Cell::new(kani::any()) };
    kani::assume(im.x.get() < 100);
    helper(&im);
}
