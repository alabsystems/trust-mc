// Task #71 RefCell representation-lane dual: the historical vacuous-ensures
// false Safe — replace_with stores on the memory-mirror lane while the
// `*im.x.as_ptr()` ensures-read resolved to the flattened state-var lane,
// so a +2 ensures over a +1 body proved VACUOUSLY. With the as_ptr
// referent-address identity both lanes coincide; this harness must FAIL.
// kani-flags: -Zfunction-contracts

use std::cell::RefCell;

struct InteriorMutability {
    x: RefCell<u32>,
}

#[kani::requires(unsafe{*im.x.as_ptr()} < 100)]
#[kani::modifies(&im.x)]
#[kani::ensures(|_| unsafe{*im.x.as_ptr()} == old(unsafe{*im.x.as_ptr()}) + 2)]
fn modify(im: &InteriorMutability) {
    im.x.replace_with(|&mut old| old + 1);
}

#[kani::proof_for_contract(modify)]
fn harness_for_modify() {
    let im: InteriorMutability = InteriorMutability { x: RefCell::new(kani::any()) };
    modify(&im)
}
