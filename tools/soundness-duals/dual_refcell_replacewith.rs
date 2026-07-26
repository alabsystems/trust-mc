// refcell soundness dual: replace_with(+2), requires <100, ensures <101.
// MUST FAIL (x=99 -> 101). Proves replace_with store + as_ptr ensures-read agree.
// kani-flags: -Zfunction-contracts -Z unstable-options --cbmc-args --object-bits 12
use std::cell::RefCell;
struct IM { x: RefCell<u32> }
#[kani::requires(unsafe{*im.x.as_ptr()} < 100)]
#[kani::modifies(&im.x)]
#[kani::ensures(|_| unsafe{*im.x.as_ptr()} < 101)]
fn modify(im: &IM) { im.x.replace_with(|&mut old| old + 2); }
#[kani::proof_for_contract(modify)]
fn harness_for_modify() {
    let im: IM = IM { x: RefCell::new(kani::any()) };
    modify(&im)
}
