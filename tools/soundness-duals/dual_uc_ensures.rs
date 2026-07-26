// UnsafeCell foundation soundness dual: +2 body, requires <100, ensures <101.
// If the shipped UnsafeCell path reads/writes memory soundly this MUST FAIL
// (x=99 -> 101). If it PASSES, the interior-mut foundation is vacuous.
// kani-flags: -Zfunction-contracts
use std::cell::UnsafeCell;
struct IM { x: UnsafeCell<u32> }
#[kani::requires(unsafe{*im.x.get()} < 100)]
#[kani::modifies(im.x.get())]
#[kani::ensures(|_| unsafe{*im.x.get()} < 101)]
fn modify(im: &IM) { unsafe { *im.x.get() += 2 } }
#[kani::proof_for_contract(modify)]
fn harness_for_modify() {
    let im: IM = IM { x: UnsafeCell::new(kani::any()) };
    modify(&im)
}
