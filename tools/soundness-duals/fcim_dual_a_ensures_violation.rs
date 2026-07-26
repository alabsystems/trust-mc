// fcim dual (a) — GENUINE postcondition violation, identical pattern to
// whole-struct/cell.rs but body adds 2: at im.x == 99 the post-value is 101,
// so ensures get() < 101 is FALSE. MUST stay VERIFICATION FAILED after the
// fc-interior-mut fix. Catches any "fix" that reads the old() snapshot mirror
// for the postcondition or drops the postcondition read link.
// kani-flags: -Zfunction-contracts

use std::cell::Cell;

struct InteriorMutability {
    x: Cell<u32>,
}

#[kani::requires(im.x.get() < 100)]
#[kani::modifies(&im.x)]
#[kani::ensures(|_| im.x.get() < 101)]
fn modify(im: &InteriorMutability) {
    im.x.set(im.x.get() + 2) // BUG: +2 makes 99 -> 101, ensures false
}

#[kani::proof_for_contract(modify)]
fn harness_for_modify() {
    let im: InteriorMutability = InteriorMutability { x: Cell::new(kani::any()) };
    modify(&im)
}
