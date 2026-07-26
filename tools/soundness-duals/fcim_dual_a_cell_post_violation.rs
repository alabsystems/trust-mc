// gate-flags: -Zfunction-contracts
// fc-interior-mut DUAL (a) — genuine postcondition violation, identical pattern
// to tests/expected/function-contract/interior-mutability/whole-struct/cell.rs.
//
// MUST stay VERIFICATION:- FAILED after the fc-interior-mut fix.
//
// Body adds 2 (not 1) while requires only guarantees x < 100: at im.x == 99
// the post-state value is 101, so `ensures im.x.get() < 101` is violated.
// This is the exact trap for a fake "fix": if the FP were silenced by reading
// the old() snapshot mirror instead of post-state, or by dropping the
// postcondition read link to the cell's real memory mirror, this harness
// would pass falsely (missed bug).

use std::cell::Cell;

struct InteriorMutability {
    x: Cell<u32>,
}

#[kani::requires(im.x.get() < 100)]
#[kani::modifies(&im.x)]
#[kani::ensures(|_| im.x.get() < 101)]
fn modify(im: &InteriorMutability) {
    // BUG: +2 instead of +1 — at im.x == 99 the ensures bound 101 is hit.
    im.x.set(im.x.get() + 2)
}

#[kani::proof_for_contract(modify)]
fn harness_for_modify() {
    let im: InteriorMutability = InteriorMutability { x: Cell::new(kani::any()) };
    modify(&im)
}
