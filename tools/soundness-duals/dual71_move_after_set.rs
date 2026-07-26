// Task #71 register-mirror coherence dual (the quarantine's stated reason
// #2): a Cell method store lands on the memory-mirror lane; moving the Cell
// by value afterwards copies the local's REGISTER mirror. If the register
// mirror is stale (still the initial 1), the moved cell reads 1 instead of
// 2 and the assert below passes — a false Safe. This harness must NOT
// report SUCCESSFUL: FAILED (correct semantics: c2.get() == 2) or
// UNDETERMINED (fail-closed) are both acceptable.
// kani-flags: -Zfunction-contracts

use std::cell::Cell;

#[kani::proof]
fn move_after_set_must_not_read_stale() {
    let c = Cell::new(1u32);
    c.set(2);
    let c2 = c; // move: copies whichever lane models the local's value
    assert!(c2.get() == 1); // TRUE semantics: c2.get() == 2 -> must fail
}
