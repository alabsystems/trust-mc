// Task #71 RefCell borrow-state dual: borrow_mut while a mutable borrow is
// live — this PANICS at runtime ("already mutably borrowed"). The harness
// must NOT report SUCCESSFUL: FAILED (panic reachable) or UNDETERMINED
// (fail-closed demotion) are both acceptable; SUCCESSFUL would mean the
// borrow-flag semantics were silently dropped (unmodeled double-borrow UB
// passing = false Safe).
// kani-flags: -Zfunction-contracts

use std::cell::RefCell;

#[kani::proof]
fn double_borrow_must_not_pass() {
    let rc = RefCell::new(7u32);
    let a = rc.borrow_mut();
    let b = rc.borrow_mut(); // panics: already mutably borrowed
    let _ = (a, b);
}
