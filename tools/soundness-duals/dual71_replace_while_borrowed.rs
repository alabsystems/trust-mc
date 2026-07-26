// Task #71 RefCell borrow-gate dual: replace() while a mutable borrow is
// live — this PANICS at runtime ("already borrowed"). The intercepted
// RefCell::replace skips the borrow-flag check, so the borrow-guard gate
// (refcell_mutator_must_fail_close) must DECLINE the interception here and
// fail closed. The harness must NOT report SUCCESSFUL: FAILED or
// UNDETERMINED are acceptable; SUCCESSFUL = the skipped borrow panic was
// silently dropped (false Safe).
// kani-flags: -Zfunction-contracts

use std::cell::RefCell;

#[kani::proof]
fn replace_while_borrowed_must_not_pass() {
    let rc = RefCell::new(7u32);
    let guard = rc.borrow_mut();
    let old = rc.replace(9); // panics: already borrowed
    drop(guard);
    assert!(old == 7);
}
