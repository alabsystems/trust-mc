// Oracle: MUST FAIL (both harnesses).
//
// Bug twin of `unstubbed_abstraction_safe.rs`. Same shape — a `Mutex` read whose
// `MutexGuard::deref` reachability abstracts away with no stub, beside an
// in-bounds raw-pointer `offset` that keeps a non-panic check in the reachable
// set — but each harness carries a bug that does NOT depend on the abstracted
// value, so the FAILED verdict is real whatever the abstraction returns.
//
// This half is what stops the D1 fix being bought with a missed bug: recording
// an unstubbed abstraction demotes a COUNTEREXAMPLE's category, and a demotion
// that also swallowed the verdict would report SUCCESSFUL here. The category is
// deliberately NOT gated: after D1 these rows are
// `OverApproximation:unstubbed_abstraction=N`, because the driver cannot tell
// from the CHC alone that the failing check is independent of the freed value
// (Task #77 — a driver-side independence proxy certifies the traps too).

use std::sync::Mutex;

/// The offset runs off the end of a four-element array. Real UB, independent of
/// whatever the abstracted `deref` returns.
#[kani::proof]
fn bug_offset_runs_past_the_allocation() {
    let m = Mutex::new(7u32);
    let _g = m.lock().unwrap();
    let a = [11i32; 4];
    let p: *const i32 = &a[3];
    let q = unsafe { p.offset(64) };
    assert!(unsafe { *q } == 11);
}

/// A plainly false assertion beside the held guard: `1 + 1 != 3` on any value
/// the abstraction could produce.
#[kani::proof]
fn bug_assertion_false_on_every_abstracted_value() {
    let m = Mutex::new(7u32);
    let g = m.lock().unwrap();
    let v = *g;
    let a = [11i32; 4];
    let p: *const i32 = &a[1];
    let q = unsafe { p.offset(1) };
    assert!(unsafe { *q } == 11 && v.wrapping_add(1) != v.wrapping_add(1));
}
