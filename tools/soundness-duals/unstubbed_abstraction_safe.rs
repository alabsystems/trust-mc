// Oracle: MUST NOT be certified (both harnesses) — `NOT_GENUINE`.
//
// WHY THIS FILE EXISTS — D1 of the adversarial review of d330fd08b.
//
// Reachability ABSTRACTS a stdlib function of its abstraction set away when it
// has neither an explicit stub nor a CHC handler (`Boundary::abstracts`), and
// says so:
//
//     warning: Function `<std::sync::MutexGuard<'_, T> as std::ops::Deref>::deref`
//              is abstracted but has no stub; result will be unconstrained.
//
// Until 2026-09-14 that fact reached the metadata NOWHERE — it was a
// compile-time warning and a path map cleared between sessions — so
// `classify_ctrex` saw a harness with zero recorded unsoundness and certified
// its counterexample `[AY:CTREX_CAT:Genuine]`. Both harnesses below are SAFE in
// real Rust: the mutex holds 7 and the offset lands inside the array. Their
// counterexample exists only because `MutexGuard::deref` returns an
// unconstrained value.
//
// The verdict is NOT what this file gates. A FAILED here is honest as long as it
// is labelled — `OverApproximation:unstubbed_abstraction=N`, or `EncodingGap` —
// because the driver cannot rule the counterexample out. What must never happen
// is a CERTIFICATE: a safe program reported FAILED with `Genuine` is the defect,
// and `NOT_GENUINE` is exactly that expectation.
//
// The in-bounds `offset` is load-bearing, not decoration. It puts a non-panic
// (memory-safety) check in the reachable set, which is what makes the aggregate
// failure class `Other` — the shape the G8 routing change (d330fd08b) sends to
// `classify_ctrex` instead of reading as an undecided verdict. Without it the
// row never reaches the classifier and the gate cannot see the defect.
//
// The bug twin is `unstubbed_abstraction_dual.rs`.

use std::sync::Mutex;

/// Safe: the mutex holds 7 and the assertion asks for 7.
#[kani::proof]
fn safe_mutex_read_matches_stored_value() {
    let m = Mutex::new(7u32);
    let g = m.lock().unwrap();
    let v = *g;
    let a = [11i32; 4];
    let p: *const i32 = &a[1];
    let q = unsafe { p.offset(1) };
    assert!(v == 7 && unsafe { *q } == 11);
}

/// Safe: the mutex value is never read, only the in-bounds offset is asserted,
/// so even an unconstrained `deref` cannot make this assertion false — but the
/// abstraction is still on the harness, and the certificate must still be
/// withheld. Pins that the taint is per-harness, not per-check.
#[kani::proof]
fn safe_mutex_held_while_offset_stays_in_bounds() {
    let m = Mutex::new(7u32);
    let _g = m.lock().unwrap();
    let a = [11i32; 4];
    let p: *const i32 = &a[0];
    let q = unsafe { p.offset(2) };
    assert!(unsafe { *q } == 11);
}
