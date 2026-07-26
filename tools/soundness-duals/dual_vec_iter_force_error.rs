// SOUNDNESS DUAL (missed-bug tripwire) — vec-iter fail-closed request must not be dropped.
//
// Guards the channel fixed in `chc/call/codegen_call_vec_iter.rs`: that lane
// consumed `CollectionCallResult.constraints` but never checked `.force_error`,
// so `forced_failure()` (raised by `unsound_sort_mismatch_failure` when an
// iterator has a non-datatype sort) emitted NO error rule — while the driver
// lists `IteratorUnsoundness` in `FAIL_CLOSED_CATEGORIES` and therefore applies
// no demotion either. Neither net was actually in place.
//
// Probes A-C put the false assertion AFTER the loop, which does not
// discriminate: dropping the iterator constraints leaves the accumulator
// unconstrained, so the assertion fails either way (conservatively).
//
// The false-Safe shape is a bug INSIDE the loop body. If the fail-closed
// request is dropped and the iterator's `next()` is left unconstrained, the
// solver may take the "iterator immediately yields None" path, never enter the
// body, and prove the harness VACUOUSLY. With the error rule actually emitted,
// the harness must report FAILED.
//
// Element 0 is 7, so `*e == 0` is genuinely violated on the first iteration.
// EXPECTED VERDICT: VERIFICATION:- FAILED. A SUCCESSFUL verdict here means the
// iterator sort-mismatch fail-closed path is being swallowed — a false-Safe
// channel is open. Never delete, never weaken.

struct RawSlice {
    inner: [u8],
}

impl RawSlice {
    fn new(bytes: &mut [u8]) -> &Self {
        unsafe { std::mem::transmute(bytes) }
    }
}

#[kani::proof]
#[kani::unwind(4)]
fn dual_vec_iter_force_error() {
    let mut v = vec![7u8, 8u8];
    let raw = RawSlice::new(v.as_mut_slice());
    for e in &raw.inner {
        // REAL VALUES ARE 7 AND 8. This must be reported FAILED.
        assert!(*e == 0, "loop body element must not be provable as 0");
    }
}
