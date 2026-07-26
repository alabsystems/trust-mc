// kani-flags: -Z mem-predicates
//
// SOUNDNESS DUAL (missed-bug tripwire) — a Vec whose backing has GENUINELY
// invalid provenance must NOT be treated as valid.
//
// EXPECTED VERDICT: VERIFICATION:- FAILED. A SUCCESS here means the
// drop-validity provenance fix over-reached: it began treating a Vec built
// from raw/unsafe parts as a valid allocation instead of ONLY the provably
// allocating collection constructors (into_vec / bounded_any / …).
// Never delete, never weaken.
//
// `Vec::from_raw_parts` is UNSAFE: it does NOT allocate, it adopts a
// caller-supplied pointer. Here the pointer is an arbitrary address with no
// allocation backing it, so `can_dereference` on the Vec's buffer must be
// FALSE and the assert must FAIL. The provenance fix is gated on the
// constructor's callee path (and only registers CONCRETE fresh obj_ids), so
// this from-raw-parts pointer is never registered as a provably-valid backing
// and `heap_access_checks` keeps emitting the real `obj_valid` select for it.
//
// Adversarial twin of `dual_bounded_any_vec_valid.rs` (which must stay
// SUCCESSFUL).
//
// Run:
//   trust-mc-driver --ay-chc -Z unstable-options -Z mem-predicates \
//     --harness-timeout=15s dual_vec_from_invalid_ptr_drop.rs
#[kani::proof]
fn dual_vec_from_invalid_ptr_drop() {
    let addr: usize = kani::any();
    // An arbitrary address with no allocation provenance behind it.
    let dangling: *mut u8 = core::ptr::without_provenance_mut(addr);
    // Adopt the invalid pointer as a Vec buffer. The buffer is NOT a live
    // allocation, so dereferencing it is UB.
    let v: Vec<u8> = unsafe { Vec::from_raw_parts(dangling, 4, 4) };
    // Only the allocation/provenance check can reject this, so
    // `can_dereference` must be FALSE and the assert must FAIL.
    assert!(kani::mem::can_dereference(v.as_ptr()));
    // Do not model a (double) free of the invalid buffer.
    core::mem::forget(v);
}
