// kani-flags: -Z valid-value-checks -Z mem-predicates
//
// VALVALID_ARRAY_NONZERO_KANIMEM dual (allocation half): value-validity must be
// CONJOINED with the allocation/bounds check, never replace it. An arbitrary
// address with no provenance points at UNALLOCATED memory; the u32 bit-pattern
// living there is value-valid, so if value-validity alone drove
// `can_dereference` this would wrongly PROVE. The allocation predicate must
// still reject the unallocated pointer.
//
// (Note: a pointer to a *dropped stack local* is deliberately NOT used here —
// trust-mc's access predicate treats stack-local obj_ids as always-live, an
// orthogonal liveness-modeling gap unrelated to this value-validity change.)
//
// Run:
//   trust-mc-driver --ay-chc -Z unstable-options -Z valid-value-checks \
//     -Z mem-predicates --harness-timeout=15s dual_candref_dead_ptr.rs
//
// Expected: VERIFICATION:- FAILED (pointer to unallocated memory).
#[kani::proof]
fn dual_candref_dead_ptr() {
    let addr: usize = kani::any();
    // An arbitrary address with no allocation backing it.
    let p: *const u32 = core::ptr::without_provenance(addr);
    // Bytes there would be a valid u32; only the allocation check can reject
    // this, so can_dereference must be FALSE and the assert must FAIL.
    assert!(kani::mem::can_dereference(p));
}
