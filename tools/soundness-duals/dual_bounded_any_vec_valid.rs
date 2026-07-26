// SOUNDNESS DUAL (parity half) — provably-valid collection backing must PROVE.
//
// EXPECTED VERDICT: VERIFICATION:- SUCCESSFUL.
//
// `kani::bounded_any::<Vec<T>, N>()` builds its buffer via
// `<[T]>::into_vec(Box<[T; N]>)`, i.e. an owned, live heap allocation. When the
// outer `Result`/`Option::bounded_any` is inlined, that inner `into_vec` call
// is over-approximated (RawVec/allocator internals have no MIR the inline
// walker can descend into). The over-approximated Vec must still carry VALID
// heap provenance so each `Vec::drop` dealloc-validity / `can_dereference`
// check PROVES instead of failing spuriously.
//
// A FAILED here means the drop-validity provenance fix regressed: an
// over-approximated `into_vec` Vec is being given an arbitrary/invalid backing
// pointer again. This uses `Result<Vec<bool>, Vec<bool>>` to exercise TWO such
// backing allocations in one transition. Paired with
// `dual_vec_from_invalid_ptr_drop.rs` (which must stay FAILED) this pins the
// fix to provably-valid constructors only.
//
// NB: `Vec<u8>` (e.g. `bounded_any::<Vec<u8>, N>()`) additionally trips a
// SEPARATE, pre-existing `store_dropped_transition` demotion on its nested
// bv8 region array, unrelated to provenance — hence `Vec<bool>` here.
//
// Run:
//   trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=15s \
//     dual_bounded_any_vec_valid.rs
#[kani::proof]
fn dual_bounded_any_vec_valid() {
    let r: Result<Vec<bool>, Vec<bool>> = kani::bounded_any::<_, 4>();
    // Read the over-approx Vec, then let it drop at end of the arm. There is NO
    // assertion about the length (the over-approx leaves it symbolic) — the
    // only obligations are the memory-safety / drop-validity checks, which must
    // all PROVE because each backing IS a valid heap allocation.
    match r {
        Ok(v) => {
            core::hint::black_box(v.len());
        }
        Err(v) => {
            core::hint::black_box(v.len());
        }
    }
}
