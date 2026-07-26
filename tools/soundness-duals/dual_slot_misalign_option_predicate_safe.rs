// SAFE TWIN of dual_slot_misalign_option_predicate.rs.
//
// Identical shape, TRUE polarity: a fresh 3-element iterator's first next() IS
// Some, so is_some() holds. MUST PASS. This twin is what makes the fail-close
// meaningful — it proves the slot-misalignment net rejects only corrupt frames
// and did not simply turn every iterator proof into a failure.
#[kani::proof]
#[kani::unwind(6)]
fn dual_slot_misalign_is_some_must_pass() {
    let a = [1u32, 2u32, 3u32];
    let s: &[u32] = &a;
    let mut it = s.iter();
    assert!(it.next().is_some(), "TRUE: first next() is Some(1)");
}
