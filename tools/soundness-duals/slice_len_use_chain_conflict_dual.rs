// Oracle: MUST FAIL.
//
// Pass 5d copies path-insensitive slice metadata across whole-local `Use`
// assignments. The source has two conflicting whole-local producers, while the
// copied local and RangeFull result each have only one. Propagating one stale
// source candidate through the apparently unique copied local can revive false
// length authority and prove this assertion. Every Use propagation endpoint
// must therefore have a unique whole-local producer.

#[kani::proof]
fn use_chain_must_not_revive_conflicting_slice_length() {
    let a4 = [1u8, 2, 3, 4];
    let a8 = [1u8, 2, 3, 4, 5, 6, 7, 8];
    let choose_short: bool = kani::any();
    let source: &[u8] = if choose_short { &a4 } else { &a8 };

    // Keep a distinct MIR local so the metadata prepass exercises its `Use`
    // propagation lane before RangeFull consumes the value.
    let copied: &[u8] = source;
    let copied_ref = &copied;
    let full: &[u8] = &(*copied_ref)[..];

    assert!(full.len() == 4);
}
