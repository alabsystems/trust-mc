// Oracle: MUST FAIL.
//
// A RangeFull Index call is an identity operation, not fresh length authority.
// The source local below has two array-backed slice producers with different
// lengths. The global `subslice_len` side table used to retain one producer and
// copy it to `full`; because `full` itself has only one call definition, the
// side-table multiplicity guard then accepted that stale length and could prove
// the false assertion. The call-provenance walk must carry the source conflict
// through the RangeFull destination instead.

#[kani::proof]
fn range_full_must_not_erase_conflicting_source_lengths() {
    let a4 = [1u8, 2, 3, 4];
    let a8 = [1u8, 2, 3, 4, 5, 6, 7, 8];
    let choose_short: bool = kani::any();
    let source: &[u8] = if choose_short { &a4 } else { &a8 };
    let full: &[u8] = &source[..];

    assert!(full.len() == 4);
}
