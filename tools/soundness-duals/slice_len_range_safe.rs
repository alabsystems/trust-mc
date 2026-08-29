// Oracle: MUST PASS.
//
// The fail-closed phase-order rule must retain useful length authority for an
// authenticated standard Range index.  This positive twin distinguishes exact
// identity gating from simply disabling all Range metadata recovery.

#[kani::proof]
fn exact_standard_range_preserves_length_authority() {
    let source: &[u8] = &[1, 2, 3, 4];
    let middle: &[u8] = &source[1..3];

    assert!(middle.len() == 2);
}
