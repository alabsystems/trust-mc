// SOUNDNESS DUAL — offset in-bounds bug MASKED by (but independent of) the
// isize-overflow property (THE CRITICAL MISSED-BUG GUARD).
//
// Marker: OFFSET_PROV_GENUINE_CERT (grep-anchor).
//
// A non-ZST offset whose count (50) fits isize AND whose byte product
// (50 * 4 = 200) fits isize — so the isize-overflow obligation is SATISFIED (it
// does NOT fire) — but which steps a 4-element (16-byte) stack allocation far
// out of bounds and then DEREFERENCES the result. The only real bug is the
// out-of-bounds access, caught (if at all) by the in-bounds / allocation-bound
// net that the `offset_provenance_unresolved` demotion covers.
//
// MUST be FAILED, both BEFORE and AFTER the certification change. This is the
// guard that the EncodingGap→Genuine offset certification NEVER reports the
// in-bounds bug as verified / SUCCESSFUL: because the isize-overflow property
// does NOT fire here, there is no independent violated check to certify, and
// the (demoted / genuinely-caught) OOB failure must persist. The certification
// only ever relabels an ALREADY-FAILED verdict; it can never turn FAILED into
// Safe. If this flips to SUCCESSFUL, STOP — the change unmasked a missed bug.
#[kani::proof]
fn dual_offset_masked_inbounds() {
    let arr: [i32; 4] = [1, 2, 3, 4];
    let p: *const i32 = arr.as_ptr();
    unsafe {
        let v = *p.add(50); // 200 bytes past a 16-byte alloc: OOB deref — MUST FAIL
        core::hint::black_box(v);
    }
}
