// SOUNDNESS DUAL — offset non-ZST isize-overflow certified GENUINE.
//
// Marker: OFFSET_PROV_GENUINE_CERT (grep-anchor for the per-property
// counterexample-certification extension of #78).
//
// A non-ZST `ptr.add(count)` where `count = isize::MAX + 1` (as usize). The
// count itself does NOT fit isize, so the isize-overflow safety check
// (`pointer_overflow` / "Offset value overflows isize") is VIOLATED regardless
// of allocation size or provenance. That check reads only `count` and the
// pointee size (both concrete) — it is data-INDEPENDENT of the allocation-bound
// check the same site demotes via `offset_provenance_unresolved`.
//
// MUST be FAILED, and — because the harness's approximation accounting is now
// COMPLETE and the violated overflow property is independent — the driver MUST
// certify the counterexample as **Genuine**, NOT EncodingGap. Verify via the
// driver's `CTREX breakdown` line (`... 0 EncodingGap, ... 1 Genuine`) and the
// `[AY:CTREX_CAT:Genuine:...]` marker, not just the FAILED verdict.
//
// If this stays EncodingGap, the offset-provenance accounting did not complete
// (accounted != taint total) or the EncodingGap→Genuine routing did not fire.
#[kani::proof]
fn dual_offset_overflow_genuine() {
    let mut x = 7i32;
    let ptr: *mut i32 = &mut x as *mut i32;
    let count: usize = (isize::MAX as usize) + 1;
    let _ = unsafe { ptr.add(count) };
}
