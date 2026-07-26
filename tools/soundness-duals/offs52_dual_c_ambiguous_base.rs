// KEYSTONE #52 DUAL (c) — branch-merged (ambiguous) base object.
// The pointer local has TWO assignment sites (one per branch); the metadata
// side-tables are flow-insensitive (last-processed-block wins), so resolving
// provenance here could claim the WRONG object. `small` is [i32;2] (8 bytes),
// `big` is [i32;16] (64 bytes). `*p.add(3)` is a REAL OOB on the `small`
// path (needs 16 bytes). If wrong-object recovery resolved p to `big`
// (bound 64), the OOB would be proven Safe.
// MUST NOT be SUCCESSFUL — the single-assignment gate must refuse the stack
// lane and the OffsetProvenanceUnresolved demotion (or a genuine CTREX) must
// keep this FAILED/UNDETERMINED.

#[kani::proof]
fn dual_c_ambiguous_base() {
    let small: [i32; 2] = [1, 2];
    let big: [i32; 16] = [7; 16];
    let c: bool = kani::any();
    let p: *const i32 = if c { small.as_ptr() } else { big.as_ptr() };
    unsafe {
        let x = *p.add(3); // OOB iff c — MUST NOT prove Safe
        core::hint::black_box(x);
    }
}
