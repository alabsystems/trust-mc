// Oracle: corpus-rev Kani, measured 2026-09-24: all three harnesses FAIL
// ("assertion failed: n == 0" twice, "assertion failed: bytes.len() == 0").
//
// WHY THIS FILE EXISTS (known red on chc): a slice-pattern loop over a slice
// built from an array is DEAD in the CHC encoding. The unsize cast
// `&[u8; 10] -> &[u8]` (and `a.as_slice()`) reaches the loop-carried BV128
// slot as a zero-extended THIN pointer -- the debug trace reads
// "propagate_ref_metadata: ambiguous whole-local producer ... source=copy-cast"
// -- so the loop guard `len >= 1` reads bits 127..64 of that slot, which are
// 0 at entry. The bounded straight-line discharge then prunes the loop edge as
// infeasible and emits `(rule (=> false error))`: the harness PROVES while
// the loop really runs ten times. A direct `bytes.len()` read is served by a
// side table and stays correct (slice_len_is_ten, the control).
//
// Found by the test review of land/array-param-mid-guard: it is also why that
// branch's lost_error_rules_dual.rs row does not exercise its invariant check.

#[kani::proof]
fn slice_loop_counts_to_ten() {
    let a: [u8; 10] = kani::any();
    let mut bytes: &[u8] = &a;
    let mut n: u32 = 0;
    while let [_first, rest @ ..] = bytes {
        bytes = rest;
        n += 1;
    }
    assert!(n == 0);
}

#[kani::proof]
fn slice_loop_as_slice_counts_to_ten() {
    let a: [u8; 10] = kani::any();
    let mut bytes = a.as_slice();
    let mut n: u32 = 0;
    while let [_first, rest @ ..] = bytes {
        bytes = rest;
        n += 1;
    }
    assert!(n == 0);
}

// Control: the same slice, read directly, no loop.
#[kani::proof]
fn slice_len_is_ten() {
    let a: [u8; 10] = kani::any();
    let bytes: &[u8] = &a;
    assert!(bytes.len() == 0);
}
