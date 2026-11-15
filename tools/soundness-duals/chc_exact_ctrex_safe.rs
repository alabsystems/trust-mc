// Oracle: MUST be SUCCESSFUL (both harnesses).
//
// Safe twin of `chc_exact_ctrex_dual.rs`. Same shapes, offsets that stay inside
// the allocation, so nothing is reachable to derive. If the exact-derivation
// path ever starts claiming a counterexample here, the routing added for group
// G8 (docs/chc-unknown-root-causes-2026-09-14.md) has turned a decided-safe
// harness into a false bug report.

/// In-bounds offset: one element forward from the first of five.
#[kani::proof]
fn safe_offset_stays_in_bounds() {
    let a = [7i32; 5];
    let ptr: *const i32 = &a[0];
    let q = unsafe { ptr.offset(1) };
    assert!(unsafe { *q } == 7);
}

/// The same, reached through a nondeterministic-but-constrained index.
#[kani::proof]
fn safe_offset_from_any_index_stays_in_bounds() {
    let a = [7i32; 5];
    let i: usize = kani::any();
    kani::assume(i < 4);
    let ptr: *const i32 = &a[i];
    let q = unsafe { ptr.offset(1) };
    assert!(unsafe { *q } == 7);
}
