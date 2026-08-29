// Oracle: MUST FAIL.
//
// The `unreachable_unchecked` IS reachable — `x` is unconstrained, so `x >= 100`
// happens. Reaching it is UB and must be refuted.
//
// WHY THIS FILE EXISTS
//
// A guard that folds to `BoolConst(false)` is a PROOF that an edge is
// infeasible, and when the target is an `Unreachable` block that proof IS the
// harness's obligation. It used to leave NO trace: the edge was skipped and no
// property was registered, so a harness whose only obligation was an
// unreachable arm emitted ZERO checks and V4 reported a PROVED harness as
// vacuous (`Enum/niche.rs`, `Closure/zst_unwrap.rs`, `StdOverrides/arg.rs`,
// `Vectors/issue-763.rs`).
//
// Registering the property makes that discharge visible. The danger is
// registering it when the edge is NOT provably infeasible — that would report a
// reachable UB site as a passing check. This file is the tripwire for exactly
// that: its guard is NOT constant-false, so the edge must still be emitted and
// the obligation must still be refuted.
//
// Its twin `unreachable_discharge_dual_safe.rs` constrains the same shape so
// the unreachable genuinely is unreachable, and must SUCCEED.

fn inner(x: u32) -> u32 {
    if x < 100 { x } else { unsafe { std::hint::unreachable_unchecked() } }
}

#[kani::proof]
fn bug_reachable_unreachable() {
    let x: u32 = kani::any();
    let _ = inner(x);
}
