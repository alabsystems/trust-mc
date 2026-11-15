// Oracle: corpus-rev Kani -Z loop-contracts (see the manifest entry for the
// measured verdict of every harness).
//
// WHY THIS FILE EXISTS: design 5 (docs/chc-hole-fix-designs-2026-09-24.md,
// "Legacy loop-contract latch"). A loop the CHC #47 proof rule DECLINES keeps
// the cyclic LEGACY encoding: an explicit `loop_modifies` clause declines the
// whole body, and so does a loop that stores to a local without a havocable
// type (a slice). Its latch read the register fn's raw `{ true }` body, so the
// invariant was never evaluated and every harness below that Kani FAILS on its
// invariant alone was a clean CHC SUCCESSFUL. The latch now carries a
// reachable-state check, and every legacy latch is booked fail-closed because
// that check is not the inductive step:
//
// * `*_noninductive_bug`: the invariant holds on every reachable state but is
//   not inductive. Only Kani's step check sees it; the concrete loop never
//   can, so the fix must not report SUCCESSFUL (the booking).
// * `*_step_bug`: the invariant breaks on a reachable state (the latch check).
// * `should_panic_noninductive_bug`: a certified panic must not hide the step
//   Kani fails ("failures other than panics").
// * `walked_helper_*`: the loop sits in a callee reached through a fn pointer,
//   which the CHC walker walks as its RAW body (no loop-contract rewrite at
//   all); walked_helper_step_bug was a clean SUCCESSFUL on main.
// * `nested_declined_in_rule_*`: a declined loop inside a loop the rule DOES
//   instrument runs on outer-havocked state; it takes the nested-legacy
//   sentinel, never the reachable-state check.
// * `*_safe`: valid invariants. A demoted FAILED is tolerated, a Genuine
//   counterexample is not. (`nested_declined_in_rule_kani_assigns` is correct
//   too, but Kani fails its inferred assigns clause.)

#![feature(proc_macro_hygiene)]
#![feature(stmt_expr_attributes)]

#[kani::proof]
fn mod_noninductive_bug() {
    let mut i: u32 = 0;
    // Reachable: 0, 2, 4, 6, 8, 10. From a havocked i == 9 one step gives 11.
    #[kani::loop_invariant(i <= 10)]
    #[kani::loop_modifies(&i)]
    while i < 10 {
        i += 2;
    }
}

#[kani::proof]
fn mod_step_bug() {
    let mut i: u32 = 0;
    // Breaks on the reachable state i == 4.
    #[kani::loop_invariant(i <= 3)]
    #[kani::loop_modifies(&i)]
    while i < 10 {
        i += 1;
    }
}

#[kani::proof]
fn mod_inductive_safe() {
    let mut i: u32 = 0;
    #[kani::loop_invariant(i <= 10)]
    #[kani::loop_modifies(&i)]
    while i < 10 {
        i += 1;
    }
    assert!(i == 10);
}

#[kani::proof]
fn slice_noninductive_bug() {
    let a: [u8; 4] = kani::any();
    let mut bytes: &[u8] = &a;
    // Reachable lengths: 4, 2, 0. From a havocked length 5 one step gives 3.
    #[kani::loop_invariant(bytes.len() != 3)]
    while let [_, _, rest @ ..] = bytes {
        bytes = rest;
    }
}

#[kani::proof]
fn slice_step_bug() {
    let a: [u8; 4] = kani::any();
    let mut bytes: &[u8] = &a;
    // Breaks on the reachable length 2.
    #[kani::loop_invariant(bytes.len() >= 3)]
    while let [_, rest @ ..] = bytes {
        bytes = rest;
    }
}

#[kani::proof]
#[kani::should_panic]
fn should_panic_noninductive_bug() {
    let mut i: u32 = 0;
    #[kani::loop_invariant(i <= 10)]
    #[kani::loop_modifies(&i)]
    while i < 10 {
        i += 2;
    }
    assert!(i != 10, "reached on every run");
}

fn helper_step_bug() -> u32 {
    let mut i: u32 = 0;
    #[kani::loop_invariant(i <= 1)]
    while i < 4 {
        i += 1;
    }
    i
}

// Called through a fn pointer, the helper is not MIR-inlined into the harness:
// the CHC walker walks its raw body, where the register call answers `true`.
#[kani::proof]
fn walked_helper_step_bug() {
    let f: fn() -> u32 = helper_step_bug;
    assert!(f() == 4);
}

fn helper_safe() -> u32 {
    let mut i: u32 = 0;
    #[kani::loop_invariant(i <= 4)]
    while i < 4 {
        i += 1;
    }
    i
}

#[kani::proof]
fn walked_helper_safe() {
    let f: fn() -> u32 = helper_safe;
    assert!(f() == 4);
}

// The program is correct, but Kani FAILS it: its inferred assigns clause for
// the outer loop does not include the inner loop's `bytes` ("Check assigns
// clause inclusion for loop"). Kept as the oracle says: NOT SUCCESSFUL.
#[kani::proof]
fn nested_declined_in_rule_kani_assigns() {
    let a: [u8; 4] = kani::any();
    let mut n: u32 = 0;
    #[kani::loop_invariant(n <= 2)]
    while n < 2 {
        let mut bytes: &[u8] = &a;
        #[kani::loop_invariant(bytes.len() <= 4)]
        while let [_, rest @ ..] = bytes {
            bytes = rest;
        }
        n += 1;
    }
}

#[kani::proof]
fn nested_declined_in_rule_bug() {
    let a: [u8; 4] = kani::any();
    let mut n: u32 = 0;
    #[kani::loop_invariant(n <= 2)]
    while n < 2 {
        let mut bytes: &[u8] = &a;
        // Breaks on the reachable length 2.
        #[kani::loop_invariant(bytes.len() >= 3)]
        while let [_, rest @ ..] = bytes {
            bytes = rest;
        }
        n += 1;
    }
}
