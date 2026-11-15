// gate-flags: -Z quantifiers
//
// DUAL for Quantifiers fix B1 (quantifier_encoding: by-name-only debug-const
// resolution, replay-priority bounds, fail-closed empty ranges).
//
// Oracle (per harness; Rust/Kani semantics, design trust-mc-reds-final §4.6,
// decision C7 in docs/DECISION_QUEUE.md: the oracle, not a lane's
// fail-closed policy, decides `expected`):
//   false_forall_must_fail                                 -> FAILED
//   empty_range_nonliteral_bound_must_not_vacuously_prove  -> SUCCESSFUL
//   empty_range_local_const_bound_must_not_vacuously_prove -> SUCCESSFUL
//   nonliteral_bound_nonempty_must_fail                    -> FAILED
//   local_const_bound_nonempty_must_fail                   -> FAILED
//
// A forall over an EMPTY range is true, so harnesses 2 and 3 are safe
// programs; a lane that fails closed on them pays a known-red false failure.
// The vacuity guard that the old "want: NOT-SUCCESSFUL" header kept is held by
// the two must-fail twins at the end: the same bound shapes over a NON-empty
// range, where an encoding that collapses the bound to an empty range (and the
// forall to `true`) proves a false assertion.

// Harness 1: a genuinely FALSE forall must FAIL.
// arr[0] == 1 violates arr[i] > 1 for i in (0, 3).
// If bound mis-resolution collapses the range (the B1 by-type bug shape) the
// forall becomes vacuous `true` and this asserts trivially — false Safe.
#[kani::proof]
fn false_forall_must_fail() {
    let arr: [i32; 3] = [1, 2, 3];
    kani::assert(
        kani::forall!(|i in (0, 3)| arr[i as usize] > 1),
        "forall arr[i] > 1 must be falsified by arr[0] == 1",
    );
}

// Harness 2: empty-range forall over a NON-literal (nondet, assumed-zero)
// bound. The forall is true (empty range): SUCCESSFUL is the oracle. The
// encoder's fail-closed empty-range policy routes a non-literal bound to the
// sound nondet fallback instead of emitting bool_const(true), so a lane that
// takes it reports a (known-red) false failure, never a false Safe.
// (Kani reports this harness FAILED, measured 2026-09-26 with the corpus-rev
// Kani, while it proves harness 3; the forall over `0..0` holds either way.)
#[kani::proof]
fn empty_range_nonliteral_bound_must_not_vacuously_prove() {
    let n: usize = kani::any();
    kani::assume(n == 0);
    let arr: [i32; 3] = [1, 2, 3];
    let result = kani::forall!(|i in (0, n)| arr[i as usize] > 100);
    kani::assert(result, "empty-range forall over nondet bound must not prove vacuously");
}

// Harness 3: empty-range forall over a local const-initialized bound (not a
// literal at the MIR callsite). True (the range 0..0 is empty): SUCCESSFUL is
// the oracle. This is the shape that reaches the empty_quantifier_range_expr
// gate directly: `n` resolves to 0 via replay/debug-const, and because the
// bound operands are locals (not two literal constants) the encoding may fail
// closed.
#[kani::proof]
fn empty_range_local_const_bound_must_not_vacuously_prove() {
    let n: usize = 0;
    let arr: [i32; 3] = [1, 2, 3];
    let result = kani::forall!(|i in (0, n)| arr[i as usize] > 100);
    kani::assert(result, "empty-range forall over local bound must not prove vacuously");
}

// Harness 4 (vacuity guard for harness 2): the same non-literal bound shape,
// NON-empty. arr[i] > 100 is false for every i in 0..3: must FAIL. An
// encoding that turns this bound into `true` is a missed bug.
#[kani::proof]
fn nonliteral_bound_nonempty_must_fail() {
    let n: usize = kani::any();
    kani::assume(n == 3);
    let arr: [i32; 3] = [1, 2, 3];
    let result = kani::forall!(|i in (0, n)| arr[i as usize] > 100);
    kani::assert(result, "forall over a non-empty nondet-bounded range is false here");
}

// Harness 5 (vacuity guard for harness 3): the local const-initialized bound
// resolved by replay/debug-const, NON-empty: must FAIL.
#[kani::proof]
fn local_const_bound_nonempty_must_fail() {
    let n: usize = 3;
    let arr: [i32; 3] = [1, 2, 3];
    let result = kani::forall!(|i in (0, n)| arr[i as usize] > 100);
    kani::assert(result, "forall over a non-empty locally bounded range is false here");
}
