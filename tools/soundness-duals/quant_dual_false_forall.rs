// gate-flags: -Z quantifiers
// want: NOT-SUCCESSFUL
//
// DUAL for Quantifiers fix B1 (quantifier_encoding: by-name-only debug-const
// resolution, replay-priority bounds, fail-closed empty ranges).
//
// Every harness in this file must be NOT-SUCCESSFUL (FAILED or Unknown).
// A SUCCESSFUL verdict on any harness is a false Safe = missed bug.

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
// bound must NOT vacuously prove.
// want: NOT-SUCCESSFUL — post-fix this must FAIL or be Unknown. The bound `n`
// is not a literal constant at the callsite, so the fail-closed empty-range
// policy routes the quantifier to the sound nondet fallback (assert(nondet)
// always FAILED) instead of emitting bool_const(true).
#[kani::proof]
fn empty_range_nonliteral_bound_must_not_vacuously_prove() {
    let n: usize = kani::any();
    kani::assume(n == 0);
    let arr: [i32; 3] = [1, 2, 3];
    let result = kani::forall!(|i in (0, n)| arr[i as usize] > 100);
    kani::assert(result, "empty-range forall over nondet bound must not prove vacuously");
}

// Harness 3: empty-range forall over a local const-initialized bound (not a
// literal at the MIR callsite) must NOT vacuously prove either.
// want: NOT-SUCCESSFUL. This is the shape that reaches the new
// empty_quantifier_range_expr gate directly: `n` resolves to 0 via
// replay/debug-const, the range collapses to 0..0, but because the bound
// operands are locals (not two literal constants) the encoding fails closed.
#[kani::proof]
fn empty_range_local_const_bound_must_not_vacuously_prove() {
    let n: usize = 0;
    let arr: [i32; 3] = [1, 2, 3];
    let result = kani::forall!(|i in (0, n)| arr[i as usize] > 100);
    kani::assert(result, "empty-range forall over local bound must not prove vacuously");
}
