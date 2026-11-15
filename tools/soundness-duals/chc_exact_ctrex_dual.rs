// Oracle: MUST FAIL (both harnesses).
//
// The CHC lane can DERIVE a counterexample outright: when the predicate
// dependency graph gives a constraint-free zero-arity derivation of `error`, or
// an acyclic derivation witness backed by a model, `interpret_chc_trivial_unsafe`
// reports it and prints
//
//     [AY:CTREX] CHC verification: counterexample reachable (exact CHC derivation)
//
// WHY THIS FILE EXISTS — the derivation was reported as an UNKNOWN:
//
// When per-property attribution finds no `error_p{N}` for the derived path, that
// interpreter falls back to the legacy aggregate `chc.0` property, whose class is
// "chc" and whose failure class is the kind of the reachable check. A pointer
// overflow (or any non-panic check) therefore arrived as
// `FailedProperties::Other` with no non-`chc` failing property, which is the
// exact spelling of "the solver did not decide" — and `harness_runner` read it
// that way, printing
//
//     [AY:CTREX_CAT:Unknown]
//     [AY:UNKNOWN_QUALITY:Clean]
//
// for a counterexample it had derived exactly. Measured 2026-09-14 on three
// corpus units (docs/chc-unknown-root-causes-2026-09-14.md, group G8):
// tests/expected/pointer-overflow/main.rs, tests/kani/Overflow/pointer_overflow_fail.rs
// and tests/expected/valid-value-checks/non_null.rs, all three FAILED with a
// fail oracle, all three scored `unknown` instead of parity.
//
// The verdict was never wrong, so this file gates on the verdict AND on the
// category: a FAILED here that carries `[AY:CTREX_CAT:Unknown]` is the defect
// back, and a SUCCESSFUL is a missed bug. The safe twin is
// `chc_exact_ctrex_safe.rs`.

/// `isize::MAX` bytes past an interior element overflows the offset computation.
/// Upstream Kani reports "Offset in bytes overflows isize".
#[kani::proof]
fn bug_offset_overflows_isize() {
    let a = [0i32; 5];
    let ptr: *const i32 = &a[1];
    let _ = unsafe { ptr.offset(isize::MAX) };
}

/// The same overflow reached through a nondeterministic-but-constrained index,
/// so the derivation is not purely propositional.
#[kani::proof]
fn bug_offset_overflows_isize_from_any_index() {
    let a = [0i32; 5];
    let i: usize = kani::any();
    kani::assume(i < 5);
    let ptr: *const i32 = &a[i];
    let _ = unsafe { ptr.offset(isize::MAX) };
}
