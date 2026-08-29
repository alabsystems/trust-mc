// Oracle: MUST FAIL. Every harness below hides its ONLY obligation behind a
// call, which is exactly what the transitive obligation-free certificate must
// refuse to certify.
//
// WHY THIS FILE EXISTS
//
// `ArtifactMetadata.obligation_free_body` is positive compiler evidence that
// zero emitted checks means "nothing to prove" rather than "we dropped it".
// The driver's V4 vacuity gate trusts it: a certified harness with no checks
// is reported SUCCESSFUL instead of VACUOUS. So a certificate handed to a
// harness that DOES have an obligation is a false-Safe channel — the only
// thing that saves it is the encoder happening to emit the check anyway,
// which is luck, not soundness.
//
// The certificate used to require "no Call and no Assert terminator in this
// body", which no harness that calls anything could satisfy. It now walks the
// call graph. These are the cases that walk must refuse.
//
// The non-vacuity twin is NOT here: a harness this certificate certifies emits
// zero checks by definition, and a zero-check run is exactly what this wall
// refuses to score as a pass. The certificate itself is asserted directly in
// `integration_obligation_free_walk_tests.rs`, which can read it; this file
// only holds the verdict-level tripwires the wall CAN score.
//
// CAUGHT ONE ALREADY: `assert!` is REDEFINED by trust-mc's own `library/std`
// to call `kani::assert`, whose body is an empty `Return`. The first version
// of the walk followed it, saw a no-op, and CERTIFIED `bug_assert_one_deep`.
// The marker-attribute check exists because of that.

// The classic: an assert one call deep. Lowers to `kani::assert`, NOT to an
// `Assert` terminator.
fn assert_inner() {
    assert!(false);
}
#[kani::proof]
fn bug_assert_one_deep() {
    assert_inner();
}

// Arithmetic overflow three frames down, behind two obligation-free frames.
fn lvl3(x: u32) -> u32 {
    x + 1
}
fn lvl2(x: u32) -> u32 {
    lvl3(x)
}
fn lvl1(x: u32) -> u32 {
    lvl2(x)
}
#[kani::proof]
fn bug_overflow_three_deep() {
    let _ = lvl1(u32::MAX);
}

// `unwrap` on `None` one call deep.
fn unwrap_inner(o: Option<u32>) -> u32 {
    o.unwrap()
}
#[kani::proof]
fn bug_unwrap_one_deep() {
    let _ = unwrap_inner(None);
}

// A raw dereference of a null pointer. No `assert!`, no kani hook — this is
// the memory-safety class, and it is only refused because rustc still emits an
// `Assert` terminator for the null/alignment check.
fn deref_inner(p: *const u32) -> u32 {
    unsafe { *p }
}
#[kani::proof]
fn bug_null_deref_one_deep() {
    let _ = deref_inner(std::ptr::null());
}

// `unreachable_unchecked` on a path that IS reachable.
fn unreachable_inner(x: u32) -> u32 {
    if x < 100 { x } else { unsafe { std::hint::unreachable_unchecked() } }
}
#[kani::proof]
fn bug_unreachable_unchecked_one_deep() {
    let x: u32 = kani::any();
    let _ = unreachable_inner(x);
}

/// DEVIRTUALIZED virtual call whose concrete body HAS an obligation.
///
/// The walk used to return `Unknown` for every `InstanceKind::Virtual`, so a
/// harness whose only call was `(x as &dyn Super).method()` could not be
/// certified and reported VACUOUS even when it genuinely had nothing to prove
/// (`kani/DynTrait/upcast.rs`). It now devirtualizes through the encoder's own
/// `try_devirtualize`, which refuses blanket impls, generic impls and any
/// multi-candidate trait by returning None.
///
/// That resolution must never CERTIFY a concrete body that has an obligation.
/// The assertion below is FALSE and must be refuted; if this file reports
/// SUCCESSFUL, devirtualization is blessing a body it should have walked into.
trait DvTrait {
    fn f(&self);
}

struct DvStruct;

impl DvTrait for DvStruct {
    fn f(&self) {
        assert!(1 == 2);
    }
}

#[kani::proof]
fn bug_devirtualized_body_has_obligation() {
    let x: &dyn DvTrait = &DvStruct;
    x.f();
}

