// Oracle: MUST FAIL.
// gate-flags: -Z stubbing
//
// A STUB can carry an obligation the original does not have. `clean()` has
// nothing to prove; `panicking()` asserts false; the harness stubs the first
// with the second. The program under verification is therefore the PANICKING
// one, and this harness must report FAILED.
//
// WHY IT IS HERE
//
// The obligation-free certificate (`codegen_ay/obligation_free_walk.rs`) walks
// the call graph with raw `Instance::resolve`, which returns the ORIGINAL body
// — so it saw `clean`, found nothing to prove, and answered `certified=true`
// on THIS harness. Measured exactly that: `certified=true` alongside a FAILING
// check. It was not yet a false Safe only because the encoder emitted the
// check anyway, and the certificate is precisely the fallback for when it does
// not. Closed by refusing to certify any harness whose codegen unit stubs
// anything (`BodyTransformation::has_stubs`).
//
// This is the third false-Safe channel in this feature with ONE root cause:
// the walk must read what the ENCODER reads, never a parallel view of the
// program. The other two were `assert!` (redefined by trust-mc's own
// `library/std` into a Kani hook with an empty body) and a per-FILE
// certificate flag standing in for a per-HARNESS answer.
//
// If this file ever reports SUCCESSFUL, the certificate is laundering a stub.

fn clean() {}

fn panicking() {
    assert!(false);
}

#[kani::proof]
#[kani::stub(clean, panicking)]
fn bug_stub_adds_the_obligation() {
    clean();
}
