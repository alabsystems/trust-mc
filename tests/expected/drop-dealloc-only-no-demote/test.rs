// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

// Regression (#3017): a harness that merely constructs and drops a stdlib owning
// container (`String` / `Vec` / `Box` of drop-irrelevant elements) without
// proving anything over it must NOT be demoted PROOF -> FAILURE. Such a Drop is
// dealloc-only — invisible to the BMC value model — so the (already-skipped)
// drop terminator is observationally exact and may not poison a clean verdict.
//
// Before the fix, `<Vec<u8> as Drop>::drop` (the `String`'s destructor at scope
// exit, whose stdlib MIR is unavailable) recorded `unsupported_with_fallback`
// and the whole proof was demoted to FAILURE. `bmc_ty_drop_is_dealloc_only`
// (terminator.rs) now skips that demotion for dealloc-only containers while
// staying conservative: a container carrying a *user* `Drop` (a real value-level
// side effect) is still treated as non-trivial and still demotes.

struct WithString {
    rank: u8,
    // `name` is never read by the proof; only constructed and dropped. Its
    // destructor (Vec<u8> dealloc) is what previously demoted the harness.
    #[allow(dead_code)]
    name: String,
}

#[kani::proof]
fn dealloc_only_drop_does_not_demote() {
    let v: u8 = kani::any();
    kani::assume(v < 5);
    let s = WithString { rank: v, name: String::from("scratch") };
    assert!(s.rank <= 4, "scalar property holds; the String drop must not demote");
}
