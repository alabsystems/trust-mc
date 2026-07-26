// Captured-ref walk gap NESTED dual — VIOLATED inner postcondition.
// inner() is contract-checked AS AN ASSERTION inside outer()'s inline walk,
// so inner's ensures closure is translated by the virtual-inline walker and
// reads captured refs through `(*_1).N` env projections (the fixed shape).
// inner's ensures is deliberately WRONG (+1 claimed, +2 done). MUST FAIL —
// ideally a genuine CTREX on inner's ensures line. SUCCESSFUL = no-ship.
// kani-flags: -Zfunction-contracts

struct S {
    a: u32,
    b: u32,
}

#[kani::requires(s.a < 100)]
#[kani::modifies(&mut s.a)]
#[kani::ensures(|_| old(s.a + 3) == s.a)] // matches: 1 + 2
fn outer(s: &mut S) {
    s.a += 1;
    inner(s);
}

#[kani::ensures(|_| old(s.a + 1) == s.a)] // WRONG: inner adds 2
fn inner(s: &mut S) {
    s.a += 2;
}

#[kani::proof_for_contract(outer)]
fn harness_outer() {
    let mut s = S { a: kani::any(), b: kani::any() };
    outer(&mut s);
}
