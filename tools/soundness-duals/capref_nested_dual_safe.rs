// Captured-ref walk gap NESTED dual — SAFE twin.
// Same shape as capref_nested_dual.rs, but inner's ensures matches its body
// (+2). MUST PASS or stay an honest unknown/demotion — never a fabricated CEX.
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

#[kani::ensures(|_| old(s.a + 2) == s.a)] // matches body
fn inner(s: &mut S) {
    s.a += 2;
}

#[kani::proof_for_contract(outer)]
fn harness_outer() {
    let mut s = S { a: kani::any(), b: kani::any() };
    outer(&mut s);
}
