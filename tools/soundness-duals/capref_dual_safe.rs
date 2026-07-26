// Captured-ref walk gap dual — SAFE twin.
// Identical shape to capref_dual.rs but the postcondition matches the body
// (+1). MUST PASS (or stay an honest unknown/demotion) — a fabricated CEX
// here means the capture resolution feeds wrong values.
// kani-flags: -Zfunction-contracts

struct S {
    a: u32,
    b: u32,
}

#[kani::requires(s.a < 100)]
#[kani::modifies(&mut s.a)]
#[kani::ensures(|_| old(s.a + 1) == s.a)] // matches body
fn bump(s: &mut S) {
    s.a += 1;
}

#[kani::proof_for_contract(bump)]
fn harness_bump() {
    let mut s = S { a: kani::any(), b: kani::any() };
    bump(&mut s);
}
