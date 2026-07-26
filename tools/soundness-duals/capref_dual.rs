// Captured-ref walk gap dual — VIOLATED postcondition.
// The ensures closure reads captured refs (`(*_1).N` projections through the
// closure env). The postcondition is deliberately WRONG: body adds 2, ensures
// claims +1. MUST FAIL — ideally with a genuine CTREX on the ensures line,
// carried by the now-walked closure. A SUCCESSFUL verdict is an instant no-ship.
// kani-flags: -Zfunction-contracts

struct S {
    a: u32,
    b: u32,
}

#[kani::requires(s.a < 100)]
#[kani::modifies(&mut s.a)]
#[kani::ensures(|_| old(s.a + 1) == s.a)] // WRONG: body adds 2
fn bump(s: &mut S) {
    s.a += 2;
}

#[kani::proof_for_contract(bump)]
fn harness_bump() {
    let mut s = S { a: kani::any(), b: kani::any() };
    bump(&mut s);
}
