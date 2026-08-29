// Oracle: MUST be SUCCESSFUL. (Strict: no demotion allowance — the header
// below requires a clean PASS as the non-vacuity witness.)
//
// WAS RED, FIXED 2026-08-24: it failed with "0 EncodingGap, 0
// OverApproximation, 1 Genuine" — a false positive on a CORRECT program. Root
// cause was NOT interior mutability as such: in codegen_decl_ref_numeric, Pass 2
// composed projections onto a closure-capture base that Pass 2.5 only repaired
// AFTERWARDS, so `im.x` resolved to the closure environment's own storage and
// the post-state read landed on a memory cell nothing ever writes (a free BV,
// making a true postcondition refutable). Fixed by running Pass 2.5 before
// Pass 2 as well as after.
//
// Task #71 adversarial dual twin: same shape as dual71_wrong_ensures.rs but
// with the CORRECT ensures (+1). This harness must PASS (SUCCESSFUL) — it is
// the non-vacuity witness that the FAILURE of the wrong-ensures dual comes
// from the model actually observing the store, not from blanket failure.
// kani-flags: -Zfunction-contracts

use std::cell::Cell;

struct InteriorMutability {
    x: Cell<u32>,
}

#[kani::requires(im.x.get() < 100)]
#[kani::modifies(&im.x)]
#[kani::ensures(|_| im.x.get() == old(im.x.get()) + 1)]
fn modify(im: &InteriorMutability) {
    im.x.set(im.x.get() + 1)
}

#[kani::proof_for_contract(modify)]
fn harness_for_modify() {
    let im: InteriorMutability = InteriorMutability { x: Cell::new(kani::any()) };
    modify(&im)
}
