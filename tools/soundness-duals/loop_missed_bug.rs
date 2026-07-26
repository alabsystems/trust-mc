// SOUNDNESS DUAL (missed-bug tripwire) — loop-invariant / loop-rule fail-close backstop.
//
// EXPECTED VERDICT: VERIFICATION:- FAILED. A SUCCESS here means the loop proof
// rule (or any straightline/loop abstraction) proved away a REAL, reachable
// assertion violation: a false-Safe channel is open. Never delete, never weaken.
//
// Reconstructed 2026-07-19 from archived artifacts
//   patches/loop_missed_bug__RNvCs6I1LSmx8D1k_15loop_missed_bug4main.symtab.{smt2,vc.json}
// after the source was lost from the shared scratchpad.
//
// Property multiset (archived vc.json):
//   memory_safety x2
//   assertion "attempt to subtract with overflow" x2   (8 - i, then a - 1)
//   assertion "attempt to shift left with overflow"    (1u8 << b, b < 8 required)
//   assertion "attempt to add with overflow"           (count + 1)
//   assertion "assertion failed: count <= 7"           (the REAL bug: count == 8)
//
// The loop body's arithmetic checks are all safe but only if the loop is
// reasoned precisely (i in 0..8 => a in 1..=8 => b in 0..=7). The exit assert
// count <= 7 is genuinely violated (count == 8): a weak/unsound loop rule that
// havocs count or proves the exit unreachable would falsely mask it.

#[kani::proof]
fn main() {
    // Symbolic seed (unused): matches the archived VC's havocked bv8 and its
    // two memory_safety properties (p0/p1).
    let _seed: u8 = kani::any();
    let mut count: u32 = 0;
    for i in 0..8u32 {
        let a = 8 - i; // subtract with overflow: needs i <= 8 (holds)
        let b = a - 1; // subtract with overflow: needs a >= 1 (holds)
        let _c = 1u8 << b; // shift left with overflow: needs b < 8 (holds)
        count = count + 1; // add with overflow (holds)
    }
    // REAL reachable bug: count == 8 here.
    assert!(count <= 7);
}
