// SOUNDNESS DUAL (missed-bug tripwire) — loop-rule ==0 exit-relation probe.
//
// EXPECTED VERDICT: VERIFICATION:- FAILED. A SUCCESS here means the loop proof
// rule proved a genuinely violated ==0 exit relationship: false-Safe channel open.
// Never delete, never weaken.
//
// Reconstructed 2026-07-19 from archived artifacts
//   patches/probe_eq0__RNvCs5dWVUthjISf_9probe_eq04main.symtab.{smt2,vc.json}
// after the source was lost from the shared scratchpad.
//
// Property multiset (archived vc.json) — identical family to loop_missed_bug.rs:
//   memory_safety x2
//   assertion "attempt to subtract with overflow" x2
//   assertion "attempt to shift left with overflow"
//   assertion "attempt to add with overflow"
//   assertion "assertion failed: count == 0"          (the REAL bug: count == 8)

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
    // REAL reachable bug: count == 8 != 0 here.
    assert!(count == 0);
}
