// SOUNDNESS DUAL (missed-bug tripwire) — FC-06 modifies-frame enforcement:
// same-object, offset-adjacent out-of-frame write (the "dropped field offset"
// leak). Run with `-Z function-contracts`.
//
// TWO harnesses, BOTH must produce VERIFICATION:- FAILED:
//   check_evil            — contract CHECK mode: `evil` declares modifies(&p.a)
//                           but ALSO writes p.b (same object, offset +4). The
//                           frame check must flag the p.b store.
//   caller_relies_on_frame — a caller (requires satisfied: p.a = 10 < 100) that
//                           relies on the frame: p.b must be unchanged because
//                           it is outside modifies(p.a). With the evil callee
//                           it IS changed -> must FAIL. If contract replacement
//                           swallows the callee's real writes (fail-open), this
//                           falsely passes: false-Safe channel open.
// Never delete, never weaken.
//
// Sibling control (frame enforcement works cross-object) survives at
//   audit/modifies-frame-offset-drop_control.rs
// Reconstructed 2026-07-19 from archived artifacts
//   audit/modifies_frame_offset_drop_repro__RNvCs9RDmIyMQFpg_32...10check_evil
//   audit/modifies_frame_offset_drop_repro__RNvCs9RDmIyMQFpg_32...22caller_relies_on_frame
//     .symtab.{smt2,vc.json}
// (Pair{fld_a:bv32, fld_b:bv32}; footprint {obj,off 0,len 4} vs store at +4;
//  constant 100 from the requires clause).
//
// Property multisets (archived vc.json):
//   check_evil:             memory_safety x8 (live: the two frame store-checks)
//   caller_relies_on_frame: assertion "p.a < 100"
//                           assertion "p.b must be unchanged: it is outside modifies(p.a)"

#[repr(C)]
struct Pair {
    a: u32,
    b: u32,
}

// EVIL: declares it only modifies p.a, but also writes the offset-adjacent
// field p.b of the SAME object.
#[kani::requires(p.a < 100)]
#[kani::modifies(&p.a)]
fn evil(p: &mut Pair) {
    p.a = 1;
    p.b = 7; // out-of-frame write: same object, field offset dropped -> must be flagged
}

#[kani::proof_for_contract(evil)]
fn check_evil() {
    let mut p = Pair { a: kani::any(), b: kani::any() };
    evil(&mut p);
}

#[kani::proof]
fn caller_relies_on_frame() {
    let mut p = Pair { a: 10, b: 42 }; // requires satisfied: 10 < 100
    evil(&mut p);
    kani::assert(p.a < 100, "p.a < 100");
    // REAL bug: evil wrote p.b = 7. Only a fail-open frame/contract path can
    // "prove" this.
    kani::assert(p.b == 42, "p.b must be unchanged: it is outside modifies(p.a)");
}
