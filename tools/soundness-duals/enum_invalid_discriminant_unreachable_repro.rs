// SOUNDNESS DUAL (missed-bug tripwire) — MISSED-BUG F: transmute of an invalid
// discriminant into a small enum, then a match on it. The invalid-enum-
// construction UB check must FAIL; the "unreachable otherwise" gate of the
// match must NOT swallow it.
//
// EXPECTED VERDICT: VERIFICATION:- FAILED, with the failing check
//   "invalid enum construction: value is not a valid discriminant for this enum".
// A SUCCESS here means the invalid-discriminant path was classified
// unreachable and the UB check was swallowed: false-Safe channel open.
// Never delete, never weaken.
//
// Reconstructed 2026-07-19 from archived artifacts
//   audit/enum_invalid_discriminant_unreachable_repro__RNvCsigOLm3DhAlX_43...
//     35transmute_invalid_enum_discriminant.symtab.{smt2,vc.json}
// (single bv8 havoc; live error path guarded by `raw == 3`; enum therefore has
//  valid discriminants {0,1,2}).
//
// Property multiset (archived vc.json):
//   memory_safety x2
//   assertion "invalid enum construction: value is not a valid discriminant for this enum"
//   assertion "\"reachable: match on invalid transmuted enum\""

#[repr(u8)]
#[derive(Copy, Clone)]
enum Small {
    A = 0,
    B = 1,
    C = 2,
}

#[kani::proof]
fn transmute_invalid_enum_discriminant() {
    let raw: u8 = kani::any();
    if raw == 3 {
        // UB: 3 is not a valid discriminant of Small. The UB check must FAIL.
        let e: Small = unsafe { std::mem::transmute(raw) };
        match e {
            // Keeps the match arms live: if the invalid-discriminant path is
            // (wrongly) treated as reachable-and-valid, this arm is the canary.
            Small::A => assert!(false, "reachable: match on invalid transmuted enum"),
            Small::B | Small::C => {}
        }
    }
}
