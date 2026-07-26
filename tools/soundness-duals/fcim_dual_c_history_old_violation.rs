// gate-flags: -Zfunction-contracts
// fc-interior-mut DUAL (c) — history/old() dual of
// tests/expected/function-contract/history/copy_pass.rs.
//
// MUST stay VERIFICATION:- FAILED after the fc-interior-mut fix
// (specifically after the copy_pass mirror-unification sub-fix unifies the
// old() snapshot mirror obj with the ensures-capture mirror obj).
//
// ensures claims the value is UNCHANGED while the body increments it: after
// unifying the two memory mirrors (the never-written 0x6d twin with the real
// 0x2 mirror), the old snapshot (v) and the post-state read (v + 1) must
// differ => FAILED. Catches any unification that aliases the old() snapshot
// WITH post-state (both would read v + 1 and the ensures would hold falsely).

struct NoCopy<T>(T);

impl<T: kani::Arbitrary> kani::Arbitrary for NoCopy<T> {
    fn any() -> Self {
        Self(kani::any())
    }
}

// BUG: value changes but the contract claims it does not.
#[kani::ensures(|result| old(ptr.0) == ptr.0)]
#[kani::requires(ptr.0 < 100)]
#[kani::modifies(&mut ptr.0)]
fn modify(ptr: &mut NoCopy<u32>) {
    ptr.0 += 1;
}

#[kani::proof_for_contract(modify)]
fn main() {
    let mut i = kani::any();
    modify(&mut i);
}
