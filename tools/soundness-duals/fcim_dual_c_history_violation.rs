// fcim dual (c) — history/old() violation: ensures old(ptr.0) == ptr.0 while
// the body does ptr.0 += 1. After any old()/post-state mirror unification the
// old snapshot (v) vs post-read (v+1) MUST differ => VERIFICATION FAILED.
// Catches unification that aliases the old() snapshot with post-state.
// kani-flags: -Zfunction-contracts

struct NoCopy<T>(T);

impl<T: kani::Arbitrary> kani::Arbitrary for NoCopy<T> {
    fn any() -> Self {
        Self(kani::any())
    }
}

#[kani::ensures(|result| old(ptr.0) == ptr.0)]
#[kani::requires(ptr.0 < 100)]
#[kani::modifies(&mut ptr.0)]
fn modify(ptr: &mut NoCopy<u32>) {
    ptr.0 += 1; // BUG w.r.t. contract: old(ptr.0) != ptr.0 afterwards
}

#[kani::proof_for_contract(modify)]
fn main() {
    let mut i = kani::any();
    modify(&mut i);
}
