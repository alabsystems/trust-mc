// Violated-ensures dual for history/copy_pass.rs (kani-flags: -Zfunction-contracts)
// Body increments by 1, but the ensures claims +2. This is a GENUINE contract
// violation and MUST fail with a Genuine CTREX. It proves the deref+field
// ensures check is a LIVE error rule (not a lost/vacuous check), so the FP on
// the real copy_pass is a fabricated CEX on a VALID contract, not fail-open.
struct NoCopy<T>(T);
impl<T: kani::Arbitrary> kani::Arbitrary for NoCopy<T> {
    fn any() -> Self { Self(kani::any()) }
}
#[kani::ensures(|result| old(ptr.0) + 2 == ptr.0)] // WRONG: body only adds 1
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
