// Recursion-unwinding-assertion false certificate — BUG twin.
//
// The no-blinding half of `recursion_unwind_dual_safe.rs`. Same `Box<dyn Byte>`
// drop-glue shape, but the assertion is FALSE: `num` is assumed to be zero and
// the harness asserts it is not. The engine must still report
// `VERIFICATION:- FAILED`.
//
// Why it is here: the fix for the safe twin makes a FAILED harness whose search
// hit the recursive-inline bound report an UNCERTIFIED failure (category
// `Unknown`) rather than `[AY:CTREX_CAT:Genuine]`. That only ever weakens a
// CLAIM about a failure; it must never turn a failure into a pass. A SUCCESSFUL
// verdict here is a missed bug and a P0.
//
// Shape taken from `kani/DynTrait/unsized_cast.rs`.

trait Byte {
    fn eq(&self, byte: u8) -> bool;
}

impl Byte for u8 {
    fn eq(&self, byte: u8) -> bool {
        *self == byte
    }
}

fn all_zero(num: Box<dyn Byte>) -> bool {
    num.eq(0x0)
}

#[kani::proof]
fn check_box_drop_glue_still_reports_the_real_bug() {
    let num: u8 = kani::any();
    kani::assume(num == 0);
    let boxed: Box<dyn Byte + Sync> = Box::new(num);
    // FALSE: `num` is zero, so `all_zero` holds.
    assert!(!all_zero(boxed));
}
