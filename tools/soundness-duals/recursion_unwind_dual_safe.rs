// Recursion-unwinding-assertion false certificate — SAFE twin.
//
// The program is correct: `num != 0` is assumed, `Byte::eq(0)` is therefore
// false for it, and both harnesses assert exactly that. Nothing here can be
// disproved. What CAN happen is that the engine runs out of unwind budget in
// the `Box`/`Rc` drop-glue dyn dispatch (two candidates, the walker relabels
// the failure `recursion unwinding assertion`, class `recursion`, id 1) and
// reports FAILED on a truncated search.
//
// MUST NOT CERTIFY. A truncated search says nothing whatsoever about the
// program, so the harness may report SUCCESSFUL, or FAILED without
// `[AY:CTREX_CAT:Genuine]` — never a certified counterexample. Measured
// regression this pins: on the trustc route at seal 8595,
// `kani/DynTrait/unsized_cast.rs` and `unsized_rc_cast.rs` reported
// `Failed Checks: recursion unwinding assertion` with `[AY:CTREX_CAT:Genuine]`,
// a CERTIFIED failure on a correct program, because
// `harness_runner::unwind_bound_exhausted` recognised only class `"unwind"`
// (the loop bound) and not class `"recursion"` (the recursive-inline bound).
//
// Shape taken from `kani/DynTrait/unsized_cast.rs` and `unsized_rc_cast.rs`.

use std::rc::Rc;

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

fn all_zero_rc(num: Rc<dyn Byte>) -> bool {
    num.eq(0x0)
}

#[kani::proof]
fn check_box_drop_glue_is_not_a_counterexample() {
    let num: u8 = kani::any();
    kani::assume(num != 0);
    let boxed: Box<dyn Byte + Sync> = Box::new(num);
    assert!(!all_zero(boxed));
}

#[kani::proof]
fn check_rc_drop_glue_is_not_a_counterexample() {
    let num: u8 = kani::any();
    kani::assume(num != 0);
    let rc: Rc<dyn Byte + Sync> = Rc::new(num);
    assert!(!all_zero_rc(rc));
}
