// fcim dual (d) — static-havoc gate: same as static_interior_mut.rs mut_field
// harness but WITHOUT #[kani::should_panic]. The assert_eq!(mut_field(), 0)
// MUST FAIL once contract-boundary havoc of interior-mut statics is real
// (not const-folded). While the havoc sub-fix is deferred, this dual is
// expected to (falsely) pass — documenting the deferral.
// kani-flags: -Zfunction-contracts

extern crate kani;

use std::cell::UnsafeCell;

pub struct WithMut {
    regular_field: u8,
    mut_field: UnsafeCell<u8>,
}

unsafe impl Sync for WithMut {}

static ZERO_VAL: WithMut = WithMut { regular_field: 0, mut_field: UnsafeCell::new(0) };

#[allow(dead_code)]
#[kani::ensures(|result| *result == 0)]
pub fn regular_field() -> u8 {
    ZERO_VAL.regular_field
}

#[kani::ensures(|result| *result == old(unsafe { *ZERO_VAL.mut_field.get() }))]
pub unsafe fn mut_field() -> u8 {
    unsafe { *ZERO_VAL.mut_field.get() }
}

#[kani::proof_for_contract(mut_field)]
fn check_mut_field_havoc() {
    assert_eq!(unsafe { mut_field() }, 0); // MUST FAIL once statics are havoced
}
