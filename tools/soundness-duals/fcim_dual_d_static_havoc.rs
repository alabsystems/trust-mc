// gate-flags: -Zfunction-contracts
// fc-interior-mut DUAL (d) — static interior-mutability havoc gate, dual of
// target/kani-domination/kani/tests/kani/FunctionContracts/static_interior_mut.rs
// with the #[kani::should_panic] REMOVED.
//
// MUST be VERIFICATION:- FAILED after the static-havoc sub-fix lands: the
// assert_eq!(mut_field(), 0) must be falsifiable because contract mode havocs
// statics with interior mutability across the contract boundary. If the
// harness PASSES, the static is still being const-folded to its initializer 0
// (the under-approximation this dual pins) and the havoc is not real.
//
// NOTE: the static-havoc sub-fix is DEFERRED in the current change set (see
// report); until it lands this dual documents the expected post-fix verdict.

extern crate kani;

use std::cell::UnsafeCell;

pub struct WithMut {
    regular_field: u8,
    mut_field: UnsafeCell<u8>,
}

/// Just for test purpose.
unsafe impl Sync for WithMut {}

/// A static definition of `WithMut`
static ZERO_VAL: WithMut = WithMut { regular_field: 0, mut_field: UnsafeCell::new(0) };

/// The mutable field can be anything.
#[kani::ensures(|result| *result == old(unsafe { *ZERO_VAL.mut_field.get() }))]
pub unsafe fn mut_field() -> u8 {
    unsafe { *ZERO_VAL.mut_field.get() }
}

// NO #[kani::should_panic]: this harness must FAIL, proving the
// contract-boundary havoc of the interior-mut static is real (not const-fold).
#[kani::proof_for_contract(mut_field)]
fn check_mut_field_havocked() {
    assert_eq!(unsafe { mut_field() }, 0); // ** must be falsifiable post-havoc
}
