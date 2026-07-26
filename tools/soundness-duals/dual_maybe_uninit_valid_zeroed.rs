// MAYBE_UNINIT_WRITE_BYTES_BROADCAST dual — over-conservatism guard.
//
// A `MaybeUninit::<u64>::zeroed()` assume_init'd is a valid 0 (u64 has no niche
// validity constraint), so asserting `== 0` MUST verify SUCCESSFUL. The
// broadcast validity fix must not over-conservatively break the valid case.
//
// Oracle: MUST be SUCCESSFUL.
// kani-flags: -Z valid-value-checks
use std::mem::MaybeUninit;

#[kani::proof]
fn maybe_uninit_valid_zeroed_is_zero() {
    let maybe = MaybeUninit::zeroed();
    let v: u64 = unsafe { maybe.assume_init() };
    assert_eq!(v, 0);
}
