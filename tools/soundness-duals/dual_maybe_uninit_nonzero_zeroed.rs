// MAYBE_UNINIT_WRITE_BYTES_BROADCAST dual — missed-bug guard.
//
// A `MaybeUninit::<NonZeroU32>::zeroed()` assume_init'd MUST be detected as an
// invalid value: 0 is not a valid `NonZeroU32`. If the broadcast validity read
// (build_write_bytes_limit) ever swallows this into SUCCESS, the fix is reading
// wrong/constant bytes = a false Safe. This is the load-bearing soundness net.
//
// Oracle: MUST be FAILED — "Invalid value of type `std::num::NonZero<u32>`".
// kani-flags: -Z valid-value-checks
use std::mem::MaybeUninit;
use std::num::NonZeroU32;

#[kani::proof]
fn maybe_uninit_nonzero_zeroed_is_invalid() {
    let maybe = MaybeUninit::zeroed();
    let v: NonZeroU32 = unsafe { maybe.assume_init() };
    let _g = v.get();
}
