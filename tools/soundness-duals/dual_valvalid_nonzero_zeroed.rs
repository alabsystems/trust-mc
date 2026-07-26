// VALVALID_PUNNED_ARRAY_DUAL — union / MaybeUninit soundness net.
//
// This shape is NOT recovered by the `[char; N]` array-index fix (the invalid
// value is a scalar read punned out of a MaybeUninit UNION allocation, which
// the CHC type-indexed memory model still havocs — a separate, out-of-scope
// gap). It is pinned here as a soundness tripwire: a zeroed
// `MaybeUninit<NonZeroU32>` read as `NonZeroU32` is an invalid value (`0`
// violates the `1..=MAX` niche) and MUST STAY non-passing. The array fix must
// never turn it into a false SUCCESS.
//
// Oracle: MUST be non-passing (FAILED) — never a clean/Genuine SUCCESS.
// kani-flags: -Z valid-value-checks
use std::mem::MaybeUninit;
use std::num::NonZeroU32;

#[kani::proof]
fn nonzero_zeroed_invalid() {
    let maybe = MaybeUninit::<NonZeroU32>::zeroed();
    let _v: NonZeroU32 = unsafe { maybe.assume_init() };
}
