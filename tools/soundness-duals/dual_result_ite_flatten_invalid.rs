// FLATTEN_ITE_HETERO dual (CRITICAL / missed-bug tripwire).
//
// `char::from_u32_unchecked(x)`'s debug precondition lowers to a heterogeneous
// `Result<char, CharTryFromError>` = `ite(is_valid_char(x), Ok(..), Err(..))`
// whose flattened destination the ITE decomposition (`decompose_dt_ite_to_scalars`)
// must split into disjoint tag/ok/err slots. The decomposition MUST stay
// EXACTLY equivalent to the original datatype ite: `is_ok = is_valid_char(x)`.
//
// Here `x = u32::MAX` is NOT a valid Unicode scalar value, so the precondition
// `is_ok` is false and using the result as a `char` is UB. If the flatten
// dropped or over-constrained the validity check (e.g. forced the tag true or
// pinned the ok-slot to a valid value), this harness would wrongly SUCCEED —
// a corpus-wide missed bug. It MUST be FAILED.
//
// Oracle: MUST be FAILED — invalid `char` reached / precondition violated.
// kani-flags: -Z valid-value-checks -Z mem-predicates
#[kani::proof]
fn result_ite_flatten_invalid() {
    let x: u32 = u32::MAX; // > 0x10FFFF -> not a valid char
    let c = unsafe { char::from_u32_unchecked(x) };
    // The invalid value must not be dereferenceable as a `char`.
    assert!(kani::mem::can_dereference(&c as *const char));
    std::hint::black_box(c);
}
