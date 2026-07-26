// FLATTEN_ITE_HETERO dual (positive twin of dual_result_ite_flatten_invalid).
//
// `char::from_u32_unchecked`'s debug precondition lowers to a
// `Result<char, CharTryFromError>` = `ite(is_valid_char(x), Ok(from_u32(x)),
// Err(..))`. The flattened destination of that Result is heterogeneous
// (Ok's char BV32 vs Err's ZST/Bool placeholder), so the ITE-of-constructors
// must decompose into disjoint tag/ok/err slots (see
// `decompose_dt_ite_to_scalars`). For a VALID char the precondition holds, so
// using the produced `char` must verify SUCCESSFULLY — the decomposition must
// not spuriously reject a valid value (the char_validity::check_char_ok gap).
//
// Oracle: MUST be SUCCESSFUL.
// kani-flags: -Z valid-value-checks -Z mem-predicates
#[kani::proof]
fn result_ite_flatten_valid() {
    let x = kani::any_where(|v: &u32| char::from_u32(*v).is_some());
    let c = unsafe { char::from_u32_unchecked(x) };
    assert!(kani::mem::can_dereference(&c as *const char));
    std::hint::black_box(c);
}
