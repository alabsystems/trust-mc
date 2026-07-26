// SOUNDNESS DUAL (enum variant discrimination across array-read vs literal).
//
// Guards that the enum-literal-consistency fix discriminates VARIANTS, not just
// payloads: an array of `None::<u8>` must compare equal to the `None` literal
// and NOT equal to any `Some(_)` literal.
//
// EXPECTED VERDICTS:
//   check_none_eq_none  -> VERIFICATION:- SUCCESSFUL  (None == None is true)
//   check_none_ne_some  -> VERIFICATION:- FAILED (Genuine)  (None == Some(0) is false)
//
// A SUCCESS on check_none_ne_some would mean the tag/discriminant comparison was
// forced true across variants — a false-Safe. Never delete, never weaken.
#[kani::proof]
fn check_none_eq_none() {
    let a = [None::<u8>; 5];
    let i: usize = kani::any();
    kani::assume(i < 5);
    assert_eq!(a[i], None);
}

#[kani::proof]
fn check_none_ne_some() {
    let a = [None::<u8>; 5];
    let i: usize = kani::any();
    kani::assume(i < 5);
    assert_eq!(a[i], Some(0));
}
