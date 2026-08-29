// Oracle: MUST FAIL.
//
// Array rest patterns use `ProjectionElem::Subslice { from_end: false }`, where
// `to` is an ABSOLUTE end index. They must not be evaluated as
// `len - from - to`, and `(from=0, to=0)` is an EMPTY range rather than the
// `[0..len-0]` identity used when `from_end: true`.
//
// Both assertions below are false and must be refuted. They pin the two values
// whose accidental conflation motivated the polarity repair: a two-element
// middle range and a zero-element prefix range.

#[kani::proof]
fn bug_from_start_subslice_uses_trailing_count() {
    let a: [i64; 5] = [1, 2, 3, 4, 5];
    let middle = match &a {
        [_, middle @ .., _, _] => middle,
    };

    // MIR is Subslice { from: 1, to: 3, from_end: false }: length 2.
    assert!(middle.len() == 1);
}

#[kani::proof]
fn bug_empty_from_start_subslice_is_full_range() {
    let a: [i64; 4] = [1, 2, 3, 4];
    let empty = match &a {
        [empty @ .., _, _, _, _] => empty,
    };

    // MIR is Subslice { from: 0, to: 0, from_end: false }: length 0.
    assert!(empty.len() == a.len());
}
