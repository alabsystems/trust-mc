// Oracle: MUST FAIL.
//
// A Range-shaped argument is not authority to synthesize the return slice's
// length.  This ordinary downstream function accepts `1..3` but deliberately
// returns an empty slice.  Pointer-metadata phase-order recovery must require
// an authenticated standard Index/SliceIndex implementation, not scan every
// call for a Range argument.

#[inline(never)]
fn ordinary_range_consumer(source: &[u8], _: std::ops::Range<usize>) -> &[u8] {
    &source[..0]
}

#[kani::proof]
fn range_argument_alone_has_no_length_authority() {
    let source: &[u8] = &[1, 2, 3, 4];
    let consume = ordinary_range_consumer as fn(&[u8], std::ops::Range<usize>) -> &[u8];
    let result = consume(source, 1..3);

    assert!(result.len() == 2);
}
