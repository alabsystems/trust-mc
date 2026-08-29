#![feature(slice_index_methods)]

// Oracle: MUST PASS.
//
// The fail-closed RangeFull rule must retain useful exact authority when every
// source producer agrees. Both branches below have length four, so RangeFull
// preserves that unanimous length and the assertion remains provable.

#[kani::proof]
fn range_full_preserves_unanimous_source_length() {
    let lhs = [1u8, 2, 3, 4];
    let rhs = [5u8, 6, 7, 8];
    let choose_lhs: bool = kani::any();
    let source: &[u8] = if choose_lhs { &lhs } else { &rhs };
    let full: &[u8] = &source[..];

    assert!(full.len() == 4);
    let expected: usize = kani::any();
    kani::assume(expected == 4);
    assert!(full.len() == expected);
}

// Exercise core's exact SliceIndex route directly. Its method order is
// `(index, source)`, the inverse of Index::index's `(source, index)` order.
// Authentication must accept this exact DefId/order pair while continuing to
// reject the downstream suffix-compatible twin.
#[kani::proof]
fn exact_slice_index_order_preserves_unanimous_source_length() {
    let lhs = [1u8, 2, 3, 4];
    let rhs = [5u8, 6, 7, 8];
    let choose_lhs: bool = kani::any();
    let source: &[u8] = if choose_lhs { &lhs } else { &rhs };
    let full =
        <std::ops::RangeFull as std::slice::SliceIndex<[u8]>>::index(std::ops::RangeFull, source);

    assert!(full.len() == 4);
}
