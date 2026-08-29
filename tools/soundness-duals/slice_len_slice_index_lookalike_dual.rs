// Oracle: MUST FAIL.
//
// The registry's compatibility recognizer routes this exact downstream suffix
// as SliceIndexIndex. Its signature also uses SliceIndex's real argument order
// (index, source), but its DefId is unrelated to core's SliceIndex trait and its
// body deliberately returns only three elements. A suffix/signature/order match
// must never authorize the slice identity handler.

use std::ops::RangeFull;

mod mymod {
    pub mod slice {
        pub mod index {
            use std::ops::RangeFull;

            pub struct SliceIndex;

            impl SliceIndex {
                pub fn index(_: RangeFull, source: &[u8]) -> &[u8] {
                    &source[..3]
                }
            }
        }
    }
}

#[kani::proof]
fn slice_index_path_lookalike_has_no_identity_authority() {
    let source = [1u8, 2, 3, 4];
    let result = mymod::slice::index::SliceIndex::index(RangeFull, &source);

    assert!(result.len() == source.len());
}
