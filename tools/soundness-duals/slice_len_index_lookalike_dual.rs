// Oracle: MUST FAIL.
//
// The stub registry intentionally accepts suffix-compatible Index paths, but
// such a match is only a routing hint. This downstream lookalike has the exact
// `mymod::ops::Index::index` suffix and a RangeFull-shaped signature while its
// semantics are deliberately NOT identity: it returns a three-element slice.
// Treating the registry match as proof authority fabricates length four and
// makes the false assertion verify. DefId authentication must leave this call
// to its real body instead.

use std::ops::RangeFull;

mod mymod {
    pub mod ops {
        use std::ops::RangeFull;

        pub struct Index;

        impl Index {
            pub fn index(source: &[u8], _: RangeFull) -> &[u8] {
                &source[..3]
            }
        }
    }
}

#[kani::proof]
fn index_path_lookalike_has_no_identity_authority() {
    let source = [1u8, 2, 3, 4];
    let result = mymod::ops::Index::index(&source, RangeFull);

    assert!(result.len() == source.len());
}
