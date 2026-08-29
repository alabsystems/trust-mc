// Oracle: MUST FAIL.
//
// Exact trait identity alone does not authenticate an implementation.  A
// downstream crate may implement the standard `Index` trait for a local index
// type and a slice receiver, and that implementation need not be identity.
// TrustMC must not route such a method through its core slice-index semantics.

struct LocalIndex;

impl std::ops::Index<LocalIndex> for [u8] {
    type Output = [u8];

    fn index(&self, _: LocalIndex) -> &Self::Output {
        &self[..0]
    }
}

#[kani::proof]
fn downstream_index_impl_has_no_core_identity_authority() {
    let source: &[u8] = &[1, 2, 3, 4];
    let result: &[u8] = &source[LocalIndex];

    assert!(result.len() == source.len());
}
