// Oracle: MUST FAIL.
//
// The callee below IS an implementation of core's exact Index trait, so DefId
// authentication alone is intentionally insufficient. Its receiver is a
// downstream carrier whose trimmed type name is `Vec`, not a slice or array.
// The real body returns only three elements; accepting that carrier as slice
// identity would fabricate length four and prove the false assertion.

use std::ops::RangeFull;

mod mymod {
    use std::ops::{Index, RangeFull};

    pub struct Vec<T>(pub [T; 4]);

    impl<T> Index<RangeFull> for Vec<T> {
        type Output = [T];

        fn index(&self, _: RangeFull) -> &Self::Output {
            &self.0[..3]
        }
    }
}

#[kani::proof]
fn custom_vec_and_index_names_have_no_slice_authority() {
    let source = mymod::Vec([1u8, 2, 3, 4]);
    let result = <mymod::Vec<u8> as std::ops::Index<RangeFull>>::index(&source, RangeFull);

    assert!(result.len() == 4);
}
