use external_vec_lookalike::{alloc::vec::Vec as ForeignVec, EvilVec, LibraryVec};

#[kani::proof]
pub fn external_len_safe() { let v = ForeignVec { value: 3u64, other: 7 }; assert!(v.len() == 7); }
#[kani::proof]
pub fn external_len_bug() { let v = ForeignVec { value: 3u64, other: 7 }; assert!(v.len() == 0); }
#[kani::proof]
pub fn external_capacity_safe() { let v = ForeignVec { value: 3u64, other: 7 }; assert!(v.capacity() == 8); }
#[kani::proof]
pub fn external_capacity_bug() { let v = ForeignVec { value: 3u64, other: 7 }; assert!(v.capacity() == 0); }
#[kani::proof]
pub fn external_empty_safe() { let v = ForeignVec { value: 3u64, other: 7 }; assert!(!v.is_empty()); }
#[kani::proof]
pub fn external_empty_bug() { let v = ForeignVec { value: 3u64, other: 7 }; assert!(v.is_empty()); }
#[kani::proof]
pub fn external_pointer_safe() { let v = ForeignVec { value: 3u64, other: 7 }; assert!(unsafe { *v.as_ptr() } == 3); }
#[kani::proof]
pub fn external_pointer_bug() { let v = ForeignVec { value: 3u64, other: 7 }; assert!(unsafe { *v.as_ptr() } == 9); }
#[kani::proof]
pub fn external_mut_pointer_safe() { let mut v = ForeignVec { value: 3u64, other: 7 }; assert!(unsafe { *v.as_mut_ptr() } == 3); }
#[kani::proof]
pub fn external_mut_pointer_bug() { let mut v = ForeignVec { value: 3u64, other: 7 }; assert!(unsafe { *v.as_mut_ptr() } == 9); }
#[kani::proof]
pub fn external_slice_safe() { let v = ForeignVec { value: 3u64, other: 7 }; assert!(v.as_slice()[0] == 3); }
#[kani::proof]
pub fn external_slice_bug() { let v = ForeignVec { value: 3u64, other: 7 }; assert!(v.as_slice()[0] == 9); }
#[kani::proof]
pub fn real_reexport_safe() { let v = LibraryVec::from([3u64]); assert!(v.len() == 1 && unsafe { *v.as_ptr() } == 3); }
#[kani::proof]
pub fn real_reexport_bug() { let v = LibraryVec::from([3u64]); assert!(v.len() == 2); }
#[kani::proof]
pub fn external_trait_on_real_vec_safe() { let v = LibraryVec::from([3u64]); assert!(EvilVec::len(&v) == 0); }
#[kani::proof]
pub fn external_trait_on_real_vec_bug() { let v = LibraryVec::from([3u64]); assert!(EvilVec::len(&v) == 1); }
