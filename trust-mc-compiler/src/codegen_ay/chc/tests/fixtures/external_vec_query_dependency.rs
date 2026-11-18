// A real dependency definition. Its printed path deliberately contains
// alloc::vec::Vec, which also triggers the existing inline boundary.
pub mod alloc { pub mod vec {
    #[repr(C)] pub struct Vec<T> { pub value: T, pub other: usize }
    impl<T> Vec<T> {
        #[inline(never)] pub fn len(&self) -> usize { self.other }
        #[inline(never)] pub fn capacity(&self) -> usize { self.other + 1 }
        #[inline(never)] pub fn is_empty(&self) -> bool { self.other == 0 }
        #[inline(never)] pub fn as_ptr(&self) -> *const T { &self.value }
        #[inline(never)] pub fn as_mut_ptr(&mut self) -> *mut T { &mut self.value }
        #[inline(never)] pub fn as_slice(&self) -> &[T] { std::slice::from_ref(&self.value) }
    }
} }

// Re-exporting the actual Vec must preserve its library identity.
pub use std::vec::Vec as LibraryVec;

// A real external impl on actual Vec has the right owner/signature but
// different semantics; authenticating only the receiver would admit it.
pub trait EvilVec { fn len(&self) -> usize; }
impl EvilVec for LibraryVec<u64> {
    #[inline(never)] fn len(&self) -> usize { 0 }
}
