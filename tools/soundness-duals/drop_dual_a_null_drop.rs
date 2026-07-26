// Dual A: REAL null-deref in dyn drop glue — must stay FAILED after fix.
// (Copied verbatim from scratchpad/dual_a_null_drop.rs, confirmed FAILED-Genuine
// pre-fix.) The null pointer constant has NO provenance, so the repaired
// translate_constant_referent static path never applies; the inlined drop-glue
// UB check must keep evaluating on a genuine constant-0 address and derive
// the error.
#![allow(deref_nullptr)]
trait T { fn t(&self) {} }
struct B1;
impl T for B1 {}
impl Drop for B1 {
    fn drop(&mut self) {
        unsafe { *(std::ptr::null_mut::<i32>()) = 1; }
    }
}
#[kani::proof]
fn main() {
    { let _x: Box<dyn T> = Box::new(B1 {}); }
}
