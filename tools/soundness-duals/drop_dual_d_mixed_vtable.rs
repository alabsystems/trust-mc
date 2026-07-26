// Dual D (vtable-guard rider): symbolic vtable selects UB candidate — must stay FAILED.
// (Copied verbatim from scratchpad/dual_d_mixed_vtable.rs, confirmed FAILED-Genuine
// pre-fix.) MANDATORY gate for the shipped vtable-guard rider: with the error
// rules now guarded per candidate, the UB candidate's error rule must remain
// satisfiable under the vtable value that selects UbDrop.
#![allow(deref_nullptr)]
static mut CELL: i32 = 0;
trait T { fn t(&self) {} }
struct SafeDrop;
impl T for SafeDrop {}
impl Drop for SafeDrop { fn drop(&mut self) { unsafe { CELL = 1; } } }
struct UbDrop;
impl T for UbDrop {}
impl Drop for UbDrop {
    fn drop(&mut self) { unsafe { *(std::ptr::null_mut::<i32>()) = 1; } }
}
#[kani::proof]
fn main() {
    {
        let x: Box<dyn T>;
        if kani::any() { x = Box::new(SafeDrop {}); } else { x = Box::new(UbDrop {}); }
        let _ = &x;
    }
}
