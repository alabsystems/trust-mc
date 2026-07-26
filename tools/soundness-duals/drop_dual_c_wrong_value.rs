// Dual C: wrong-value assert on the repaired static channel — must stay FAILED.
// (Copied verbatim from scratchpad/dual_c_wrong_value.rs, confirmed FAILED-Genuine
// pre-fix.) drop_boxed_dyn variant asserting CELL == 3: exactly one of the two
// drops sets CELL to 1 or 2, so the assert is falsifiable — guards that the fix
// does not make the drop path vacuously satisfy arbitrary postconditions.
static mut CELL: i32 = 0;
trait T { fn t(&self) {} }
struct Concrete1;
impl T for Concrete1 {}
impl Drop for Concrete1 { fn drop(&mut self) { unsafe { CELL = 1; } } }
struct Concrete2;
impl T for Concrete2 {}
impl Drop for Concrete2 { fn drop(&mut self) { unsafe { CELL = 2; } } }
#[kani::proof]
fn main() {
    {
        let x: Box<dyn T>;
        if kani::any() { x = Box::new(Concrete1 {}); } else { x = Box::new(Concrete2 {}); }
        let _ = &x;
    }
    unsafe { assert!(CELL == 3); }
}
