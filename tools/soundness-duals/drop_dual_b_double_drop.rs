// Dual B: drop-count bug through the repaired static-write channel — must stay FAILED.
// (Copied verbatim from scratchpad/dual_b_double_drop.rs, confirmed FAILED-Genuine
// pre-fix.) drop_in_place + scope-end drop increments COUNT twice; with the fix
// routing the static store to the real address, the encoder must SEE the second
// increment and fail assert!(COUNT == 1). Before the fix this bug class was
// invisible (stores went to address 0).
static mut COUNT: i32 = 0;
struct D;
impl Drop for D { fn drop(&mut self) { unsafe { COUNT += 1; } } }
#[kani::proof]
fn main() {
    {
        let mut x = D;
        unsafe { std::ptr::drop_in_place(&mut x); }
    } // scope-end drop runs again -> COUNT == 2
    assert!(unsafe { COUNT } == 1);
}
