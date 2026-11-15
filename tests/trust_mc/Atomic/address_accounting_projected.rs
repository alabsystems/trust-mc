use std::sync::atomic::AtomicU32;
static CELLS: [AtomicU32; 2] = [AtomicU32::new(11), AtomicU32::new(23)];
#[kani::proof]
fn projected_return_safe() {
    let mut pointer = CELLS[0].as_ptr();
    {
        let output = &mut pointer;
        *output = CELLS[1].as_ptr();
    }
    assert!(pointer == CELLS[1].as_ptr(), "projected return writes pointee");
}
#[kani::proof]
fn projected_return_wrong_root() {
    let mut pointer = CELLS[0].as_ptr();
    {
        let output = &mut pointer;
        *output = CELLS[1].as_ptr();
    }
    assert!(pointer == CELLS[0].as_ptr(), "old pointer must not survive projected return");
}
