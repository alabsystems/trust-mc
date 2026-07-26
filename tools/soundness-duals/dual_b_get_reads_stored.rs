// Dual (b): Cell::get must read the REAL stored value. set(5) then assert
// get()==6 MUST FAIL (get returns 5). Proves load reads the value that store
// wrote (not an unconstrained/fabricated value that could vacuously satisfy 6).
use std::cell::Cell;

#[kani::proof]
fn dual_b() {
    let c: Cell<u32> = Cell::new(kani::any());
    c.set(5);
    assert!(c.get() == 6);
}
