// P2-S1 soundness dual: a contracted function whose ensures holds for the
// INITIALIZER value of a `static mut` but breaks for other values.
//
// Kani contract semantics: a `#[kani::proof_for_contract]` CHECK harness must
// prove the contract for ARBITRARY ambient static state (statics are
// havocked). With statics pinned to initializers this FALSELY PROVES
// (fail-open). After P2-S1 it must FAIL.

static mut COUNTER: u32 = 0;

/// The ensures `result == 1` only holds when COUNTER starts at its
/// initializer (0). For any other ambient value (e.g. COUNTER_pre = 5 ->
/// result = 6) the contract is violated, so a correct contract checker
/// MUST reject it.
#[kani::modifies(std::ptr::addr_of!(COUNTER))]
#[kani::ensures(|result| *result == 1)]
pub unsafe fn bump() -> u32 {
    unsafe {
        COUNTER = COUNTER.wrapping_add(1);
        COUNTER
    }
}

#[kani::proof_for_contract(bump)]
fn check_bump() {
    unsafe {
        let _ = bump();
    }
}
