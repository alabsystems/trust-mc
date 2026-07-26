// Dual A (loop-contract skeptic): targets the RESTORED violation conjunct in
// per-property error rules. `i == 3` satisfies the loop guard `i > 2` and
// `3 - 4` genuinely underflows u16, so the subtract-overflow check is a REAL
// bug. This MUST stay VERIFICATION:- FAILED after the pruner fix — a
// SUCCESSFUL here means the restored/retained guard made the error rule
// body-UNSAT and silently deleted a real error edge (task-#57 regression
// class). Plain loop, no loop contracts, no extra flags needed.

#[kani::proof]
fn dual_a_underflow() {
    let mut i: u16 = kani::any();
    while i > 2 {
        i = i - 4;
    }
}
