// Inline-asm fail-closed dual (guards the CHC InlineAsm path in
// transition_gen.rs). The ONLY inline asm treated as a no-op edge is an
// operand-free template exactly equal to `nop` (Case A). Every other inline
// asm — anything with operands or a non-nop template — MUST hit the
// fail-closed branch (Case B) that emits an untranslatable-assert error rule,
// so an asm block that modifies state can never yield a vacuous PROOF.
//
// Here the asm writes x = 5, then we assert x == 0. If the fail-closed edge
// were ever weakened to "drop the asm as a no-op", trust-mc would prove
// x == 0 (a MISSED BUG). This MUST stay VERIFICATION:- FAILED — the
// InlineAsm untranslatable check fires before any vacuous discharge.
//
// (arm64 template; the suite runs on aarch64-apple-darwin. The fail-closed
// branch keys on the terminator shape, not the instruction, so the exact
// mnemonic is not load-bearing — only that operands are present / template
// is not the bare `nop`.)

#[kani::proof]
fn asm_writes_dual() {
    let mut x: u64 = 0;
    unsafe {
        core::arch::asm!("mov {0:x}, #5", out(reg) x);
    }
    assert!(x == 0);
}
