// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-verify-fail
//
// Adversarial dual (gate repro B) for the recursion const-fold fix (#4290).
//
// MUST report VERIFICATION FAILED (u8 add overflow) after the fix:
// sum(3) unrolls to ((0 + 100) + 100) + 100 and the third add computes
// 200 + 100 = 300 > 255 INSIDE the unrolled recursive arm. A FAILED verdict
// here proves the SwitchInt const-folder (a) selects the LIVE recursive arm
// for n != 0 (no over-pruning of live error edges) and (b) preserves the
// overflow obligations of every unrolled frame. If this test ever passes,
// the const-fold prune is deleting live obligations — fail the gate.

fn sum(n: u8) -> u8 {
    match n {
        0 => 0,
        _ => sum(n - 1) + 100,
    }
}

#[kani::proof]
fn main() {
    let _ = sum(3);
}
