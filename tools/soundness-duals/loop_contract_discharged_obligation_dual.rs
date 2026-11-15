// Oracle: MUST NOT report SUCCESSFUL (corpus-rev Kani, measured 2026-09-24:
// both FAIL "Check invariant after step").
//
// WHY THIS FILE EXISTS (known red on chc until design 5): the lost_error_rules_dual.rs shape
// PLUS one post-loop assertion the compiler discharges statically. On the
// legacy loop-contract encoding the CHC latch reads the raw `{ true }` body of
// `kani_register_loop_contract`, so the invariant-preservation check has no
// derivation. For lost_error_rules_dual.rs the driver's V4 vacuity probe
// catches that (every check site is unreachable -> VACUOUS). Here the
// discharged assertion's obligation is `false`-bodied, has no block atom, and
// makes the probe decline by design (vacuity_probe.rs,
// no_probe_when_one_obligation_of_several_has_no_block_atom), so the lost
// check is credited as proved.
//
// Found by the test review of land/array-param-mid-guard; the root cause is
// the legacy latch, which 290ac7cb8 tried to fix and which was reverted for
// the regressions in loop_contract_register_walk_dual.rs.
//
// FIXED by design 5 (docs/chc-hole-fix-designs-2026-09-24.md, "Design 5"):
// the legacy latch evaluates the invariant through the closure's Fn::call
// shim and asserts it (a reachable-state check), and CHC codegen books every
// legacy latch fail-closed, so neither harness can report SUCCESSFUL.

#![feature(proc_macro_hygiene)]
#![feature(stmt_expr_attributes)]

#[kani::proof]
fn fabricated_len_breaks_after_step() {
    let a: [u8; 10] = kani::any();
    let s = a.as_slice();
    let mut bytes = s;
    #[kani::loop_invariant(bytes.len() != 9)]
    while let [first, rest @ ..] = bytes {
        if first.is_ascii_whitespace() {
            bytes = rest;
        } else {
            break;
        }
    }
    assert!(s.len() == 10);
}

#[kani::proof]
fn lost_rules_plus_discharged_assert() {
    let a: [u8; 10] = kani::any();
    let s = a.as_slice();
    let mut bytes = s;
    #[kani::loop_invariant(bytes.len() == s.len())]
    while let [first, rest @ ..] = bytes {
        if first.is_ascii_whitespace() {
            bytes = rest;
        } else {
            break;
        }
    }
    assert!(s.len() == 10);
}
