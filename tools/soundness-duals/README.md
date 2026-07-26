# tools/soundness-duals — missed-bug tripwires (gate suite)

These files are **soundness duals**: deliberately buggy (or paired safe-twin)
programs run by the gate scripts on every soundness-relevant change. They are
the tripwires that keep the false-Safe (missed-bug) channels closed.

**Every `*_repro.rs` / `*dual*` bug file's expected verdict is
`VERIFICATION:- FAILED`.** A `SUCCESSFUL` verdict on any of them means a
false-Safe channel has reopened — treat it as a P0 soundness regression, not a
win. Safe-twin / `*_control.rs` files document which neighbouring behavior is
expected to pass (or to fail for a *different*, honest reason) so a fix can be
localized.

**Never delete these files. Never weaken them** (no shrinking asserts, no
narrowing assumes, no removing arms/fields). If a dual must change, the change
needs the same adversarial missed-bug review as a solver change.

## The six core gate tripwires

| file | harness(es) | flags | expected |
|---|---|---|---|
| `loop_missed_bug.rs` | `main` | — | FAILED (`assertion failed: count <= 7`) |
| `probe_eq0.rs` | `main` | — | FAILED (`assertion failed: count == 0`) |
| `devirt_missed_bug_1.rs` | `check_inner_dyn_coercion_missed_bug` | — | FAILED |
| `vtable-smartptr-discriminant-loss_repro.rs` | `check` | — | FAILED (`s < 1000`) |
| `modifies-frame-offset-drop_repro.rs` | `check_evil`, `caller_relies_on_frame` | `-Z function-contracts` | FAILED (both) |
| `enum_invalid_discriminant_unreachable_repro.rs` | `transmute_invalid_enum_discriminant` | — | FAILED (`invalid enum construction: …`) |

Classes covered: loop-rule fail-close backstop (A), dyn-coercion devirt
under-collection (B), vtable discriminant loss through a smart pointer (C),
modifies-frame offset-drop leak (FC-06 / E), invalid-enum-discriminant UB
swallowed by the unreachable-otherwise gate (F).

## Provenance

The six core files were lost from the shared scratchpad and were
**semantically reconstructed on 2026-07-19** from their surviving emitted
artifacts (`<crate>__<mangled>.symtab.smt2` + `.vc.json` under the session
scratchpad `patches/` and `audit/` dirs). Each reconstruction was validated
against the archived `vc.json` property-kind+message multiset and re-verified
to produce `VERIFICATION:- FAILED` on the then-current build. Per-file headers
name their exact archived artifacts.

The remaining files are the surviving session duals collected from the
scratchpad (`patches/`, `audit/`) and prior agent worktrees (`dual69_*`,
`dual71_*`, `dual_w2_*`, `rec55_*`, `fcim_*`, `lc_*`, `offs52_*`, `capref_*`,
`drop_dual_*`, `fastmath_*`, …), moved here so the whole suite is git-tracked
and cannot be lost to scratchpad cleanup again.

## Running

Single file (harness optional):

```sh
trust-mc-driver --ay-chc -Z unstable-options [-Z function-contracts] \
  --harness-timeout=45s [--harness NAME] tools/soundness-duals/FILE.rs
```

Gate scripts should reference these files via a `DUALS=<repo>/tools/soundness-duals`
variable instead of scratchpad paths (see the session `gate-dual-paths.sed.sh`
patch that repoints `$SP/patches/*.rs` and `$AUD/*.rs`).
