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

## Manifest-driven gate (plan gate G4 groundwork)

`manifest.toml` is the machine-read oracle for every file here, for the
negative pack in `negative/`, and for the eight `tests/ay` soundness-ledger
files. `scripts/soundness-dual-gate.py` runs it; `run_dual_wall.py` guessed
expectations from prose at run time and is kept only for history.

Each `[[entry]]` names the file, its flags, the lanes it applies to (`bmc` is
the default lane, `chc` is `--ay-chc`) and `oracle`, which quotes where the
expectation comes from. Each `[[entry.harness]]` carries one expectation:

| expected | match | gating | other |
|---|---|---|---|
| `FAILED` | FAILED | SUCCESSFUL = missed-bug; Genuine FAILED with `forbid_genuine` = false-certificate | INCONCLUSIVE = unknown |
| `NOT_SUCCESSFUL` | FAILED or INCONCLUSIVE | SUCCESSFUL = missed-bug | |
| `SUCCESSFUL` | SUCCESSFUL | Genuine FAILED = false-certificate | demoted FAILED = false-failure |
| `NOT_GENUINE` | SUCCESSFUL, or FAILED without `[AY:CTREX_CAT:Genuine]` | Genuine FAILED = false-certificate | |
| `TOLERATED` | any decided verdict | | |

A **false-certificate** is a counterexample the engine certified
`[AY:CTREX_CAT:Genuine]` ("a real counterexample, no encoding doubt") that the
manifest says cannot exist. It is a confident wrong bug report: the
certification channel failed the way a missed bug's proof channel fails, so it
gates by default. A FAILED that the engine itself demoted (`OverApproximation`,
`EncodingGap`, `Unknown`) makes no such claim and stays `false-failure`, which
gates only under `--strict`.

`covers` and `checks` add per-check truths: a violable check that reads
SUCCESS, or a satisfiable cover that reads UNSATISFIABLE or SUCCESS, is a
missed bug even when the harness verdict matches. UNDETERMINED always matches.
`property` records the coarse class of the failing check; it is reported
(`property_ok`) and never gates. A file whose expectation cannot be read off
its own comments carries `needs_review` with the reason instead of a guess,
and scores `unclassified`.

`known_red = true` (with `evidence`, `known_red_class`, and optionally
`known_red_lanes`) marks a row that is red today for a documented reason. It is
still reported, but it does not fail the gate in those lanes **for that class
only**: `known_red_class` names the one class the row is red for, and any other
non-match class is scored as if the flag were absent, so a row parked for a
false certificate cannot mask a later missed bug. Such a row is also listed as
`known_red_class_changed`. A known-red row that turns green is listed as
`known_red_now_green` so the flag gets removed.

### Running

```sh
python3.12 scripts/soundness-dual-gate.py --validate          # manifest vs tree, no bundle
scripts/build-pinned-ay-cli.sh                                # the pinned ay CLI; prints its path
python3.12 scripts/soundness-dual-gate.py \
  --bundle ~/trust-mc/target/trust-mc \
  --jobs 3 --timeout 30 --report tools/soundness-duals/reports/<name>.json
```

`--ay-dir` defaults to the directory `scripts/build-pinned-ay-cli.sh` builds
into, keyed by the Cargo.toml AY pin:
`~/Library/Caches/trust-mc-ay-cli-<first 9 characters of the pin>/release`
(`TRUST_MC_AY_CLI_CACHE_ROOT` replaces `~/Library/Caches`). The script builds
ay with `--features cli` in a detached worktree under that cache, never in
`../ay`, reuses a binary whose `--version` already names the full pin, and
leaves the old unkeyed `~/Library/Caches/trust-mc-ay-cli` alone. Pass
`--ay-dir` only to gate against a CLI somewhere else.

The gate sets `TRUST_MC_SYSROOT=<bundle>`, `RUSTFLAGS=-Awarnings` and puts the
ay directory first on PATH, and refuses (exit 2) unless `ay --version` names
the Cargo.toml AY pin. It runs one driver process per (file, lane) in a
scratch working directory, with `--harness-timeout=<timeout>s` and a
wall-clock limit of `180 + harnesses * (2 * timeout + 30)` seconds. It exits 1
when any missed-bug, false-certificate or error row is not known-red for its
lane and class, or when no row reached a decided verdict (an empty selection, or a
driver that crashed or hung on everything, never reads as a pass); `--strict`
also fails on false-failure and unknown rows. It exits 0 otherwise. `--lane`,
`--only <path substring>` and `--kind dual|negative|ledger` narrow a run;
`--log-dir` keeps the driver logs.

The report records provenance: bundle driver sha256 and `--version`, compiler
sha256, the driver mtime, the HEAD of the checkout holding the bundle at gate
time (`checkout_at_run`: not proof of the build commit), the ay version and
pin, trust-mc HEAD and dirty state and the manifest sha256 read at start (with
`changed_during_run` flags), the inherited verdict-relevant environment
(`inherited_env`: `TRUST_*`, `AY_*`, `KANI_*`, `CBMC_*`, `CHC_*`, `RUST*`),
load average at start and end, jobs and timeouts. Committed reports live in
`reports/`.

### Codegen determinism gate

A verdict that depends on the order of the solver's input is only reproducible
when the input is. `scripts/check-codegen-determinism.py` compiles every file
of `manifest.toml` `--runs` times per lane with `--only-codegen --keep-temps`
(no solver runs) and compares, per harness, the `.smt2` text each run emitted,
up to a renaming of declared symbols and the order of declarations; `--raw`
requires byte-identical text. It exits 1 on any other difference, and 2 when a
run emitted nothing to compare (an empty comparison never reads as a pass).

```sh
python3.12 scripts/check-codegen-determinism.py \
  --bundle ~/trust-mc/target/trust-mc --ay-dir <dir of the pinned ay CLI> \
  --runs 3 --jobs 3 --report <file>.json
```

Run it beside the dual gate on any change to codegen or harness ordering.
Measured 2026-10-01: before the fixes in `06c29b7d1`, three runs of the duals
gave 56 BMC and 410 CHC harness texts that differ in structure (harness order,
`HashMap`-ordered conjuncts and relation columns, one liveness decision); after
them, all 1631 BMC and 2340 CHC texts are byte-identical across three runs.

### Negative pack

`negative/*.rs` encodes the false-proof and wrong-verdict shapes the
2026-09-10 plan audit confirmed. Each file is a dual: must-fail harnesses
beside safe twins, with an `Oracle (per harness)` header and the audit
evidence id. Every file applies to both lanes. The rows red on the first run
are `known_red` in the lanes where they are red.

### Single file by hand

```sh
trust-mc-driver [--ay-chc] -Z unstable-options [-Z function-contracts] \
  --harness-timeout=45s [--harness NAME] tools/soundness-duals/FILE.rs
```
