<!--
Copyright 2026 Andrew Yates
SPDX-License-Identifier: Apache-2.0 OR MIT
-->

# kani-domination

The **Kani-replacement burndown harness**. It downloads Kani's *upstream*
source, runs trust-mc over Kani's own test/benchmark corpus, and measures how
much of Kani trust-mc actually replaces — the trust-mc analogue of AY's
`ay z3-audit` / `ay bench --reference-solver z3` "domination" tooling.

Where `tools/replacement-inventory` measures a **curated local** corpus
(`tests/trust-mc` + `tests/ay`), this tool measures the **full live Kani
corpus** fetched straight from `model-checking/kani` at a pinned revision, so the
denominator is "all of Kani" rather than a hand-picked subset.

## What it measures — verdict parity ("domination")

For each Kani harness it derives the verdict Kani **expects** (the *oracle*:
`// kani-verify-fail` / `// kani-check-fail` directives and `expected` files →
`fail`, otherwise `success`), runs trust-mc on the same file, parses trust-mc's
`VERIFICATION:- …` line plus its `[AY:…]` soundness markers, and classifies the
comparison:

| Class | Meaning |
|---|---|
| `parity` | verdict matches AND (if success) a **genuine** proof — zero soundness fallback. The only class that counts as real domination. |
| `unsupported` | trust-mc hit an unsupported construct / codegen panic and conservatively reported failure. The clearest **trust-mc codegen-gap** signal. |
| `false_positive` | oracle=success, trust-mc=fail via a real solver disagreement (no unsupported marker). Conservative, but a parity miss. |
| `missed_bug` | oracle=fail, trust-mc=success. **Soundness-critical** — trust-mc proved safe where Kani finds a bug. |
| `unsound_pass` | verdict matched, but the success was reached via a sound over-approximation / fallback — not a real proof. |
| `unknown` / `error` / `timeout` | indeterminate verdict / tool error / watchdog kill. |
| `crash` | the verifier (or its compiler subprocess) died on a signal (SIGABRT, …) — a hard trust-mc defect, kept out of the generic `error` bucket. |
| `build_unavailable` | a cargo-project test whose dependencies cannot be built in this environment (registry/network) — environmental, not a verifier defect. |
| `skipped` | excluded from the run (e.g. by `--limit`); recorded in the denominator. |

Two lanes feed the classifier:

* **single-file** — the default: `trust-mc-driver <file.rs>` with the header
  `// kani-flags:`. If the test's Kani `expected` file is *diagnostic-only*
  (no verdict marker) and trust-mc emits no verdict but its output contains
  every expected line (Kani compiletest `contains_lines` semantics, including
  `\`-joined consecutive blocks), that is `parity` — Kani's own pass criterion
  for error-message tests.
* **cargo** — any test directory owned by a `Cargo.toml` becomes one unit per
  Kani `expected` / `*.expected` file (mirroring Kani's `cargo-kani` mode):
  the driver runs in its `cargo trust-mc` identity inside the package,
  `--harness <stem>` unless the file is the package-wide `expected`, and the
  expected file is the primary oracle (soundness discipline retained: a
  fallback-marked SUCCESS is still `unsound_pass`, never `parity`).

## Layered denominator

`--scope` selects which Kani suites count:

* **`verification`** (primary parity number) — `expected`, `kani`, `slow`,
  `smack`, `prusti`, `std-checks`.
* **`benchmark`** — `perf`.
* **`diagnostic`** — `ui`, `coverage`, `cargo-*`, `script-based-pre`, `llbc`, …
* **`full`** — everything except the explicitly-excluded lanes (`kani-fixme`,
  `remote-target-lists`).

The burndown reports both the **verification verdict parity** (primary) and the
**full-corpus parity** (outer).

## Standalone by design

This crate is a **standalone `stable`-Rust CLI** — its own workspace, its own
`Cargo.lock`, `rust-toolchain.toml = stable`. It is deliberately **not** a member
of the trust-mc workspace, so **building it needs no nightly, no `rustc-dev` /
`rust-src`, and no ay/trust-ir git-dep resolution** — it only pulls plain
crates.io deps (`clap`, `serde`, `walkdir`, …). It drives the trust-mc verifier
as a *subprocess*; the verifier still has to be built separately (that build,
being a rustc driver, is the one that needs the heavy toolchain).

```bash
# Build the tool (stable Rust, ~5s, zero rustc dep):
cd tools/kani-domination && cargo build      #  binary: ./target/debug/kani-domination
#   (or: cargo install --path .  -> `kani-domination` on PATH)
```

## Usage

```bash
# 0. build the verifier ONCE (this — not the tool — needs the trust-mc toolchain):
#    (from repo root)  cargo build-dev

# 1. fetch Kani's source at the pinned rev
kani-domination clone

# 2. see the corpus denominators (no run)
kani-domination inventory --scope full

# 3. run trust-mc over the verification suites (resumable; streams JSONL)
kani-domination run --scope verification --timeout 15 --jobs 3
#    smoke first:  ... run --suite kani --limit 10 --timeout 20

# 4. burndown report + append a row to the committed trend ledger
kani-domination burndown <repo>/target/kani-domination/reports/results-verification.jsonl

# 5. triage: group the non-parity harnesses by normalized root cause (fix next)
kani-domination triage <repo>/target/kani-domination/reports/results-verification.jsonl
#    ... triage --only encoding_gap   # drill into one class
```

### Native harness surface (R2 re-key lane)

`run --surface native` mechanically **re-keys** each expressible legacy
`#[kani::proof]` unit to the native `#[kani::harness]` spelling before
compilation — top-of-body `let x: T = kani::any();` bindings hoist into
parameters, and the `kani::` prefix drops from `any()`/`assume()` (verdict
identity holds by construction: `#[kani::harness]` expands to the same
`#[kanitool::proof]` marker with an equivalent preamble). The re-keyer is
**fail-closed**: anything outside the certain fragment (non-binding `any()`,
`any()` under a loop/nested block, `kani::any_where`/other APIs, generics,
contracts, cargo units, …) runs legacy, and every unit records its provenance
(`rekey:native` / `rekey:legacy(<reason>)`) in its result row; the ledger row
gains additive `surface` + `rekey` keys. The default `--surface legacy` is
byte-identical to runs before the flag existed.

```bash
# planning inventory only (no verification; needs only the Kani checkout):
kani-domination rekey-dry-run --scope verification

# a native-surface measurement (results default to results-<scope>-native.jsonl):
kani-domination run --scope verification --surface native --timeout 15
```

### Backend / reproducibility

trust-mc is AY-only. The CHC path (loops/recursion) runs in-process via the
pinned `ay-chc` portfolio; the SMT/BMC path resolves an `ay` binary
(`$AY_BIN` → sibling `../ay/target/release/ay` → `PATH`). The run records the
full **authority tuple** — trust-mc `HEAD`, the `ay` pin from `Cargo.toml`, the
`ay` binary version actually used (with an `ay_rev_matches_pin` flag), and the
Kani rev — in every results file and ledger row, per the project's
replacement-proof discipline.

`--cbmc-args …` (CBMC-only solver tuning) is stripped by default since the AY
backend does not consume it; pass `--keep-cbmc-args` to forward it verbatim.

## Layout

| File | Role |
|---|---|
| `src/suites.rs` | the Kani suite → scope registry (the layered denominator). |
| `src/discover.rs` | entry-file discovery + the Kani verdict oracle. |
| `src/runner.rs` | the parallel run + verdict/marker parse + classification. |
| `src/score.rs` | layered burndown aggregation + the trend ledger. |
| `src/clone.rs` / `src/env.rs` | Kani fetch + environment/provenance discovery. |
| `burndown-ledger.jsonl` | append-only burndown trend, written locally (one row/run). |

The Kani checkout, per-test build dirs and per-run JSONL reports live under
`target/kani-domination/` (gitignored); only the ledger accumulates across runs.
