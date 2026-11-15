<!--
Copyright 2026 Andrew Yates
SPDX-License-Identifier: Apache-2.0 OR MIT
-->

# kani-spec: the generated Kani functional spec

`tools/kani-spec` turns a pinned upstream Kani revision into `spec/kani/<rev>/`,
the denominator every Kani-parity number must use (plan of record
`docs/kani-spec-engine-plan-2026-09-10.md`, gate G2, milestone M1). Nothing is
generated from trust-mc's vendored `tests/` copies, which have drifted from
upstream.

```sh
tools/kani-spec/kani-spec fetch [--seed <local kani clone>]   # pinned checkouts into the cache
tools/kani-spec/kani-spec generate                             # write spec/kani/<rev>/
tools/kani-spec/kani-spec --check                              # regenerate to a temp dir, byte-compare
tools/kani-spec/kani-spec counts                               # per-suite table from the manifest
tools/kani-spec/kani-spec radius                               # computed overlay blast radii
(cd tools/kani-spec/tests && python3.12 -m unittest)           # unit tests (stdlib only)
```

Python 3.11+ (`tomllib`), no third-party packages; the wrapper resolves the
interpreter through `scripts/ay_python.sh`.

## Inputs

* `tools/kani-spec/pins.toml`: each rev's full sha, its `rust-toolchain.toml`
  nightly, and the gitlink of every test-bearing submodule
  (`tests/perf/s2n-quic`). Generation refuses a checkout whose HEAD, channel or
  gitlink differs, or whose tree is not clean.
* Cache: `$KANI_SPEC_CACHE`, default `$HOME/Library/Caches/trust-mc/kani-spec/<rev>`,
  which sits outside every cargo workspace. `fetch` takes the commit from
  `--seed` clones first, then from upstream at `--depth 1`.
* `spec/kani/overlay.toml`: the only hand-edited file (see below).

## Collection (mirrors tools/compiletest at the pinned rev)

The suite/mode table is parsed from the rev's `scripts/kani-regression.sh`
`TESTS=( ... )` plus `kani-slow-tests.sh`, `kani-perf.sh` and
`kani-llbc-regression.sh`. The `--dry-run` configuration line is not a suite.

| Mode | Unit |
|---|---|
| kani, kani-fixme, expected, coverage-based, stub-tests | every `*.rs` not starting with `.`, `#` or `~`, recursing except `auxiliary/` |
| cargo-kani, cargo-kani-test, cargo-coverage | each `expected` or `*.expected` in a directory holding `Cargo.toml` |
| exec | each entry directly under the suite; `config.yml` is required |

* A path containing `fixme`, or else `ignore`, is collected but ignored
  upstream. The unit is kept with `ignored` set and class `fixme`.
* kani-fixme collects the whole kani tree but runs only basenames containing
  `fixme`, with the result inverted (`should_fail`). Only those are units; the
  rest are counted in the manifest's `excluded_from_units`.
* `scripts/kani-perf.sh` copies `tests/perf/overlays/<d>/*` into
  `tests/perf/<d>/`. The generator applies that copy virtually, and Kani CI
  initialises submodules, so the three s2n-quic crates are perf units.
* Header directives follow `header.rs`: a directive line starts with `//`
  (`#` outside `.rs`), directives stop at the first `fn` or `mod` line, and
  `kani-*-fail` matches only as a whole word.
* The expected file follows `runtest.rs`: expected mode uses `<test>.expected`
  or else the directory `expected` (for any file); coverage-based uses the
  directory `expected`; cargo modes use the unit file; exec uses
  `config.yml`'s `expected`.

## Outputs (`spec/kani/<rev>/`)

* `manifest.json`: kani_rev, kani_nightly, kani_version, generator_version,
  spec_version `kani@<sha>+spec.1`, and the suite table. Per suite it records
  sources, CI jobs, upstream collected count, units, ignored and excluded
  counts, classes and oracle kinds. It also holds totals, the non-compiletest
  CI steps (each anchored to its source file and sha256), the applied overlay
  corrections, and the sha256 of every other file.
* `clauses.json`: the 62-clause taxonomy, with lexical rules and unit counts.
* `units.jsonl`: one row per unit, sorted by id. A row holds id
  (`<suite>/<suite-relative path>`), suite, mode, path, the upstream test
  name, `sha256` over its sorted inputs, directives, cargo or exec details,
  and `ignored` / `should_fail`. Harnesses carry pretty name, kind,
  contract target, should_panic, unwind, solver, stubs, cfg predicates and
  `cfg_active`, `selected` (Kani's `--harness` matching) and `macro_template`.
  Rows end with clauses, classification plus reason, and tags.
* `oracles.jsonl`: one row per unit. Stage and expected exit (success,
  failure, exit code, or unchecked where compiletest ignores it); run verdict
  with its basis and completeness; per-harness verdicts with should_panic;
  checks as (property_class, description, status, location) and covers;
  summary counts; diagnostics; normalised `contains_lines` blocks (backslash
  joins, trimmed); the raw expected text; oracle kinds; overlay notes; and
  `effective`, the result a scorer reads. `effective.complete` is false when
  the verdict covers only some harnesses (one `VERIFICATION:- SUCCESSFUL` in a
  multi-harness file is not a whole-run SUCCESSFUL), and
  `effective.upstream_ignored` marks units upstream never runs, whose verdicts
  are stated, not observed. A kani-fixme unit whose `kani-*-fail` header makes
  compiletest panic before Kani runs (`upstream_outcome: props-parse-panic`)
  states no verdict and no exit status.

Every file is written with sorted keys and stable ordering, and nothing
depends on the checkout location, the clock or directory iteration order.

## Overlay

`spec/kani/overlay.toml` holds audited corrections. It is seeded from the
heuristics hard-coded in `tools/kani-domination/src/discover.rs` and the
`quarantine.rs` tables that `discover.rs` applies. Each entry names its
source, its audit, and a per-rev `blast_radius` (exact unit ids). Rule
entries are recomputed at generation, and generation fails if the set moved.
Upstream-derived oracle fields are never rewritten: a correction appears as a
note with its relation (`fills`, `agrees`, `stage` or
`overrides-ignored-unit`), and a conflict with a derived verdict on a unit
upstream runs is an error. `[[exemption]]` entries are the D1 sign-off list,
empty until signed.

## Known limits

* The harness scan is lexical: comments, strings, module and fn scopes,
  cfg predicates and crate roots. It does not expand macros, so
  `macro_rules!` harness templates are listed but not counted.
* The compared `Complete - N ... total` summaries measure the scan's
  accuracy. The remaining mismatches are autoharness function counts,
  macro templates, fail-fast runs and script-driven exec units.
* Classification and clauses are the audit prototype's lexical rules.
  Classes stay provisional until D1 exemptions are signed. Two rules keep a
  no-op flag from moving a verdict-bearing unit out of verdict-spec:
  `--output-format regular` is Kani's default, so it makes a unit cli-surface
  only when the unit's path names the output format; and `--bounds-check` /
  `--pointer-check` in cbmc-flags re-enable checks Kani already runs (see
  `kani-driver/src/call_cbmc.rs` `cbmc_check_flags`), so they do not make a
  unit cbmc-specific.
