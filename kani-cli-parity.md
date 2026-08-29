# Kani CLI Parity

## Status

trust-mc is a near-complete drop-in for the `kani-driver` CLI. Every user-facing Kani verification flag is present with matching names and semantics — harness selection (`--harness`/`--exact`/`--unwind`/`--default-unwind`), `--output-format`, `--concrete-playback`, `--coverage`, all Memory-Checks toggles, `--jobs`, `--tests`, `--target-dir`, `--randomize-layout`, `--harness-timeout`, contracts/stubbing (which are `-Z` features in both, fully mirrored), and the `list`/`autoharness`/`playback`/`verify-std` subcommands with identical arg structs. The core architectural difference (AY instead of CBMC) is handled by **keeping** the CBMC-era flags as compatibility shims so existing Kani scripts still parse: `--solver`, `--cbmc-args`, `--synthesize-loop-contracts`, `--no-slice-formula`, and `--run-sanity-checks` parse and warn+ignore, while `--gen-c`, `--print-llbc`, and `--write-json-symtab` parse and hard-error with friendly messages. The only true omissions are the Lean backend (`-Z lean` / `--print-llbc` functionality) and the `GenC` `UnstableFeature` — both intentional, since those backends were removed. On top of parity, trust-mc adds a large AY/CHC tuning surface (`--backend`, `--ay-solver`/`--smt-solver`, the `--ay-chc*` family, `--export-smtlib`, `--sarif`, `--tool-timeout`, `--config-free`, `--trust-vc-bundle`, `--proof-summary-json`, `--version-authority`, and top-level `--message-format`/`--harnesses`).

## Flag-by-flag audit

| Flag | Kani | trust-mc | Status | Note |
|------|:----:|:--------:|--------|------|
| `--harness` / `--harnesses` (filter) | yes | yes | parity | Both: `--harness` repeatable filter (`num_args(1)`, accumulated). Same semantics. |
| `--exact` | yes | yes | parity | Both require `--harnesses`; exact fully-qualified name match. |
| `--unwind` | yes | yes | parity | Both require `--harnesses`. Kani doc says "in CBMC"; trust-mc says "for bounded verification" but same flag/behavior. |
| `--default-unwind` | yes | yes | parity | Both `Option<u32>`. Kani: "in CBMC"; trust-mc: bounded verification default. |
| `--output-format` | yes | yes | parity | Both: `regular`\|`terse`\|`old`, default `regular`. trust-mc `old` = raw AY passthrough. |
| `--concrete-playback` | yes | yes | parity | Both: `print`\|`inplace`, gated by `-Z concrete-playback`, conflicts with `--quiet`(print)/`--output-format=old`/multi-threaded `--jobs`. Wired to AY models (see playback). |
| `--coverage` | yes | yes | parity | Both gated by `-Z source-coverage`. trust-mc implements it over AY SAT reachability checks (see coverage). |
| `--solver` | yes | yes | renamed | Kani: real CBMC solver selection (CaDiCaL/Kissat/`bin=...`). trust-mc: kept as hidden no-op compatibility flag (parses same value grammar, warns + ignores). AY solver selection is via `--ay-solver`/`--smt-solver` instead. |
| `--ay-solver` / `--smt-solver` | no | yes | extra | trust-mc-only: selects the AY SMT solver (`auto`/`ay`/`direct`). `--smt-solver` is a visible alias. This is the functional replacement for Kani's `--solver`. |
| `--backend` | no | yes | extra | trust-mc-only: `auto`\|`ay` backend selection (both resolve to AY today). |
| `--ay-chc` and CHC family (`--ay-chc-engine`, `--ay-chc-track`, `--ay-chc-step`, `--ay-chc-auto-invariants`, `--ay-chc-proof-core`, `--ay-chc-int-lift`, `--ay-chc-bounded-unroll`, `--ay-chc-transform`/`-transforms`, `--ay-chc-skip-verify`, `--ay-chc-no-retry`, `--ay-chc-debug`, `--ay-wide-mem`/`--wide-mem`, `--ay-logic`, `--ay-emit-bmc`, `--ay-panic-unwind`, `--export-smtlib`, `--export-chc-comp`) | no | yes | extra | trust-mc-only AY/CHC tuning surface. Most CHC sub-options validate that `--ay-chc` is set. |
| `--cbmc-args` | yes | yes | renamed | Kani: variadic passthrough to CBMC (gated by `-Z unstable-options`), the load-bearing escape hatch. trust-mc: accepted as hidden no-op (`num_args(0..)`+`allow_hyphen`), discarded with a warning since there is no CBMC backend. |
| `--gen-c` | yes | yes | renamed | Kani: generates C goto-equivalent (`-Z gen-c`). trust-mc: hidden flag that errors with a friendly "no C backend" message (exit 2). Accepted for drop-in CLIs but unsupported. |
| `--print-llbc` | yes | yes | renamed | Kani: Lean-backend LLBC dump (`-Z lean`). trust-mc dropped the Lean backend: hidden flag, errors with friendly message. `-Z lean` feature also removed from trust-mc. |
| `--synthesize-loop-contracts` | yes | yes | renamed | Kani: CBMC loop-contract synthesis. trust-mc: hidden no-op (warns); AY uses PDR invariant synthesis instead. |
| `--no-slice-formula` / `--run-sanity-checks` / `--write-json-symtab` | yes | yes | renamed | CBMC-only debug flags. trust-mc keeps them hidden: `--no-slice-formula` and `--run-sanity-checks` warn+ignore; `--write-json-symtab` errors as obsolete. Parse-compatible for Kani scripts. |
| `--c-lib` | yes | yes | parity | Both hidden, `num_args(1..)`, gated by `-Z c-ffi`. trust-mc retains the arg (C-FFI feature present in `UnstableFeature` set). |
| `--extra-pointer-checks` | yes | yes | parity | Both gated by `-Z unstable-options`. |
| `--no-default-checks` / `--no-memory-safety-checks` / `--no-overflow-checks` / `--no-undefined-function-checks` / `--no-unwinding-checks` | yes | yes | parity | Identical `CheckArgs` "Memory Checks" group in both (`solver.rs` `CheckArgs` mirrors Kani `common.rs` `CheckArgs`). |
| `--no-assertion-reach-checks` | yes | yes | parity | Identical in both. |
| `--no-assert-contracts` | yes | yes | parity | Both gated by `-Z function-contracts`. |
| `--prove-safety-only` | yes | yes | parity | Both gated by `-Z unstable-options`. |
| `--fail-fast` | yes | yes | parity | Identical. |
| `--force-build` | yes | yes | parity | Identical. |
| `--jobs` / `-j` | yes | yes | parity | Both `Option<Option<usize>>` with `NumThreads` semantics; both enforce `--output-format=terse` when multithreading. |
| `--keep-temps` | yes | yes | parity | Identical. |
| `--only-codegen` | yes | yes | parity | Identical. |
| `--no-codegen` | yes | yes | parity | Both gated by `-Z unstable-options`. |
| `--output-into-files` | yes | yes | parity | Both gated by `-Z unstable-options`. |
| `--randomize-layout` | yes | yes | parity | Both `Option<Option<u64>>`; both print the layout-seed reminder when combined with concrete playback. |
| `--tests` | yes | yes | parity | Identical. |
| `--target-dir` | yes | yes | parity | Identical, with same is-a-directory validation. |
| `--ignore-global-asm` | yes | yes | parity | Both gated by `-Z unstable-options` (Kani arg string `ignore-asm` vs trust-mc `ignore-global-asm` in the error text, flag name identical). |
| `--harness-timeout` | yes | yes | parity | Both `Timeout` type with s/m/h suffix, gated by `-Z unstable-options`. |
| `--no-restrict-vtable` / `--restrict-vtable` | yes | yes | parity | Both present; `--restrict-vtable` hidden+obsolete (errors), `--no-restrict-vtable` gated by `-Z restrict-vtable`. |
| `--tool-timeout` | no | yes | extra | trust-mc-only: timeout for tool subprocesses (compiler/linker), default 10m. |
| `--config-free` | no | yes | extra | trust-mc-only: run only bare `#[kani::proof]` harnesses with no per-harness config (default Trust-compile verification set). |
| `--trust-vc-bundle` | no | yes | extra | trust-mc-only: verify a `trust_vc` `MergeBundle` JSON directly without compiling a crate; conflicts with positional input. |
| `--sarif` | no | yes | extra | trust-mc-only: SARIF v2.1.0 results output; conflicts with `--output-format=old` and `--only-codegen`. |
| `--proof-summary-json` | no | yes | extra | trust-mc-only: informational proof-summary JSON pointer artifact. |
| `--fail-on-unvalidated-success` | no | yes | extra | trust-mc-only: exit failure if a harness succeeds without validation. |
| `--allow-vacuous` | no | yes | extra | trust-mc-only: relax the vacuity gate (V4) — treat a harness whose every non-cover check is provably UNREACHABLE (contradictory assumptions) as a pass instead of a FAILURE (`verification.rs:93`). |
| `--strict-vacuity` | no | yes | extra | trust-mc-only: escalate vacuity warnings to hard failures (V5) — a `kani::cover(...)` proved unsatisfiable becomes a failure (`verification.rs:99`). |
| `--conformance-harness` | no | yes | extra | trust-mc-only: mark a harness as a CONFORMANCE harness (V5) that must reach ≥1 satisfied `kani::cover(...)`; repeatable, matched on pretty name (`verification.rs:107`). |
| `--version-authority` | no | yes | extra | trust-mc-only top-level flag: prints trust-mc SHA/dirty state plus the declared and linked AY revisions and the lane relating them (`matched` for a git-resolved pin, `contains-pin` for an accepted `[patch]`); fails closed on a malformed inventory, a dirty linked build, a linked build that does not satisfy its lane, or a `[patch]` Cargo silently declined. |
| `--message-format` | no | yes | extra | trust-mc adds a top-level `--message-format` (`human`\|`json`) in `CommonArgs`; in Kani this exists only on the playback subcommand, not the main verification `CommonArgs`. |
| `--harnesses` (top-level list shortcut) | no | yes | extra | trust-mc adds a top-level `--harnesses` bool shortcut for listing (distinct from the `--harness` filter); validated by `validate_harnesses_shortcut`. |
| `list` / `autoharness` / `playback` / `verify-std` subcommands | yes | yes | parity | All four subcommands present with matching arg structs. autoharness: `--include-pattern`/`--exclude-pattern`/`--list`/`--format`, `-Z autoharness`, same `-Z concrete-playback` conflict. list: `--format pretty`\|`markdown`\|`json` + `--std`. verify-std: `STD_PATH` + `-Z unstable-options`. |
| playback subcommand args (`--only-codegen`, `--message-format`, `test_args`, `-p`) | yes | yes | parity | `PlaybackArgs` identical: `-Z concrete-playback` gate, `--only-codegen`, `--message-format human`\|`json`, trailing `--` test args, cargo passthrough. |
| Cargo target args | yes | yes | parity | trust-mc is a **superset**: Kani `CargoTargetArgs` = `bin`/`bins`/`lib` only; trust-mc adds `all-targets`/`bench`/`benches`/`example`/`examples`/`test`. Standalone validation rejects all of them as cargo-only (parity in rejection). |
| Cargo common args (`--all-features`/`--no-default-features`/`--features`/`-F`/`--manifest-path`/`--package`/`-p`/`--exclude`/`--workspace`) | yes | yes | parity | Byte-for-byte identical `CargoCommonArgs`. |
| Common args (`--debug`/`--quiet`/`-q`/`--verbose`/`-v`/`--enable-unstable`(obsolete)/`--dry-run`(obsolete)/`-Z`\|`--unstable`) | yes | yes | parity | Identical `CommonArgs` incl. obsolete `--enable-unstable`/`--dry-run` error handling; `-Z` feature set near-identical. |
| `-Z function-contracts` / `-Z stubbing` / `-Z loop-contracts` (contracts & stubbing) | yes | yes | parity | Contracts/stubbing are `-Z` features, not separate driver flags, in **both**. trust-mc `UnstableFeature` enum includes `FunctionContracts`, `Stubbing`, `LoopContracts`; `is_stubbing_enabled()`/`is_function_contracts_enabled()` mirror Kani. No `--no-assert-contracts` divergence. |
| `-Z lean` (Lean backend) | yes | **no** | **missing** | Kani has `-Z lean` + `--print-llbc` + Lean/cbmc conflict checks. trust-mc removed the Lean backend entirely; `--print-llbc` errors with a friendly message and the Lean `UnstableFeature` is gone. Intentional omission, not a regression. |
| `-Z gen-c` (`UnstableFeature`) | yes | **inert** | **partial** | trust-mc **retains** the `GenC` `UnstableFeature` variant (`trust-mc-metadata/src/unstable.rs:93`) but it is unwired — declared, never matched, no C backend behind it. So `-Z gen-c` parses as a recognized feature but does nothing, and the `--gen-c` flag hard-errors (no C backend). Consistent with dropping CBMC. |

## Gaps to close for drop-in parity

These are the only items where trust-mc does **not** match Kani's surface. Both are intentional backend removals rather than regressions, but they are tracked here as the actionable parity deltas.

### Missing flags (2)

1. **`-Z lean` (Lean backend) + `--print-llbc` functionality** — Kani exposes `-Z lean`, the `--print-llbc` LLBC dump, and Lean/CBMC conflict checks. trust-mc removed the Lean backend entirely: the `Lean` `UnstableFeature` is gone and `--print-llbc` is a hidden flag that hard-errors with a friendly message. To close: either re-introduce a Lean backend (out of scope while AY is the sole backend) or document the removal so consumers do not rely on `-Z lean` being accepted. **Recommended action:** keep removed; document as unsupported.
2. **`-Z gen-c` (`UnstableFeature`) + `--gen-c` functionality** — trust-mc **retains** the `GenC` `UnstableFeature` variant (`trust-mc-metadata/src/unstable.rs:93`) but leaves it unwired (declared, never matched, no C backend), so `-Z gen-c` parses inertly while `--gen-c` hard-errors. To make this a true backend would require a C/goto backend, which contradicts dropping CBMC. **Recommended action:** keep the hard-error path (correct drop-in behavior); optionally drop the inert `GenC` variant so the feature set no longer advertises a capability it does not have.

### Questionable "renamed" flags to validate

These flags parse identically to Kani but have substituted behavior. They are not gaps in the parse surface, but consumers relying on the *effect* (not just acceptance) of the flag will see different behavior, so they warrant explicit validation/documentation:

- **`--solver`** — accepted with Kani's full value grammar (CaDiCaL/Kissat/`bin=...`) but is a hidden no-op that warns and ignores. Real solver selection is `--ay-solver`/`--smt-solver`. Confirm any Kani scripts that depend on `--solver` semantics are migrated.
- **`--cbmc-args`** — variadic passthrough is accepted (`num_args(0..)`+`allow_hyphen`) but discarded with a warning; there is no CBMC backend to receive them. This is Kani's load-bearing escape hatch, so any script that smuggled CBMC options through it will silently lose them.
- **`--synthesize-loop-contracts`** — hidden no-op (warns); AY uses PDR invariant synthesis instead. Effect differs even though the flag parses.
- **`--no-slice-formula` / `--run-sanity-checks`** — CBMC-only debug flags; warn+ignore.
- **`--gen-c` / `--print-llbc` / `--write-json-symtab`** — parse but hard-error with friendly messages (the two backend removals plus the obsolete symtab dump).

## Carried-from-Kani, needs verification

Two Kani features were carried over rather than reimplemented from scratch. Both are **genuinely functional under AY, not stubbed** — the substitution is the data source (AY model output instead of CBMC traces), while the downstream Kani machinery is reused intact. Their current wiring status:

### Concrete playback — **wired**

Functional and genuinely wired to AY counterexample models, not stubbed. Flow:

1. `call_ay.rs:481` parses AY's `get-value` output on a `Failure` verdict via `ay_parse::trace::parse_kani_any_trace()`, which extracts `(ay_any_N <value>)` pairs from the SMT model and converts them to `TraceItem` assignments.
2. `parse_violation_properties` / `parse_cover_properties` attach that trace to each satisfied `Property` (`violation.rs:305,546`).
3. `harness_runner.rs:562` calls `gen_and_add_concrete_playback()` after every harness.
4. `concrete_playback/test_generator.rs:39` runs `extract_harness_values()` over `verification_result.results` (the `Property` traces) via the `concrete_vals_extractor` crate, then formats and either prints (`Print`) or injects in-place (`InPlace`) a Rust unit test.
5. The `playback` subcommand (`concrete_playback/playback.rs`) compiles and runs the generated tests with the trust-mc compiler.

Gating, conflicts (`--quiet`+print, `--output-format=old`, multi-thread `--jobs`), and `-Z concrete-playback` all match Kani. The only behavioral substitution is the value source: AY `get-value` model output replaces CBMC trace JSON, but the extractor/formatter/source-injection machinery is the real Kani pipeline carried over intact.

### Coverage — **working**

Works under AY, not dead or stubbed. The `--coverage` flag is gated by `-Z source-coverage` (`validation.rs:269`), identical to Kani. Coverage is implemented over AY rather than CBMC's coverage instrumentation:

- The compiler emits `ay_coverage_*` boolean predicates per code region.
- `call_ay.rs:543/625` builds `CoverageResults` either from per-region AY SAT reachability checks (`build_coverage_results_from_sat_checks`, querying `check_cover_satisfiability`) on the UNSAT/success path, or by parsing `ay_coverage_*` booleans from `get-value` output (`parse_coverage_results`) on the SAT path.
- Source locations come from the VC artifact location map (#1164).
- `main.rs:700-716` then writes `kanicov_<stamp>` metadata (`kanimap` source list) and per-harness `_kaniraw.json` results via `coverage/cov_session.rs`, mirroring Kani's `kanicov` layout for the downstream report tool.
- `cov_results.rs` models `CoverageRegion`/`CoverageCheck`/`CheckStatus` and a `Display` impl.

**Caveat:** `cov_session.rs` notes coverage **mappings** are not yet persisted in metadata (a TODO carried from Kani), and granularity depends on the compiler emitting `ay_coverage_*` predicates — but the end-to-end path (encode → AY-decide → serialize → save) is live.
