# Migrating from Kani to trust-mc

Author: Andrew Yates <andrewyates.name@gmail.com>

## TL;DR

trust-mc is Kani's codebase with CBMC replaced by AY. Your proof harnesses and
source annotations stay the same: keep using `#[kani::proof]`, `kani::any()`,
`kani::assume()`, and the rest of the `kani::`-prefixed API.

The main workflow change is tooling: use `targo trust-mc` instead of `cargo kani`.
If you already have a working Kani crate, start by swapping the command, then
adjust how you read trust-mc verdicts and `UNKNOWN` diagnostics.

## Quick Comparison

<!-- dscan:allow(volatile_numbers) -->
| Aspect | Kani | trust-mc |
|---|---|---|
| CLI command | `cargo kani` | `targo trust-mc` |
| Installer | Kani installer / release flow | Build from source today; see [build-from-source.md](./build-from-source.md) |
| Default solver backend | CBMC | AY (`--backend=auto` and `--backend=ay` both resolve to AY) |
| Supported proof patterns | Bounded proofs with unwind control | Same bounded proofs, plus CHC proofs for unbounded loops with `--ay-chc` |
| Output format | Human-readable verification report | `--output-format=regular|terse|old` plus machine-readable `[AY:*]` tag lines |
| Counterexample format | Failing property report / backend trace | `CTREX` verdict, plus optional [concrete playback](./reference/experimental/concrete-playback.md) test generation |
| BigInt / HashMap support | Poor fit for CBMC-heavy proofs | BigInt verification and symbolic-key `HashMap` verification are first-class goals |
| Performance envelope | Some large proofs OOM or time out under CBMC | dterm case study shows substantially less memory on proofs CBMC OOMs on (magnitude not re-measured) |

## Invocation Translation

The safest migration rule is: keep the harness, swap the command, then only
reuse flags that exist in `targo trust-mc`.

| Kani usage | trust-mc usage | Notes |
|---|---|---|
| `cargo kani --harness foo` | `targo trust-mc --harness foo` | Same harness filter flag. |
| `cargo kani --harnesses` | `targo trust-mc --harnesses` or `targo trust-mc list` | `--harnesses` is the Kani-compatible pretty-list shortcut. Use `list` for JSON or Markdown output. See [reference/list.md](./reference/list.md). |
| `cargo kani --harness foo --unwind 8` | `targo trust-mc --harness foo --unwind 8` | Same per-harness unwind override. |
| `cargo kani --default-unwind 8` | `targo trust-mc --default-unwind 8` | Same global unwind default. |
| `cargo kani -Z unstable-options --harness-timeout 60s` | `targo trust-mc -Z unstable-options --harness-timeout 60s` | Same timeout spelling; still experimental. |
| `cargo kani --output-format terse` | `targo trust-mc --output-format terse` | trust-mc supports `regular`, `terse`, and `old`. |
| `cargo kani --tests` | `targo trust-mc --tests` | Same intent: compile with `cfg(test)` and make `dev-dependencies` available in cargo mode. |
| `cargo kani -Z source-coverage --coverage --harness foo` | `targo trust-mc -Z source-coverage --coverage --harness foo` | Same coverage flag, still gated by `-Z source-coverage`. See [coverage.md](./reference/experimental/coverage.md). |
| `cargo kani -Z concrete-playback --concrete-playback=print` | `targo trust-mc -Z concrete-playback --concrete-playback=print` | Same playback flag; trust-mc also has `targo trust-mc playback ...`. |

### Not Yet Supported

- `cargo kani --visualize`: there is no `--visualize` flag in
  `trust-mc-driver/src/args/verification.rs`, `trust-mc-driver/src/args/cargo.rs`, or
  `trust-mc-driver/src/args/mod.rs` in this tree. No backlog item for a `targo trust-mc`
  equivalent was found in the checked-in docs or designs.

## What's The Same

- Harnesses still use `#[kani::proof]`.
- Nondeterministic inputs still use `kani::any()`.
- Assumptions still use `kani::assume()`.
- Coverage probes still use `kani::cover!`.
- Per-harness unwind annotations still use `#[kani::unwind(N)]`.
- Panic expectations still use `#[kani::should_panic]`.
- Existing `#[cfg(kani)]` and `#[cfg_attr(kani, ...)]` source patterns still apply.
- The current macro and API prefix is still `kani::`, as noted in the
  repository [README.md](../../README.md).

## What's Different

- trust-mc has one backend: AY. CBMC has been fully removed from the active
  verification path.
- For unbounded proofs, `--ay-chc` uses the native `ay-chc` adaptive
  twelve-engine portfolio: PDR/IC3, BMC, k-induction, PDKind, TPA, TRL,
  Decomposition, LAWI, IMC, DAR, CEGAR, and IC3 variants.
- trust-mc names the top-level outcomes you will care about as `PROOF`,
  `UNKNOWN`, `CTREX`, `ERROR`, and `BMC_SAFE`.

| Verdict | Meaning |
|---|---|
| `PROOF` | The harness was proved safe. |
| `UNKNOWN` | AY could not finish the proof or could not classify the query conclusively. |
| `CTREX` | trust-mc found a counterexample or a failing verification result. |
| `ERROR` | Compilation, codegen, or tool execution failed before trust-mc could return a proof verdict. |
| `BMC_SAFE` | A bounded-only success bucket used in report/expectation workflows: explicit BMC completed without finding a counterexample, but this is weaker than an unbounded proof. |

- trust-mc adds capabilities that Kani users usually hit CBMC limits on:
  `BigInt`, `HashMap` with symbolic keys, and CHC-based reasoning for loops that
  do not need `#[kani::unwind]`.
- On `UNKNOWN`, trust-mc emits an additional diagnostic line of the form
  `[AY:UNKNOWN-CATEGORY] ...` so you can triage the reason quickly.

## Decoding `[AY:UNKNOWN-CATEGORY]` Tag Lines

trust-mc currently groups `UNKNOWN` results into five high-level buckets. The short
version is below; see [troubleshooting.md](./troubleshooting.md) for the full
remediation table.

- `≥2 Array-sorted state parameters`: the CHC predicate shape hits the current
  array-parameter invariant synthesis limit. Track
  [#4259](https://github.com/alabsystems/trust-mc/issues/4259).
- `PDR invariant synthesis timeout`: the solver exhausted its budget without
  finding an invariant.
- `solver error (engine=X)`: the selected portfolio engines did not finish
  cleanly.
- `no error rule encoded (see #4284)`: the query has no encoded error rule, so
  the proof is degenerate or vacuous. Track
  [#4284](https://github.com/alabsystems/trust-mc/issues/4284).
- `uncategorized`: the failure did not match one of the known buckets.

## Known Gaps Where trust-mc Does Not Yet Match Kani

Compiletest regression triage is tracked under
[#4265](https://github.com/alabsystems/trust-mc/issues/4265). The best
checked-in per-harness snapshot lives in
[`reports/compiletest-per-harness-latest-trust-mc.json`](../../reports/compiletest-per-harness-latest-trust-mc.json).
It was generated on `2026-04-20` from a merged TL71 packet and predates the
current AY dependency revision in `Cargo.toml`, so use it as a stale baseline
until a fresh replacement-proof authority-tuple run replaces it. That tuple
must name the trust-mc commit, current `Cargo.toml` AY pin, report tree
fingerprint, harness count, proof inventory SHA, and non-proof closure SHA.

- Snapshot counts are intentionally not duplicated here (they go stale); read
  them from the JSON snapshot above, which is the source of truth for that run.
- The remaining parity gaps are concentrated in exactly the areas surfaced by
  that report: unsupported constructs, `UNKNOWN` solver buckets, and
  compile/codegen `ERROR` cases.

## Migrating A Project Step-By-Step

1. Build trust-mc from source. Start with
   [build-from-source.md](./build-from-source.md).
2. Run `targo trust-mc` in the crate that already works under Kani.
3. Read the verdict first, then read any `[AY:UNKNOWN-CATEGORY] ...` tag line
   if the result is `UNKNOWN`.
4. File trust-mc-specific issues at
   <https://github.com/alabsystems/trust-mc/issues>.

## Practical Migration Notes

- Start with the harnesses that already pass under Kani without elaborate
  stubbing. That gives you a clean baseline for reading trust-mc output.
- Keep your harness source unchanged unless trust-mc shows a real gap. Most of the
  early migration work is command-line and diagnostics, not annotation churn.
- If a proof depends on `dev-dependencies` inside `src/`, keep the Kani-style
  workaround: use `#[cfg(all(kani, test))]` and run `targo trust-mc --tests`. See
  [usage.md](./usage.md).
- For bounded debugging, `--unwind` and `--default-unwind` still work the way a
  Kani user would expect.
- For unbounded loops, try `--ay-chc` before assuming you need larger unwind
  bounds.
- If you want replayable failing inputs, keep using concrete playback:
  `-Z concrete-playback --concrete-playback=print` or `inplace`.
- If you need a list of harnesses before migrating CI, use `targo trust-mc list`
  and switch to `--format json` when you want machine-readable output.

## Reading trust-mc Output

When migrating from Kani, focus on three layers of output:

1. The top-level verdict: `PROOF`, `UNKNOWN`, `CTREX`, or `ERROR`.
2. The tag lines: `[AY:UNKNOWN-CATEGORY]`, `[AY:CTREX_CAT:...]`,
   `[AY:PROOF_QUALIFIERS:...]`, and similar markers.
3. Optional follow-on tools: coverage, concrete playback, or `targo trust-mc list`.

That structure is different from CBMC-centric debugging, but the payoff is that
trust-mc usually tells you faster whether you are looking at a real counterexample,
an inconclusive solver bucket, or a toolchain problem.

## Further Reading

- [troubleshooting.md](./troubleshooting.md)
- [limitations.md](./limitations.md)
- [rust-feature-support.md](./rust-feature-support.md)
- [faq.md](./faq.md)
