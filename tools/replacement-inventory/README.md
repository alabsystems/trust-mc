<!--
Copyright 2026 Andrew Yates
SPDX-License-Identifier: Apache-2.0 OR MIT
-->

# replacement-inventory

These tools maintain and audit trust-mc's frozen public replacement corpus.
The corpus is historical authority (with the documented 2026-11-14 failure-oracle correction): current source is not allowed to shrink the
denominator merely because a harness was renamed, feature-gated, or disabled.

## Canonical artifacts

`generate_inventory.py` reads
`tools/replacement-inventory/public-corpus.json` and deterministically emits:

| Path | Rows | Purpose |
| --- | ---: | --- |
| `tests/trust-mc/replacement-harness-inventory.json` | 818 | Mixed public replacement denominator. |
| `tests/trust-mc/replacement-harness-inventory.proof.json` | 485 | Rows whose expected verdict is `PROOF`. |
| `tests/trust-mc/non-proof-closure.json` | 333 | Checked justifications for negative expectations. |

Each artifact contains a `row_sha256` over its canonical rows array. Generation
is sorted and byte-deterministic. `--check` regenerates in memory, compares the
committed bytes, writes nothing, and exits nonzero on drift.

The generator does not walk the current `tests/` tree. Source binding is a
separate fail-closed step:

```bash
source scripts/ay_python.sh
"$AY_PYTHON_BIN" scripts/replacement_harness_dispositions.py --check
```

That command validates
`tests/trust-mc/replacement-harness-dispositions.json`. Every historical row
must resolve to one exact active driver harness, one unambiguous qualified
alias, an enabled cargo feature, or a source-proved `#[cfg(disabled)]` harness.
Disabled rows remain in the denominator with zero execution and proof credit;
unknown or ambiguous changes are errors.

[The remaining source audit](remaining-oracle-corrections-2026-11-14.json)
binds sixteen corrected labels to the original fork sources, including the
renamed C string and union fixtures. Eleven safe programs require proofs;
five union bugs require Genuine counterexamples. The five initialized union
controls and all 818 harness identities remain. Old unsupported diagnostics
do not supply semantic counterexamples, and historical reports retain their
original labels and hashes.

Cargo rows additionally require a reachable conventional Rust module path and
default-enabled whole-file feature gates. Every owning package must have a
committed lockfile. The current active plan contains 720 direct rows and 66
Cargo rows. Each Cargo identity is fully qualified and unique within its
package; runtime execution adds `--locked --exact` and accepts one matching
driver selection marker, so dependency drift, a prefix, zero match, or multiple
match cannot receive credit.

## Inventory CLI

```text
generate_inventory.py [--corpus PATH] [--suite NAME ...]
                      [--output PATH] [--proof-output PATH]
                      [--non-proof-output PATH]
                      [--no-proof-subset] [--no-non-proof-closure] [--check]
```

Generate the three artifacts only after an intentional corpus change:

```bash
source scripts/ay_python.sh
"$AY_PYTHON_BIN" tools/replacement-inventory/generate_inventory.py
```

The normal CI/review operation is read-only:

```bash
"$AY_PYTHON_BIN" tools/replacement-inventory/generate_inventory.py --check
"$AY_PYTHON_BIN" scripts/generate_non_proof_closure.py --check
"$AY_PYTHON_BIN" scripts/replacement_harness_dispositions.py --check
```

## Public execution

The checked source-bound plan is the only supported route for running the
historical denominator:

```bash
AY_SOLVER=ay \
AY_EXPECTED_HARNESSES=818 \
./scripts/ay-compiletest.sh --replacement-public
```

The runner validates its exact runtime record set against the disposition
artifact before producing the schema-v2 aggregate report. At the current
source state, 786 rows execute and 32 cfg-disabled `PROOF` rows are emitted as
inactive-accounted `SKIP` records. Those 32 rows receive zero credit and remain outside the active replacement
bar; local disabling cannot move any other row outside the bar.

Before executing a row, the runner requires the exact driver binary to emit a
single valid `--version-authority` line for the current clean TrustMC commit and
linked AY authority. The report and run manifest record that binary's resolved
path and SHA-256. The strict proof command re-hashes and re-attests the same
binary, so a stale, dirty, or replaced driver fails closed.
It also requires a clean tree before and after the run and an unchanged
measurement fingerprint, preventing generated or modified Cargo locks from
being reported as clean evidence.

An attempted row that selects the wrong harness remains an `ERROR`/`FAIL`
record with `execution_state=identity_mismatch`; it receives no verdict or
proof credit. The runtime accounting distinguishes attempts, completed
executions and identity mismatches. Commands, actual exit codes and log paths
are written to the run manifest before final validation, with `finalized=false`
until the clean-input and accounting checks finish. A later refusal must not
discard the rest of a run; an unfinished manifest is diagnostic evidence only.

See `replacement-proof.md` for the authority tuple, proof extraction, strict
AY audit, exact digests, and activation plan.

## `replacement_progress.py`

`replacement_progress.py` is a triage/audit view over the frozen mixed
inventory and a fresh proof-summary or ay-compiletest report. It classifies:

- `PROOF` rows as proven only for a schema-v2 `PASS`/`PROOF`, complete
  execution, clean proof qualifier, trusted-proof marker, and zero soundness
  fallback;
- non-`PROOF` rows as closed only when the observed verdict matches the frozen
  expectation; and
- source-inactive `SKIP` rows as `INACTIVE`, never as proof progress.

```bash
source scripts/ay_python.sh
"$AY_PYTHON_BIN" tools/replacement-inventory/replacement_progress.py \
  --report reports/compiletest-per-harness-latest-trust-mc.json \
  --verbose

"$AY_PYTHON_BIN" tools/replacement-inventory/replacement_progress.py \
  --report reports/compiletest-per-harness-latest-trust-mc.json \
  --format json

"$AY_PYTHON_BIN" tools/replacement-inventory/replacement_progress.py \
  --report reports/compiletest-per-harness-latest-trust-mc.json \
  --require-complete
```

Without `--report`, the tool prints `MEASUREMENT MISSING` and exits nonzero.
`--require-complete` is green only if all 818 rows are measured, every proof row
is clean and fallback-free, every negative verdict matches, and no row is
missing. This progress tool does not by itself establish current-head or solver
authority; use the strict flow in `replacement-proof.md` for a replacement
claim.

## Cover-property accounting

The five frozen `tests/expected/cover/*/main.rs` rows also require every
original named cover outcome in [cover-property-oracles.json](cover-property-oracles.json).
It records original Git object IDs and SHA-256 values for each unchanged source
and expected-output file. The source-bound disposition authority includes this
artifact's hash. `cover-unreachable` has a PROOF safety oracle; its two
UNREACHABLE properties and one SATISFIED property are still mandatory. The
current split is 485 proof / 333 negative, with the same 818 identities and
786 active rows (453 proof / 333 negative).

The public runner records individual cover descriptions and statuses from the
driver's check blocks. Runner success, replacement progress and proof extraction
require an exact match, independent of order. Missing, extra, duplicate, malformed
or wrongly labelled properties refuse parity credit. Aggregate counts and
generic `cover property N` descriptions cannot identify the original properties.
The intentionally UNDETERMINED cover requires that exact outcome alongside its
checked unwinding counterexample; UNDETERMINED does not satisfy any other cover.
Older safety-only reports remain historical measurements and cannot supply this
new property evidence. No cover-solving implementation is changed by this rule.
