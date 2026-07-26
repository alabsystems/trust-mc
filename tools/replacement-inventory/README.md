<!--
Copyright 2026 Andrew Yates
SPDX-License-Identifier: Apache-2.0 OR MIT
-->

# replacement-inventory

Deterministic harness-inventory generator for the **trust-mc** model-checking
test corpus (ay / trust-mc).

`generate_inventory.py` reads the frozen public corpus
(`tools/replacement-inventory/public-corpus.json`) — one row per
`#[kani::proof]` harness across the included verification suites — classifies
each harness's expected verification disposition, and emits a frozen JSON
inventory, a PROOF-only subset, and the non-PROOF closure. (The corpus file is
the surveyed source of truth; the generator does not re-walk the `tests/`
directories at generation time.)

## Output

| Path | Contents |
| --- | --- |
| `tests/trust-mc/replacement-harness-inventory.json` | Full inventory — every harness across both suites. |
| `tests/trust-mc/replacement-harness-inventory.proof.json` | Subset whose rows all have `expected == "PROOF"`. |

Both files share an identical shape:

```jsonc
{
  "schema_version": 1,                 // int, always 1
  "suite": "tests/trust-mc",           // inventory home suite
  "denominator": <int>,                // == len(rows)
  "row_sha256": "<hex>",               // sha256 of the rows array
  "rows": [
    {
      "file":     "trust-mc/Foo/bar.rs",  // suite-relative POSIX path
      "harness":  "module::check_thing",  // fully-qualified harness name
      "expected": "PROOF",                // PROOF | CTREX | UNKNOWN | ERROR | BMC_SAFE
      "lane":     "tests/trust-mc"        // tests/<suite> the row came from
    }
  ]
}
```

### Determinism

- Files are visited in sorted order; rows are sorted by `(file, harness)`.
- `denominator` is exactly `len(rows)`.
- `row_sha256` is the SHA-256 of `json.dumps(rows, sort_keys=True,
  separators=(",", ":"))` — the compact, key-sorted encoding of the rows array.
- Files are rendered with `json.dumps(..., indent=2, sort_keys=True)` plus a
  trailing newline.

Re-running the generator therefore reproduces byte-identical files.

### Expected-disposition classification

Each harness defaults to `PROOF`. A file may override this with header
directives in the first 50 lines:

```rust
// kani-expect: CTREX                       // file-wide default for every harness
// kani-expect: my_module::check_foo=UNKNOWN // per-harness override (wins)
```

Valid outcomes: `PROOF`, `CTREX`, `UNKNOWN`, `ERROR`, `BMC_SAFE`. A per-harness
`HARNESS=OUTCOME` directive takes precedence over a bare file-wide directive.

## CLI

```
generate_inventory.py [--suite NAME ...] [--output PATH] [--proof-output PATH]
                      [--no-proof-subset] [--check]
```

| Flag | Effect |
| --- | --- |
| `--suite NAME` | Suite directory under `tests/` to walk. Repeatable. Default: `trust-mc`, `ay`. |
| `--output PATH` | Full-inventory output path. Default: `tests/trust-mc/replacement-harness-inventory.json`. |
| `--proof-output PATH` | PROOF-subset output path. Default: `tests/trust-mc/replacement-harness-inventory.proof.json`. |
| `--no-proof-subset` | Skip writing/checking the PROOF subset. |
| `--check` | Verify mode — regenerate in memory, diff against the committed file(s), exit nonzero on drift. Writes nothing. |

### Generate

```sh
python3 tools/replacement-inventory/generate_inventory.py
```

Writes (or refreshes) both inventory files and prints the `denominator` and
`row_sha256` for each.

### Check

```sh
python3 tools/replacement-inventory/generate_inventory.py --check
```

`--check` regenerates each inventory **into memory** and compares it byte-for-byte
against the committed file. On a match it prints `OK` and exits `0`. On any drift
(or a missing inventory file) it writes a regenerated copy to a temp path, prints
a unified diff to stderr, and exits `1`. It never modifies the committed files,
so it is safe to run in CI as a staleness gate.

---

# replacement_progress.py — replacement progress & audit

`replacement_progress.py` cross-references the frozen inventory (above) against
a **fresh** compiletest per-harness report and computes replacement progress.

It answers two questions per row:

- **PROOF rows** — is the harness *actually proven*? (verifier `SUCCESS`,
  **zero** soundness fallback). A `SUCCESS` reached only via a sound
  over-approximation/fallback is **not** counted as proven.
- **non-PROOF rows** (`CTREX` / `UNKNOWN` / `ERROR` / `BMC_SAFE`) — is the
  observed outcome *justified*, i.e. does it match the recorded expectation?

It never fabricates progress: with no fresh report it prints
`MEASUREMENT MISSING -- no fresh run` and exits nonzero.

## Inputs

1. **Inventory** (`--inventory`, default
   `tests/trust-mc/replacement-harness-inventory.json`) — the
   `{schema_version, suite, denominator, row_sha256, rows[]}` file documented
   above; `expected` ∈ `PROOF | CTREX | UNKNOWN | ERROR | BMC_SAFE`.

2. **Fresh report** (`--report`). Either shape is auto-detected:
   - the canonical trust-mc **proof-summary** artifact
     (`trust-mc-driver/src/proof_summary.rs`, `artifact_kind:
     "trust_mc.proof_summary_pointer"`, with a `harnesses[]` array of
     `{harness, crate_name, status, effective_success, validation_status,
     proof_qualifiers[], property_counts{...}}`), or
   - a `scripts/ay-compiletest.sh` per-harness report — records carrying the
     verifier markers `[AY:CTREX_CAT:...]` (→ `ctrex_category`),
     `[AY:SOUND_FALLBACK:n]` (→ `sound_fallback`) and
     `[AY:EFFECTIVE_SUCCESS:reason]` (→ `effective_success`).

   Soundness fallback is read from `proof_qualifiers` entries of the form
   `sound_fallback=N` (proof-summary) or a `sound_fallback` field
   (ay-compiletest).

## Usage

```sh
# 1. Produce a fresh report by running compiletest under the AY backend,
#    e.g. for the trust-mc suite:
cargo build-dev
compiletest --suite trust-mc --mode trust_mc \
    --src-base tests/trust-mc --build-base build/tests/trust-mc \
    --timeout 60 --no-fail-fast --trust_mc-flag=--ay-chc
#    (the proof-summary / ay-compiletest report JSON is produced by the
#     ay-compiletest wrapper; point --report at it below.)

# 2. Audit progress (human-readable, list every outstanding row):
python3 tools/replacement-inventory/replacement_progress.py \
    --report build/tests/trust-mc/proof-summary.json --verbose

# 3. Machine-readable:
python3 tools/replacement-inventory/replacement_progress.py \
    --report build/tests/trust-mc/proof-summary.json --format json

# 4. CI gate — fail unless replacement is 100% accounted for:
python3 tools/replacement-inventory/replacement_progress.py \
    --report build/tests/trust-mc/proof-summary.json --require-complete

# 5. No report yet — prints MEASUREMENT MISSING and exits nonzero:
python3 tools/replacement-inventory/replacement_progress.py
```

## Flags

| Flag | Effect |
| --- | --- |
| `--inventory PATH` | Inventory JSON. Default: `tests/trust-mc/replacement-harness-inventory.json`. |
| `--report PATH` | Fresh proof-summary / ay-compiletest report. Omit → `MEASUREMENT MISSING`. |
| `--format {text,json}` | Output format. Default: `text`. |
| `--verbose` | List each outstanding (unproven / unclosed) row. |
| `--require-complete` | Exit nonzero unless 100% replacement accounting is reached. |

## `--require-complete` completion criterion

The suite is **complete** iff **every** inventory row was measured against the
fresh report **and**:

- every **PROOF** row is `SUCCESS` with **zero** soundness fallback
  (`proof_proven == proof_total`, `proof_fallback == 0`, `proof_regressed == 0`), **and**
- every **non-PROOF** row is justified — observed outcome equals the recorded
  expectation (`nonproof_closed == nonproof_total`, `nonproof_unjustified == 0`), **and**
- no row is missing from the report (`rows_missing == 0`).

Any missing measurement, any PROOF that passed only on fallback, any PROOF
regression, or any unjustified non-PROOF row makes the suite **incomplete**.

## Exit codes

| Code | Meaning |
| --- | --- |
| `0` | Report consumed; (with `--require-complete`) replacement is complete. |
| `1` | `--require-complete` set and replacement is **incomplete**. |
| `2` | Inventory could not be loaded. |
| `3` | `MEASUREMENT MISSING` — no / unparseable / empty fresh report. |
