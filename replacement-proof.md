# trust-mc Replacement Proof Standard

This document defines the evidence required to claim that trust-mc replaces
Kani for the frozen public harness corpus. It is a proof standard, not a claim
that the current checkout meets that standard.

## Frozen authority

The public corpus is intentionally historical. Removing, renaming, qualifying,
feature-gating, or `cfg`-disabling a source harness must not silently reduce its
denominator.

| Artifact | Rows | `row_sha256` |
| --- | ---: | --- |
| `tests/trust-mc/replacement-harness-inventory.json` | 818 | `393e71e1f522142a880a86a03f8dfdd1362dd09855c09582f0a1e507fa365a30` |
| `tests/trust-mc/replacement-harness-inventory.proof.json` | 504 | `62ddf770d23c96f5d45875e381ba310f9e0374658b50885df0a07b7c48d3c9cf` |
| `tests/trust-mc/non-proof-closure.json` | 314 | `4e47d2dac3feb0c6835b2566a98f47d1388970ec6b58098a91c3b33138f39bbf` |

The mixed inventory is the whole replacement denominator. Its 504 `PROOF`
rows are the proof-quality subset; its 314 non-`PROOF` rows are deliberate
negative expectations with checked closure records. The generator reads the
surveyed `tools/replacement-inventory/public-corpus.json`; it does not infer a
smaller authority set from whichever harnesses happen to compile today.

`tests/trust-mc/replacement-harness-dispositions.json` binds every frozen row
back to current source and to an executable driver identity. The binding is
fail-closed:

- 740 rows have an exact current harness name;
- 45 bare historical names resolve to one unique module-qualified harness;
- one function-level gate is active through its package's default `full`
  feature;
- 32 `PROOF` rows are source-bound to an exact `#[cfg(disabled)]` harness.

Therefore the current source-bound plan is 818 historical rows, 786 active
executions, and 32 inactive-accounted rows. The proof subset is 472 active plus
32 inactive rows. Inactive rows receive neither execution nor proof credit.
The 314 non-`PROOF` rows are all active. An unknown mapping, an ambiguous alias,
or a changed gate is an error rather than an implicit skip.

The 66 active Cargo rows are also bound through the conventional Rust module
graph. Their whole-file feature gates must be enabled by the owning package's
default features, their fully qualified driver identities must be unique within
that package, and every owning package must have a committed `Cargo.lock`. The
runner invokes every active row with `--locked --exact` and accepts exactly one
matching `Checking harness ...` marker. A missing/stale lock, missing module,
disabled file, zero match, prefix match, or multiple match is an execution
failure. The other 720 active rows use the direct single-file executor.

The committed disposition report records its own deterministic plan digests.
Regenerate it only when the source or authority inventory intentionally
changes, and review the row-level diff.

## Current blocking status

Strict replacement proof is red. The 32 source-inactive `PROOF` rows make a
504/504 proof packet impossible even if every active row succeeds. The public
runner records those rows as `SKIP` with `execution.state ==
"inactive_accounted"`; the runtime accounting object reports them as
`inactive_zero_credit`. Both proof extraction and the strict audit reject that
state.

The disabled rows are all in `tests/slow/tokio-proofs` and carry these source
reasons:

| Source reason | Rows | Files | Activation assessment |
| --- | ---: | ---: | --- |
| `CBMC consumes more than 10 GB` | 12 | 4 | First candidates for bounded AY trials; retain strict memory/time limits and prove each exact harness before enabling it. |
| `requires pthread_key_create` | 11 | 4 | Requires a sound thread-local/runtime model or a proved elimination path; removing the gate alone is not evidence. |
| `CBMC takes more than 15 minutes` | 5 | 4 | Trial individually under AY. These may expose state-space or async scheduling limits rather than missing semantics. |
| `requires memchr` | 2 | 2 | Requires supported `memchr` semantics/model and a clean proof. |
| `requires syscall` | 1 | 1 | Requires a sound syscall/runtime abstraction and a clean proof. |
| `requires write` | 1 | 1 | Requires a sound write model and a clean proof. |

Four of the `pthread_key_create` rows also use `spawn`, and one uses `select`;
those are additional async-runtime obligations, not separate denominator rows.
The exact source groups are listed below; paths are relative to
`tests/slow/tokio-proofs/src/`:

- `requires pthread_key_create` (11): `tokio/io_copy.rs::{copy,proxy}`,
  `tokio/io_mem_stream.rs::{ping_pong,across_tasks,disconnect,disconnect_reader,max_write_size,duplex_is_cooperative}`,
  `tokio/io_read_line.rs::read_line`, and
  `tokio/io_util_empty.rs::{empty_read_is_cooperative,empty_buf_reads_are_cooperative}`.
  Within that group, `across_tasks`, `disconnect`, `disconnect_reader`, and
  `max_write_size` also require `spawn`; `duplex_is_cooperative` also requires
  `select`.
- `CBMC consumes more than 10 GB` (12):
  `tokio/io_read_line.rs::{read_line_not_all_ready,read_line_invalid_utf8,read_line_fail,read_line_fail_and_utf8_fail}`,
  `tokio/io_read_to_string.rs::{to_string_does_not_truncate_on_utf8_error,to_string_does_not_truncate_on_io_error,to_string_appends}`,
  `tokio/io_read_until.rs::{read_until_not_all_ready,read_until_fail}`, and
  `tokio_test/io.rs::{read_error,write1,write_error}`.
- `CBMC takes more than 15 minutes` (5):
  `tokio/io_read_to_string.rs::read_to_string`,
  `tokio_test/block_on.rs::{async_block,async_fn}`,
  `tokio_test/io.rs::read1`, and
  `tokio_util/io_reader_stream.rs::correct_behavior_on_errors`.
- `requires memchr` (2): `tokio/io_lines.rs::lines_inherent` and
  `tokio/io_read_until.rs::read_until`.
- `requires syscall` (1): `tokio_stream/stream_stream_map.rs::empty`.
- `requires write` (1): `tokio/io_write_all_buf.rs::write_all_buf`.

Every listed item is gated by the exact function-level `#[cfg(disabled)]`
immediately preceding its `#[kani::proof]` attribute. The committed disposition
artifact additionally binds each item to its exact source line, so moving or
changing a gate makes `--check` fail rather than silently changing the group.

Activation should proceed in small groups: resource-only rows first, then
library models, then thread-local/syscall and spawn/select semantics. For every
row, remove `#[cfg(disabled)]`, run the exact cargo harness through AY, retain
the row in the 818 authority, regenerate/check the disposition artifact, and
require a clean `PROOF` record. The strict gate becomes eligible only when
`.summary.proof.inactive_zero_credit == 0`.

## What constitutes replacement evidence

A replacement claim must bind all evidence to one tuple:

- exact trust-mc `HEAD`;
- exact 40-hex AY revision pinned in root `Cargo.toml`;
- clean measurement tree and its report `tree_fingerprint`;
- the three authority row digests above and the checked source disposition;
- an attested live `ay` binary and report `solver_binary.commit` matching the
  pinned AY revision;
- the exact executable TrustMC driver path and SHA-256, plus its live
  `--version-authority` evidence for the current clean TrustMC commit and the
  clean linked AY authority;
- one schema-v2 report containing all 818 historical rows;
- a proof-only report containing exactly the 504 `PROOF` rows;
- logs and exit codes from the self-test, public runner, proof extraction,
  zero-fallback gate, and strict audit.

For every active inventory row the driver must actually execute the source
harness through AY. A row counts only when its expected verdict matches and its
status is `PASS`. A `PROOF` row additionally requires `verdict == "PROOF"`,
`execution_state == "complete"`, `proof_qualifiers == "clean"`, zero sound
fallback, and no retry, demotion, translation drop, BMC reroute, known false
positive, or stale authority metadata. Negative rows must retain their expected
negative outcome; a surprising `PROOF` is a regression until the expectation
and justification are deliberately reviewed.

Evidence produced with upstream Kani/CBMC, a dirty or different AY pin,
`AY_REPORT_NON_REPLACEMENT=true`, disabled expectation checking, a stale report,
or another commit/tree/inventory tuple does not count.

## Reproducible checks

Use the repository-selected Python so the evidence tools and tests run with the
supported interpreter:

```bash
source scripts/ay_python.sh

"$AY_PYTHON_BIN" tools/replacement-inventory/generate_inventory.py --check
"$AY_PYTHON_BIN" scripts/generate_non_proof_closure.py --check
"$AY_PYTHON_BIN" scripts/replacement_harness_dispositions.py --check
"$AY_PYTHON_BIN" -m unittest scripts/test_replacement_evidence_tools.py

AY_SELF_CONTAINED=1 AY_SOLVER=ay ./scripts/ay-compiletest.sh --self-test
```

Run the complete source-bound public plan with:

```bash
AY_SELF_CONTAINED=1 \
AY_SOLVER=ay \
AY_EXPECTED_HARNESSES=818 \
./scripts/ay-compiletest.sh --replacement-public
```

The runner dispatches ordinary files directly and Cargo-suite rows through
their owning package with isolated target directories and exact, fully
qualified harness selection. It validates the runtime JSONL against the
checked plan before producing the schema-v2 report. The measurement tree must
be clean before and after execution and its fingerprint must not change during
the run; Cargo lock creation or mutation therefore fails rather than becoming
evidence.
At the current source state it is expected to finish the active work but return
nonzero because 32 proof rows are inactive with zero credit. Do not convert
that expected red result into green evidence.

Once every proof row is active and the full report is clean, derive the
proof-only report:

```bash
"$AY_PYTHON_BIN" scripts/extract_replacement_proof_report.py \
  --inventory tests/trust-mc/replacement-harness-inventory.proof.json \
  reports/compiletest-per-harness-latest-trust-mc.json \
  reports/compiletest-per-harness-proof-latest-trust-mc.json
```

Extraction is intentionally red today because a `SKIP` cannot become proof
evidence. When it succeeds, compute the explicit authority tuple and run:

```bash
HEAD_SHA=$(git rev-parse HEAD)
AY_PIN=$("$AY_PYTHON_BIN" - <<'PY'
from pathlib import Path
import sys
sys.path.insert(0, "scripts")
from ay_manifest_pin import expected_ay_pin_from_cargo_toml
print(expected_ay_pin_from_cargo_toml(Path(".")))
PY
)
TREE_FINGERPRINT=$("$AY_PYTHON_BIN" - <<'PY'
from pathlib import Path
import sys
sys.path.insert(0, "scripts")
from compiletest_report_contract import _current_tree_fingerprint
print(_current_tree_fingerprint(Path(".")))
PY
)
NON_PROOF_FILE_SHA=$(shasum -a 256 tests/trust-mc/non-proof-closure.json | awk '{print $1}')

./scripts/ay-replacement-proof.sh \
  --expected-commit "$HEAD_SHA" \
  --expected-ay-pin "$AY_PIN" \
  --expected-tree-fingerprint "$TREE_FINGERPRINT" \
  --expected-harnesses 504 \
  --expected-inventory-sha 62ddf770d23c96f5d45875e381ba310f9e0374658b50885df0a07b7c48d3c9cf \
  --non-proof-closure tests/trust-mc/non-proof-closure.json \
  --expected-non-proof-closure-sha "$NON_PROOF_FILE_SHA"
```

The strict script validates current-head report authority, canonical inventory
bytes, source dispositions, live/report AY attestations, re-attests the exact
report driver bytes and `--version-authority`, checks the proof denominator,
zero-fallback row quality, non-proof closure, and the independent Rust audit.

For a non-authoritative progress view only, use:

```bash
"$AY_PYTHON_BIN" tools/replacement-inventory/replacement_progress.py \
  --report reports/compiletest-per-harness-latest-trust-mc.json \
  --verbose
```

This progress reporter is useful for triage but does not replace the
source-disposition, current-head, solver-attestation, and strict proof gates.

## Must fail closed

Reject a replacement claim when any authority digest or identity differs; a
row is missing, duplicated, ambiguous, inactive, skipped, xfailed, unknown, or
errored; an expectation changes unexpectedly; a proof uses fallback or loses
classification metadata; the report is stale or dirty; AY identity cannot be
attested; the TrustMC driver is stale, dirty, changed, or unattested; or any
required command exits nonzero. "Upstream blocked", timeout, resource cost, or
a source `cfg` explains work remaining but never grants proof credit.
