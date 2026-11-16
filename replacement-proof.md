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
| `tests/trust-mc/replacement-harness-inventory.json` | 818 | `91e3425e3e1cb4339ced9bc99f5bb24caad671f147697d02c1b95293f5dfdd98` |
| `tests/trust-mc/replacement-harness-inventory.proof.json` | 485 | `ffdde89eb28c7e8c1a4c73897e1b2c3c47078bd718046294ece8babcebe4c40f` |
| `tests/trust-mc/non-proof-closure.json` | 333 | `cd0d81801df6f0ceb4aad67818bd628991112966b455ab4772ace8629bbccaf6` |
| `tests/trust-mc/replacement-upstream-inactive.json` | 32 | `7e2eef01baaa59e5f4ee92daa7f025e3dc841071ae784dd68247dc0f464c9fe5` |

### Corrected failure oracles, 2026-11-14

The original survey labelled 27 single-harness files `PROOF` despite their
explicit `kani-verify-fail` annotations in the initial fork. Their program bodies
are unchanged; examples include the assertion `2 + 3 == 6`, which the actual
current driver correctly refutes. The survey had applied the missing expected-
output-file default to suites whose test mode uses failure annotations.

[The correction record](tools/replacement-inventory/oracle-corrections-2026-11-14.json)
names every changed row and the immutable fork/blob/source identities. Only those
27 expectations move from `PROOF` to `CTREX`: all 818 file/harness/lane identities
remain unchanged, no source program is weakened, and no row is excluded. The
current partition is 485 proof expectations and 333 negative expectations;
with the same 32 upstream-inactive proof rows, the active bar is 453 + 333 = 786.
Historical reports retain their original authority hashes and counts and do not
become measurements of this corrected authority. Counterexamples still need the
required checked evidence; this correction grants no proof or execution credit.

A subsequent [per-harness semantic audit](tools/replacement-inventory/oracle-semantic-corrections-2026-11-14.json)
corrects six more labels: two coroutine harnesses and the valid mutable-reference
division contract require PROOF; the uninitialized atomic read and two invalid
postcondition checks require CTREX. Three labels move each way, leaving the same
partition and every historical identity. The selected contract harness controls
its oracle; a different ordinary harness's file-level output is not its result.
Expected-panic test success likewise retains its raw checked CTREX outcome.

The two [safe enum examples](tools/replacement-inventory/niche-oracle-corrections-2026-11-14.json)
also require PROOF. Their unchanged sources construct the exact variants they
match, and their original outputs require only SUCCESS or UNREACHABLE checks.
The words `assertion failed` describe the checked assertion, not a failing
status. These corrections preserve every source and historical identity.
Separate reachability examples retain their existing requirements pending
qualification of their explicit unreachable-check reporting.

The two [independent-prior contract checks](tools/replacement-inventory/contract-prior-oracle-corrections-2026-11-14.json)
also require CTREX: their preconditions do not equate `prior` with the initial
target. Inputs target=0 and prior=1 violate each postcondition after increment.
The original successful output names only their separate `main` harnesses,
which pass the correct prior value and retain PROOF requirements.

The [dead-pointer negation correction](tools/replacement-inventory/memory-predicate-oracle-correction-2026-11-14.json)
requires PROOF for `thin_ptr_validity::check_invalid_ptr`: it asserts that expired
nonzero stack storage cannot be dereferenced. The original Kani failure names
an unsupported-memory limitation, not a false program assertion. Reproducing
that limitation is not a genuine refutation. The sibling `check_invalid_array`
still asserts the opposite and requires a Genuine counterexample. Both source
programs remain unchanged.

The [remaining source-oracle audit](tools/replacement-inventory/remaining-oracle-corrections-2026-11-14.json)
corrects sixteen labels: eleven safe programs need PROOF, while five union
programs with uninitialized reads or an invalid transmute-copy need Genuine
counterexamples. The safe cases include untyped byte writes/copies without
invalid typed reads, initialized swap, valid char conversion, double reversal,
address-only enum use, a nop, fixed slice destructuring and C string literals.
The renamed union and C string sources are bound to their original fork blobs;
the five initialized union controls retain PROOF. The original unsupported or
file-level failure output is not a semantic bug oracle. Every historical
identity remains, and historical measurements keep their original labels.

The cover examples also require their original property outcomes. A safety
PROOF with undetermined cover properties does not establish coverage parity.
The five original cover rows now require exact named property outcomes through
[the source-bound cover authority](tools/replacement-inventory/cover-property-oracles.json).
The runner, progress accounting and proof extraction refuse missing, duplicate,
extra, malformed or mismatched cover evidence. Generic ordinal descriptions and
aggregate counts do not establish original property identity. Only
`cover-unreachable` changes its safety oracle to PROOF; all ten cover requirements
remain. Runtime coverage parity remains open: implementing accounting and
correcting a safety label supplies no successful cover measurement.

The mixed inventory is the whole replacement denominator. Its 485 `PROOF`
rows are the proof-quality subset; its 333 non-`PROOF` rows are deliberate
negative expectations with checked closure records. The generator reads the
surveyed `tools/replacement-inventory/public-corpus.json`; it does not infer a
smaller authority set from whichever harnesses happen to compile today.

`tests/trust-mc/replacement-harness-dispositions.json` binds every frozen row
back to current source and to an executable driver identity. The binding is
fail-closed:

- 739 rows have an exact current harness name;
- 46 bare historical names resolve to one unique qualified harness, including
  the associated method `Dummy::new`;
- one function-level gate is active through its package's default `full`
  feature;
- 32 `PROOF` rows are source-bound to an exact `#[cfg(disabled)]` harness.

Therefore the current source-bound plan is 818 historical rows, 786 active
executions, and 32 inactive-accounted rows. The proof subset is 453 active plus
32 inactive rows. Inactive rows receive neither execution nor proof credit.
The 333 non-`PROOF` rows are all active. An unknown mapping, an ambiguous alias,
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

## The bar versus the denominator

A REPLACEMENT claim is bounded by what the INCUMBENT DOES. Upstream Kani ships 32
`PROOF` harnesses switched off with `#[cfg(disabled)]` because CBMC could not run
them — 12 need more than 10 GB, 5 exceed 15 minutes, 11 need
`pthread_key_create`, 2 need `memchr`, one `syscall`, one `write`. Those are not
things Kani does. Requiring them made the strict bar *harder* than replacement
and mathematically unreachable: the 32 upstream-inactive `PROOF` rows earned zero credit by
construction, so the gate could never go green however good AY became.

The bar is therefore the **786 active rows** (453 `PROOF` + 333 non-`PROOF`).

**This narrows the BAR. It does not narrow the DENOMINATOR.** All 818 historical
rows remain the authority, every one still appears in the schema-v2 report, and
the frozen-inventory rule is untouched: removing, renaming, qualifying,
feature-gating or `cfg`-disabling a source harness still must not silently reduce
it. The 32 are reported as `supersession_candidates`, grouped by upstream reason
— places trust-mc may BEAT Kani rather than merely match it.

### Why this cannot be used to lower the bar

Exclusion is PROVED against the initial fork commit `c4d858036`, never against
the working tree, and is enforced by four rules:

1. `scripts/generate_upstream_inactive_authority.py` admits a row only if it was
   already `#[cfg(disabled)]` in Kani's own source at that commit AND its reason
   is a recognised CBMC limitation. Disabling a harness today cannot make it
   eligible — verified by attack: forging
   `// CBMC takes more than 15 minutes` onto an active row leaves the generator
   emitting the same 32 rows and the same `row_sha256`.
2. Any other `cfg`-disabled `PROOF` row is `local_inactive`, and
   `scripts/ay-replacement-proof.sh` dies while that count is non-zero, naming
   the offending rows. Verified by attack: the forged row above produced
   `local_inactive=1` and blocked the gate.
3. The frozen reason text is part of the key, so editing a comment cannot move a
   row out of the bar.
4. Un-gating one of the 32 moves it INTO the bar and it counts normally —
   verified by attack: un-disabling `tokio_test/block_on.rs::async_block` gave
   `bar=473, upstream_inactive=31`. Excluded rows still receive zero execution
   and zero proof credit; they are outside the bar, not passing.

### Activating the supersession candidates

This is the next goal, and it is where the replacement claim earns its name:
these are rows the incumbent gave up on. Proceed in small groups — resource-only
rows first (the 17 `>10 GB` / `>15 min` rows, which need engine capability and no
new semantics), then library models (`memchr`, `write`), then thread-local,
syscall and spawn/select semantics. For every row: remove `#[cfg(disabled)]`, run
the exact cargo harness through AY, retain the row in the 818 authority,
regenerate both the upstream-inactive authority and the disposition artifact, and
require a clean `PROOF` record.

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
`.summary.proof.local_inactive == 0`; each activated row raises
`.summary.proof.bar` and must then carry a clean `PROOF` record.

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
  clean linked AY source equal to the pinned revision; development ancestry
  (`contains-pin`) alone does not qualify a different linked revision;
- one schema-v2 report containing all 818 historical rows;
- a proof-only report containing exactly the **453 active** `PROOF` rows, plus
  a `replacement_bar` block naming all 32 upstream-inactive rows it excludes
  (`historical` 485, `bar` 453, `upstream_inactive_zero_credit` 32,
  `local_inactive` 0, and the active-subset digest). The 32 must each be
  present in the full 818-row report as a zero-credit `SKIP` carrying its bound
  reason before extraction may exclude it — a row that is simply absent fails
  the gate. Keeping all 485 rows with 32 `SKIP`s is not available: the Rust
  auditor treats `status SKIP` as not-`PASS`, requires report keys to equal the
  inventory denominator, and the zero-fallback gate requires `summary.skip == 0`;
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

AY_SOLVER=ay ./scripts/ay-compiletest.sh --self-test
```

Run the complete source-bound public plan with:

```bash
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
At the current source state it is expected to finish the 786 active rows and
return zero when they all pass; the 32 upstream-inactive rows are reported as
`SKIP` / `inactive_accounted` with no credit. It returns nonzero on any
active-row failure, or on any row a LOCAL `#[cfg(disabled)]` removed from the
run — those stay inside the bar and are named individually. Do not convert a
red result into green evidence by disabling the row that produced it.

Once every proof row is active and the full report is clean, derive the
proof-only report:

```bash
"$AY_PYTHON_BIN" scripts/extract_replacement_proof_report.py \
  --inventory tests/trust-mc/replacement-harness-inventory.proof.json \
  reports/compiletest-per-harness-latest-trust-mc.json \
  reports/compiletest-per-harness-proof-latest-trust-mc.json
```

Extraction demands the 453 active `PROOF` rows, and separately requires each of
the 32 upstream-inactive rows to be present in the full report as a zero-credit
`SKIP`. A `SKIP` never becomes proof evidence; it only has to be accounted for.
Compute the explicit authority tuple and run:

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
  --expected-harnesses 485 \
  --expected-inventory-sha ffdde89eb28c7e8c1a4c73897e1b2c3c47078bd718046294ece8babcebe4c40f \
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
row is missing, duplicated, ambiguous, xfailed, unknown, or errored; a row is
inactive or skipped anywhere but the 32-row upstream-inactive set, or one of
those 32 is missing from the full report or carries any credit; an
expectation changes unexpectedly; a proof uses fallback or loses
classification metadata; the report is stale or dirty; AY identity cannot be
attested; the TrustMC driver is stale, dirty, changed, or unattested; or any
required command exits nonzero. "Upstream blocked", timeout, resource cost, or
a source `cfg` explains work remaining but never grants proof credit.
