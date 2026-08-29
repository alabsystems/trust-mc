# Replacement Audit CLI

`replacement-progress` is the reviewer-facing measurement command. It combines
the frozen mixed inventory, the proof-only inventory, the checked non-proof
closure, and optional schema-v2 per-harness reports. Full reports may be supplied
directly; rows outside the proof inventory are ignored for the proof numerator.
By default it reads the canonical `tests/trust-mc` inventories and closure.

Use the pinned solver environment for measurements:

```bash
export PATH=/path/to/ay/target/release:$PATH
export AY_NO_PULL=1
export AY_SELF_CONTAINED=1
export AY_SOLVER=ay
ay --version
```

The progress output is intended to be enough to re-check the arithmetic: it
prints the canonical command, workspace authority context, expected commit/AY
pin, inventory row digests, non-proof closure digest, per-report file and row
digests, duplicate-key rejection status, and the exact progress formula.

## Partial Progress

A clean partial proof measurement should not use `--require-complete`. The
command exits zero when the inputs are readable and reports the measured proof
numerator plus any missing proof inventory rows:

```bash
cargo run --manifest-path tools/replacement-audit/Cargo.toml --locked \
  --bin replacement-progress -- \
  --report reports/compiletest-per-harness-latest-trust-mc.json
```

Repeated `--report` arguments may be used for shards or focused lanes:

```bash
cargo run --manifest-path tools/replacement-audit/Cargo.toml --locked \
  --bin replacement-progress -- \
  --report reports/compiletest-per-harness-proof-latest-lane-a.json \
  --report reports/compiletest-per-harness-proof-latest-lane-b.json
```

Partial output is expected to say `status=NOT_REPLACEMENT`. The first line is a
machine-readable summary: `accepted_proof_quality=N/D` counts only clean
proof-quality rows accepted under current authority metadata, and
`closed_non_proof=N/D` counts only valid non-proof closure rows. The
`proof_inventory ... progress=N/D` value mirrors accepted proof progress for
older parsers. This is measurement evidence, not a 100% replacement claim.

## Recording A Clean Measurement

When recording a repository status update, fill the measurement only from a
clean report set accepted by `replacement-progress`. For example, this
historical focused lower-bound measurement predates the current inventory and
must not be copied into a current replacement claim:

- trust-mc commit: `b7b7b3e56a094229e34a03d230215e9cf194be81`.
- AY pin: `1e3f8ae53f560662630a1aa8842ec814a345456f`.
- Solver binary commit: `1e3f8ae53f560662630a1aa8842ec814a345456f`.
- Tree fingerprint:
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- Report status: `NOT_REPLACEMENT`.
- Accepted accounting: `195/1045 (18.7%)`.
- Proof-quality progress: `15/865 (1.7%)`.
- Missing proof rows: `850`.
- Report files: `22`.
- Proof inventory seen: `56/865`.
- Duplicate report keys: `0`.
- Non-quality proof reasons include `proof_qualifiers_trivial_safe_no_error_rule=34`.

Do not copy numerators from older commits, dirty reports, stale solver binaries,
reports with duplicate harness keys, or another AY pin. A partial measurement is
progress evidence only; it becomes a replacement claim only when
`--require-complete`, the strict proof gate, and the zero-fallback canary all
pass on the same clean tuple.

## Direct Driver Evidence

Raw `./scripts/trust-mc --harness ...` logs are not replacement-progress input. They
must first be converted into the same clean schema-v2 proof report used by the
Rust audit:

```bash
python3 scripts/direct_driver_proof_report.py \
  reports/direct-driver-proof-manifest.json \
  reports/direct-driver-proof-latest.json \
  --inventory tests/trust-mc/replacement-harness-inventory.proof.json

cargo run --manifest-path tools/replacement-audit/Cargo.toml --locked \
  --bin replacement-progress -- \
  --report reports/direct-driver-proof-latest.json
```

The manifest records each direct command, log, exit code, file, and harness. The
converter only accepts `./scripts/trust-mc` commands with the AY CHC replacement
flags, a zero exit code, final `[AY:PROOF]`, `[AY:PROOF_QUALIFIERS:clean]`, no
fallback/drop/demotion/retry markers, and a matching proof-inventory row. It
writes actual commit, tree-state, tree-fingerprint, AY pin, solver-binary
attestation, and the exact TrustMC driver's path, SHA-256, and
`--version-authority` evidence. If the report authority is dirty or stale,
`replacement-progress` will report the rows but will not count them as
`accepted_proof_quality`. The strict script additionally validates and
re-attests the live driver bytes before invoking the Rust audit.

Long reviewer summaries remain bounded and parseable. Report path lists,
authority-failure details, and count summaries emit sample entries plus
`omitted=` or `omitted_keys=` when more data exists than the CLI prints.

## Qualified Proofs

Rows marked with qualified proof metadata remain excluded from
replacement-quality proof progress unless the source/report schema carries
explicit sound metadata for that qualification. Today the automatic numerator
only accepts `proof_qualifiers=clean`.

In particular, `proof_qualifiers=should_panic` proves the expected panic path,
not the absence of an error-headed obligation, and
`proof_qualifiers=trivial_safe=no_error_rule` means the emitted CHC had no rule
deriving `error`. The smallest sound path is to regenerate evidence that
preserves an error-headed obligation and reports `proof_qualifiers=clean`;
otherwise the row needs a separate source/encoding audit and must stay outside
the automatic replacement proof numerator.

## Full Accounting

Use `--require-complete` for the full replacement accounting gate. This exits
nonzero unless the proof report covers the entire proof inventory with clean
replacement-quality proof rows and the non-proof closure covers every non-PROOF
row in the mixed inventory:

```bash
cargo run --manifest-path tools/replacement-audit/Cargo.toml --locked \
  --bin replacement-progress -- \
  --require-complete \
  --report reports/compiletest-per-harness-latest-trust-mc.json
```

For a replacement claim, follow that progress gate with `replacement-audit` or
`scripts/ay-replacement-proof.sh` using the explicit commit, AY pin, tree
fingerprint, proof denominator, inventory SHA, and non-proof closure SHA.
