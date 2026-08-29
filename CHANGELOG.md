# Changelog

All notable trust-mc changes should be recorded here.

trust-mc is a pre-release Rust verifier derived from Kani. This file tracks
the changes in each release; released sections are dated from their git tag.

The manifest version is currently `0.3.0` (bumped 2026-08-28 in `7e2a5fe19`).
No `v0.3.0` tag has been cut, so the entries below remain under
`[Unreleased]` until one is.

## [Unreleased]

### Fixed (soundness — vacuous and empty "proofs")
- A harness whose path constraints are contradictory no longer reports a clean
  proof. `kani::assume(false)`, mutually exclusive assumptions, or an
  unreachable body all made the BMC query `unsat` for the wrong reason;
  because `kani::assume(false)` compiles to a top-level `(assert false)`, no
  check carried a non-trivial guard, the compiler emitted no `ay_reach_*`
  flag, and the V4 vacuity gate could never fire. A whole-harness
  reachability probe now runs after a would-be proof; a definitive `unsat`
  reclassifies the checks UNREACHABLE and the run reports
  `VERIFICATION:- VACUOUS (...)`, or passes loudly under `--allow-vacuous`.
  Only a decided `unsat` reclassifies anything, so an undecided probe cannot
  invent a vacuity verdict.
- A harness that produced NO verification conditions is now
  `INCONCLUSIVE (no checks)` with `[AY:VACUOUS:no-checks]` instead of
  SUCCESSFUL. The `INCONCLUSIVE (no checks)` verdict already existed but sat
  after the success arms and so was unreachable. Observed on
  `Option::<u32>::None.unwrap()`, which panics unconditionally at run time yet
  yields an obligation-free query — the underlying codegen gap is still open;
  this makes it loud rather than silent. Deliberately diverges from Kani, and
  is documented in `trust-mc explain kani`.
- Running the new gates over 105 corpus harnesses surfaced two latent vacuous
  proofs with no false positives — `kani::any::<Duration>()` produces an
  infeasible value, and a 2^29-aligned type makes its harness unreachable. See
  `docs/findings/2026-08-20-vacuous-proofs-in-the-corpus.md`.
- AY pin advanced to `5a6d1581f6`, which fixes a false UNSAFE: a fact clause's
  constant and repeated head arguments were dropped from its level-0
  must-summary, so `(hdr #x00 n)` claimed every state was proven reachable and
  PDR emitted a 1-step counterexample with no assignments on SAFE programs.

### Added (the standalone `trust-mc` binary)
- `trust-mc` is now a self-describing front door. `explain [TOPIC]` describes
  how the tool works from inside the tool (pipeline, harnesses, bounded vs
  unbounded proving, reading verdicts and `[AY:...]` markers, soundness,
  cargo use, Kani differences, flags, install, exit codes), `quickstart` is a
  five-minute walkthrough, `example [NAME]` hands out seven harnesses that are
  verified to prove or fail as labelled (`basic`, `bug`, `bounds`, `unsafe`,
  `assume`, `cover`, `loop`), `flags [--all]` prints the engine's flag
  reference, and `help <command|topic>` reaches every page. All of it works
  with nothing installed.
- `doctor` now also checks `trust-mc-compiler` beside the engine and that it
  can load its rustc, the engine's `--version` and `--version-authority`, and
  that the `ay` binary on `PATH` is the same AY commit the engine links
  (bounded verdicts come from the binary, CHC verdicts from the link).
  `version --verbose` prints the same provenance in four lines.
- New translated flag `--timeout <T>` (30s, 2m, 1h) → `-Z unstable-options
  --harness-timeout T`. Mistyped commands get a suggestion; a directory
  argument is explained rather than reported as a missing file.
- `tests/cli.rs`: end-to-end tests of the binary; the verification ones skip
  themselves (loudly) without a built engine and solver.

### Changed
- `cargo-trust-mc` / `targo-trust-mc` share the front door's engine discovery
  (`$TRUST_MC_SYSROOT`, the nearest `target/trust-mc`, then
  `${KANI_HOME:-~/.kani}`), so a local `cargo build-dev` serves `cargo
  trust-mc` too. They no longer refuse to run from a checkout, and no longer
  auto-download a release bundle on first use — `setup` is explicit.
- AY pin advanced `63cbda0f0a` → `5bd74669349190eae57027c91c0430b4980046ac`
  (v0.13.0, 36 commits). Soundness gate 8/8 at the new pin.

### Fixed (soundness — split-pointer memory model)
- CHC heap bounds checks now fire for the dominant OOB shape — a known
  allocation dereferenced through a symbolic offset (`*a.as_ptr().add(i)`).
  Two root causes closed: (1) `const_bv_value` could not fold
  `extract(63,32)(concat(const_id, symbolic_offset))`, so every split-add
  pointer lost its obj_id at the deref and the bounds clause was silently
  dropped (the audit's reproduced false-proof BLOCKER); a lane-aware
  `const_extract_value` folds through concat/extract/extend structure.
  (2) Pointer steps with non-constant deltas kept the source's
  `ref_targets` element tracking with the offset dropped, so derefs of
  `base.add(sym_i)` resolved through an offset-less backing-array select —
  false proofs on OOB harnesses and false CTREX on in-bounds ones; symbolic
  deltas now clear element-precise metadata and take the checked memory path.
- All remaining full-width pointer `bvadd`/`bvsub` sites now use the
  obj_id-preserving split step: inline + stub `wrapping_byte_*`, inline
  `BinOp::Offset`, and both slice-index address builders.
  `step_split_pointer` gained a constant fast-path (fully-constant inputs
  fold to a literal address; zero offsets return the pointer unchanged) so
  constant-address scalarization and static discharge keep working.
- `copy` / `copy_nonoverlapping` / `write_bytes` now emit span UB
  obligations when the target's obj_id const-folds: src-readable /
  dst-writable allocation bounds over `count * size_of::<T>()`, alignment,
  span-fits-u32, count×size no-overflow, and (copy_nonoverlapping) range
  disjointness when both pointers land in the same allocation — previously
  zero UB checks were emitted for these intrinsics.

### Changed
- Split `trust-mc-driver` CLI dependencies behind the default `cli` feature so
  embedded native-facade builds with `default-features = false` do not pull
  binary-only crates.
- Kept native solver dependencies feature-specific: `ay-chc-native` enables the
  library-facing AY facade and CHC crates, while `ay-direct` owns direct solver
  parser and binding dependencies.

### Fixed
- `trust-mc-trust-bmc`: float constants now lower to their EXACT IEEE-754 bit
  patterns (F64 verbatim, F32 via a bit-certified demotion of the widened
  payload) instead of a `bitvec_const(0, width)` placeholder that modeled every
  float constant as +0.0 — wrong bits that could falsely prove or falsely
  refute any obligation depending on the constant's value. Constants with no
  exact encoding (F16, non-widened F32 payloads, malformed vectors) fail
  closed. Ops that would interpret float bits non-bit-accurately fail closed
  in both lanes: `ICmp` over float types (bit equality is not IEEE equality:
  `-0.0 == +0.0`, `NaN != NaN`), non-`Xchg` atomic RMW on non-integer types,
  compare-exchange over types without exact modeled bits, and `BoundedOutput`
  postconditions whose f64 bounds have no exact integer encoding against the
  return type (float returns, fractional/out-of-range bounds; unsigned returns
  now compare unsigned).
- Removed unused direct `trust-mc-driver` dependencies on `tokio`, `num-bigint`, and
  `ay-core`.
- Gated native BMC solver tests behind the solver features they require.

## [0.2.0] - 2026-08-19

Cut at `cc08303c9`; the first revision to ship the repo's own sysroot bundle
(`SYSROOT=target/trust-mc`, `EXPOSES=trust-mc-driver`).

### Changed
- Version 0.1.0 -> 0.2.0 across the shipped surface (root, `trust-mc-driver`,
  `trust-mc-core`, `library/*`, `trust-mc-cov`). The guide and test-fixture
  manifests stay at their inert 0.1.0.

### Fixed
- `trust-mc-trust-bmc` now admits the single-cell `Alloca` that the CHC
  translator already handled (`074fb51cb`).
- `codegen_ay` encoder false positives: 25 root causes diagnosed, several of
  them fixed (`75dba631c`).

## [0.1.0] - 2026-08-18

Cut at `46af2081f`, the first tag on the public 0.x line.

### Changed
- Version 0.67.0 -> 0.1.0 across all sixteen workspace manifests (root, driver,
  core, the codegen family, the kani library tree, the build tool, replay,
  trust-bmc, metadata) plus the evidence-test fixture literal. Owner policy of
  2026-08-18: the public 0.x line restarts at 0.1.0, because the 0.67 minor
  count was internal iteration cadence rather than a public signal. Runtime
  evidence carries `env!("CARGO_PKG_VERSION")`, so records follow the manifests
  automatically.

History before this tag is not itemized here.
