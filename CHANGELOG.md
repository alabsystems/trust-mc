# Changelog

All notable trust-mc changes should be recorded here.

trust-mc is a pre-release Rust verifier derived from Kani. This file tracks

## [Unreleased]

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
