# CHC Solver Architecture

Author: Andrew Yates <andrewyates.name@gmail.com>

## Overview

trust-mc uses the native ay-chc portfolio solver for all CHC (Constrained Horn Clause)
unbounded verification. AY is trust-mc's sole solver backend.

## Native ay-chc Path

**Enable:** On by default (`ay-chc-native` is a default feature in `trust-mc-driver`).

**Source:** `trust-mc-driver/src/call_ay/chc.rs` (`try_ay_chc_solver`)

**Bump guardrail:** Before trusting any AY rev bump, run
`./scripts/ay-bump-canary.sh`. The first gate is
`cargo check -p trust-mc-driver --all-targets --features "ay,ay-chc-native"`,
which catches `ay-chc` public API drift (`#3571`, upstream `ay#3604`).

### How It Works

1. Parses SMT-LIB2 CHC file into `ChcProblem` struct
2. Applies optional transformation pipeline (clause inlining, array instantiation)
3. Runs portfolio of engines in parallel:
   - PDR (Property-Directed Reachability) - two variants
   - BMC (Bounded Model Checking)
   - PDKIND (K-induction with PDR)
   - TPA (Transition Power Abstraction)
4. Returns structured result: `InvariantModel` or `Counterexample`

### Capabilities

| Capability | Status |
|------------|--------|
| Multiple engines (portfolio) | yes |
| Structured invariant output | yes |
| Structured counterexample | yes |
| Transformation pipeline | yes |
| LemmaHintProvider | pending (available, not integrated - #866) |
| Back-translation | yes |
| Pure Rust (no subprocess) | yes |

### Strengths

- **Portfolio solving**: Runs multiple algorithms in parallel, returns first result
- **Structured output**: Returns proper Rust types, no stdout parsing
- **Transformation support**: Can preprocess problems for better solving
- **No external dependencies**: Self-contained, no external solver binaries required

### Known Limitations

- **Complex invariants**: May struggle with polynomial/factorial invariants
- **Limited benchmarking**: Not extensively tested on CHC-COMP benchmarks

## Typed Compiler Backend

**Enable:** `trust-mc-driver/default-features = false, features = ["native-typed-chc-pdr"]`.

**Source:** `trust-mc-driver::native::NativeTypedChcPdrRunner`,
`trust-mc_core::ChcPdrSolveRequest`, and
`trust-mc_trust_bmc::trust-mc_chc_pdr_obligations_from_native_bundle`.

This is the in-process compiler verifier backend for Rust MIR/trust_ir handoff. It
accepts `trust-mc_core::MirChcPdrObligation` values with typed `ChcVc` relations,
rules, query target, trust_ir lineage/compiler-fact metadata, and trust_ir native replay
metadata. Production CHC/PDR decisions lower the typed VC directly into
`ay_chc::ChcProblem`; SMT-LIB rendering is not used for routing or proof
decisions.

`solve_full_verification` returns:

- `ChcPdrSolveOutcome`: typed solver status and CHC/PDR statistics.
- `FullVerificationVerdict`: proof-strength-explicit evidence with transcript,
  replay log, checked proof report, typed CHC problem digest, and PDR invariant
  model when available.
- `FullVerificationCacheKey`: covers trust-mc version/commit/dirty bit, ay identity,
  trust_ir snapshot/replay metadata, proof mode/options/resource limits, normalized
  input hash, and obligation-set hash.
- `artifact_directory`: deterministic path derived from the cache key.

Compiler integrations that require exact-module proof authority must call
`NativeTrustIrChcPdrRunner::solve_bundle_native_proof_grade` and retain the
opaque authority borrowed from each live response with `authorized_native_proof`.
That bundle entry point performs full module validation, conservative semantic
preflight, fresh translation, and private seal recomputation. The serialized
transport record and public `FullVerificationVerdict` remain diagnostic
candidates and cannot restore or replace that in-process authority.

The generic `NativeTypedChcPdrRunner::solve_native_proof_grade` and
`solve_typed_chc_pdr_native_proof_grade` names are compatibility entry points.
They accept source-unbound typed obligations and therefore fail closed rather
than minting exact-module authority. Likewise,
`trust-mc_core::accepted_native_typed_chc_pdr_proof` rejects public CHC/PDR
candidates pending fresh consumer replay; compiler integrations must not treat
those public values as Trust-admissible proofs.

The trust_ir dependency is pinned to the single exact revision declared by the
trust-mc member manifests. That authority requires every native request to carry
replay identity plus transcript digest. trust-mc preserves that identity and
`NativeReplayContext` atoms in native CHC metadata, including atom payload
digests and obligation/assertion/span bindings. `scripts/check-shared-pins.sh`
rejects divergent declarations or a pin that is not the live private
development main.

Current API request: ay-chc should expose replay log, checked proof report,
invariant/counterexample artifact bytes, and their digests as typed API outputs.
trust-mc currently packages accepted metadata and invariant debug output into
digest-backed evidence artifacts at the adapter boundary.

## Current Default Behavior

```
CHC/HORN query detected:
└── Native ay-chc portfolio solver
    ├── PDR (two variants)
    ├── BMC
    ├── PDKIND
    └── TPA
```

The `auto` solver mode uses the native ay-chc portfolio solver for all CHC queries.

## Related Issues

- #866: Integrate ay-chc LemmaHintProvider for domain-specific hints
- #867: Complete ay_dpll native API coverage

---
Document created: 2026-01-28 by Researcher
Updated: 2026-06-13 (AY is the sole solver; native `ay-chc` portfolio)
Part of #868, #4224
