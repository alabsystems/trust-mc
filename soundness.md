<!-- Copyright 2026 Andrew Yates -->
<!-- SPDX-License-Identifier: Apache-2.0 OR MIT -->
<!-- dscan:allow(volatile_numbers) -->
<!-- Author: Andrew Yates <andrewyates.name@gmail.com> -->

# Soundness Boundaries

trust-mc's current trust boundary is defined by three category families in
`trust-mc-driver/src/unsoundness_counts.rs:29-86`: **17 demoted**, **5
fail-closed**, and **12 sound-approximation** categories. The metadata enum in
`trust-mc-metadata/src/diagnostics.rs:27-69` carries the same split, and the driver
has a compile-time coverage assertion so new categories cannot silently escape
classification.

- false-`PROOF` or replacement-quality hard gates that demote successful
  results to failure,
- sound over-approximations that keep `PROOF` but qualify it with
  `sound_fallback_count`, and
- fail-closed paths that force conservative failure or `UNKNOWN` instead of
  risking a false `PROOF`.

`PROOF` with `sound_fallback_count = 0` is the strongest result surface trust-mc
currently exposes; new fallback usage on a previously zero-fallback harness is
an encoding-quality regression (see "Strongest Proof Surface" below). `scripts/zero_fallback_canary.sh` implements that comparison over the
per-harness compiletest report (roadmap item 6.1, landed).

## U* False-PROOF / Replacement-Quality Hard Gates

These categories are listed in `DEMOTED_CATEGORIES`. If any of them fire, the
driver demotes `PROOF` to failure and records the reason in
`demotion_reasons`.

| ID | Category | Source | User-visible signal | What a result means |
|----|----------|--------|---------------------|---------------------|
| U1 | `constant_zero_fallback` | `trust-mc-metadata/src/diagnostics.rs:371-381` | `demotion_reasons` | MIR constants that could not be extracted were replaced with zero. Any apparent `PROOF` is invalid and is demoted. |
| U2 | `internal_workaround` | `trust-mc-metadata/src/diagnostics.rs:584-594` | `demotion_reasons` | Pre-inlined collection internals were modeled with symbolic workarounds. Successful runs are treated as untrusted and demoted. |
| U3 | `chc_fallback` | `trust-mc-metadata/src/diagnostics.rs:252-260` | `demotion_reasons` | CHC encoding used type/size fallback defaults. A surviving `PROOF` would rely on fallback widths and is therefore rejected. |
| U4 | `type_sort_fallback` | `trust-mc-metadata/src/diagnostics.rs:521-534` | `demotion_reasons` | Type resolution fell back to a hard-coded sort such as `bv32`. Proof obligations no longer match the real Rust type widths. |
| U5 | `signedness_fallback` | `trust-mc-metadata/src/diagnostics.rs:543-556` | `demotion_reasons` | Signed/unsigned intent could not be recovered, so codegen used an operation-specific default. Division, remainder, and cast semantics may be wrong. |
| U6 | `unsupported_construct_fallback` | `trust-mc-metadata/src/diagnostics.rs:663-676` | `demotion_reasons` | An unsupported construct continued with fallback data instead of stopping. The model can diverge from real Rust semantics, for example by defaulting enum state. |
| U7 | `unconstrained_assignment` | `trust-mc-metadata/src/diagnostics.rs:685-700` | `demotion_reasons` | BMC left an SSA assignment unconstrained after `codegen_rvalue` returned `None`. The solver could invent values the program never produces. |
| U8 | `bmc_store_coercion_fallback` | `trust-mc-metadata/src/diagnostics.rs:702-714` | `demotion_reasons` | BMC substituted fresh symbolic store values when array element sorts did not line up. A proof can depend on values the real program never wrote. |
| U9 | `store_dropped_transition` | `trust-mc-metadata/src/diagnostics.rs:304-315` | `demotion_reasons` | CHC store translation dropped a state update, so downstream reads may see stale or symbolic values. |
| U10 | `diverging_call_drop` | `trust-mc-metadata/src/diagnostics.rs:411-423` | `demotion_reasons` | A diverging call was claimed by dispatch but emitted no rule, silently pruning a path unless demoted. |
| U11 | `kani_mem_overapprox` | `trust-mc-metadata/src/diagnostics.rs:723-735` | `demotion_reasons` | `kani::mem` predicates were over-approximated as `true`. Replacement-quality proofs hard-gate on this because the harness has no concrete memory-safety assurance from those predicates. |
| U12 | `inferable_predicate` | `trust-mc-metadata/src/diagnostics.rs:462-477` | `demotion_reasons` | A call was summarized with an uninterpreted, solver-inferable predicate. This can be useful diagnostically, but it is not trusted as replacement-quality proof evidence. |
| U13 | `fp_bitvector_encoding` | `trust-mc-metadata/src/diagnostics.rs:782-791` | `demotion_reasons` | Floating-point values were modeled as bitvectors instead of SMT FP sorts, losing IEEE 754 rounding and NaN semantics. |
| U14 | `rounding_assertion_bypass` | `trust-mc-metadata/src/diagnostics.rs:830-840` | `demotion_reasons` | A float rounding assertion was weakened to a finiteness tautology. The assertion is not checked as written, so any apparent proof is demoted. |
| U15 | `offset_provenance_unresolved` | `trust-mc-metadata/src/diagnostics.rs:432-446` | `demotion_reasons` | Pointer-offset provenance could not be resolved, so the offset's base allocation is unknown to the model. |
| U16 | `vec_field_fallback` | `trust-mc-metadata/src/diagnostics.rs:622-633` | `demotion_reasons` | Vec field selection fell back to a fresh symbolic because the base sort was not a datatype. Reclassified from sound-approximation: minting a solver-controlled symbolic for a program-produced value can mask a real violation. |
| U17 | `pointee_synthesis_fallback` | `trust-mc-metadata/src/diagnostics.rs:642-654` | `demotion_reasons` | Pointer dereference codegen synthesized an unconstrained symbolic value because tracking was incomplete. Reclassified from sound-approximation for the same reason as U16. |

## O* Over-Approximation / Weakened-PROOF Interpretation

These categories are listed in `SOUND_APPROXIMATION_CATEGORIES`. They do not
demote `PROOF`, and all but `chc_sound_havoc_drop` increment
`sound_fallback_count` and therefore mark the result as weaker than a
zero-fallback proof. For non-`PROOF` runs, the same
counts also feed `ctrex_category` and `unknown_quality`.

| ID | Category | Source | User-visible signal | What a result means |
|----|----------|--------|---------------------|---------------------|
| O1 | `assume_dropped_transition` | `trust-mc-metadata/src/diagnostics.rs:287-295` | `sound_fallback_count` | CHC dropped one or more `kani::assume` guards. The solver explored a superset of behaviors, so `PROOF` is weaker and `CTREX` may be less actionable. |
| O2 | `chc_coerce_eq_drop` | `trust-mc-metadata/src/diagnostics.rs:269-278` | `sound_fallback_count` | Call-result equality constraints were dropped after a sort mismatch, leaving destinations unconstrained. |
| O3 | `chc_translation_drop` | `trust-mc-metadata/src/diagnostics.rs:324-362` | `sound_fallback_count` | Place, constant, or projection translation returned `None`, so the affected state remained unconstrained. |
| O4 | `into_option_drop` | `trust-mc-metadata/src/diagnostics.rs:565-575` | `sound_fallback_count` | `Result::Err` was converted to `None`, which skipped a translation path and weakened the resulting constraints. |
| O5 | `abstracted_fallback` | `trust-mc-metadata/src/diagnostics.rs:603-613` | `sound_fallback_count` | Pre-inlined UTF8/Cow/String internals were approximated with fresh symbolic values instead of precise semantics. |
| O6 | `unhandled_calls` | `trust-mc-metadata/src/diagnostics.rs:390-402` | `sound_fallback_count` | A call fell through dispatch and returned an unconstrained value. The path is still explored, but with weakened semantics. |
| O7 | `sort_harmonize_fresh_var` | `trust-mc-metadata/src/diagnostics.rs:737-750` | `sound_fallback_count` | Phi merge harmonization introduced fresh symbolic values after flatten/unflatten or sort mismatch failures. |
| O8 | `ptr_metadata_unconstrained` | `trust-mc-metadata/src/diagnostics.rs:759-769` | `sound_fallback_count` | Pointer metadata such as slice length or vtable was replaced with an unconstrained symbolic value. |
| O9 | `static_init_incomplete` | `trust-mc-metadata/src/diagnostics.rs:771-780` | `sound_fallback_count` | Static initialization could not be reconstructed from the allocation, so the static stayed unconstrained. |
| O10 | `aggregate_encoding_gap` | `trust-mc-metadata/src/diagnostics.rs:793-817` | `sound_fallback_count` | Aggregate or discriminant construction fell back to a fresh symbolic because precise ADT encoding was unavailable. |
| O11 | `stub_approximation` | `trust-mc-metadata/src/diagnostics.rs:819-828` | `sound_fallback_count` | A CHC stub returned a fresh symbolic value instead of a precise modeled result. |
| O12 | `chc_sound_havoc_drop` | `trust-mc-metadata/src/diagnostics.rs:346-361` | (excluded from `sound_fallback_count`) | The recognized-clean subset of translation drops (certified fresh havoc). A spurious counterexample is still tagged `OverApproximation`, but the driver excludes this category from the sound-fallback proof qualifier, so an all-SoundHavoc proof still counts as clean. |

## F* Fail-Closed / Conservative Failure

These categories are listed in `FAIL_CLOSED_CATEGORIES`. They are allowed to
increase false failures or `UNKNOWN`, but they must not leave a false `PROOF`
behind.

| ID | Category | Source | User-visible signal | What a result means |
|----|----------|--------|---------------------|---------------------|
| F1 | `assert_untranslatable` | `trust-mc-metadata/src/diagnostics.rs:479-484` | explicit fail-closed rule | CHC could not translate an assertion operand, so it emitted a conservative failing rule. Expect extra failures, never a trusted proof from that path. |
| F2 | `heap_check_untranslatable` | `trust-mc-metadata/src/diagnostics.rs:493-498` | explicit fail-closed rule | Heap predicates that could not be translated are forced into conservative failure rather than silently skipped. |
| F3 | `heap_check_unknown_layout` | `trust-mc-metadata/src/diagnostics.rs:507-512` | explicit fail-closed rule | Unsupported layout-sensitive heap checks are rejected conservatively. |
| F4 | `iterator_unsoundness` | `trust-mc-metadata/src/diagnostics.rs:197-208` | forced failure plus warning | Iterator verification was skipped because iterator sorts were not representable. The path is forced away from `PROOF` rather than silently trusted. |
| F5 | `bigint_unsoundness` | `trust-mc-metadata/src/diagnostics.rs:234-243` | forced failure plus warning | BigInt or BigRational verification could not be expressed faithfully, so the affected path fails closed instead of yielding a false proof. |

## Strongest Proof Surface

The current strongest proof surface is defined as:

1. verdict is `PROOF`
2. `sound_fallback_count` is absent or `0`

Those zero-fallback harnesses are the best regression canaries for exact
semantics. If a previously zero-fallback harness starts reporting
`sound_fallback_count > 0`, encoding quality regressed even if the top-line
verdict stayed `PROOF`. `scripts/zero_fallback_canary.sh` (roadmap item 6.1)
automates this check over the per-harness compiletest report.

## Discriminating Regression Guards

Tests whose primary purpose is to guard a named correctness regression carry a
`DISCRIMINATING: #N` comment. Use this marker only when all three are true:

1. the test protects a specific issue or fix,
2. reverting that fix would make the test fail or flip verdict, and
3. the comment can explain the regression in one or two lines.

**Per-test form** (for mixed unit-test files):

```rust
/// DISCRIMINATING: #2660 — dropped SMT assert commands must demote Success to Failure.
/// Reverting the demotion fix would turn this into a false positive.
#[test]
fn test_failed_assert_demotes_result() { ... }
```

**File-level form** (for single-lineage compiletest files):

```rust
//! DISCRIMINATING: #155 — stale SSA path-condition regressions.
//! Any PASS/PROOF result here means the false-proof bug resurfaced.
```

Do not use this marker for generic smoke tests, broad coverage additions, or
unresolved open-gap harnesses that only document current limitations.

## Machine-Checked False-PROOF Ledger

Closed false-`PROOF` lineages are pinned in
`tests/ay/soundness_ledger.toml`. `cargo test -p trust-mc-driver soundness_ledger`
validates that every ledger entry still points at a real `tests/ay/` fail
harness, that the file still carries `kani-verify-fail`, and that each accepted
verdict is advertised by either `kani-expect:` or
`soundness-accepted-verdict:`. The latter is for deliberate fail-closed
non-`PROOF` outcomes where CTREX remains preferred but UNKNOWN/ERROR is accepted
to prevent a false proof. This is the repo-local fail-closed contract for the
current soundness regression corpus.
