# Troubleshooting UNKNOWN verdicts

Author: Andrew Yates <andrewyates.name@gmail.com>

When trust-mc returns `verdict=UNKNOWN`, the driver now prints a category tag on the
next line (`[AY:UNKNOWN-CATEGORY] ...`) so you can triage without reading SMT.

| Category tag | Meaning | Remediation |
|---|---|---|
| `≥2 Array-sorted state parameters` | A predicate has ≥2 `Array` sorts in its argument list, hitting the ay-chc Array-param invariant-synthesis limit. | Track or contribute to #4259 (heap-to-scalar promotion). Consider promoting small fixed-size arrays to scalar state vars. |
| `PDR invariant synthesis timeout` | All portfolio engines ran out of budget without producing a result. | Increase `--harness-timeout`, simplify loop invariants, or add a loop-hint via `--ay-chc-loop-hints`. |
| `solver error (engine=X)` | No engine completed and none timed out — all returned `NotApplicable` / `Disabled` / `Unknown`. | Engine misconfiguration or unsupported problem class. File a bug with the SMT artifact. |
| `no error rule encoded` | VC had `(query error)` but no rule derives it (see #4284). Degenerate / vacuous. | Confirm your harness has a reachable assertion. |
| `uncategorized` | None of the above matched. | Re-run with `--verbose` and inspect the per-engine budget report. |

## Top 10 "my harness doesn't verify" failure modes

These are the highest-frequency failure shapes we see when a harness that looks
reasonable still fails to verify under trust-mc.

### 1. Unsupported intrinsic (`UNSUPPORTED` / `ERROR`)

Symptom:
- The report says a construct "is not currently supported by trust-mc", or the run
  terminates as `ERROR` around an intrinsic-heavy code path.

Diagnosis:
- trust-mc reached an intrinsic or library operation that does not have a complete
  lowering or stub yet.
- The intended graceful surface is an unsupported result. If trust-mc ICEs or
  panics instead, that is a bug, not expected behavior. Track
  [#4297](https://github.com/alabsystems/trust-mc/issues/4297).

Fix:
- Reduce the harness to the smallest intrinsic call that triggers the failure.
- Check [rust-feature-support.md](./rust-feature-support.md) before assuming the
  intrinsic should already work.
- If the tool crashes instead of surfacing unsupported, file an issue with the
  reduced repro and mention `#4297`.

### 2. `#[cfg(kani)]` library proof cannot see a dev-dependency

Symptom:
- A proof under `src/` fails with `error[E0432]: unresolved import ...` for a
  crate that is listed under `[dev-dependencies]`.

Diagnosis:
- `targo trust-mc` without `--tests` builds the library target alone, so
  `dev-dependencies` are not resolved.
- This is the current documented workaround shape, tracked under
  [#4302](https://github.com/alabsystems/trust-mc/issues/4302) and
  [#4298](https://github.com/alabsystems/trust-mc/issues/4298).

Fix:
- Gate the proof with `#[cfg(all(kani, test))]`, not just `#[cfg(kani)]`.
- Run `targo trust-mc --tests`.
- See the worked example in [usage.md](./usage.md#using-dev-dependencies-in-library-proofs).

### 3. `UNKNOWN`: `≥2 Array-sorted state parameters`

Symptom:
- The run ends in `UNKNOWN` and the next line is
  `[AY:UNKNOWN-CATEGORY] ≥2 Array-sorted state parameters ...`.

Diagnosis:
- The CHC predicate shape currently exceeds the native array-parameter
  invariant-synthesis limit.
- This is the tracked heap-to-scalar promotion gap in
  [#4259](https://github.com/alabsystems/trust-mc/issues/4259).

Fix:
- Prefer smaller heap shapes in the harness when possible.
- Split a large proof into helper harnesses that isolate one array-rich phase at
  a time.
- If the array is small and fixed-size, try a heap-to-scalar refactor or a
  scalarized model while `#4259` is still open.

### 4. `UNKNOWN`: PDR invariant synthesis timeout

Symptom:
- The harness stays in CHC long enough to hit a timeout and reports
  `PDR invariant synthesis timeout`.

Diagnosis:
- The solver did not find a usable invariant within the current budget.
- This is common when the loop state mixes arithmetic, arrays, and multiple
  control branches.

Fix:
- Raise `--harness-timeout` and keep `-Z unstable-options` enabled.
- Simplify the harness so the loop state is smaller or more local.
- Prefer invariants that are easy to discover from the loop body instead of
  relying on deep solver search.

### 5. `UNKNOWN`: `no error rule encoded`

Symptom:
- The tag line says `no error rule encoded (see #4284)`.

Diagnosis:
- trust-mc did not encode a reachable error rule for the harness, so the query is
  vacuous or degenerate.
- This often happens when the harness has no assertion or the assertion is
  unreachable under the assumptions.

Fix:
- Make sure the harness actually contains a reachable `assert!` or equivalent
  failing condition.
- Double-check that `kani::assume()` has not ruled out every interesting path.
- Track follow-up work under
  [#4284](https://github.com/alabsystems/trust-mc/issues/4284).

### 6. `CTREX` on symbolic floats that "should be equal"

Symptom:
- A float-heavy harness returns `CTREX`, often on exact equality or arithmetic
  identities that look harmless.

Diagnosis:
- trust-mc currently encodes symbolic floats through BV arithmetic in the affected
  path, not full IEEE-754 reasoning.
- That can produce real-looking counterexamples for properties that only hold
  under idealized float semantics.

Fix:
- Avoid exact-equality claims on symbolic float arithmetic when a tolerance or
  structural reformulation is enough.
- Minimize the float expression and compare it against the tracked
  float-BV-fallthrough note (issue #1739, ctrex-fail recovery classification).
- If the property truly needs precise symbolic float support, file the reduced
  case as an upstream AY-theory blocker.

### 7. BigInt or `HashMap` proof fails with a sort mismatch

Symptom:
- A harness using `BigInt` or a symbolic-key `HashMap` fails with sort mismatch,
  translation drop, or unexpected `CTREX`/`UNKNOWN`.

Diagnosis:
- The failing path is usually not "BigInt is unsupported"; it is a specific
  operand, constant, or aggregate translation mismatch.
- The failing shape is usually covered by the operand-translation
  completeness audit (2026-04-16).

Fix:
- Sanity-check the exact value and key types flowing into the failing
  expression.
- Reduce the proof to the smallest operation that still triggers the mismatch.
- Compare the failing type shape against the gaps called out in the design doc
  before filing a bug.

### 8. Array-heavy function returns `UNKNOWN` even though the logic is simple

Symptom:
- The core function is small, but any harness that touches arrays or array-like
  heap state ends in `UNKNOWN`.

Diagnosis:
- The solver may be spending all of its budget on array-state reasoning rather
  than on the control flow or arithmetic you care about.
- This is adjacent to the same heap-to-scalar promotion gap tracked under
  `#4259`.

Fix:
- Rewrite the harness around scalar summaries of the array where practical.
- Inline a small fixed-size model instead of the full heap representation.
- If you can show that a scalarized version proves quickly while the original
  stays `UNKNOWN`, attach both to the issue; that is strong evidence for
  heap-to-scalar work.

### 9. A `std` collections method is missing a stub

Symptom:
- The proof gets stuck on a collection helper such as a `Vec`, `HashMap`,
  iterator, or string-adjacent method that exists in normal Rust but does not
  verify cleanly in trust-mc.

Diagnosis:
- The method body may compile, but the verification path still depends on a
  stub or dispatch case that has not been implemented yet.
- This is especially common on collection combinators and less frequently used
  convenience methods.

Fix:
- Reduce the failure to the smallest method call that still reproduces it.
- Search the existing issue tracker before opening a duplicate.
- File the bug with the `stdlib-stubs` label so it lands in the right backlog.

### 10. `CTREX` appears after a AY bump on a harness that used to `PROOF`

Symptom:
- A previously stable proof flips to `CTREX` right after changing the pinned AY
  revision.

Diagnosis:
- This may be a real solver regression, a changed heuristic in the CHC
  portfolio, or a trust-mc integration mismatch against the new AY revision.

Fix:
- Run the AY bump guardrails first: `scripts/check-ay-pin.sh`, then
  `cargo check -p trust-mc-driver --all-targets --features "ay,ay-chc-native"`,
  then the corpus suites (`scripts/ay-compiletest.sh`,
  `scripts/ay-soundness-gate.sh`). The single `ay-bump-canary.sh` wrapper for
  this ceremony is planned but NOT yet implemented (roadmap item 6.1).
- If the failure reproduces on the corpus suites, keep the reduced artifact and
  file a AY issue with the same reproducer.
- If it only reproduces in trust-mc and not in the corpus flow, file it in trust-mc as
  a backend-integration regression.
