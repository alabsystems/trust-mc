<!--
Copyright 2026 Andrew Yates
SPDX-License-Identifier: Apache-2.0 OR MIT
-->

# kani-domination

The **Kani-replacement burndown harness**. It downloads Kani's *upstream*
source, runs trust-mc over Kani's own test/benchmark corpus, and measures how
much of Kani trust-mc actually replaces — the trust-mc analogue of AY's
`ay z3-audit` / `ay bench --reference-solver z3` "domination" tooling.

The replacement criterion has three parts — every Kani test case, the same
verdict, and **as good or better runtime and memory** — so the tool measures
all three: every row records its wall time and peak memory, the same runner
drives upstream Kani over identical units under identical oracles
(`run --engine kani`), and `compare` joins the two results files row for row
(see "Two engines, one oracle" and "Per-unit resource accounting" below).

Where `tools/replacement-inventory` measures a **curated local** corpus
(`tests/trust-mc` + `tests/ay`), this tool measures the **full live Kani
corpus** fetched straight from `model-checking/kani` at a pinned revision, so the
denominator is "all of Kani" rather than a hand-picked subset.

## What it measures — verdict parity ("domination")

For each Kani harness it derives the verdict Kani **expects** (the *oracle*:
`// kani-verify-fail` / `// kani-check-fail` directives and `expected` files →
`fail`, otherwise `success`), runs trust-mc on the same file, parses trust-mc's
`VERIFICATION:- …` line plus its `[AY:…]` soundness markers, and classifies the
comparison:

| Class | Meaning |
|---|---|
| `parity` | verdict matches AND (if success) a **genuine** proof — zero soundness fallback. The only class that counts as real domination. |
| `unsupported` | trust-mc hit an unsupported construct / codegen panic and conservatively reported failure. The clearest **trust-mc codegen-gap** signal. |
| `false_positive` | oracle=success, trust-mc=fail via a real solver disagreement (no unsupported marker). Conservative, but a parity miss. |
| `missed_bug` | oracle=fail, trust-mc=success. **Soundness-critical** — trust-mc proved safe where Kani finds a bug. |
| `unsound_pass` | verdict matched, but the success was reached via a sound over-approximation / fallback (the `[AY:SOUND_FALLBACK:N]` marker or the `sound_fallback=N` proof qualifier), or a SUCCESSFUL harness carries a proof qualifier the scorer does not recognise — not a real proof. |
| `trivial_safe_pass` | verdict matched, but a SUCCESSFUL harness carries the proof qualifier `trivial_safe=no_error_rule`: no CHC rule derives `error`, which the compiler calls lost checks, not proved checks. Not a proof; outside parity (scorer version 5, "Proof qualifiers" below). |
| `unattributed_pass` | verdict matched, but a SUCCESSFUL harness carries `unattributed_check=chc.0`: every check is the anonymous `chc.0` fallback, which names no property. Outside parity (scorer version 5). |
| `unknown` / `error` / `timeout` | indeterminate verdict / tool error / watchdog kill. |
| `crash` | the verifier (or its compiler subprocess) died on a signal (SIGABRT, …) — a hard trust-mc defect, kept out of the generic `error` bucket. |
| `build_unavailable` | a cargo-project test whose dependencies cannot be built in this environment (registry/network) — environmental, not a verifier defect. |
| `skipped` | excluded from the run (e.g. by `--limit`); recorded in the denominator. |

### Multi-harness success: every harness, and self-reports per harness

A file-level `SUCCESSFUL` needs **every** harness to report `SUCCESSFUL`
(`runner::parse_verdict`): any `VERIFICATION:- INCONCLUSIVE` line, or a
`Checking harness` section with no `SUCCESSFUL` verdict of its own, makes the
observed verdict `unknown` (reason: `a harness did not report SUCCESSFUL beside
SUCCESSFUL sibling(s)`), and an `INCONCLUSIVE` line counts as an indeterminate
verdict rather than a tool error. Until 2026-09-14 one `SUCCESSFUL` line was
enough, so a clean harness beside an INCONCLUSIVE one scored `parity` — or
`unsound_pass`, when the INCONCLUSIVE harness's own section happened to print
a self-report (`unconstrained_assignment` inside `[AY:UNKNOWN_QUALITY:…]`, a
demotion, a preamble warning).

A self-reported unsoundness confession now taints a success only through the
harness that printed it (`runner::self_report_taints_success`): only a section
that reports `SUCCESSFUL` carrying one makes the file `unsound_pass`. It stays
fail-closed wherever attribution is impossible: a single-harness run, a
multi-harness run with no `Manual Harness Summary:` line, or a confession
printed outside every section (preamble, summary, stderr). The row's
`self_reported_unsound` field still records the whole run.

Measured by `rescore` (rules otherwise at this commit), the verdict rule moves:

* `results-verification-bmc` (19 rows): `unsound_pass -> unknown` for the five
  fixtures in `src/fixtures/self-report/` (`kani/Intrinsics/Atomic/Stable/AtomicPtr/main.rs`,
  `kani/Invariant/percentage.rs`, `kani/ProjectionElem/OpaqueCast/check_opaque_cast.rs`,
  `kani/Stubbing/StubPrimitives/stub_slice_methods.rs`,
  `kani/Coroutines/rustc-coroutine-tests/smoke.rs`); `parity -> unknown` for
  `kani/SwitchInt/main.rs`, `kani/Intrinsics/SIMD/Shuffle/main.rs`,
  `kani/BitwiseShiftOperators/shift_neg_vals.rs`,
  `expected/loop-contract/multiple_loops.rs`,
  `expected/function-contract/trait_impls/associated_fn.rs`; `parity ->
  vacuous` for `std-checks/core/mem.expected`, `kani/Stubbing/trait_methods.rs`,
  `kani/Intrinsics/typed_swap_nonoverlapping.rs`,
  `kani/AggregateRvalue/slice_ptr.rs`; `error -> unknown` for
  `kani/Print/main.rs`, `kani/Intrinsics/NonRet/abort.rs`.
* `results-verification-chc-m1`: `parity -> vacuous` for
  `std-checks/core/mem.expected`, `kani/NondetVectors/main.rs`,
  `kani/MemPredicates/foreign_type.rs`,
  `kani/Intrinsics/typed_swap_nonoverlapping.rs`; `error -> unknown` for
  `expected/bounded-arbitrary/string/string.rs`.
* The Kani reference file (`results-verification-kanisrc`): no row.

### Kani's unsupported-construct check, reproduced

For a construct upstream Kani does not encode (an `Intrinsic::Unimplemented`
such as `volatile_set_memory`, a foreign function reached through a fn
pointer), Kani emits a check `<construct> is not currently supported by Kani`
that FAILS when reached, and a fail-oracle expected file names it
(`expected/foreign-function/expected`, `expected/report/unsupported/reachable/expected`,
…). The engine now reproduces that check (`emit_kani_unsupported_check`,
`fix/stub-gaps2`) and records it as the approximation
`kani_unsupported_construct_check`, unidentified on purpose, so the driver never
certifies such a failure Genuine and prints
`[AY:CTREX_CAT:OverApproximation:kani_unsupported_construct_check=N]`. Scored
by the verdict rules alone that is `unknown`, although Kani's compiletest
passes it.

`runner::unsupported_check_parity` credits `parity` (note: `parity: the
harness(es) the expected file names fail on exactly Kani's unsupported-construct
check …`) only when **all** of these hold: the trust-mc engine; a fail oracle
that is not compile-fail; an expected file naming at least one such check and
every expected line(-block) present in the output; the FAILED harnesses are
exactly the ones the expected file names (`Verification failed for -`, or every
FAILED harness when it names none) and every other harness is a clean
SUCCESSFUL; in each failing harness every FAILURE check is an
unsupported-construct check the expected file names; every `[AY:CTREX_CAT:…]`
there is `Genuine` or `OverApproximation` whose every entry is
`kani_unsupported_construct_check=N`; and no UNKNOWN reason, inconclusive
solver, demotion or encoding-gap evidence. Anything else — a failing check that
is another property, an extra failing check, another approximation reason, an
`EncodingGap` / `Unknown` / missing category, a missing expected line, an
unnamed failing harness, a tainted sibling — keeps the class the verdict rules
give. A SUCCESSFUL never reaches the rule: against a fail oracle it is
`missed_bug`. Fixtures: the two expected files verbatim with synthetic
transcripts (`src/fixtures/unsupported-check/`). A unit with no expected file
(`kani/VolatileIntrinsics/core_intrinsics.rs`, a `kani-verify-fail` exit-status
test) names no check, so the rule cannot apply to it.

Measured by `rescore`: no row of chc-m1 or bmc moves under this rule — their
logs predate the engine change, so they carry no
`kani_unsupported_construct_check` category.

### Certified no-checks successes: the `parity-no-checks` sub-column

For a harness whose obligation set is empty and whose body the compiler
certified obligation-free (D16), the driver prints
`[AY:PROOF_QUALIFIERS:no_checks=compiler_certified_obligation_free]` and
`VERIFICATION:- SUCCESSFUL (no checks — compiler-certified obligation-free)`.
Nothing was proved because there was nothing to prove. Every row now records
`certified_no_checks`: how many harnesses of the run carry that qualifier (the
larger of the marker count and the verdict-line count; absent = 0). Before
2026-09-14 the runner had neither the field nor a parser, so every row read 0
although the driver printed both lines (the chc-m1 logs carry 25 of them in 23
unit logs).

Scoring is unchanged in kind: such a success is still `parity` against a
success oracle (Kani reports the shape SUCCESSFUL) and still `missed_bug`
against a fail oracle, and it can never be `exceeds_oracle`. The burndown
shows the parity rows that rest on one in a **`parity-no-checks` sub-column**
(of parity, not beside it): the headline's "of which no-checks", a per-suite
column, the unit list in the text report, and `parity_no_checks` in each scope
of the ledger row. Measured on chc-m1 under the rules through this change: 23
rows carry the qualifier — 20 parity (the sub-column), 2 `unknown`
(`kani/FunctionSymbols/issue1243.rs`, `kani/FloatingPoint/main.rs`, where a
sibling harness is undecided) and 1 `error` (`expected/unwind-flags-conflict/main.rs`,
a compile-fail oracle trust-mc verified).

### Proof qualifiers: `trivial_safe_pass` and `unattributed_pass`

The driver prints `[AY:PROOF_QUALIFIERS:<q>,<q>…]` once per harness whose
result is a success (`trust-mc-driver/src/harness_runner.rs`,
`proof_qualifiers_marker`), `clean` when the list is empty. Until scorer
version 5 the runner never read it: any `SUCCESSFUL` without a sound-fallback
count, a self-report or an `(UNVALIDATED)` suffix scored `parity`, whatever its
qualifiers said. Every qualifier the driver can print (grepped 2026-09-14 at
`43c591daa`):

| Qualifier | Printed by | Meaning | Scored |
|---|---|---|---|
| `clean` | `proof_qualifiers_marker`, list empty | no qualifier | unchanged |
| `no_checks=compiler_certified_obligation_free` | `settle_no_checks_result` (`harness_runner.rs`, D16) | empty obligation set, body certified obligation-free | unchanged: `parity` + `parity-no-checks`; `missed_bug` against a fail oracle; never `exceeds_oracle` |
| `trivial_safe=no_error_rule` | `interpret_chc_trivial_safe` (`call_ay/chc/native_result.rs`; constant in `call_ay/chc.rs`) | the CHC problem queries `error` and no rule derives it (below) | `trivial_safe_pass` |
| `unattributed_check=chc.0` | `unattributed_chc_check_qualifier` (`harness_runner.rs`, `f3bd8bc19`) | every non-cover check of the success is the anonymous `chc.0` fallback (`Property::is_unattributed_chc_check`), which names no property, so the proof cannot show that the expected assertions reached the encoding | `unattributed_pass` |
| `sound_fallback=N` | `proof_qualifiers_marker`, `sound_fallback_count > 0` (beside `[AY:SOUND_FALLBACK:N]`) | the encoding fell back somewhere | `unsound_pass` (as the marker already made it) |
| anything else | — | unknown to this scorer | `unsound_pass`, named `(unrecognised)` in the note |

Rules (`runner::success_taint`, `runner::section_success_taint`):

* A qualifier belongs to the `Checking harness` section that printed it. Only
  sections that report `SUCCESSFUL` count; a marker outside every section
  (preamble, summary, stderr) cannot be attributed and counts, fail-closed.
* The most severe qualifier over those sections decides the class:
  `unsound_pass` over `trivial_safe_pass` over `unattributed_pass`. `clean` is
  clean only alone; `clean` beside another qualifier, or an empty marker, is
  unrecognised.
* The three classes are outside parity and inside the denominator. Against a
  fail oracle the same success is `missed_bug`, and it is never
  `exceeds_oracle`. A multi-harness fail-oracle file whose failing harnesses
  are right takes the class of a qualified sibling success (the rule that has
  made a tainted sibling `unsound_pass` since version 2).
* The row records every qualifier (`proof_qualifiers`); the note names each
  tainting qualifier and the harnesses carrying it, also on a `missed_bug`.
  Reports: `trivial-safe` / `unattributed` columns (markdown),
  `trivial-safe-pass=` / `unattributed-pass=` and `tsp=` / `uap=` (text),
  `trivial_safe_pass` / `unattributed_pass` (ledger row).

**Why `trivial_safe=no_error_rule` is not parity.** The qualifier is a proof
that no check can fail only if the missing `error` rule means the checks were
discharged. The code says they were lost:

* **Driver.** `try_ay_chc_solver` (`call_ay/chc/native.rs`) short-circuits when
  the SMT has `(query error)` and `smt_error_query_is_trivially_safe` finds no
  satisfiable rule deriving `error`. The false-bodied `(rule (=> false error))`
  shape goes to `interpret_chc_false_error_safe` instead and stays `clean`. The
  per-property lane's `AllQueriesPruned` (AY pruned every query as vacuously
  safe) takes the same path, with the same qualifier. `interpret_chc_trivial_safe`
  reports `SUCCESSFUL` without a solver and lists every property of the
  artifact table (`property_report::chc_success_properties`) as SUCCESS, so the
  result is not empty. That keeps the D16 no-checks gate out of it:
  `no_checks_gate_fires` needs `results.is_empty()`.
* **Compiler.** `discharge_straightline_safety`
  (`trust-mc-compiler/src/codegen_ay/chc/straightline_proof.rs`) writes the
  unsat `(=> false error)` obligation only for a VC it proved. For a VC with
  registered properties and no error rule it refuses and warns `registered
  properties but no error rules (lost checks, not proved checks)`: the error
  rules were lost to a collapsed encoding (walk abort, const-prop plus orphan
  prune), not discharged, and two such shapes were 1-2 s false Safes (#67).
  Compiler tests assert functions keep an error-headed obligation "otherwise
  compiletest reports trivial_safe=no_error_rule"
  (`chc/tests/test_call_fn_ptr_function_symbols.rs`,
  `chc/tests/test_call_fn_inline_ptr_comparison_helpers.rs`).
* **Corpus.** chc-m1 carries 35 such markers in 25 unit logs, and each of those
  25 logs also carries that compiler warning on stderr. Three more logs carry
  the warning without the qualifier, all with FAILED or INCONCLUSIVE
  verdicts. In each of the 35 sections the harness is one Kani verifies: a
  success oracle, or a harness the expected file does not name as failed.
  Kani (`results-verification-kanisrc`) scores all 25 units parity. No corpus
  bug hid behind the shortcut, but no check was proved either. Hence a visible
  class outside parity.

The success-oracle transcripts in chc-m1 carry every assertion as SUCCESS and
nothing else to tell a lost encoding from a proved one, so the class is the
only honest place for them until the compiler keeps the error rules.

Fixtures (`src/fixtures/proof-qualifiers/`, stdout plus stderr, corpus path as
`/corpus`; reconstructions, since the log excerpts they were first cut from were
never committed under the root `.gitignore`'s `*.out` and are lost — each file
says so on its first line): chc-m1-shaped logs for `trivial_safe=no_error_rule`
(`kani/Assert/in_match.rs`, `kani/Cast/float_to_int_saturating.rs`,
`expected/offset-bounds-check/out_of_bounds_ub_check.rs` and `offset_from.rs`
with their expected files), `clean` (`kani/CodegenMisc/main.rs`) and the
certified no-checks qualifier (`kani/DynTrait/upcast.rs`), and a Trust-lane
driver log for `unattributed_check=chc.0` (`smack/structures/point.rs`). No
measured log carries `sound_fallback=N`; its tests use the driver's own
strings from `harness_runner_tests.rs`.

Measured by `rescore` (see scorer version 5 below).

### Compile-fail oracles

A Kani expected file with no verdict marker whose **only content is a
compile-time diagnostic or a Kani ICE** is a **compile-fail oracle**: oracle
`fail` with `check_fail`, the same shape as a `// kani-check-fail` header, and
never oracle `success` (`discover::compile_fail_basis`):

* **Diagnostic** — an `error:` / `error[E…]` line (or rustc's abort line, or
  the bare level token `error`), and no line of verification output
  (`Checking harness`, `Status:`, `VERIFICATION`, `Complete -`, a
  `SUCCESS`/`FAILURE` token, …). kani-compiler and kani-driver refusals printed
  at `error` level count too (`expected/unwind-flags-conflict`,
  `expected/function-stubbing-no-harness`): Kani refuses to verify either way.
* **Kani ICE** — `Kani unexpectedly panicked` / `internal compiler error`.
* **Manifest** — a file that quotes only a diagnostic's MESSAGE, which nothing
  in the file marks as one, is listed in `quarantine::COMPILE_FAIL_ORACLES`
  with upstream Kani's own output as evidence, and applies only while the file
  still carries the quoted text.

`warning:`-only files, CBMC runtime messages (`object-bits/insufficient`) and
report lines (`report/verification-time`) stay verdict-indeterminate text:
Kani verifies those units.

Such a unit is `parity` **only** when trust-mc also fails to compile with that
diagnostic (`runner::compile_failed_as_expected`): a nonzero exit, no
`VERIFICATION:-` line at all, every expected line(-block) in the output, and no
panic unless the oracle's diagnostic is one — the expected file quotes an ICE
banner, or its manifest entry is marked `upstream_ice` because upstream Kani
itself panics with the quoted message (`expected/offset-invalid-args/*`:
kani-compiler's `broken MIR` panic carries `Cannot offset …`, and so does
trust-mc's). A verification verdict of either polarity is `error`. Before this, these rows had a `success` oracle and the
verdict-less `contains_lines` arm credited them with no exit-status check, so
`expected/unwind-flags-conflict` scored parity on a trust-mc run that printed
the refusal and then `VERIFICATION:- SUCCESSFUL` with exit 0. The Kani engine
keeps its compiletest criterion (`contains_lines` for the `expected` suite).
`rescore` re-derives each row's oracle from its logged expected file
(`discover::rederive_oracle`) and prints every oracle that moved.

Measured at the pinned corpus: 22 verification units move from oracle
`success` to a compile-fail oracle — 11 by a diagnostic line, 1 by the ICE
banner, 10 by the manifest:

```
diagnostic  expected/function-contract/attribute_complain.rs
diagnostic  expected/function-contract/history/old_old.rs
diagnostic  expected/function-contract/history/ui/statement.rs   (bare `error`)
diagnostic  expected/function-contract/missing_contract_for_check.rs
diagnostic  expected/function-contract/missing_contract_for_replace.rs
diagnostic  expected/function-contract/modifies/check_invalid_modifies.rs
diagnostic  expected/function-contract/mutual_recursion_unsound.rs
diagnostic  expected/function-stubbing-no-harness/main.rs
diagnostic  expected/issue-2589/issue_2589.rs
diagnostic  expected/stubbing-ambiguous-path/main.rs
diagnostic  expected/unwind-flags-conflict/main.rs
ice         expected/intrinsics/sub_with_overflow_ice_fixme/arithmetic_zst_fixme.rs
manifest    expected/assert-arg-error/test.rs
manifest    expected/async_proof/main.rs
manifest    expected/function-contract/history/ui/noncopy_ignore.rs
manifest    expected/function-contract/history/ui/old_result.rs
manifest    expected/offset-invalid-args/invalid_offset_ty.rs
manifest    expected/offset-invalid-args/non_ptr_arg.rs
manifest    expected/stub-set-cycle/main.rs
manifest    expected/stub-set-invalid-entry/main.rs
manifest    expected/stub-set-not-a-stub-set/main.rs
manifest    expected/stubbing-type-mismatch-after-rename/main.rs
```

The files that already carried `error[E` / `error: aborting due to` (the
`simd-*` family, `transmute_diff_size`, `float-to-int-in-range/invalid_*`,
`panic/arg-error`, `ensures_with_two_mut_refs_fail`) were compile-fail oracles
before and are unchanged.

Every row also carries `scorer_version` (the classification rules it was
scored under; see "Scoring rules" below), `tiebreak_applied` (the Kani
`contains_lines` tiebreak turned a false positive into parity), and
`log_path` (the unit's full driver log, see "Per-unit logs and `rescore`").

Two lanes feed the classifier:

* **single-file** — the default: `trust-mc-driver <file.rs>` with the header
  `// kani-flags:`. If the test's Kani `expected` file is *diagnostic-only*
  (no verdict marker) and trust-mc emits no verdict but its output contains
  every expected line (Kani compiletest `contains_lines` semantics, including
  `\`-joined consecutive blocks), that is `parity` — Kani's own pass criterion
  for error-message tests.
* **cargo** — any test directory owned by a `Cargo.toml` becomes one unit per
  Kani `expected` / `*.expected` file (mirroring Kani's `cargo-kani` mode):
  the driver runs in its `cargo trust-mc` identity inside the package,
  `--harness <stem>` unless the file is the package-wide `expected`, and the
  expected file derives the oracle. Its verdict is then scored by the same
  rules as a single-file unit (a fallback-marked SUCCESS is `unsound_pass`;
  a FAILED goes through the counterexample-quality gate before it can be
  parity).

Discovery accepts every harness spelling the corpus uses: `#[kani::proof]`,
`#[kani::proof_for_contract(f)]`, the `cfg`-guarded
`#[cfg_attr(kani, kani::proof)]` / `#[cfg_attr(kani, kani::proof, kani::unwind(3))]`
/ `#[cfg_attr(kani, kani::proof_for_contract(f))]` forms, a
`#[kani::should_panic]`-decorated proof, and a bare `#[proof]`. Before
2026-09-12 only the `#[kani::proof` prefix was recognised, so eight
verification-scope files whose every harness is `cfg_attr`-guarded (one in
`expected`, seven in `kani`) were missing from the denominator: it is 1134
units at the pinned Kani rev, not 1126. `inventory --list` prints every
entry with its oracle, harness count, lane and expected file.

## Scoring rules — `scorer_version`

Every row, provenance sidecar and ledger row names the version of the
classification rules it was scored under, so rows scored under different
rules can never be read as one series. `run` refuses to resume a results
file whose rows carry another version, `burndown` refuses to ledger a mixed
file, and both reports print the version and the tiebreak count.

* **1** — every row before the field existed (ledger rows 1-62). A row or
  sidecar without the field reads as 1.
* **5** (2026-09-14) — the driver's proof qualifiers are read per harness
  section ("Proof qualifiers" above): `trivial_safe=no_error_rule` scores
  `trivial_safe_pass`, `unattributed_check=chc.0` scores `unattributed_pass`,
  and `sound_fallback=N` or any unrecognised qualifier scores `unsound_pass`;
  all are `missed_bug` against a fail oracle and never `exceeds_oracle`. New
  row field: `proof_qualifiers`; new classes and report / ledger columns
  `trivial_safe_pass`, `unattributed_pass`. `rescore` also accepts a row
  carrying the oracle re-derived from its own log. Version 4 refused every
  rescored file with a moved compile-fail oracle (its `unwind-flags-conflict`
  row), the Kani reference file included.

  Measured by rescoring `results-verification-chc-m1` (1134 rows, scorer 3,
  trust-mc `04d4e4e67`) under version 4 and under version 5, from the same
  logs. 23 rows move, all `parity -> trivial_safe_pass`:
  `kani/Assert/in_match.rs`, `kani/BitwiseShiftOperators/main.rs`,
  `kani/BitwiseShiftOperators/Usize/main.rs`,
  `kani/Cast/float_to_int_saturating.rs`, `kani/Closure/zst_unwrap.rs`,
  `kani/Count/Unstable/Cttz/main.rs`, `kani/DynTrait/std_lib_add_duplicate.rs`,
  `kani/Enum/niche.rs`, `kani/FloatToIntInRange/test.rs`,
  `kani/Intrinsics/Atomic/Unstable/AtomicNand/main.rs`,
  `kani/Intrinsics/ExactDiv/main.rs`, `kani/Intrinsics/PtrOffsetFrom/main.rs`,
  `kani/Intrinsics/PtrOffsetFromUnsigned/check_unsigned_ptr_offset_from.rs`,
  `kani/Intrinsics/discriminant_value.rs`, `kani/PointerOffset/offset_from.rs`,
  `kani/Vectors/issue-763.rs`, `expected/loop-contract/loop_with_true_invariant.rs`,
  `expected/loop-contract/while_let_loop_for_slice.rs`,
  `expected/reach/div-zero/unreachable/test.rs`,
  `expected/reach/rem-zero/unreachable/test.rs`, `expected/union/static_union.rs`,
  and the fail-oracle files `expected/offset-bounds-check/out_of_bounds_ub_check.rs`
  and `expected/offset-bounds-check/offset_from_unsigned.rs` (a qualified
  sibling success). The other two of the 25 qualified logs do not move:
  `expected/offset-bounds-check/offset_from.rs` stays `missed_bug`, its note
  now naming the qualifier, and `kani/Intrinsics/SIMD/Operators/bitmask.rs`
  stays `unknown` because a sibling harness timed out. Class totals: parity
  808 -> 785, trivial_safe_pass 0 -> 23, every other class unchanged.
  Verification parity is **793/1096 (72.4%) -> 770/1096 (70.3%)**;
  parity-no-checks stays 20 and missed bugs stay 2. No chc-m1 log carries
  `unattributed_check` (they predate `f3bd8bc19`) or `sound_fallback=`.
  `results-verification-kanisrc-v4` (Kani engine, 1134 rows, scorer 4): 0 rows
  move, oracles, notes and upstream-ignored tags are identical, and no row
  records a qualifier.
* **4** (2026-09-14) — five fail-closed changes, each with its own section
  below: upstream-ignored units score in a `fixme` column outside the
  denominator (missed bugs excepted); diagnostic-only and ICE expected files
  are compile-fail oracles; a file-level success needs every harness
  SUCCESSFUL and a self-report taints only the SUCCESSFUL harness that printed
  it; a failure on exactly Kani's unsupported-construct check the expected
  file names is parity; certified no-checks successes are counted
  (`certified_no_checks`, the `parity-no-checks` sub-column) and never
  `exceeds_oracle`. New row fields: `upstream_ignored`, `certified_no_checks`;
  new attestation fields: `load_start`, `load_end`, `trust_mc_jobs`.

  **How older rows compare.** A version-3 (or older) row is not comparable
  with a version-4 row as it stands: its oracle may be the old `success` for a
  compile-fail unit, it carries no `upstream_ignored` or `certified_no_checks`
  (they read as false / 0), and its class may rest on a rule version 4 closed.
  `run` refuses to resume such a file, `burndown` refuses a mixed file and
  `flips` refuses mixed tuples. `rescore` makes it comparable from its unit
  logs alone: it re-derives the oracle from the logged expected file, tags
  `upstream_ignored` from the log (older logs: compiletest's path rule) or the
  spec, and re-applies every rule. What it cannot recover is run state: host
  load and `trust_mc_jobs` are not in a version-3 sidecar, so a rescored file
  prints but never ledgers (plan D18). `rescore --out <path>` writes elsewhere
  than beside the input.

  Measured on `results-verification-chc-m1` (1134 rows, scorer 3, trust-mc
  `04d4e4e67`): 22 oracles move `success -> fail` (the compile-fail list), and
  7 classes move — `parity -> vacuous` for `std-checks/core/mem.expected`,
  `kani/NondetVectors/main.rs`, `kani/MemPredicates/foreign_type.rs`,
  `kani/Intrinsics/typed_swap_nonoverlapping.rs`; `parity -> error` for
  `expected/unwind-flags-conflict/main.rs`; `unknown -> error` for
  `expected/function-contract/mutual_recursion_unsound.rs`; `error -> unknown`
  for `expected/bounded-arbitrary/string/string.rs`. Raw class totals: parity
  813 -> 808, vacuous 11 -> 15, error 7 -> 8, every other class unchanged.
  Verification parity: 813/1130 (71.9%) under version 3 -> **793/1096
  (72.4%)** under version 4 — the denominator loses the 37 upstream-ignored
  units (15 parity, 10 unknown, 6 error, 3 corpus_invalid, 2 encoding_gap,
  1 false_positive) and the 1 remaining corpus-invalid unit; 20 of the 793 are
  parity-no-checks; missed bugs stay 2.
* **3** (2026-09-13) — the Kani engine is scored by Kani's own compiletest
  criterion per suite (see "Two engines, one oracle"): exit status for the
  `kani`-mode suites, `contains_lines` for the `expected` / `cargo-kani`
  ones; Kani's `unsupported_construct` lines never decide a class; a
  kani-driver panic is `error`; a file Kani finds no harness in is
  `vacuous`. The trust-mc rules are identical to version 2, so `rescore` of
  a trust-mc file moves no class; a trust-mc file at version 2 must still be
  rescored (its logs suffice) before `run` will resume it.
* **2** (2026-09-12) — fail-closed scoring. Every path that can credit a
  verdict checks its quality first:
  * A **cargo unit's** verdict is scored by the verdict rules like any other
    unit. Version 1 took the `contains_lines` arm for every cargo unit
    *before* the counterexample-quality gate, so an encoding-gap,
    over-approximated or demoted FAILED whose output happened to contain the
    expected summary lines scored `parity`. `contains_lines` now only
    decides **diagnostic-only** rows (no `VERIFICATION:-` verdict at all),
    and only when the output carries no `UNVALIDATED`, vacuous, fallback or
    demotion marker.
  * **`unsupported`** is never taken over a genuine counterexample. A FAILED
    verdict backed by a `Genuine` CTREX beside an unsupported-construct
    warning is the verdict: `parity` against a fail oracle, `false_positive`
    against a success oracle.
  * **The Kani tiebreak** (`contains_lines` on the false-positive arm) credits
    `parity` only when the expected file itself names exactly the harnesses
    trust-mc failed (`Verification failed for - <name>` lines — the one
    shape where the expected file vouches for a failing harness). An
    expected file that is silent about the failing harness (the
    `function-contract/modifies/field_replace_pass` shape) proves nothing
    about it, so the row stays `false_positive` with the refusal in its
    note. Such rows record `tiebreak_applied: true`; the reports and the
    ledger row print the count. Measured 2026-09-12: no expected file in the
    verification suites has the naming shape without also carrying
    `VERIFICATION:- FAILED`, so in this corpus the tiebreak never fires
    under version 2 — the rows version 1 credited through it are false
    positives to triage, and an explicit `quarantine::ORACLE_FIXUPS` entry
    (evidence-quoted) or an `--engine kani` run is the sanctioned route to
    credit.
  * A **multi-harness fail oracle** must agree on *which* harnesses fail: a
    harness the expected file names as failed that trust-mc verified is a
    `missed_bug`; an extra failing harness is a `false_positive` when the
    expected file's `Complete - … N failures` count shows its list is
    complete and `unknown` when the list may be partial; a genuine
    counterexample against a success oracle is a `false_positive` whatever
    a sibling harness did; and a sibling SUCCESS that is not a clean proof
    (fallback, `UNVALIDATED`, self-reported unsoundness) makes the file an
    `unsound_pass`, not `parity`.
  * Output carrying `[AY:SOLVER_PIN_MISMATCH:` is `error` on every path
    (unchanged from version 1).

`rescore` applies the current rules to an existing run without re-running
it (below).

## Per-unit logs and `rescore`

Every unit's driver invocation is written to
`<reports_dir>/logs/<results-file-stem>/<suite>/<file with "/" as "__">.log`
(overwritten when the unit is re-run) and the row records the path relative
to the reports directory (`log_path`; the sidecar's `log_root` names that
directory). The log is self-contained: a `key: value` header with the exact
argv, cwd, the variables set on and removed from the child, the exit code,
`timed_out`, whether the outer watchdog retried, `wall_ms`, `max_rss_kb`,
`tree_peak_rss_kb`, and the byte length of each section; then the expected
file's content (`=== EXPECTED ===`), the classified attempt's
`=== STDOUT ===` and `=== STDERR ===`, and — for a retried unit — the
killed first attempt's output after them. The declared lengths are what the
reader trusts, so a driver line that looks like a separator cannot corrupt
the split and a truncated log is refused. A trust-mc unit's header also names
its compiler `route` (`dev-cli` / `trustc`, the row's `route`), so a log read
on its own says which route produced it.

The unit log is the one per-unit output mechanism, on both engines and both
routes. It replaces the `KANI_DOMINATION_KEEP_OUTPUT=<dir>` attribution aid
(`<dir>/<route>/<suite>/<rel>.out`, the combined output of one unit, off by
default) that the Trustc-route work added in parallel: every unit's raw stdout
and stderr are now always kept, together with the argv and environment that
reproduce the unit, so a cross-route difference ("the trustc child exited
101") is attributed by comparing the two results files' `log_path`s. The runner
prints a notice and ignores the variable when it is set.

```bash
kani-domination rescore <reports>/results-verification.jsonl
#   -> <reports>/results-verification-rescored.jsonl (+ its sidecar, re-stamped)
```

`rescore` re-classifies every row from its log under the current scorer,
carries the measurements (timings, memory, flags, re-key provenance) over,
writes the sibling `<stem>-rescored.jsonl`, and prints every row whose
classification moved (`old -> new`, with the new note) plus per-class
totals. It is fail-closed: a row without a log (written before logs were
captured), a log that does not parse, or a log whose identity disagrees with
its row refuses the whole file, because a half-rescored file would be a
mixed-scorer file. Re-scoring a rescored file changes nothing: a row may carry
the oracle its log recorded or the one re-derived from that log (before scorer
version 5 only the former, so a rescored file whose compile-fail oracle had
moved was refused). The route checks
are part of the scorer, so `rescore` applies them exactly as `run` did: it
refuses a file whose rows mix routes or disagree with the sidecar (or a Trustc
file without one), checks each Trustc row's output against the sidecar's
`route_attestation`, re-applies the temporary harness-name normalization, and
refuses a row whose log names a different route than the row.

## Layered denominator

`--scope` selects which Kani suites count:

* **`verification`** (primary parity number) — `expected`, `kani`, `slow`,
  `smack`, `prusti`, `std-checks`.
* **`benchmark`** — `perf`.
* **`diagnostic`** — `ui`, `coverage`, `cargo-*`, `script-based-pre`, `llbc`, …
* **`full`** — everything except the explicitly-excluded lanes (`kani-fixme`,
  `remote-target-lists`).

The burndown reports both the **verification verdict parity** (primary) and the
**full-corpus parity** (outer).

### Upstream-ignored units: the `fixme` column (plan D1)

Kani's compiletest collects every test but **ignores** one whose path contains
`fixme`, or else `ignore` (`tools/compiletest/src/header.rs:191-198`,
`make_test_description`, every mode; a directory component counts, and so
does a cargo unit's expected-file name). In `kani-fixme` mode the base name
decides instead (header.rs:201-217). No upstream Kani verdict exists for such
a unit, so it cannot measure replacement.

Discovery tags a unit `upstream_ignored` when EITHER source says so, and
neither can untag:

* compiletest's path rule (`discover::compiletest_ignores`), applied to the
  checkout-relative `tests/<suite>/<rel>` so the checkout's own location never
  matters;
* the generated spec's `fixme` class or `ignored` message
  (`spec/kani/<corpus rev>/units.jsonl`, `src/spec.rs`). No spec for the rev
  means the path rule alone decides, and the run says so; a spec that exists
  but does not parse refuses the run.

`run` and `inventory` print `N upstream-ignored unit(s) (compiletest path rule
A, spec fixme class B)` and name any unit only one source tags;
`inventory --list` lists every tagged unit. Every row carries
`upstream_ignored` (absent = false), and so does every unit log (a log
written before the header reads as the path rule on its own suite and file).

Scoring: the row keeps its real classification, but the burndown counts it in
the **`fixme` column** — in `total`, in no class counter, and **outside the
parity denominator** (`denominator = total - corpus_invalid - fixme`). The
report prints the column's classes and every unit in it; the ledger row gains
`fixme`, `fixme_by_class`, `fixme_missed_bugs` and each scope's `denominator`.
The one exception is **`missed_bug`**: trust-mc proving a harness the file
expects to fail is a soundness finding whether or not Kani's regression suite
runs the file, so such a row stays in `missed_bug`, in the denominator and in
`fixme_missed_bugs`.

Measured at the pinned corpus (`4c0fce8`): 37 of the 1134 verification units
are upstream-ignored, and both sources name the same 37 (15 `expected`, 22
`kani`; the spec's 38th verification-suite `fixme` id,
`kani/Helpers/vtable_utils_ignore.rs`, declares no harness and is not a unit):

```
expected/function-contract/history/ui/noncopy_ignore.rs
expected/function-contract/modifies/refcell_fixme.rs
expected/function-contract/modifies/unsafe_rc_fixme.rs
expected/function-contract/modifies_fat_pointer/string_rewrite_ignore.rs
expected/intrinsics/sub_with_overflow_ice_fixme/arithmetic_zst_fixme.rs
expected/loop-contract/array_icr_for_loop_fixme.rs
expected/loop-contract/fixme_box.rs
expected/loop-contract/fixme_decreases_struct_field.rs
expected/loop-contract/fixme_decreases_with_modifies.rs
expected/loop-contract/fixme_multi_dim_decreases.rs
expected/loop-contract/fixme_nested_loops_decreases.rs
expected/offset-bounds-check/fixme_offset_usize.rs
expected/slice_c_str/c_str_fixme.rs
expected/uninit/delayed-ub/slices_fixme.rs
expected/uninit/fixme_unions.rs
kani/Asm/main_fixme.rs
kani/Cleanup/unwind_fixme.rs
kani/DynTrait/vtable_restrictions_fail_fixme.rs
kani/ForeignItems/fixme_option_ref.rs
kani/ForeignItems/fixme_varadic.rs
kani/FunctionCall/Variadic/fixme_main.rs
kani/FunctionContracts/fixme_receiver_contracts.rs
kani/FunctionContracts/fixme_static_interior_mut.rs
kani/FunctionContracts/fixme_static_mut.rs
kani/FunctionSymbols/fixme_main.rs
kani/Intrinsics/SIMD/Operators/remainder_float_fixme.rs
kani/Intrinsics/fixme_catch_unwind.rs
kani/Intrinsics/fixme_try.rs
kani/PointerOffset/fixme_wrap_nonzero_offset.rs
kani/Pointers_Basic/fixme_from_raw.rs
kani/SizeAndAlignOfDst/main_assert_fixme.rs
kani/Slice/fixme_issue_707.rs
kani/Stubbing/StubPrimitives/fixme_stub_lowered_methods.rs
kani/Stubbing/fixme_stub_trait_default_method.rs
kani/Unwind-Attribute/fixme_lib.rs
kani/Vectors/any/fixme_append.rs
kani/VolatileIntrinsics/main_fixme.rs
```

Three of them (`kani/Intrinsics/fixme_try.rs`, `kani/Asm/main_fixme.rs`,
`kani/FunctionSymbols/fixme_main.rs`) are also on the corpus-invalid
quarantine; the `fixme` column takes them first, so `corpus_invalid` counts
only the one quarantined unit upstream does run.

## Standalone by design

This crate is a **standalone CLI** — its own workspace, its own `Cargo.lock`,
built on the repository's Trust pin (`targo`). It is deliberately **not** a
member of the trust-mc workspace, so **building it needs no `rustc_private`
crates and no ay/trust-ir git-dep resolution** — it only pulls plain crates.io
deps (`clap`, `serde`, `walkdir`, …). It drives the trust-mc verifier as a
*subprocess*; the verifier still has to be built separately (that build, being
a rustc driver, links the Trust seal's rustc internals).

```bash
# Build the tool (~10s, zero rustc_private dep), from this directory:
targo --unverified build --release
#   binary: tools/kani-domination/target/release/kani-domination
```

## Usage

```bash
# 0. build the verifier ONCE (this — not the tool — builds the rustc driver):
#    kani-domination build   (runs `targo --unverified build-dev` at the repo root)

# 1. fetch Kani's source at the pinned rev into the corpus cache
#    (~/Library/Caches/trust-mc/kani-domination/<rev> on macOS; see "Host isolation")
kani-domination clone

# 2. see the corpus denominators (no run); --list prints every entry + oracle
kani-domination inventory --scope full

# 3. run trust-mc over the verification suites (resumable; streams JSONL)
kani-domination run --scope verification --timeout 15 --jobs 3
#    smoke first:  ... run --suite kani --limit 10 --timeout 20

# 4. burndown report + append a row to the committed trend ledger
kani-domination burndown <repo>/target/kani-domination/reports/results-verification.jsonl

# 5. triage: group the non-parity harnesses by normalized root cause (fix next)
kani-domination triage <repo>/target/kani-domination/reports/results-verification.jsonl
#    ... triage --only encoding_gap   # drill into one class
#    every row's full driver log: <reports>/logs/results-verification/<suite>/<file>.log

# 5b. apply a scorer change to an existing run without re-running the corpus
kani-domination rescore <repo>/target/kani-domination/reports/results-verification.jsonl

# 6. the reference: upstream Kani on the SAME units (needs a Kani install, not
#    the verifier; results default to results-<scope>-kani.jsonl)
kani-domination run --engine kani --scope verification --timeout 15 --jobs 3

# 7. verdict agreement + wall-time / peak-memory ratios, trust-mc over Kani
kani-domination compare <reports>/results-verification.jsonl <reports>/results-verification-kani.jsonl
#    ... compare --format json --worst 50
```

## Two engines, one oracle

`run --engine <trust-mc|kani>` picks the verifier. The default, `trust-mc`, is
byte-identical to runs before the flag existed: same command lines, flags,
environment, classification and file names. `kani` drives **upstream Kani** so
that its rows can stand as the reference for trust-mc's. Everything that
decides what a unit *is* stays shared — discovery, the oracle, the expected
file, the cwd (checkout root for single files, package dir for cargo units),
the per-unit isolated `--target-dir`, the scrubbed child environment, the
`RUSTFLAGS` from `// compile-flags:`, the outer watchdog and its one retry,
and the resource accounting — so two results files join row for row.

What differs under `--engine kani`:

* **Resolution.** `$KANI_BIN`, else `~/.cargo/bin/kani`, with `cargo-kani`
  beside it; `kani --version` must succeed and report the pinned oracle,
  `kani 0.67.0` (`KANI_ORACLE`, a stock-as-oracle: kept, pinned, never a
  blocker). A set-but-missing `KANI_BIN`, a failing `--version` or another
  version refuses the run. Nothing installs Kani: the default launcher sets
  itself up (a bundle download and a `rustup toolchain install`) whenever its
  home is missing, so it runs only over an existing `$KANI_HOME` or
  `~/.kani/kani-0.67.0`, passed to every child as `KANI_HOME`, and every Kani
  child runs with `RUSTUP_AUTO_INSTALL=0`. Without one the run stops with
  `NOT RUN: oracle kani 0.67.0 not installed`. The install is
  attested in the sidecar (`engine`, `engine_version`, `engine_path`,
  `engine_sha256`, and a `kani_attestation` with the `cargo-kani` sha256, the
  Kani home and its `rust-toolchain-version`) in place of the driver
  attestation.
* **Invocation.** Single-file units run `kani <file> --target-dir <iso>
  <kani-flags…>` — Kani's own compiletest `run_kani` spelling (which passes
  no `--target-dir` at all) plus the isolated target dir, placed **before**
  the header flags because `--cbmc-args` swallows every argument after it.
  Until 2026-09-13 the runner appended `--target-dir` after the flags, so on
  the 14 verification units with a CBMC tail (a `// cbmc-flags:` header or a
  `--cbmc-args` in `kani-flags`) CBMC received it and refused (`Usage error!
  Unknown option: --target-dir`, `CBMC failed with status 64`) and Kani
  reported `VERIFICATION:- FAILED`: parity by accident on the fail-oracle
  units, `unsupported` / `false_positive` on the success-oracle ones
  (`kani/Vectors/vector_extend_in_new.rs`, `expected/loop-contract/multiple_loops.rs`,
  `expected/function-contract/history/stub.rs`, …). Cargo units run
  `cargo-kani kani --target-dir <iso> [--harness <stem>]` in the package dir
  as `run_cargo_kani_test` does. The `kani-flags` header goes
  through **verbatim**: no `-Z unstable-options`, `--ay-chc` or
  `--harness-timeout` is injected, `--cbmc-args` and its tail are kept (Kani
  consumes them; `--keep-cbmc-args` is moot), and a `// cbmc-flags:` header —
  which the trust-mc lane has no use for — is appended the way compiletest
  appends it (`-Zunstable-options --cbmc-args …`). `--extra-driver-flag`
  values land before any `--cbmc-args`. There is deliberately no per-harness
  timeout: Kani runs its corpus the way its compiletest runs it, under the
  outer watchdog only, so its verdicts are the reference and not a
  budget-shaped variant of it.
* **Toolchain.** `RUSTUP_TOOLCHAIN` is scrubbed from every child and never set
  again; the `kani` launcher selects the nightly its install was built for
  (recorded as `kani_toolchain`). `--backend` is ignored and the sidecar
  records `cbmc`. `--surface native` is refused (upstream Kani has no
  `#[kani::harness]`).
* **Classification** follows Kani's own compiletest, per suite
  (`runner::classify_kani`; the criterion is `suites::SUITES[*].criterion`,
  read off the `--mode` in `scripts/kani-regression.sh`, `kani-slow-tests.sh`,
  `kani-perf.sh` and `kani-llbc-regression.sh` at the pinned rev):
  * `kani`, `smack`, `prusti` and `firecracker` are compiletest's `kani`
    mode (`TestCx::verify`): the test passes iff `kani` exits successfully,
    inverted by `// kani-verify-fail`; no expected file is consulted. Kani
    exits 0 exactly when every harness prints `VERIFICATION:- SUCCESSFUL`, so
    the row is scored on that verdict against the oracle — `parity` when they
    agree, `false_positive` (Kani FAILED, oracle success) or `missed_bug`
    (Kani SUCCESSFUL, oracle fail) when they do not.
  * `expected`, `ui`, `llbc`, `std-checks`, `slow`, `perf` and the `cargo-*`
    suites are compiletest's `expected` / `cargo-kani` modes
    (`TestCx::verify_output`): the test passes iff stdout+stderr contain every
    line(-block) of the expected file (`contains_lines`); the exit status is
    not consulted. A match is `parity`. Otherwise the verdict rules above
    explain the miss, and a verdict that agrees with the oracle while a line
    is missing is `unknown` with the first missing block in the note, because
    compiletest fails that test.
  * Kani prints no `[AY:…]` markers: a `SUCCESSFUL` is its proof and a
    `FAILED` is CBMC's counterexample, in multi-harness files too (a fail
    oracle whose expected file names a harness Kani verified is a
    `missed_bug`). Its `unsupported_construct` check lines and its
    `Found the following unsupported constructs` warning are part of every
    normal transcript — any unit that reaches `Location::caller` or a foreign
    function prints them, with either verdict — and never decide a class;
    `unsupported` is a trust-mc class. Until 2026-09-13 they scored 108 of
    1122 verification rows `unsupported`, 90 of them fail-oracle units Kani
    fails exactly as its compiletest expects.
  * Fail-closed departures from compiletest, each spelled out in the note: a
    run with no verdict (a compile error, a rejected flag, a kani-driver
    panic) is `error` even where its nonzero exit would satisfy a
    `kani-verify-fail` test, because a failure to run is not a counterexample;
    a file Kani finds no harness in (`No proof harnesses … were found`) is
    `vacuous` although compiletest passes it on exit 0; and a kani-driver
    panic is `error` even when the expected file's diagnostic lines were
    printed before it. `timeout`, `crash`, `build_unavailable` and the
    `kani-check-fail` compile-error rule apply unchanged. A non-parity row on
    a path with `fixme` or `ignore` in it says so in its note: compiletest
    skips those paths, so no upstream verdict exists for them.
  * A `contains_lines` parity whose run also printed `VERIFICATION:- FAILED`
    for a harness the (SUCCESSFUL) expected file never names is still parity
    — Kani's own criterion credits it — but the note names the harness
    (`expected/function-contract/gcd_rec_replacement_pass.rs` under 0.67.0:
    `gcd_harness` fails, the expected file lists only the two harnesses that
    pass).
  * The trust-mc rules are untouched: `classify_kani` is reached only for
    `--engine kani` rows, and the trust-mc classifier no longer carries any
    Kani-only spelling. This is scorer version **3**.

**Measured 2026-09-13, the installed Kani against the pinned corpus.** The
`kani` on this host is the 0.67.0 release (nightly-2025-11-21); the pinned
corpus rev `4c0fce8` is dated 2026-06-03, pins nightly-2025-12-03 and its
library carries `kani::stub_set!` / `use_stub_set`, `#[kani::loop_decreases]`,
typed quantifier variables (`|i: u64 in (0, 10)|`) and harnesses with
arguments, none of which 0.67.0 has. So 44 verification units — the
`kani/Stubbing/stub_set_*`, `expected/stub-set-*`, `expected/loop-contract/*decreases*`,
`kani/Quantifiers/*`, `kani/ArithOperators/unsafe_*_fail.rs` and
`function-contract/history` families — end in `kani-compiler exited with
status 101` over a rustc `E0433` / "functions used as harnesses cannot have
any arguments" and are `error` under 0.67.0 whatever the classifier does;
they need a Kani built at the corpus rev. Likewise `--solver z3` /
`#[kani::solver(bitwuzla)]` units need solvers this host lacks (0.67.0 then
panics on CBMC's `ERROR` status, upstream #4519), `kani/Slice/extra_checks_fail.rs`
passes compiletest only because the driver rejects `--extra-pointer-checks`
without `-Z unstable-options` (a nonzero exit on a `kani-verify-fail` test,
at the corpus rev too), and a handful of non-`fixme` `kani`-suite units
(`FloatingPoint/float_remainder.rs`, `ArithOperators/rem_float.rs`,
`Cast/float_to_int_saturating.rs`,
`Intrinsics/Atomic/Stable/CompareExchange/compare_exchange_failure.rs`) and
`expected/function-contract/gcd_rec_replacement_pass.rs` get a genuine
`FAILED` from 0.67.0 against a success oracle. Those rows are Kani-version
and host gaps, recorded as such; the scorer no longer manufactures any
others.
* **Files.** Results default to `results-<scope>-kani.jsonl` with the same
  sidecar shape. A resume compares the engine first (a sidecar written before
  `--engine` existed is a trust-mc file) and then the Kani install, so a Kani
  row can never join a trust-mc file or vice versa; a Kani run refuses to
  resume a file with no sidecar at all. `burndown` refuses a Kani results
  file unless it only prints (`--no-append` or `--ledger none`): the ledger
  is trust-mc's trend line. `score` and `triage` work on either.
* **No route.** `--engine kani` ignores `--route` and its inputs (`--key`,
  `--trustc`, `--backend-dylib`, `--allow-smoke-key`, `--allow-off-tuple`) with
  a notice: the route is how the trust-mc driver compiles, and upstream Kani
  compiles with its own toolchain. Kani rows and sidecars carry no `route`.

### `compare`

`compare <trust-mc results.jsonl> <kani results.jsonl>` joins the two files on
`(suite, file)` — for a cargo unit the file is its expected-file path, which
already names the harness — and prints (text, or `--format json`):

* units in both files, and the ones only in either;
* the verdict agreement matrix: `(oracle, trust-mc class, kani class)` counts,
  plus how many joined units share a classification, are parity under both,
  under one only, or neither;
* over the units where **both** engines reach `parity`, the ratio
  trust-mc / Kani of wall time (`wall_ms`) and peak memory
  (`tree_peak_rss_kb`, falling back to `max_rss_kb`): median, p90, geometric
  mean, the totals and their ratio, and the counts where trust-mc is lower,
  higher or equal; a row with no `wall_ms` but a `duration_ms` (a results
  file from a tool before `wall_ms` existed) is measured by its
  `duration_ms` — the whole unit, including a killed first attempt on a
  retried unit — and the output counts how many both-parity rows per side
  that fallback served; a unit with no data on either side (a row with
  neither field, or no memory fields) is counted as `no_data` and excluded,
  and the output says which side lacks memory data and on how many units;
* the worst `--worst` (default 25) units on each axis, highest ratio first;
* the units Kani solves that trust-mc does not, and vice versa, each with the
  non-solving engine's note.

The positional order is the contract; a sidecar that names the other engine
is a swapped invocation and is refused, and a file without a sidecar is taken
by position with a warning.

### `flips` — the noise floor (plan G9)

A delta between two configurations means something only if it is larger than
the run-to-run variation of one configuration. `flips` measures that
variation from N results files produced under **one measurement tuple**:

```bash
kani-domination run --out r1.jsonl …   # the same command N times
kani-domination run --out r2.jsonl …
kani-domination run --out r3.jsonl …
kani-domination flips r1.jsonl r2.jsonl r3.jsonl        # --format json
```

It refuses (fail-closed) unless every file has a provenance sidecar and all of
them name the same tuple: everything `run` compares before a resume
(`model::resume_mismatch`: scorer version, engine, backend, timeout, surface,
`ay` version, driver / compiler sha256, sysroot, `ay` path, the Kani install,
route and route attestation), plus the corpus rev, `jobs`, scopes and the
rows' own scorer version; each difference is named. `--allow-tuple-mismatch`
reports anyway, marked `tuple: NOT IDENTICAL`. It then joins the files on
`(suite, file)` and prints:

* the **flip set** — every unit whose classification is not the same in every
  run, with its class per run (and `[upstream-ignored]` where it applies) —
  and its size as a share of the joined units, the noise floor;
* each run's verification parity over its own denominator, and the parity
  spread (max − min) across runs;
* each class's count per run, with its spread;
* the units missing from some runs, never joined.

A claimed parity delta smaller than the parity spread, or a moved unit that is
in the flip set, is within the noise floor.

## Per-unit resource accounting

Every row records how much the unit cost, under either engine:

| Field | Meaning |
|---|---|
| `wall_ms` | spawn to reap of the attempt whose output was classified. `duration_ms` (older) is the whole unit and includes a killed first attempt when the outer watchdog retried. |
| `max_rss_kb` | `ru_maxrss` of the direct child as `wait4` reports it, KB (macOS bytes are normalized). Exact, not sampled. The direct child is the driver or the `kani` launcher, but on Linux the kernel folds the peak of every descendant the child itself reaped into this figure — as the **largest single-process peak**, never a sum — so it is usually close to the tree peak. |
| `tree_peak_rss_kb` | peak resident memory of the **whole process tree** the unit spawned (driver, compiler, solvers; launcher, kani-driver, CBMC): the maximum over samples of the sum of `VmHWM` across every live descendant, floored at `max_rss_kb`. Linux only; absent elsewhere. |

The child runs in its **own process group** and is polled every 50 ms; each
poll walks its descendants through `/proc/<pid>/task/*/children` (or a full
`/proc` scan on a kernel without them) and reads each one's `VmHWM`. The
limits of that sampling, stated plainly:

* it is a **sum of per-process high-water marks** at one instant, which can
  overstate — two processes' peaks need not coincide — and it can understate,
  because a process that starts and exits between two polls is never seen and
  one that exited before a poll has already left the sum;
* it never reports less than the direct child's exact `ru_maxrss`, and a unit
  too short to be sampled at all reports exactly that;
* `max_rss_kb` is exact but is a maximum over processes, not a sum, so it
  cannot see two solvers resident at once;
* polling costs the runner a few `/proc` reads per live process every 50 ms;
  it does not touch the measured processes.

Quote `tree_peak_rss_kb` for "how much memory did this unit need" and
`max_rss_kb` for "how big was the largest process", and say which.

Timing and killing are also where the old runner was unsound. An
outer-watchdog kill used to reach only the direct child, leaving the driver's
compiler and solver subtree running — the orphan population documented in
`docs/findings/2026-08-24-external-cancellation-orphans-the-solver-tree.md`,
whose background load skewed the very timings recorded here. The watchdog now
SIGKILLs the whole process group plus every descendant the `/proc` walk can
still see (enumerated before the leader dies, since its children are
reparented after). Because a child in its own group is outside the terminal's
foreground group, the runner also forwards SIGINT/SIGTERM/SIGHUP to every
live group itself (a lock-free table of atomics, so the handler can never
skip a kill), then re-raises with the default disposition.

The measurement is still a wall clock on a shared host: `--jobs` peers, other
builds and the load average recorded in the sidecar all bear on `wall_ms`, and
a ratio between two runs made under different load is a ratio of two hosts.
Run both engines on the same host, with the same `--jobs`, as close together
as the corpus allows.

### Native harness surface (R2 re-key lane)

`run --surface native` mechanically **re-keys** each expressible legacy
`#[kani::proof]` unit to the native `#[kani::harness]` spelling before
compilation — top-of-body `let x: T = kani::any();` bindings hoist into
parameters, and the `kani::` prefix drops from `any()`/`assume()` (verdict
identity holds by construction: `#[kani::harness]` expands to the same
`#[kanitool::proof]` marker with an equivalent preamble). The re-keyer is
**fail-closed**: anything outside the certain fragment (non-binding `any()`,
`any()` under a loop/nested block, `kani::any_where`/other APIs, generics,
contracts, cargo units, …) runs legacy, and every unit records its provenance
(`rekey:native` / `rekey:legacy(<reason>)`) in its result row; the ledger row
gains additive `surface` + `rekey` keys. The default `--surface legacy` is
byte-identical to runs before the flag existed.

```bash
# planning inventory only (no verification; needs only the Kani checkout):
kani-domination rekey-dry-run --scope verification

# a native-surface measurement (results default to results-<scope>-native.jsonl):
kani-domination run --scope verification --surface native --timeout 15
```

### Compiler route (`--route dev-cli|trustc`)

`run --route` picks the compiler the driver builds each unit with (T1-D1,
`docs/trust-lane-t1-implementation.md` S8). `dev-cli`, the default, is the driver
child this runner always spawned: `trust-mc-compiler` from `TRUST_MC_SYSROOT`,
argv unchanged. `trustc` runs every unit through
`trust-mc-driver --compiler-route trustc --trustc <p> --backend-dylib <p>` with
`TRUST_MC_SYSROOT=<KEY>` (`docs/trust-lane-trustc-route.md`):

```bash
K=target/trust-mc/keyed/driver-948b36c62eacc5d1
TRUST_MC_TEST_BIN=<trust-built trust-mc-driver> AY_BIN=<pinned ay> \
  kani-domination run --route trustc --key "$K" --backend chc --timeout 15 --jobs 3
#   --trustc   default: TRUST_MC_TRUSTC, then KEY.json compiler.trustc
#   --backend-dylib  default: TRUST_MC_BACKEND_DYLIB, then $K/codegen-backends/librustc_codegen_trust_mc.dylib
#   --key      default: TRUST_MC_SYSROOT
```

Before the first unit the runner attests the route (`route::attest_trustc`) and
records it in the sidecar as `route_attestation`: the trustc path, sha256 and
commit, the seal build, PROVENANCE sha256, `reported_commit` and
`artifact_driver_sha256`, the installed `librustc_driver-*` name and sha256, the
KEY directory and `KEY.json` sha256, the KEY's `key_source`, `source.kind`, PROVENANCE path (which must be the seal's)
and class, `driver_sha256`, `installed_driver_sha256`, `library_mode`, trust-mc HEAD
and posture rustflags, the backend path, sha256 and the rustc driver it links,
and `tools/tuple-check --json` with that seal held. Fail closed, every way:

* **Preflight.** Any disagreement among those artifacts (another driver, a KEY
  bound to another installed driver, a trustc outside its sysroot, a backend
  linking another driver, a missing `KEY.json`) records every unit as `error`
  without running the driver, and `run` exits nonzero.
* **Smoke KEY.** A KEY whose `library_mode` is not `parity` is refused before any
  unit; `--allow-smoke-key` runs it as non-counting, and `burndown` never appends
  its row (T1-D5).
* **Off-tuple seal.** A seal for which `tools/tuple-check --json` does not pass
  (or cannot run) is refused before any unit; `--allow-off-tuple` runs it as
  non-counting, and `burndown` never appends its row: a row from other inputs is
  not a row of `tools/tuple.toml`. `counted` in the sidecar is true only when the
  preflight is clean, the KEY is parity and the tuple-check passed, and
  `ledger_refusal` names which one failed.
* **Per unit.** A driver refusal (`compiler route trustc refused`), output with no
  `[AY:COMPILER_ROUTE]` marker, or a marker naming another trustc, commit, rustc
  driver, backend sha256 or KEY is an `error` row (note `route-error: ...`),
  decided after the corpus quarantine, so it is never parity, never `unknown` and
  never `corpus_invalid`. A DevCli row carrying Trustc route output is `error`
  too.
* **Rows and denominators.** Every row carries `route`, and the sidecar and the
  ledger row carry `route` and `route_attestation`. `score`, `burndown` and a
  resume refuse a report whose rows mix routes or disagree with the sidecar
  (rows written before the flag are `dev-cli`), and a resume refuses a rebuilt
  backend, another trustc or commit, another KEY, `KEY.json` or grade.

Per-test target directories on this route live under
`<user cache>/trust-mc/kani-domination/build/trustc-<backend>`, never under
`/tmp`; the default results file gains a `-trustc` suffix.

**Route and engine are orthogonal.** `--engine` picks the verifier and `--route`
the compiler the trust-mc driver uses, so `--engine trust-mc` runs on either
route and `--engine kani` has none (see "Two engines, one oracle"). A default
results file carries both tags (`results-<scope>[-native][-kani][-trustc].jsonl`),
and a resume compares the engine, the route (with the route attestation) and
`scorer_version` against the file's rows and sidecar, refusing on any
difference.

**Refusing a ledger row.** `burndown` prints the summary first, then refuses to
append (exit nonzero, naming the reason from `score::ledger_refusal`) a Kani
file, an uncounted Trustc run (preflight failure, tuple-check not `pass`,
non-parity KEY, `counted` false) or a file mixing scorer versions. Pass
`--no-append` or `--ledger none` to print only.

**Temporary:** the Trustc route prints harness names crate-qualified
(`Checking harness forget_no_drop::main...`). Until the driver fix lands, the
runner strips the single-file crate prefix from the `Checking harness` and
`Verification failed for -` lines before scoring
(`route::strip_crate_qualified_harness_names`, called from
`runner::score_unit`, so `rescore` applies it too; the unit log keeps the
driver's bytes unmodified); remove it with that fix.

### Backend / reproducibility

trust-mc is AY-only. The CHC path (loops/recursion) runs in-process via the
pinned `ay-chc` portfolio; the SMT/BMC path resolves an `ay` binary
(`$AY_BIN` → `$TRUST_MC_AY_BIN` → the pin-keyed
`~/Library/Caches/trust-mc-ay-cli-<first 9 of the Cargo.toml AY pin>/release/ay`
that `scripts/build-pinned-ay-cli.sh` builds → sibling `../ay/target/release/ay` → `PATH`)
and hands it to every driver child as `TRUST_MC_AY_BIN`, so the solver the
driver runs is the one the row records. The run records the
full **authority tuple** — trust-mc `HEAD`, the `ay` pin from `Cargo.toml`, the
`ay` binary version actually used (with an `ay_rev_matches_pin` flag), and the
Kani rev — in every results file and ledger row, per the project's
replacement-proof discipline.

`--cbmc-args …` (CBMC-only solver tuning) is stripped by default since the AY
backend does not consume it; pass `--keep-cbmc-args` to forward it verbatim.

## Layout

| File | Role |
|---|---|
| `src/suites.rs` | the Kani suite → scope registry (the layered denominator). |
| `src/discover.rs` | entry-file discovery + the Kani verdict oracle + the upstream-ignored tag. |
| `src/spec.rs` | reads the generated spec's `fixme` class for the upstream-ignored cross-check. |
| `src/runner.rs` | the parallel run (both engines) + verdict/marker parse + classification (`score_unit`, shared with `rescore`) + per-unit resource accounting and the process-group watchdog. |
| `src/unitlog.rs` / `src/rescore.rs` | the per-unit driver log format, and re-scoring a results file from its logs. |
| `src/compare.rs` | the trust-mc vs Kani join: agreement matrix and wall/memory ratios. |
| `src/flips.rs` | the flip set across N identical-tuple runs (the noise floor). |
| `src/score.rs` | layered burndown aggregation + the trend ledger (trust-mc rows only). |
| `src/clone.rs` / `src/env.rs` | Kani fetch + environment/provenance discovery (the verifier, or the Kani install). |
| `burndown-ledger.jsonl` | append-only burndown trend, written locally (one row/run). |

Per-test build dirs and per-run JSONL reports live under
`target/kani-domination/` (gitignored); only the ledger accumulates across runs.
The Kani checkout lives in the corpus cache described below, not in the tree.

## Host isolation — a row measures the verifier, not the host

Measured on 2026-09-08: all six cargo-unit rows (`std-checks` ×5,
`slow/tokio-proofs`) were `error` in both lanes and had never measured
anything. Three host facts combined. The Kani clone sat under
`<trust-mc>/target`, so every corpus `cargo` inherited trust-mc's
`.cargo/config.toml`. The driver ran `cargo +<toolchain>`, which needs rustup
proxies this host does not have. And its bare `cargo locate-project` failed, so
`[package.metadata.kani]` flags were silently dropped. The runner and driver now
close each of those:

* **Corpus location.** The default is `<user cache>/trust-mc/kani-domination/<kani-rev>`:
  `~/Library/Caches` on macOS, `$XDG_CACHE_HOME` or `~/.cache` elsewhere. That is
  outside every cargo workspace. `--kani-dir <path>` or
  `KANI_DOMINATION_CORPUS_DIR` names another checkout. `run` **refuses** to run
  cargo units from a checkout whose ancestors carry a `.cargo/config.toml`.
  Kani's own config at the checkout root and `$CARGO_HOME`'s are allowed, and
  `clone` warns about such a location. A checkout left at the old
  `target/kani-domination/kani` is no longer read.
* **Child environment.** Every verifier child has toolchain and cargo-build
  selectors removed (`RUSTUP_TOOLCHAIN`, `RUSTC`, `RUSTC_WRAPPER`, `RUSTFLAGS`,
  `CARGO_ENCODED_RUSTFLAGS`, `CARGO_TARGET_DIR`, …; the list is
  `env::SCRUBBED_CHILD_ENV`), plus every `CARGO_BUILD_*`, `CARGO_TARGET_*`,
  `CARGO_PROFILE_*` and `CARGO_UNSTABLE_*` variable, which cargo reads as
  configuration. Those variables describe how the runner was
  launched. A test's own `kani-rustflags` header still sets `RUSTFLAGS`. The
  `RUSTFLAGS="-Awarnings"` workaround in `docs/KANI-LANE-REVIVAL.md` is not needed
  for runs through this tool. Neither engine has a toolchain forced on it:
  the driver resolves the one its compiler links, and the `kani` launcher
  selects its own install's nightly.
* **Toolchain cargo without proxies (driver).** `trust-mc-driver` runs the
  cargo of the toolchain that built it: its build script records `$RUSTC
  --print sysroot` as `MC_DRIVER_BUILD_SYSROOT`, and the driver runs
  `<that sysroot>/bin/cargo` directly, with `RUSTC` set to the sibling `rustc`
  and the toolchain `bin` appended to PATH. When that cargo is missing it
  refuses and names `targo --unverified build-dev`; there is no rustup lookup,
  no `cargo +<tc>` and no `stable` fallback (removed 2026-09-28; the 2026-09-08
  fix tried `rustup which cargo --toolchain <tc>` first).
* **`AY_BIN` fails closed.** If `AY_BIN` (or `TRUST_MC_AY_BIN`) names a missing
  file, the run stops instead of falling through to whatever `ay` is on PATH.
* **`TRUST_MC_JOBS`.** Every verifier child gets `TRUST_MC_JOBS=<--jobs>`
  (`route::JOBS_ENV`; both routes, and the Kani engine's children for a
  uniform environment, which upstream Kani ignores), so the driver knows how
  many peers share the host: `fix/driver-deadline` caps its in-process solver's
  memory at physical memory / (2 × jobs). Both attestations record the value
  as `trust_mc_jobs`, each unit log's `env_set` shows it, and a resume across a
  different value is refused (it changes the verifier's memory budget).
  Sidecars written before 2026-09-14 have no `trust_mc_jobs`; their children
  never received the variable.
* **Rows come from the pinned solver only.** Each verifier child gets
  `TRUST_MC_AY_BIN` set to the `ay` the attestation names, and the driver
  refuses that binary unless it is the `Cargo.toml` pin.
  `TRUST_MC_ALLOW_UNPINNED_AY` is removed from the child environment,
  `--allow-unpinned-ay` is dropped from test flags, and `run` refuses it as an
  extra driver flag, so an off-pin `ay` yields `error` rows rather than demoted
  successes. Any output carrying `[AY:SOLVER_PIN_MISMATCH:` is scored `error`
  whatever its verdict and whichever arm would otherwise apply, and a
  `SUCCESSFUL (UNVALIDATED)` verdict never scores `parity` or
  `exceeds_oracle`; against a failing oracle it is still `missed_bug`.
* **Attestation.** The provenance sidecar, and each ledger row it produces,
  carries an `attestation` object with these fields: the driver's path, sha256
  and `--version`; the `trust-mc-compiler` beside it and its sha256; the sysroot; the `ay` binary's path and how it was found
  (`AY_BIN` / `TRUST_MC_AY_BIN` / `pinned-cache` / `sibling` / `PATH`); the Trust toolchain channel and rustc
  commit; the `[patch]`-linked ay tree's HEAD and dirty flag; the corpus
  directory; the 1/5/15-minute load average at start and end; and which
  scrubbed variables were present. Such ledger rows also gain `jobs`. Sidecars
  written before this change have no attestation, and `score` never invents
  one for them.
* **Host load (plan D18).** Both attestations (trust-mc and Kani) also record
  `load_start` and `load_end`, each a `HostLoad`: the 1/5/15-minute
  `loadavg`, and `competing` — the live `cargo`, `rustc`, `trust-mc-driver`
  and `kani-driver` processes on the host that are **not** this runner or its
  own descendants (`env::COMPETING_PROCESS_NAMES`; names are `argv[0]`'s
  basename, else `comm`) — with `own_excluded` counting the matches the run
  itself owned. `load_start` is taken when the sidecar is first written,
  before any unit; `load_end` after `run_all` has reaped every child. On Linux
  both come from `/proc/loadavg` and a `/proc` scan (`source: "/proc"`);
  elsewhere `competing` is unknown. `score` / `burndown` print both samples.
  A counted row must record host load: `burndown` refuses to append a row
  whose attestation lacks either sample (a sidecar written before 2026-09-14,
  or a run that did not finish), naming plan D18. The chc-m1 sidecar
  (`results-verification-chc-m1.jsonl.provenance.json`) is such a file: it
  has `load_average_start`/`_end` but no `load_start`/`load_end`, so its rows
  (and any `rescore` of them, which re-attests nothing) print but never ledger.
* **Resume keeps the attestation honest.** The sidecar attests every row in the
  results file, including rows kept by a resume. So `run` without `--fresh`
  refuses to resume a file whose recorded attestation names a different
  engine, driver or compiler sha256, sysroot, `ay` binary or version, backend,
  timeout, surface or scorer version (for a Kani file: a different Kani or
  `cargo-kani` sha256 or version). A trust-mc file whose earlier rows have no
  attestation is resumed with none recorded; a Kani run refuses such a file.
  The rows' own `scorer_version` is checked as well, so a file with no
  sidecar at all still cannot mix scorers.
