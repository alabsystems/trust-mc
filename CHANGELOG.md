# Changelog

All notable trust-mc changes should be recorded here.

trust-mc is a pre-release Rust verifier derived from Kani. This file tracks
the changes in each release; released sections are dated from their git tag.

The manifest version is `[package] version` in `Cargo.toml` — read it there.
That sentence used to name `0.3.0` and say no tag had been cut; both went stale
on 2026-08-29, when `v0.3.0` through `v0.6.0` were all tagged (annotated tags,
tagger date 2026-08-29, present on `origin`). Verified 2026-08-30: the public
tier `alabsystems/trust-mc` has `main` and `v0.6.0` at the same commit,
`997c11c7b0e13bf6c92fb63789ceea760d529fc3`.

The `[Unreleased]` section below was never split per tag, so it still carries
work that shipped in `0.3.0`–`0.6.0`; `git log v0.5.0..v0.6.0` is the exact
per-release record until it is.

## [Unreleased]

### Fixed (TI-P-0a: trust-mc builds against trust-ir v70 and refuses its tensor region by name)
- trust-ir bd313b4fb (wire v67-v70) adds `Ty::Tensor`, the six `Inst::Tensor*`
  instructions, `Constant::TensorBlob` and `Module.blobs`, which trust-mc's
  exhaustive matches did not compile against and no lowering models. Every
  entry now refuses them by name, fail-closed
  (`trust-mc-trust-bmc/src/tensor_region.rs`; DECISION_QUEUE "Refuse trust-ir's
  tensor region at every entry"): the shared BMC/CHC module input and the
  native-bundle boundary
  (`NativeTrustMcBundleError::TensorRegionNotModeled { constructs }`) refuse
  the module whole; `family_for_inst` (`SemanticsFamily::Tensors`), the BMC and
  CHC translators (`TrustIrChcUnsupportedReason::TensorRegion`),
  `checked_ty_to_sort`, `const_to_expr`, both lanes' switch lowering and
  `collect_inst_value_uses` fail closed per construct; the driver's
  proof-authority gate refuses the region before its per-instruction walk
  (located, then module-wide), so none reaches an admitting arm. The census
  reads a blob in every stored constant, a `Switch` case included. Every TrustIR
  declaration and `tools/tuple.toml` name bd313b4fb (was e664453c4, v66).

### Changed (the release bundle is cut on one Trust seal — owner orders 2026-09-28/29, plan REL-C1)
- `<seal>/bin/targo --unverified bundle` cuts the release bundle on that Trust
  seal and refuses, before it builds anything, a compiler without a Trust
  identity, a launching cargo outside the seal's `bin/`, a `RUSTUP_TOOLCHAIN`
  other than `trust`, a checkout not pinned to `trust`, a seal without the
  `bin/cargo` and `bin/rustc` an install runs, and a `RUSTC_WRAPPER`-style
  compiler override. The published 20065 bundle was cut on
  `nightly-2025-12-03` and recorded that name in `rust-toolchain-version`; a
  bundle now records `trust`, a `trust-seal` file (commit, store build,
  `librustc_driver` and its sha256, std source) and the seal's
  `bin/rustc --version` — the line `trust-mc setup --use-local-toolchain`
  compares, which the `trustc` spelling it used to record never matched.
- The release build remaps `$HOME`, `$CARGO_HOME`, the sibling checkouts, the
  seal root and the std sources (`/rustc/<seal commit>`) on every unit, builds
  the verification, no_core and playback libraries with the release
  trust-mc-compiler from the seal's own rust-src (named explicitly), and bakes no
  path to the build seal: no absolute rpath in trust-mc-compiler and no
  `MC_DRIVER_BUILD_SYSROOT` in trust-mc-driver (`MC_RELEASE_BUNDLE`). A release
  install without its `toolchain` link is refused by the driver, naming the link.
- kissat is no longer bundled: it was copied from PATH, and `--solver kissat`
  is CBMC-only and ignored. A bundle cut without a version argument is named for
  trust-mc's own `[package] version`, not build-trust-mc's `0.1.0`. Recipe and
  the seal-bump step:
  `docs/DISTRIBUTION.md`, "Cutting the release bundle on a Trust seal".

### Fixed (`--ay-emit-bmc` declares ALL, not QF_AUFBV, for a floating-point VC)
- The BMC IR emitter (`emit_bmc`, the `--ay-emit-bmc` route) declared `(set-logic QF_AUFBV)` for a VC
  with floating-point terms. QF_AUFBV has no floating point. ay routes by the declared logic, so `fp.rem`
  and `fp.add` went to a procedure that does not interpret them, and ay's model gate answered `unknown`.
  The float `%`, `rem_euclid` and `div_euclid` BMC e2e tests hit this. The emitter now widens such a logic
  to `ALL`. It keeps HORN, ALL, any `*FP*` logic, and a logic named with `--ay-logic`.
- The default BMC route (`finalize_counterexample_query`) still declares QF_AUFBV for float queries. The
  same widening there gave +15 parity rows on the 86 float corpus files, with a 1.53x wall-time cost. It
  is held for the owner, with its patch and A/B, in `docs/bmc-fp-logic-default-2026-10-14.md`.

### Changed (pins: ay d65293086 -> 29a0f2cab, the answer to the per-row model-gate ask)
- The eight ay declarations and `tools/tuple.toml` `[ay]` move to ay `29a0f2cab` (ay main). On the per-row CHC route,
  ay's `_BV_LIA_INDEP` lanes no longer publish the BV lane's Int-blind witness unchecked when the AUFLIA cross-check
  answers `unknown`, so its model gate catches nothing on `safe_wide_array_as_bytes` and the two `safe_static_*`
  harnesses of `const_pointer_read_type_dual.rs` (the 2026-10-13 ask, now answered). Verdicts unchanged. trust-ir
  and Clean stay on the ty cohort (DECISION_QUEUE AY-SAFE-CHC-PIN).

### Changed (pins: ay 8e7b3fe6 -> d65293086, the answer to the safe-CHC ask)
- The eight ay declarations and `tools/tuple.toml` `[ay]` move to ay `d65293086` (ay main), which decides
  the seeded const-pointer query of `safe_symbolic_from_elem` in seconds with no invalid model (the
  2026-10-09 ask, now answered). Its CHC row and the six the per-file watchdog left unattempted after it
  (`const_pointer_read_type_dual.rs`) are no longer known-red. trust-ir and Clean stay on the ty cohort
  (DECISION_QUEUE AY-SAFE-CHC-PIN). Three other harnesses of the file still trip ay's model gate on the
  per-row route, without a wrong verdict: the 2026-10-13 ask.

### Fixed (the direct-SMT composer's verdicts no longer depend on the machine's load)
- Every budget of the acyclic direct-SMT composer (`direct_smt_cex.rs`: the
  fused query, the abstract query, the relevance-slice probes and their phase)
  was a wall-clock slice, and a wall-clock slice is also spent while the
  scheduler runs other threads. Its queries cost tens to hundreds of
  milliseconds of CPU (TMC-1 `struct_elem#2`: 235-250 ms; the in-degree-256
  wide join: 50-100 ms), but at a load of 110-140 on an 18-core host a thread
  gets a sixth of a core, and the same query ran its second out undecided.
  Whether a function was proved through ChcValidity or refuted with a
  replayable witness then depended on the load: base failed
  `wide_joins_keep_their_verdicts` 3 times in 6 and
  `shared_rows_equal_per_request_rows_on_random_programs` 3 times in 3,
  alternating with the fixed head at the same load (0 in 6, 0 in 3).
- `check_sat_on_budget` keeps the wall slice per attempt and reads the
  thread's CPU clock (`ay_sys::thread_cpu_time`) around it, as ay's own
  `probe_arm` does: an undecided attempt whose slice ran out with less than
  half the budget computed was robbed, not spent, and is re-run once or twice
  in a slice stretched to deliver the budget at the measured share (at most 8
  times the budget). An attempt that decided, declined early or computed
  through half its budget is final, so an idle machine runs the single check
  it always ran. The slicing phase is spent by CPU, with an 8x wall backstop.
  `ay-chc-native` now enables `ay-sys` (already a dependency of ay-chc).
- The composer decides each clause body once per decision. The round that
  only confirms the fixpoint used to ask every body again, doubling the time
  of a decision whose body stays undecided (`struct_elem#2`, close to the 8 s
  native watchdog under load).
- `shared_rows_equal_per_request_rows_on_random_programs` counts two
  not-proved rows of which one names the native watchdog's wall-clock ceiling
  (`WALL_CLOCK_CEILING`, now the one spelling of both watchdog reasons) as a
  timing flip, inside the existing one-in-ten limit, instead of a reason
  difference: an expiry is not a reason. Two different reasons neither clock
  chose still fail.
- Regression tests: `every_clause_body_is_decided_once_per_decision`,
  `only_a_robbed_attempt_is_re_run_in_a_stretched_slice`,
  `a_phase_budget_is_spent_by_work_with_a_wall_backstop`.

### Fixed (V60-ABI: a typed signature ABI is refused at every entry, not read as absent)
- trust-ir wire v60 lets a `FuncTy` record a typed signature ABI
  (`FuncTy::abi`): caller copies, argument extension, hidden results, pair and
  cast carriers, and which lowered parameters carry each source argument.
  trust-mc's lowerings model an entry and a call by the lowered parameter list
  alone, and trust-mc compiled against v60 since 3d315a17 without reading the
  field, so a descriptor-bearing module was translated as if the record were
  absent. Now every entry refuses it, by name, as trust-ir's reference
  interpreter and ByteV1 reflector do, for every row of the table, used or not
  (`trust-mc-trust-bmc/src/signature_abi.rs`):
  - the native-bundle boundary (the driver's runner and `trust-mc-replay`
    through it) refuses the bundle before validation hashes it:
    `NativeTrustMcBundleError::TypedSignatureAbiNotModeled { func_ty }`;
  - the CHC translator adds an unconditional `error` rule with the
    `TrustIrChcUnsupportedReason::TypedSignatureAbiTransport` diagnostic;
  - the BMC translator adds an always-failing violation naming the row.
- No Trust producer stamps a typed ABI today, so nothing that verified before
  is refused. Wire v59's effect summaries need no change: trust-mc reads no
  `FunctionSummary`. DECISION_QUEUE V60-ABI.
- Regression tests on trust-ir's own v60 golden
  (`tests/fixtures/typed_signature_abi.module.json`):
  `a_typed_signature_abi_refuses_the_native_bundle_before_translation` (BMC,
  CHC, PDR; trust-ir validates the bundle; the unrecorded twin translates) and
  `a_typed_signature_abi_makes_the_direct_translators_fail_closed`.

### Changed (pins: trust-ir 3d315a17 -> 7e350a12, the ty main cohort; Clean 1ad47bdd -> 625396d8; ay b1b0b9de -> 8e7b3fe6; the retired `function_budget_ms` key)
- The eight trust-ir / trust-ir-build declarations and `tools/tuple.toml`
  `[trust_ir]` move to trust-ir 7e350a122a, the revision ty main
  (2a4e66266) pins with trust-cg df4542db8 and Clean 625396d83. It names
  Clean 625396d8, so `[clean]` and Cargo.lock's clean-kernel row move there.
  The eight trust-ir commits change no API trust-mc calls.
- ay moves to 8e7b3fe6b, the ay ty main and trust-ir 7e350a12 pin (ay's
  introspection twins), by `scripts/bump-ay-pin.py`; `[ay]` follows. Beside
  it the lock loses `ay-cdclt`, which `ay-dpll` depends on at b1b0b9de and
  not at 8e7b3fe6. 8e7b3fe6 is not a descendant of b1b0b9de: it is the r11
  branch tip ay main merged, so this move leaves out the 383 ay commits
  b1b0b9de has beyond it, for the one ay every cohort member names. The
  lock now names one source each of ay (the `../ay` path), trust-ir (the
  `../trust-ir` path), Clean (625396d8) and trust-vc (a9edcdd4), and replays
  with `--locked` beside those siblings, as Trust's
  `scripts/check_submodule_lock_coherence.sh` resolves it.
- The root `[trust]` table drops the retired `function_budget_ms = 3000`, with
  no `backstop` in its place (Trust's first-party pin ledger, entry (z);
  Trust DECISION_QUEUE BUDGET-1a). A targo built from current Trust main
  refuses the key in a workspace's own root, so the sibling lock-coherence
  check failed on trust-mc. The builtin clocks now apply: 5,000 ms per query,
  as before, and 120,000 ms per function instead of 3,000 ms.

### Changed (pins: trust-ir 588390da -> 3d315a17, D1b construction doors that refuse; Clean 01ffe310 -> 1ad47bdd)
- All eight trust-ir / trust-ir-build declarations (trust-mc-driver x4,
  trust-mc-replay x1, trust-mc-trust-bmc x3) and `tools/tuple.toml`
  `[trust_ir]` move to trust-ir 3d315a178b, trust-ir main with D1b landed,
  the revision trust-cg (cd7a0e01b), clean and ty move to with it. It names
  Clean 1ad47bdd, so `[clean]` and Cargo.lock's clean-kernel row move there;
  that is the lock's only change. trust-ir and ay still resolve through the
  `[patch]` path tables; ay stays b1b0b9de.
- D1b makes trust-ir's construction doors refuse instead of panic:
  `ModuleBuilder::build` returns `Result<Module, BuildError>`, the plain
  `Module` table doors return `Result<_, IdSpaceExhausted>`,
  `Module::add_function` is gone (`try_add_function`), and the blob entries
  return `Result`. Every trust-mc call site is test code, so the adoption
  (8bfb28424) spells each one `.expect("<door>: test fixture")`; no
  production path changes.

### Fixed (TRUST-MC-FREM-2: float `rem_euclid` / `div_euclid` are not the integer stubs)
- The `div_euclid` / `rem_euclid` stubs, BMC (`try_codegen_math_unary_call`)
  and CHC (`codegen_euclid`, both dispatch sites), matched the method name
  alone, so they also claimed `f32` / `f64`. Both lanes carry a float as its
  IEEE bit pattern, and `ty_signedness_shallow` reads a float as unsigned, so
  they computed `bvurem` / `bvudiv` over the bit patterns and added an integer
  "euclidean division by zero" check. Through the atpkg front door
  (trust-mc 20065), the FALSE `x == 5.0 => x.rem_euclid(3.0) != 2.0` was
  `VERIFICATION:- SUCCESSFUL` on the default (BMC) route and on `--ay-chc`.
  The TRUE `5.0.rem_euclid(3.0) == 2.0` and `(-5.0).div_euclid(3.0) == -2.0`
  were `FAILED` with `[AY:CTREX_CAT:Genuine]`.
- The stubs now claim only primitive-integer operands (by value; in CHC also
  behind one reference, as `num_traits::Euclid` passes them), using
  `trust_mc_codegen_shared::is_primitive_integer_ty`. A float call takes the
  ordinary call path. The BMC mini-inliner inlines std's body, whose `%` is
  the exact `fmod`, so the true claims prove and the false one is refuted. In
  the CHC lane the result is havocked as a recorded sound approximation, so a
  counterexample is `OverApproximation`, never `Genuine`. The BMC check also
  declines a by-reference operand, whose BMC value is a pointer; no test
  exercises that case.
- Regression tests: `test_bmc_e2e_f64_{rem,div}_euclid_*`,
  `test_bmc_f64_rem_euclid_records_no_integer_division_by_zero_check` and
  `test_chc_*_euclid_*`. `test_bmc_e2e_i32_rem_euclid_stub_still_proves_unsat`
  checks that the integer stub still claims integers.

### Fixed (TRUST-MC-FREM-1: float `%` is C `fmod`, not the IEEE remainder)
- The BMC lane lowered Rust float `%` (`bv_float_binop`, so scalar `Rem` and
  `simd_rem` lanes alike) to SMT-LIB `fp.rem`, which is the IEEE 754
  remainder: the quotient is rounded to nearest, so `fp.rem(5, 3) = -1`, while
  `5.0 % 3.0 == 2.0`. The atpkg front door (trust-mc 20065) reported the TRUE
  harness `x == 5.0 => x % 3.0 == 2.0` as `VERIFICATION:- FAILED` with
  `[AY:CTREX_CAT:Genuine]`. `%` is now `fp_fmod`, which is exact:
  `r = fp.rem(x, y)`. When `r` is nonzero, not NaN and opposite in sign to `x`,
  the result is `fp.add(RNE, r, copysign(|y|, x))`. The add is exact, and the
  doc comment carries the proof. NaN, infinite operands, zero divisors and
  signed zeros already agreed and are untouched. The same defect was fixed in
  trust-ir as TRUST-IR-AY-FREM-1.
- Not affected: the CHC constant fold (host `%`), the CHC float table (an
  unconstrained function), and the trust-ir lane trustc links
  (`trust-mc-trust-bmc`), which refuses float arithmetic. Through trustc
  `-Ztrust-verify` every float `%` row comes back `unsupported` from trust-mc.
- Regression tests, all solved by ay: `float_arithmetic_frem_tests.rs` covers
  f64/f32/f16 bit for bit against host `%` (including `-6 % 3 == -0.0` and a
  tie quotient), plus symbolic f32 `x >= 0 => x % 3 >= 0`. The end-to-end
  tests are `test_bmc_e2e_f{64,32}_rem_*` (source -> MIR -> BMC VC -> ay).

### Changed (pins: trust-ir 3208b39e -> 588390da, wire v57 -> v58; ay 2fb40f95 -> b1b0b9de; Clean stays 01ffe310)
- All eight trust-ir / trust-ir-build declarations (trust-mc-driver x4,
  trust-mc-replay x1, trust-mc-trust-bmc x3) and `tools/tuple.toml`
  `[trust_ir]` move to trust-ir main 588390da82, the revision ty main
  (058b1baa31) and trust-cg main (d7dc0695d5) pin. It names Clean 01ffe310,
  so `[clean]` and Cargo.lock's clean-kernel row stay.
- The eight ay declarations and `tools/tuple.toml` `[ay]` move to ay
  b1b0b9de07, the revision ty main pins (`scripts/bump-ay-pin.py`, which
  re-resolved Cargo.lock beside it). The lock gains back the two `ay-cdclt`
  edges (`ay-diff-logic`, `num-integer`) that b1b0b9de declares and 2fb40f95
  did not, so it replays under `--locked` beside the cohort's ay, the one
  Trust's `scripts/check_submodule_lock_coherence.sh` resolves it against.
  The lock names one Clean source (01ffe310), one trust-vc source and no
  trust-cg; trust-ir and ay resolve through the `[patch]` path tables.
- Wire v58 (trust-ir WS3.9 / WS3.13) is read faithfully. `StructDef.origin` /
  `EnumDef.origin` (`TypeOrigin`) is cross-module identity that may only split
  or refuse; neither lane links modules or compares types across them, and
  both encode a struct by its id, fields and declared layout, so the key is
  carried and never read (`a_struct_origin_key_changes_no_encoding`: a keyed
  definition, under either key form, translates to exactly its unkeyed twin's
  CHC). `Module.closure_layouts` gives a closure type a byte frame through
  `Module::ty_layout_shape`; both lanes take only its SIZE. A bulk write that
  names a whole closure object is now exact in the CHC lane (a copy moves
  every capture, a fill sets every integer capture), which holds whatever the
  capture offsets are; a range inside the frame keeps failing closed by name
  (`BulkMemoryUnplacedRange`), because no lane derives a capture's byte
  offset; and a closure type with no row keeps the pre-v58 refusal
  (`BulkMemoryTransfer`). Tests: `closure_cells_take_only_the_declared_frame_size`
  (CHC, against rustc's reordered frame) and
  `bmc_closure_cells_prove_no_undetermined_capture` (BMC, with and without a
  frame, memory checks on and off). The test-only `StructDef` literals name
  `origin: None`.

### Added (decision AGG-DT and its ay ask: `MAX_AGGREGATE_LEAVES` stays until ay's datatype identity is linear; docs only)
- `docs/ay-asks/2026-10-01-datatype-sort-cost-follows-leaf-count` records why
  struct-DAG expansion is not yet modeled with datatype sorts. At the pinned
  ay, a datatype sort costs its flattened leaf count: the proof identity
  prints the definition inline at every occurrence, and `ChcSort`'s `Hash`
  recurses through it. The ask's measurements are 147 B per leaf for each
  occurrence, and a lost verdict from k = 10 (1,024 leaves). The ask also
  ships `gen_struct_dag.py` and the repro files. `docs/DECISION_QUEUE.md`
  AGG-DT keeps the fail-closed bound and names the ay dependency and
  trust-mc's own prerequisites. The doc comment on `MAX_AGGREGATE_LEAVES`
  names the dependency too. No code changes.

### Changed (CHC translation — design step 8e; approved by the owner 2026-10-01, landed 2026-10-08 as reviewed, `docs/DECISION_QUEUE.md`, 8e)
- An ACYCLIC function's typed CHC is one non-recursive query: the entry
  block's relation, its fact, and one `error` rule whose body encodes every
  block by reachability, prefix, transition-selector and error-site Booleans
  (`trust-mc-trust-bmc/src/translate_chc_large_block.rs`, which carries the
  equisatisfiability argument against the per-block encoding and the walk that
  maps a model back to its block path, `LargeBlockMap::counterexample_path`).
  Merged blocks declare no relation: on the ever-init drop-flag family the
  relation arguments go from `5 N²` (per block) to 0, and the query grows
  linearly in N. Cyclic functions keep one relation per block. New public API:
  `ChcTranslationOutput::large_block`, `LargeBlockMap` / `LargeBlockPath` /
  `LargeBlockEdge` / `LargeBlockErrorSite`,
  `trust_ir_function_to_chc_translation_output_per_block` and
  `trust_ir_to_chc_translation_outputs_per_block` (the per-block encoding of any
  function), and `ChcTranslationWork::large_block_*` counters.
- A merged block reads every input through an atom: a column whose in-edges
  differ is a chain of depth-one definitions over the in-edges that pass
  another term than the column's most frequent one, under an at-most-one
  ladder on the block's in-selectors; in-edge terms are compared by identity
  (atoms by value, compound terms by shared node). The query's size is linear
  and its depth constant in a join's in-degree (the review measured an
  exponential translation, a quadratic query and a depth equal to the
  in-degree before).
- Fat-pointer parts across blocks: the large-block query reads a
  `PtrFromParts` value's parts exactly in every block its building block
  DOMINATES (region dominator tree); the per-block encoding, and any read that
  is not dominated, sees an OPAQUE value with an unbounded metadata havoc. This
  closes a false proof the review found (a raw slice's length read in a later
  block took the `isize::MAX`-bounded `slice_len` symbol) and a spurious,
  consumer-admitted refutation on main (a later per-block rule read an earlier
  rule's variables free).
- The consumer's refutation replay (`independently_replay_typed_chc_pdr_refutation_witness`)
  reads translation havocs under the witness's model: a havoc under an
  implication whose plain Boolean antecedent the model sets false, or in the
  unselected branch of an `ite` whose plain Boolean condition the model fixes,
  is not read (`bounded_unroll::derivation_reads_translation_havoc`, walking
  with the memoized `direct_smt_cex::HavocReads`; the soundness argument is on
  it). Per-block CHC is judged as before. Its node budget was deleted (the walk
  is linear in the consumer's own clause), and so were the replay's 65 536
  binding and 262 144 trace ceilings (the trace is bounded by the problem's
  clauses, the model by the exact binding count).
- The acyclic composer runs the fused query first on its existing per-query
  budget and slices only an undecided body (no new wall-clock budget), skips
  slices satisfiable by construction (linear), and steers a model that reads a
  havoc away from its havoc-reading choices until one reads none (all
  untrusted: they change which proof or witness is found first, never what a
  verdict means). Clause variables are collected in linear time
  (`clause_vars`; ay-chc's `HornClause::vars` is quadratic).
- The composer mints a witness in the form the consumer's replay reads when
  the solver's model is not one (`direct_smt_cex::replayable_model`): a
  variable the model left out takes the value of the variable a top-level
  equation equates it with (the entry fact's head arguments), else its sort's
  zero, and a finite-map array binding becomes the constant array of its
  default — used only when the consumer's own replay admits it. Found by the
  corpus parity run: a real `splat_index_param` dump (now a fixture,
  `trust-mc-trust-bmc/tests/fixtures/splat_index_param_native_bundle.json`)
  was refuted per block with an admitted witness and as one query with a
  refused one.
- The consumer's refutation replay asks the derivation under the witness's
  total model as a closed formula (`derivation[v := value]`, when ay's
  substitution leaves no variable; otherwise the pinned form
  `derivation ∧ ⋀ v = value` as before). Both are satisfiable exactly when the
  derivation holds under the model, so what the replay admits is unchanged; at
  a 1 024-way switch the pinned form took 1.2 to 1.3 s, past the composer's
  1 s budget, and refused an honest large-block witness the closed form
  confirms in 0.12 s.
- Not done, with the owner's approval of 8e: the size-scaled, deterministic
  solver-effort bound for the large-block query that was to replace the
  composer's fixed 1 s per-query budget. The pinned ay's `SmtContext` has no
  deterministic effort control, and on the wide-switch family the bound that
  binds at ay 2fb40f95 is not the 1 s budget but four fixed size ceilings in
  ay-chc (`docs/ay-asks/2026-10-01-large-query-size-ceilings-and-deterministic-effort`).

### Changed (pins: trust-ir 839418cf -> 3208b39e; Clean 3c82461c -> 01ffe310; lock replays under --locked)
- All eight trust-ir / trust-ir-build declarations (trust-mc-driver x4,
  trust-mc-replay x1, trust-mc-trust-bmc x3) and `tools/tuple.toml` `[trust_ir]`
  move to trust-ir main 3208b39ebc, the revision ty main (6a0e6c2d22) and
  trust-cg main (7ec11048d1) pin, and the one the Trust superproject's
  `first-party/trust-ir` gitlink moves to in train T9. Its Clean declarations
  name 01ffe310, so `[clean]` and Cargo.lock's clean-kernel row move with it.
- Cargo.lock was re-resolved with `targo metadata` beside the cohort's sibling
  checkouts (trust-ir 3208b39e, ay main 7c90b76d through the `[patch]` path
  table). Besides the clean-kernel source it adds the two dependencies AY's
  `ay-cdclt` gained (`ay-diff-logic`, `num-integer`). Before this, the lock
  named Clean 3c82461c while the trust-ir checkout beside it named 01ffe310, so
  `metadata --locked` refused it (Trust's
  `scripts/check_submodule_lock_coherence.sh`).
- trust-ir 839418cf..3208b39e changes no IR surface file: wire v57 throughout,
  so neither lane's reading of any instruction changes.

### Changed (pins: trust-ir 5290adb2 -> 839418cf, wire v51 -> v57; Clean afe42324 -> 3c82461c)
- All eight trust-ir / trust-ir-build declarations (trust-mc-driver x4,
  trust-mc-replay x1, trust-mc-trust-bmc x3) and `tools/tuple.toml` `[trust_ir]`
  move to trust-ir main 839418cf0a, the revision trust-cg main (530a9319a5)
  pins. Its five Clean declarations name 3c82461c, so `[clean]` and Cargo.lock's
  one clean-kernel row move with it; no other lock row changes.
- trust-ir amendment S makes `Inst`, `Ty`, `Constant`, `Module`, `Function`,
  `Block` and `InstrNode` the level-R aliases of generic carriers. A level-R
  value has no extension (`NoExt` is uninhabited), so the BMC lane's exhaustive
  `Ty` and `Constant` matches close the `Ext` arm with `unreachable()`.
- `Inst::Assert` carries `kind` (v52, `AssertKind`) and `site` (v54,
  `PanicSite`). Both lanes keep their reading: the check fails iff `cond` is
  false, and a failed check is a terminal panic outcome whatever its identity.
- New instructions, each refused BY NAME in both lanes (BMC unsupported-semantics
  VC, CHC error rule): `CallCannotUnwind` / `CallIndirectCannotUnwind` (v53, CHC
  `NoUnwindCallBoundary`), `AssertInvoke` (v54, CHC `UnwindingCheck`),
  `DropInvoke` (v55, CHC `DropGlue`) and `InvokeIndirect` (v56, CHC
  `IndirectCall`). Neither lane models a no-unwind boundary, an unwind edge,
  drop glue or indirect dispatch, so reading any of them as its `Call` / `Assert`
  / `Drop` / `CallIndirect` twin would decide obligations past something never
  modeled. The native proof-grade gate lists all five as triaged; the coverage
  matrix places `AssertInvoke` in ControlFlow and the other four in Calls.
  Regression:
  `test_unwind_boundary_calls_and_unwinding_twins_fail_closed_by_name_in_both_lanes`.

### Changed (P3 of the spawn census by construction — the native lane on trust-ir's reachability engine)
- The native proof-grade gate (`validate_native_bundle_proof_authority_input`)
  validates every function trust-ir's reachability engine says a request
  reaches (`function_dependencies::inspect_module_reachability`, the union of
  each request's `thread_closure`), not its own worklist over `Inst::Call`,
  which is deleted. The engine also follows an `Invoke`, a `SeqMap` element
  function, an exactly resolved `CallIndirect` and an unresolved one's pool
  (every function the module turns into a callable of that shape). The CHC
  translator folds a body only at a direct `Call` and refuses the other three
  sites with an error rule, so the gate only refuses more: a bundle whose
  request reaches a refused construct through one of them is now refused
  whole, where the former gate admitted it and the request went unproved at
  that site. trust-mc's classifier (`NativeBundleDeclarations`) walks every
  stored body, names no thread start, foreign symbol or link alias, and
  resolves no runtime service; the gate reads the reached set, never a census
  verdict. It fails closed on a census that fell back, on a request that
  names no function ("requested function #N is missing"; it said "requested
  or reachable", and a reached function can no longer be missing), and on a
  closure holding a `Missing` or `Ambiguous` sink, where the engine walks no
  body (defense in depth: the module validation before it refuses both). The
  reached set would stay complete for a translator that folded an `Invoke`, a
  `SeqMap` or an exact `CallIndirect`, but not a pool call: on this lane any
  UNKNOWN sink (every `Assert`, `HeapAlloc`, `Dealloc`, `Drop` and bodyless
  declaration) leaves the pools unclosed, so such a translator must first
  refuse a closure holding an `UnclosedPool` or `OpenPrincipal` sink. Functions
  are validated in module order, so a bundle with several violations may
  cite another one first. `ElementReadingFunctions` keeps its backward walk
  over `Call`: it follows the translator's summaries, which the engine does
  not model.
  Differential (a scratch build that kept the former worklist and gate beside
  the new ones and logged both at every gate call): trust-mc-driver's and
  trust-mc-replay's tests made 1620 gate calls over 853 distinct modules,
  and the reached sets and gate results are identical except in the new
  test (`proof_grade_gate_validates_every_function_the_engine_reaches`):
  its `Invoke`, exact-indirect and pool shapes, which the former gate
  admitted, and its missing request (the renamed message). Over 2970 native
  bundles the installed seal's trustc (9192) dumps for 824 `tests/ui/trust`
  fixtures, and the 7 bundles committed in trust's call-summary census and
  trust-mc's native-cli cohort, every reached set is identical and every
  bundle is admitted or refused alike; 25 bundles with several violations
  cite another one first. None of those modules takes a function's address,
  so their `CallIndirect` pools are empty.

### Changed (decisions: agents take them; TMC-3 and 8f taken 2026-10-02)
- `docs/DECISION_QUEUE.md` is the record of proof-authority choices, not a
  list of questions for the owner: agents take the fail-closed, reversible
  option, record it with its reasoning and keep going (owner directive
  2026-10-02; also in `CLAUDE.md` and `AGENTS.md`).
- TMC-3 is taken: the `Alloca` lanes will classify bulk operands as tracked
  uses, landing as one change with the producer-layout check, the
  definite-initialization bulk arm and the bulk-write array differential.
  Until that change lands the gate is unchanged.
- 8f is taken: one shared seal-time re-lowering per `ChcVc` first, then
  `Arc`-shared evidence bytes, then one domain-separated v3 envelope for the
  obligation-set identity and the binding hashes. No code changes yet.

### Changed (P3 of the spawn census by construction — the abstraction boundary by identity)
- Reachability and the codegen inline gate decide which standard-library
  bodies to abstract (collections, `String`, `Cow`, slices, atomics,
  `std::fs`, `Mutex`/`RwLock`, hashbrown, `RangeIteratorImpl`) from
  definitions, not from `def_path_str`/`Instance::name` text:
  `kani_middle/std_abstraction.rs` resolves each anchor for each codegen unit
  (real definition paths in the sysroot crate, diagnostic and lang items, the
  crate std's `HashMap` keeps its table in) and keeps each former
  `ABSTRACT_FUNCTION_PREFIXES` spelling as the printed path it named. Whether
  an anchor counts follows how the session prints it, derived per printer
  from the printer's own queries (`visible_parent_map`, `extern_crate`): an
  item is abstracted where the leading segments of its path name an anchor
  printed as a spelling, or a qualified path names one whose printed path ends
  with a spelling. So `VecDeque`, `LinkedList`, `BTreeMap`, `BTreeSet`,
  `vec::IntoIter` and `Global` stay collected in a `no_std` crate (their
  `alloc::` paths were never spelled), and under `Instance::name`, which
  prints `<crate>::alloc::..` through `extern crate alloc`, the inline gate
  abstracts only qualified paths there, as before. `fetch_update` keeps its
  body wherever a segment of the path starts with that name, generic
  arguments included. Sysroot crates are found by lang item, since Kani's
  sysroot loads a second crate named `std`. Fail closed: an anchor that does
  not resolve is matched by its former spellings over the text (the old rule,
  `std::std::` collapse included); one printed under a spelled crate as no
  spelling, or a `HashMap` table outside a crate named `hashbrown`, is
  abstracted wherever named. Each warns once, and each function abstracted
  that way is recorded as an unstubbed abstraction.
  Differential (a scratch build with the former matcher deciding and both
  logged at both sites, seal 9192): the 974-file single-file corpus under
  `--only-codegen` gave 22205 distinct decisions (14925 reachability, 7280
  inline gate) and none differs; 31 probes, `no_std` and `extern crate alloc`
  crates among them, gave 1187 and differ only in the accidents below.
  What the text matched by accident and definitions do not, so now collected
  (none in the corpus): a spelling inside a longer segment (every
  `GlobalAlloc` impl through `std::alloc::Global`; a `no_std` crate's
  `btree_map`/`btree_set` iterators through `alloc::collections::btree`),
  `hashbrown` anywhere in a qualified path (a user module or type, a local
  closure's file name), a projection's trait. The spellings
  `alloc::collections::btree_map::BTreeMap::` and
  `alloc::collections::btree_set::BTreeSet::` never matched a printed path
  (`alloc::collections` re-exports both types) and are gone.

### Removed
- `tools/main-thread-purity` and its `ideas/` prototype: string-path
  reachability over synthetic fixtures, wired to nothing; trust-ir's
  reachability engine (`function_dependencies.rs`) carries its fixtures from
  trust-ir 5290adb2, which is ahead of trust-mc's trust-ir pin (bf7ee706).

### Added (trust-ir WS3.20 bulk memory — exact whole-object `MemCopy`/`MemSet`, size independent of the byte count, linear in the cell)
- CHC: a `memcpy`/`memmove`/`memset` whose operands point into single-cell
  stack allocations decides its undefined behaviour exactly (in bounds
  `bytes <=u size_of(cell) - offset`; a `memcpy` within one cell overlaps iff
  `bytes >u |dst_off - src_off|`; `bytes == 0` is a no-op) and writes exactly
  where `bytes` is the size of an object starting at the destination: the
  same-typed source object, or the fill byte repeated into every integer leaf
  (`const_array` per leaf). Each condition is one comparison of the count with
  a type's size, so a constant 2^40, or a symbolic count, costs what 4 does;
  and one write costs the cell's leaves plus its path, as a `Store` through the
  same lanes does (the guards of the nested objects accumulate down the path,
  one `ite` per leaf off it), whatever the nesting depth
  (`trust-mc-trust-bmc/src/translate_chc_bulk_memory.rs`). A defined lane run
  of a tracked cell havocs it and fails closed (`BulkMemoryUnplacedRange`):
  its exact form is a lambda array, which neither `ay_bindings::Expr` nor
  `ay_chc::ChcExpr` has (asked in
  `docs/ay-asks/2026-10-01-array-range-write-former`). Other operands keep the
  havoc-and-fail-closed model (`BulkMemoryTransfer`), now silent at
  `bytes == 0`; through a pointer whose provenance is known but whose place is
  not (a symbolic `GEP` index), that cell is havocked. In blocks a CFG cycle
  reaches, a whole-lane write is absorbed by the shape-only array like a lane
  `Store`, and a fill obeys the same integer-leaf rule as everywhere else.
- BMC: a bulk write of one whole single-cell `Alloca` is exact (a same-typed
  copy takes the source's whole region array; a fill writes the repeated byte
  into an integer cell), with out-of-bounds and self-overlap reported as
  violations.
- Fixed (BMC, memory checks off): a compound cell is one placeholder element
  and a lane `GEP` reads index `k`, so a whole-cell write that stored only
  index 0 left every other lane stale — a false proof after a whole-cell
  `memcpy` (new on this branch, caught in review) and after a whole compound
  `Store` (pre-existing). A compound `Store` now lands on a fresh array.
- The proof-authority gate is unchanged: no `Alloca` lane admits a cell a bulk
  operand reaches, so proof-grade bundles keep the fail-closed model. Admitting
  them is `docs/DECISION_QUEUE.md` TMC-3, which now also names what must land
  with it (a bulk arm in the definite-initialization check, bulk writes in the
  TMC-1 array differential) and records the review.
- The CHC translator memoizes its type queries per translation (composite
  shapes, byte layouts, constant-lane evidence, first sub-objects, the fill
  rule): `trust-mc-trust-bmc/src/translate_chc_ty_facts.rs`. One trust-ir
  layout walk per type tree seeds the layouts of the structs and arrays nested
  in it; the struct field-overlap check is one sorted sweep per struct instead
  of every pair at every `GEP` step; `update_binding_lane` copies only what it
  keeps. trust-ir's own layout walk is still exponential on types that share a
  sub-type and quadratic on a chain
  (`docs/findings/2026-10-01-trust-ir-layout-walk-unfolds-shared-subtypes.md`);
  a bulk write now pays it once.
- Every havoc the bulk arm introduces is a declared translation havoc (the
  reserved name the refutation gates read).
- Tests: `trust-mc-trust-bmc/tests/bulk_memory_differential.rs` (both lanes
  against trust-ir's interpreter: 6,468 CHC cases with checks on and off over
  nested arrays, arrays of structs, padding, newtype chains, structs of
  structs and cross-type copies; BMC compound and scalar cells), and the
  depth, provenance, enclosing-object, loop-block, fill-byte and type-fact
  fixtures in `translate_chc_bulk_memory_tests.rs`.

### Changed (native bundle solve — design step 8c, approved by the owner 2026-09-29)
- `NativeTrustIrChcPdrRunner::solve_bundle_native_proof_grade*` solves and
  replays ONCE per normalized CHC input. Requests with a byte-identical
  normalized input, an identical lowering input and one timeout share one run
  of each engine call: the acyclic direct-SMT decision, the IC3 loop lane (one
  run serves both of its call sites), the strict PDR run, the bounded-unroll
  witness search (keyed by its ladder) and the fresh invariant replay (keyed by
  the model bytes). A `ChcVc` allocation is lowered once for the solve of every
  request on it. On one function that is every request. Each request still
  gets its own evidence, its own identity and its own private seal, minted only
  if the share group that answered ITS solve admits its fresh seal-time
  re-lowering; a CHC-validity seal also requires that group's acyclic `Safe`
  decision, the derivation it stands on. The seal records the request's own
  identity and the shared digest (`PrivateSealRequestBinding`), and the
  verifier refuses a seal minted for another request or another input. A row
  with no candidate never pays for the seal's re-lowering. Every row is equal,
  private seal included, to the row a per-request solve returns, on the
  driver's bundle corpus (both proof kinds), a looping refutation and 56
  randomly generated programs. New: `solve_bundle_native_proof_grade_with_work`
  and `NativeBundleSolveWork`. Details, the review and the evidence:
  `docs/DECISION_QUEUE.md`, 8c; the residual per-row cost is the OPEN item 8f;
  the TCB row is in the superproject's `docs/TCB.md`.

### Changed (proof-grade gate — decisions TMC-1 and TMC-2, approved by the owner 2026-09-29)
- The native proof-grade gate admits an array element read (`ExtractElement`)
  exactly where the CHC translator models it as the exact `select` on SMT-array
  lanes under the access's own bounds obligation: a non-empty fixed-size array
  of a tracked element, a result of exactly the element type, an integer index,
  a block no loop reaches (`trust_mc_trust_bmc::ProofGradeElementReads`, built
  once per function, each array type's shape decided once). A vector,
  sequence, empty-array or untracked-element read, an element/result type
  mismatch, an index of no integer type and a read in a block a loop reaches
  stay refused, by name — and so does a `Call`, in a block a loop reaches, of a
  callee whose summarized body reads an element
  (`shape_only_array_in_callee`; `trust_mc_trust_bmc::ElementReadingFunctions`,
  one linear pass over the module). Evidence: a differential of the
  proof-grade lane against the trust-ir reference interpreter over fixed-seed
  random array programs, which also solves every refused program behind the
  gate (`trust-mc-driver/src/native/array_gate_differential.rs`; numbers in
  `docs/DECISION_QUEUE.md`, TMC-1).
- The gate's frozen array extent for promoted and borrowed stack cells is
  deleted (`gate_array_extent_is_legacy_admitted`, `legacy_gate_leaf_count`,
  `LEGACY_GATE_ARRAY_LANES = 256`, `PromotedAllocaReject::ArrayExtentPendingDecision`):
  an array cell of any length is admitted on the same argument as any other
  promoted or borrowed cell.

### Fixed (soundness — refutations: an equality on a translation havoc was read as its definition)
- The bounded-unroll refutation lane's grounding gate read any top-level
  `(= v e)` with `e` grounded as a definition of `v`. When `v` is a fresh value
  the CHC translator introduced (an unmodeled read, an opaque result), the
  equality is a constraint the solver satisfies by choosing `v`: the error
  clause of `assert(r != 263)` is `(= r 263)`. The TMC-1 review found the
  instance: a safe loop calling a summarized element reader was "refuted" on
  the proof-grade `refuted` channel, and the consumer's independent replay
  accepted the witness. Every translator havoc is now declared through
  `ChcVc::declare_havoc_var` under the reserved name prefix
  `trust_mc_core::chc::TRANSLATION_HAVOC_VAR_PREFIX`, which survives into the
  lowered problem and its normalized-input digest; the grounding gate never
  grounds such a variable (the entry fact included), and the consumer's replay
  of an acyclic direct-SMT witness refuses a derivation that reads one.

### Fixed (soundness and cost — CHC element reads)
- A summarized callee's element read honors `check_memory_bounds` (no rule
  when it is off, a fresh value outside the bounds), takes a lane only when its
  sort is exactly the result type's (no width normalization), and no longer
  narrows the summary's path by its in-bounds condition: that copied one more
  conjunct into every later obligation of the path, quadratic in the reads of a
  callee block (1,424 / 5,349 / 20,699 distinct edges at 50 / 100 / 200 reads,
  measured by the TMC-1 review; now a constant amount per read). A callee's
  element operand types are gathered once per translation, not once per
  summary attempt.
- A SIMD vector read in a block states the bounds rule of its lane count (an
  out-of-bounds vector read is trust-ir undefined behaviour), and a read whose
  length is unknown (a sequence) fails closed with memory checks on
  (`UnmodeledElementLength`) instead of being an unconstrained value with no
  obligation.

### Fixed (soundness — CHC call summaries: a callee's element read had no bounds obligation)
- `try_direct_call_summary` read an array element in a summarized callee as a
  fresh value with no bounds condition, relying on a separately emitted
  `Assert` that nothing requires, so an out-of-bounds read inside a summarized
  callee left the caller's CHC safe (a false proof in the diagnostic lane; the
  proof-grade gate refused every element read until TMC-1). The summary now
  states the same obligation as the block translator (`lane_access_of`, the
  index read by its declared signedness), reads the exact lane of a carried
  array, and declines where it cannot state the obligation.

### Fixed (soundness — BMC lane: statics had one address, orders read addresses, stand-ins went unrecorded)
- Two statics reached through raw-pointer constants are no longer one cell.
  Every such allocation had the literal address `0x1000` and none of its bytes
  in `memory`, so after `*(&raw mut A) = 5` the assertion `*(&raw mut B) == 5`
  PROVED, and a true assertion about a static's initial value failed certified
  `Genuine`. Each global allocation (static or constant memory) now has ONE
  address symbol per harness, from one table shared by the raw-pointer lane and
  the constant-reference lane (`&S`, `&S[i]`), so `ptr::eq(&S, P)` for `const P:
  *const u32 = &raw const S` holds (it failed certified `Genuine` on main). The
  symbol is kept apart from every heap object and registered stack object
  (`register_stack_object`; without it the solver put `static mut A` on a later
  `Box`) and from every other named allocation, and an allocation the
  raw-pointer lane can read has its initializer bytes on the harness's INITIAL
  memory array (`statement/global_alloc.rs`); bytes the initializer does not
  determine stay free and are recorded. A pointer into an allocation the lane
  did not name is declined, never aliased.
- A reference constant into the MIDDLE of an allocation is read and placed at
  its offset. The pointee was decoded from the allocation's first byte, so for
  `const E: &u32 = &[1u32, 2, 3][1]` the assertion `*E == 1` PROVED (a false
  proof on main), and `&PAIR.1` was placed at `PAIR`'s base
  (`statement/operand_ref.rs` `const_ref_pointee_bytes`). The CHC lane has the
  same defect and is not changed here: it is recorded known-red with evidence
  in `tools/soundness-duals/manifest.toml`.
- A whole-value (datatype / array / Int) store no longer leaves a stale byte
  image behind it. Where the Rust type is known it replaces only its object's
  bytes and writes every field the layout determines
  (`statement/typed_memory_store.rs`); elsewhere byte memory becomes a fresh
  array, recorded `symbolic_store_havocs_byte_memory`. An untracked `&mut`
  deref store is mirrored into byte memory, path-guarded.
- `PartialOrd` / `Ord` read the compared values through every reference level.
  MIR-inlined `<*const T as Ord>::cmp` ordered the addresses of the two pointer
  VARIABLES and certified a false failure
  (`kani/PointerComparison/ptr_comparison.rs::check_thin_ptr`). A side that is
  only an address after peeling, or a compared type that holds a reference, is
  a fresh result, recorded.
- Stand-ins are recorded, so a counterexample that reads one is never
  certified `Genuine`: an unguarded `unsupported_cfg_cycle` violation,
  `Try::branch`'s success value (it was the constant `FALLBACK_PTR`) and its
  assumed `Continue` on a non-allocator `Try`, and the DST `size_of_val` /
  `align_of_val` / `checked_size_of_raw` / `checked_align_of_raw` fallbacks.
- `std::alloc::realloc(ptr, layout, new_size)` (the `Layout` form) is
  modelled, and `kani::any::<Box<T>>()` allocates an arbitrary payload instead
  of returning an arbitrary pointer.
- A stub encoder that returns no block for a call WITH a MIR return target is
  the recorded unsupported fallback, never `Diverge`, at every nested result of
  `try_codegen_stdlib_stub_call` (`CallDispatchOutcome::from_nested_target_for_call`).
  This backs up the per-arm `.map(Some)` rule of
  `docs/dispatch-diverge-hazard-2026-09-17.md`; `from_nested_target`, which
  mapped an inner `None` to `Diverge`, is deleted, and the 16 arms of the
  simple and pointer/memory sub-dispatchers that still spelled `Some(..)` are
  now `.map(Some)` too.
- Duals: `tools/soundness-duals/bmc_static_address_identity_dual.rs` (its
  `bug_two_statics_claimed_aliased` is SUCCESSFUL on the old lane — the false
  proof), `bmc_raw_ptr_ord_ref_level_dual.rs` and
  `bmc_global_alloc_object_dual.rs` (a static beside a Box, one static reached
  as a reference and as a raw pointer, reference constants at an offset).
  Measured 2026-09-29/30 on aarch64 macOS, Trust seal 9192, ay `48c98a43d`,
  trust-ir `bf7ee706`, `scripts/soundness-dual-gate.py` at 30 s, main
  `0e21bc2b0` against the final tree, bundles run side by side: BMC lane
  missed-bug 1 -> 0 and false-certificate 14 -> 5 (match 1341 -> 1359 with the
  11 rows of the new dual, which main scores missed-bug 1, false-certificate 3,
  false-failure 1). Three rows went match -> unknown in the full run under
  load (host load 35-60), all solver budget exhaustion: on a side-by-side
  re-run two matched on this tree while the merge before the review fixes went
  unknown on them, and the third (`dual_p3_splice_stale_cex.rs`) was unknown
  on both trees and is unknown in main's own full run. Five known-red rows are
  now green and their flags are removed, so a return to a false certificate
  gates again. CHC lane: the review
  fixes touch no CHC code; the merge before them measured no row worse there.
  Kani corpus `4c0fce8c3`, BMC, 15 s, two rounds, on the merge:
  `Drop/forget_no_drop.rs`, `Static/method_static_var.rs` and
  `expected/derive-arbitrary/box` go FAILED `Genuine` -> SUCCESSFUL;
  `Tuple/tuple_trait.rs` and `ptr_comparison.rs` `check_thin_ptr` go FAILED
  `Genuine` -> INCONCLUSIVE.

### Removed (soundness — a narrowed native translation proved what the function can fail)
- `TranslateOptions::narrow_to_target_block` is deleted, with everything that
  decided which obligations a narrowed translation still answered:
  `NativeUnmodeledReason::OutsideNarrowedTarget`, the per-siting failure loci,
  and the CFG-reachability query that served both. `native_unmodeled_obligations`
  loses its `narrowed_to` parameter. The option dropped the fail-closed rule of
  every unmodeled construct in a block that could not precede a target block,
  and nothing outside tests ever set it. Three rounds of rules for which rows
  the narrowed CHC still answered each left a false PROVED: a `condbr` check or
  an `overflow` row whose failing edge reached an unmodeled `dealloc` or a
  bodyless panic, a row on a direct self-call whose callee panics on its other
  arm, and a check whose failing edge makes that self-call. A proof stands for
  a function only when its CHC keeps every rule the function can reach: the
  self-call's inductive hypothesis is exactly the claim that the function fails
  nowhere, and an obligation's failure can lie on any edge past its site. So a
  translation that drops a live rule answers no obligation, and narrowing had
  nothing left to do. Every bundle it proved is now a driver regression that
  must reach the solver and not prove under any option the proof-grade runner
  accepts.

### Fixed (soundness — an exhausted RECURSION bound is not a counterexample either)
- A `recursion unwinding assertion` no longer certifies
  `[AY:CTREX_CAT:Genuine]`. The driver already refused to certify a truncated
  search — "the unwind budget ran out, so the search was TRUNCATED. Nothing was
  disproved … emphatically not `Genuine`" — but `unwind_bound_exhausted` keyed
  on `property_id.class == "unwind"`, the BMC loop bound, and the
  recursive-inline bound that `verdict_policy::recursion_unwind_property` plants
  carries class `"recursion"`. Same meaning, different spelling, so the rule
  missed it and a harness whose search ran out of budget in `Box`/`Rc` drop-glue
  dyn dispatch reported a CERTIFIED failure on a correct program. It now keys on
  `"unwind" | "recursion"`; the verdict is untouched (still FAILED), only the
  claim about it changes — `Unknown` plus the `[AY:CTREX_NOT_CERTIFIED]` caveat,
  whose wording now names recursion beside loops. `extract_harness_values` skips
  class `"recursion"` too, so no concrete-playback `#[test]` is minted for a bug
  that was never found.
  Measured on the canonical-trustc route at Trust seal 8595:
  `kani/DynTrait/unsized_cast.rs` and `kani/DynTrait/unsized_rc_cast.rs` go
  `false_positive` -> `unknown`, closing two of the seven CHC soundness
  exceedances ledger row 68 recorded, with the DevCli route unchanged at
  `parity`. Duals: `tools/soundness-duals/recursion_unwind_dual_safe.rs`
  (`NOT_GENUINE`) and `recursion_unwind_dual_bug.rs` (the no-blinding twin).
  Unit tests in `trust-mc-driver/src/harness_runner_tests.rs` and
  `concrete_playback/test_generator.rs`. Full working, including the five units
  still open and one hypothesis implemented and falsified:
  `docs/t1-rows-2-exceedances.md`.

### Fixed (the Trust lane builds again after two nightly-only rvalue spellings)
- `codegen_ay/chc/call/codegen_call_iterator_adapter/range.rs` matched
  `Rvalue::Use(op)` and `codegen_ay/obligation_free_walk.rs` matched
  `Rvalue::Use(op)` and `Rvalue::ShallowInitBox(..)`. Trust's `rustc_public`
  gives `Use` a second field (`WithRetag`) and has no `ShallowInitBox` variant,
  so `trust-mc-engine` failed to compile on the Trust toolchain with three
  errors — the backend dylib, and therefore every counted Trustc row, could not
  be built. Both `Use` patterns take the `..` spelling `rustc_compat` documents
  as correct on BOTH toolchains, and the `ShallowInitBox` arm is
  `#[cfg(not(trust_toolchain))]` with the walk's existing catch-all failing any
  unclassified rvalue closed. No behaviour change on the frozen nightly.


### Changed (D16, second step — a compiler-certified empty obligation set exits 0, visibly)
- A harness whose obligation set is EMPTY is settled by the compiler's
  obligation-free certificate (`ArtifactMetadata.obligation_free_body`) once
  the walk behind it counts STATEMENT sites (`codegen_ay/obligation_free_walk.rs`,
  f5305896b: unchecked arithmetic and shifts, integer division, pointer
  offsets, raw-pointer dereferences, signed negation, `Index` projections,
  trait-object pointer comparisons, `copy_nonoverlapping`; every rvalue, cast
  or statement kind it does not name fails closed). Certified, the harness
  exits 0 as Kani reports the shape — through the no-checks gate, never around
  it, and never as a clean pass: `[AY:VACUOUS:no-checks]` says the compiler
  certified it, the verdict line reads `VERIFICATION:- SUCCESSFUL (no checks —
  compiler-certified obligation-free)`, the proof qualifier
  `no_checks=compiler_certified_obligation_free` displaces `clean`,
  `--proof-summary-json` files `successful_no_checks` (and counts them in
  `successful_no_checks_harnesses`), and `--sarif` leaves a `note` under
  `trust_mc.harness.no_checks` instead of an empty report. Not certified, it
  is `INCONCLUSIVE (no checks)` with exit 1 as before, and the marker now says
  an obligation may have been dropped. `tests/expected/empty` and
  `tests/expected/associated-fn` pin the certified shape; `tests/cli.rs`
  (`a_harness_with_no_checks_is_never_a_clean_proof`,
  `sarif_separates_an_undecided_harness_from_an_empty_one`,
  `a_failing_harness_always_leaves_a_sarif_finding`) pin both shapes in both
  lanes. Must-fail duals for every statement site kind
  (`tools/soundness-duals/obligation_free_stmt_dual.rs`) and must-certify twins
  (`obligation_free_stmt_dual_safe.rs`) sit beside the terminator duals.

### Fixed (soundness — `offset_from`'s distance precondition is an obligation on the CHC lane)
- Under `--ay-chc`, `ptr.offset_from(origin)` was UB-checked for same-allocation
  and (for `offset_from_unsigned`) a non-negative distance, but NOT for the third
  precondition Kani's model carries: the byte distance must be an EXACT multiple
  of `size_of::<T>()`. `expected/offset-from-distance-check/main.rs`, a harness
  whose entire purpose is that UB, printed `VERIFICATION:- SUCCESSFUL` with
  `[AY:PROOF_QUALIFIERS:clean]`. The CHC path intercepts the kani_core
  `ptr_offset_from` model and replaces its body, so the obligation existed
  nowhere on that lane; the BMC lane has emitted it since #72, which is why only
  CHC missed it. It is now emitted with the model's own message, and a
  counterexample is certified `[AY:CTREX_CAT:Genuine]`. Tripwires:
  `tools/soundness-duals/offset_from_distance_dual.rs` and its safe twin, pinned
  in `tools/soundness-duals/manifest.toml`.
- The same interception was SILENT when it could not state those checks at all —
  a pointer width other than 64, or `int_lift`, where the split-pointer
  representation they are written against does not exist — while still replacing
  the model body, so such a harness could return a clean proof with none of the
  three preconditions stated. It now records the fail-closed sound fallback
  `ptr_offset_from_ub_checks_unavailable`.

### Known (BMC certifies a counterexample on a safe `offset_from`)
- Found by the tripwire above, and NOT caused by it: under the default BMC lane,
  a `&buf[0]`-derived `*const u8` that never leaves its own 8-byte object comes
  back `VERIFICATION:- FAILED` with `[AY:CTREX_CAT:Genuine]`, reporting
  `pointer arithmetic overflow` and `Offset result and original pointer should
  point to the same allocation`. `Genuine` means "no encoding doubt", so it is a
  confident WRONG bug report rather than a demoted false failure. It reproduces
  identically on the trustc compiler route, so it is the engine's and not a
  route's. Nothing unsound passes because of it. The three rows of
  `tools/soundness-duals/offset_from_distance_dual_safe.rs` pin it as
  `known_red_class = "false-certificate"` on the `bmc` lane, with the
  expectation left at `SUCCESSFUL` so a fix flips them green on its own.

### Fixed (soundness — a harness with no obligations is never a clean pass)
- `#[kani::proof] fn h() { let _x: u8 = 3; }` printed `VERIFICATION:- SUCCESSFUL`
  and exited 0 in both lanes. Under `--ay-chc` it also printed `[AY:PROOF] CHC
  verification: property proven`. Its `--sarif` report was empty. It is
  `INCONCLUSIVE (no checks)` with `[AY:VACUOUS:no-checks]` and exit 1 again, and
  SARIF files `trust_mc.harness.no_checks`, as this file, the README and
  `explain kani` already said. The cause was 886f60544 (2026-08-25): the V4b
  no-checks gate was skipped whenever the compiler certified the body
  obligation-free (`ArtifactMetadata.obligation_free_body`). The certificate now
  only words the marker. A second check of the same invariant runs after the
  two-lane loop retry, the one later step that sets a success itself. Measured
  2026-09-11 on one frozen bundle (driver `49e87e91`, compiler `21075df7`,
  pinned ay 0.26.0 `94bf24d0f`): the certified `let _x: u8 = 3;` was SUCCESSFUL
  with exit 0 in both lanes. The uncertified, equally obligation-free
  `std::hint::black_box(3u8)` was `INCONCLUSIVE (no checks)` with exit 1 in both
  lanes. The certificate was the only difference.
  Cost, stated rather than hidden: the Kani rows the certificate had moved from
  `vacuous` to parity (`expected/empty`, `expected/associated-fn`,
  `Enum/one_two`, `DynTrait/upcast` and the rows counted in 61a0923c5,
  c0f72bcee, 2662b9ab0, 5d7bc3397 and efc81cd44) are `vacuous` again.
  D16 (updated 2026-09-11, `docs/kani-spec-engine-plan-2026-09-10.md`)
  sequences what comes next. Now, every harness with an empty obligation set
  is `INCONCLUSIVE (no checks)` with exit 1 in every lane. After the compiler
  port lands and `obligation_free_walk.rs` counts statement-level obligation
  sites (unchecked arithmetic, offsets, copies, raw derefs), a
  compiler-certified obligation-free harness will exit 0 with
  `[AY:VACUOUS:no-checks]`, a non-clean proof qualifier and a SARIF note. It
  will never be a clean SUCCESSFUL, and never a skipped gate. The two in-repo
  expected files return to the stance of c6746cbd6.

### Fixed (soundness — the external `ay` must be the pinned AY)
- The driver no longer runs whatever `ay` is first on `PATH`. The bounded lane,
  its cover and vacuity probes, the CHC cover check and the external CHC proof
  fallback now resolve `$TRUST_MC_AY_BIN` (when set; never silently replaced by
  `PATH`) or `ay` on `PATH`, read its commit from `ay --version` once per
  process, and refuse any build that is not the `rev` of `ay` in
  `[workspace.dependencies]` — another commit, a dirty build, no build stamp,
  or no answer. The refusal happens before anything is compiled and names the
  binary, its version, the pin and the fix. Measured on 2026-09-11: this
  host's `PATH` held an aterm-store ay 0.13.0 (`dd4de9e94`) against a pin of
  0.26.0 (`94bf24d0f`), and every bounded verdict had been that binary's.
- `--allow-unpinned-ay` / `TRUST_MC_ALLOW_UNPINNED_AY=1` runs an off-pin binary
  anyway: a warning, `[AY:SOLVER_PIN_MISMATCH:found=<commit>:pin=<commit>]` on
  every harness, and every success reported as `SUCCESSFUL (UNVALIDATED)`
  (so `--fail-on-unvalidated-success` fails the run).
- `trust-mc doctor` reports an off-pin `ay` as not ready with the same fix,
  falling back to the front door's own manifest pin when the engine is missing
  or will not attest its linked AY.
- The `--trust-vc-bundle` lane applies the same rule as a harness run: with
  an accepted off-pin `ay` it prints the marker and reports a success as
  `SUCCESSFUL (UNVALIDATED)`, never a clean `SUCCESSFUL`.
- Under `--allow-unpinned-ay` the two-lane loop-contract retry no longer turns
  a harness it rescues into FAILED. The child lanes inherit the switch and
  demote their own successes, while the merge accepted only a clean
  `SUCCESSFUL`. A lane's `SUCCESSFUL (UNVALIDATED)` now counts when the lane
  also prints `[AY:LOOP_TWO_LANE:success-unvalidated-only-by-unpinned-ay]`
  (the solver pin was its only caveat) and the parent accepted the same
  solver. The merged verdict is still marked and demoted, and a success
  unvalidated for any other reason still rescues nothing.
- A debug build no longer panics (`linear logic results must remain
  validated`, exit 101) when `--allow-unpinned-ay` demotes a linear-logic
  success; the demotion broke that assertion for every such harness and for
  the `--trust-vc-bundle` lane. Release builds compile the assertion out and
  were unaffected.
- Evidence tools attest the binary the driver actually runs. kani-domination
  resolves `AY_BIN`, then `TRUST_MC_AY_BIN`, then `../ay`, then `PATH`, and
  passes the result to the driver as `TRUST_MC_AY_BIN`, so a ledger row's
  `ay_binary_version` cannot describe a different solver than the one run.
  The replacement-proof and soundness-gate scripts attest `$TRUST_MC_AY_BIN`
  when it is set.
- kani-domination never scores a row from an off-pin solver. Verifier children
  lose `TRUST_MC_ALLOW_UNPINNED_AY` (listed among the attestation's scrubbed
  variables), `--allow-unpinned-ay` is dropped from test flags and refused as
  an extra driver flag, and any output carrying `[AY:SOLVER_PIN_MISMATCH:` is
  scored `error`. Separately, `VERIFICATION:- SUCCESSFUL (UNVALIDATED)` (from a
  non-linear logic tier as well as an off-pin solver) passed `clean_success`,
  because `VERIFICATION:- SUCCESSFUL` is a substring of it, and scored `parity`.
  It now scores `unsound_pass` against a passing oracle, never
  `exceeds_oracle`, and stays `missed_bug` against a failing one.

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

- An undecided harness no longer prints an EMPTY check table. When the solver
  answers `unknown` (or returns a model naming no violation) there is no
  per-check verdict to read, so the report showed `RESULTS:` with nothing under
  it and `** 0 of 0 failed` — the report of a harness that emitted no obligation
  at all, which is the opposite diagnosis. The checks the compiler actually
  emitted are now listed with `Status: UNDETERMINED` and their real
  descriptions, rebuilt from the same SMT declarations the UNSAT path uses, and
  the summary carries the count (`** 0 of 23 failed (23 undetermined)`), as Kani
  does. 75 of the 462 `tests/expected` harnesses printed the empty table.
  `Undetermined` claims nothing, so no obligation is dropped and nothing
  undecided is promoted. The `INCONCLUSIVE (solver undecided …)` verdict — in
  both the console and the `--proof-summary-json` / `--sarif` channel — now keys
  on "no check is DECIDED" rather than "there are no checks", which those two
  populated tables would otherwise have fallen through into a wrong `FAILED`
  verdict. `INCONCLUSIVE (no checks)` keeps its literal empty-table key for the
  case where the solver fell over before any check existed.

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
- AY pin advanced to `c3fd4bcf6cbae5564fe4c7b23f1c5690abf6e4e2` (v0.23.0),
  via `8ccb70761d3f87905936b787d7bc1a3b1eccaf30` on 2026-08-31. The v0.23.0
  line delivers essentially every API-level ask on the trust-mc → AY ledger:
  per-query CHC obligation discharge with partial results, scalar-return
  uninterpreted functions with congruence, exact wide bit-vectors and i128
  widening (W1/W11), a deterministic sequential mode, same-invocation proof
  telemetry, construction-boundary cancellation, and strict proof binding to
  exact SMT-LIB queries. Adoption of those surfaces is separate work and is in
  progress; a delivered capability earns no parity credit until trust-mc calls
  it and the corpus is re-measured.
  The intervening pin advances between `5bd746693` and `8ccb70761` were never
  recorded here; this entry closes the gap rather than reconstructing each one.
- TrustIR pin advanced `77b1adf14` → `31e9e618dba7ce3e220b2989cf2fc050c2de24ea`
  (trust-ir main, wire format v40, 2026-09-12), in the same commit as
  `tools/tuple.toml`. v40 adds `FatPtrKind::ContainerVtable` — the `dyn`-tail
  container pointer (`*const ArcInner<dyn Any>` inside `Arc<dyn Any>`), whose
  metadata is an opaque VTABLE WORD and never a length — and the CHC
  translator's exhaustive carrier census refused to compile (E0004) rather
  than fold it into a neighbour. It now names the kind as its own census class
  (`FatPtr_ContainerVtable`) and classifies it by metadata meaning with
  `TraitObject`: a `PtrMetadata` read of either vtable-word kind is refused as
  `PointerMetadata` whatever `metadata_ty` a producer spelled, and the
  `len <= isize::MAX` bound is now matched exhaustively over the kinds. The
  BMC lane already refused the read by name (`Debug` of the pointer type).
  The Clean revision TrustIR consumes is unchanged (`feb5b3a9d`).

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
