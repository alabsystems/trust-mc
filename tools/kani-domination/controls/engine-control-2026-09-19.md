# Engine-suite control, 2026-09-19 — bound VERIFIED, not asserted

The trust-mc-engine lib suite's known-fail set, captured with the per-AY-test bound's inheritance
**observed** rather than assumed. Previous controls had to be adopted from session scratchpads and carried
"asserted, not verified" on the bound; this one does not.

## Run identity

```
tree                  1681cf0c6a4386cb412288869956e8908e414127  (branch fix/zst-extent-obligation)
compiled inputs vs main  0 differing AT CAPTURE (main was 49d3c7dc0) -> this was MAIN's control
                      see the VALIDITY WINDOW below before reusing it
driver                aac6d73ab5beeca4
ay CLI                ay 0.27.0+build.10306.7bb59d28b71ffd631100b61204ef43a285a4a626@2026-09-18T22:53:38Z
toolchain             nightly-2025-12-03
command               cargo test --locked -p trust-mc-engine --lib --features ay,compiler-corpus-tests
result                7550 tests · 7515 passed · 15 failed · 20 ignored · 0 filtered out · 1951.23s
cargo status           101 (test failures), propagated as the payload's own exit code
```

## The bound, observed

`TRUST_MC_AY_TEST_TIMEOUT_SECS=120` is **mandatory** at this ay pin: unbounded, the suite deadlocks
(~7527 results, then threads parked in `futex_do_wait`). But it cannot be read out of a suite log — all
four read sites are bare `std::env::var` chains falling back through `TRUST_MC_Z3_TEST_TIMEOUT_SECS` to a
compiled-in default, so an unset variable yields a **silent default**, and the value surfaces only in an
`Err` at `statement/tests/mod.rs:231` when a test actually times out. "0 mentions in the log" is therefore
exactly what a correctly-bounded run that never hit the bound looks like: an unfalsifiable check.

Observed instead from the test process's own environment, by two parties independently:

```
this session:   95 samples, 00:17:22 -> 00:49:18 (the full 1951s run)
                = 94 timed loop samples (~21s apart, max gap 21s) + 1 hand read
                  tagged MANUAL at 00:18:32 -- same pid, exe and value as the rest,
                  taken to confirm the process existed before announcing it
                1 distinct value, 1 distinct pid (99964), 1 distinct exe
                trust_mc_engine-3b1b06f73b07cbd4 ; 0 BOUND-ABSENT rows
peer agent:     62 bound-present samples over 30.5 unbroken minutes (no gap > 45s),
                plus 18 trailing "no process" rows — which prove the sampler could still
                have recorded an absence at the moment it recorded none
```

The method, for reuse:

```sh
for d in /proc/[0-9]*; do
  p=${d#/proc/}; exe=$(readlink "/proc/$p/exe" 2>/dev/null) || continue
  case "$exe" in *deps/trust_mc_engine-*)
    tr '\\0' '\\n' < "/proc/$p/environ" | grep '^TRUST_MC_AY_TEST_TIMEOUT_SECS=' ;;
  esac
done
```

Match on the **exe** (hash-suffixed), never on cmdline text, and keep sampling after the suite exits so
"process gone" and "process present without the bound" cannot render identically. This session's sampler stops
when the suite does, so its file cannot make that distinction -- the peer's 18 trailing "no process" rows can,
and that is the better design: it proves the sampler was still able to record an absence at the moment it
recorded none. Adopt the trailing rows next time.

The evidence file tags each row's provenance (`MANUAL` vs timed). Keep that distinction: a hand sample and a
loop sample are equally valid evidence about the process, but a reader must be able to tell how many of each
there are without re-deriving it from timestamps.

## Validity window

A control is a fact about the tree it was taken against, not a standing property of `main`.

    captured against   tree 1681cf0c6, main at 49d3c7dc0, ay pin 7bb59d28b71f
    STALE as of        56dd529dd (2026-09-21) -- the AY cohort moved to 5d900fd2fd27,
                       **217 commits of solver fixes**. Also 5460a52a8 (trust-mc-driver/src/native.rs)
                       and 3b1bce6f9 (trust-ir Inst::MakeAggregate, fail-closed).

**The pin bump is the staleness that matters, and the mechanism is measured, not assumed.** The engine suite does
NOT shell out to an `ay` binary: ay is linked **in-process** as crate dependencies -- `ay_bindings`, `ay-dpll`,
`ay-frontend`, `ay-chc` in `trust-mc-engine/Cargo.toml` -- and `run_ay_on_smt2_with_timeout`
(`statement/tests/mod.rs`) calls `ay_frontend::parse` then `ay_dpll::Executor::new()` directly, with the bound
enforced by a `std::thread::spawn` timer rather than a process watchdog. `TRUST_MC_AY_BIN` never enters it; the
only `Command::new` nearby is a `z3` fallback in the integration runner. So the bump changes **the code compiled
into the test binary**, not a subprocess it calls, and `Cargo.toml` is one of the two files the bump touched.
The 15-row set is therefore at real risk from those 217 commits, by a firmer mechanism than a subprocess would be.

A correction worth carrying: this file's earlier "0 compiled inputs differing" framing counted only
`trust-mc-*/src` and `library/` paths and never contemplated a **dependency** bump as a compiled input. It is one.

`trust-mc-driver/src/native.rs` remains the lesser concern (the engine lib tests do not link the driver), and
`3b1bce6f9` is a trust-ir cohort repair. Treat the set as **historical**: valid for the pin it names, and
re-capture at the new pin before using it to judge or gate anything.

**How to re-capture cheaply:** the run is ~33 minutes and the method is in this file. Check first whether anything
under `trust-mc-compiler/`, `trust-mc-engine/` or `library/` changed since `49d3c7dc0`; if only the driver or docs
moved, a re-capture confirms rather than corrects, and saying so is more useful than either silence or a bare
re-run.

## The 15 known failures

```
codegen_ay::chc::tests::test_bootstrap_arrays_tier3::visible_state::test_bootstrap_arrays_pop_restores_probe_solver_unsat_mem_track
codegen_ay::chc::tests::test_call_alloc::test_box_new_double_dyn_payload_solver_produces_proof
codegen_ay::chc::tests::test_call_alloc::test_box_new_predecessor_dyn_payload_solver_produces_proof
codegen_ay::chc::tests::test_call_block_on::test_block_on_dispatch_claims_call_without_loop_exhaustion
codegen_ay::chc::tests::test_call_block_on::test_manual_block_on_dispatch_ref_destination_avoids_coerce_drop
codegen_ay::chc::tests::test_call_rc_dyn_value::test_check_rc_dyn_diff_raw_parts_full_shape_classification
codegen_ay::chc::tests::test_call_rc_dyn_value::test_check_rc_dyn_raw_parts_metadata_stays_within_current_ceiling
codegen_ay::chc::tests::test_call_rc_dyn_value::test_probe_7_vs_8_diagnostic_comparison
codegen_ay::chc::tests::test_call_referent_resolve::test_box_inner_dyn_referent_restores_fat_pointer_semantics
codegen_ay::chc::tests::test_call_virtual_inline_solver::test_rc_outer_dyn_semantic_solver_produces_proof
codegen_ay::chc::tests::test_transition_gen::test_nested_box_dyn_drop_solver_produces_unsat
codegen_ay::statement::tests::atomic::test_atomic_load_empty_args_returns_none
codegen_ay::statement::tests::atomic::test_atomic_store_insufficient_args_returns_target
codegen_ay::statement::tests::dispatch::mir_string_slice_clone::test_mir_slice_eq_dispatch
codegen_ay::statement::tests::dispatch::mir_string_slice_clone::test_mir_vec_as_slice_eq_dispatch
```

Byte-identical to this session's earlier run at `2ba77a675`, which is the prediction (zero compiled inputs
differ between the trees) rather than a coincidence. The peer agent's own 16-row control shares 15 of these;
the difference is `test_bootstrap_lra_scale_call_keeps_receiver_target_resolution`, which is
**concurrency-deterministic, not flaky** — PASS 3/3 solo, FAIL 3/3 under `--test-threads 4`, on both
bundles, because the translation-drop site-reason map is polluted across concurrent tests. Exclude it by
name; its presence is evidence about thread count, not about a branch.
