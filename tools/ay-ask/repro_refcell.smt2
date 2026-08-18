; ============================================================================
; ROOT CAUSE — CONFIRMED BY INSTRUMENTING AY (2026-08-08, pin 610856d76)
;
; ay SOLVES this problem and then DISCARDS its own answer:
;   "Adaptive: BV-native acyclic BMC probe solved the problem"
;   "...promoting Safe via CheckedQueryOnlyDischarge"
;   -> unknown (:reason-unknown "CHC SAFE certificate failed final clause
;                                discharge; demoted to unknown for soundness")
;
; THE DEFECT: the interpretation reaching `apply_interp_to_args`
; (ay-chc/src/pdr/verification/helpers.rs:236) has a parameter list with a
; DUPLICATE NAME. Instrumented output on this file:
;
;   BINDPROBE vars=["_main_95", "_main_1_fld3__out", "_main_95"]
;             args=["_main_1_fld2", "_main_1_fld3", "_main_95"]
;             formula=(= _main_95 (_ bv3 8))  =>  (= _main_95 (_ bv3 8))
;
; `_main_95` occupies BOTH position 0 and position 2. `substitute` is
; first-match by name, so the formula binds ambiguously and lands on argument
; #2 instead of #0. Clause 7 is
;   (main__bb54 _main_1_fld2 _main_1_fld3 _main_95) => (main__bb2 _main_1_fld2)
; which is a TAUTOLOGY under correct binding, and it is reported
; "implication failed".
;
; NOTE the parameter names are CLAUSE variable names, not the canonical
; `__p{pred}_a{idx}` names that `build_canonical_predicate_vars`
; (ay-chc/src/pdr/solver/helpers/mod.rs:11) generates — canonical names are
; distinct by construction. So the interpretation on this path is built
; elsewhere, from clause-derived names whose uniqueness is not enforced.
; WHERE that list is constructed was NOT traced; that is the next step.
;
; What is MEASURED, not inferred:
;   * the zip in apply_interp_to_args is correct (positional, no length
;     mismatches observed anywhere in the run);
;   * an earlier hypothesis that this was "invariant synthesis degrading in the
;     presence of an array column" is NOT what the instrumentation shows.
; ============================================================================
; ============================================================================
; repro_refcell.smt2 — minimized ay CHC reproducer
; ============================================================================
;
; SOURCE HARNESS
;   target/kani-domination/kani/tests/kani/Drop/drop_after_mutating_refcell.rs
;   (harness `main`; trust-mc flags: none)
;   Real VC emitted by the driver:
;     drop_after_mutating_refcell__RNvCsfgVJttMSBA2_...4main.symtab.smt2
;     2430 lines / 515 KB, 77 relations (max arity 142, 8 Array-sorted columns
;     per block relation), 109 rules, 34 property checks.
;   This file: 37 lines, 10 relations, 10 rules, max arity 3.
;
; WHAT AY CANNOT DO (one sentence)
;   ay proves this CHC system Safe and then throws the proof away: its
;   always-on SAFE-certificate discharge gate cannot substitute an invariant
;   interpretation into a clause whose body predicate carries an ARRAY-SORTED
;   ARGUMENT, so it misbinds the remaining scalar arguments, declares the
;   tautological clause `bb54(x, arr, y) => bb2(x)` an "implication failed",
;   and demotes the verdict to `unknown` — even though that array is never
;   read, never written, and never constrained anywhere in the problem.
;
; AY VERDICT (verbatim)
;   $ ay solve --timeout 300000 repro_refcell.smt2
;   unknown
;   (:reason-unknown "CHC SAFE certificate failed final clause discharge; demoted to unknown for soundness")
;   ...wall_time_ms=12
;
;   NOT a budget problem: ay gives up after 12 ms with a 300 000 ms budget.
;   `--no-validate` and `--competition` do NOT disable the gate.
;
; INDEPENDENT CONTROL
;   $ z3 repro_refcell.smt2      ->  unsat   (= SAFE in this dialect)  in 0.00 s
;   z3 also decides the FULL 2430-line VC in 0.40 s; ay is unknown there at
;   15 s, 60 s and 300 s.
;
; THE ONE-LINE ABLATION THAT PROVES THE CAUSE
;   Delete the middle (Array (_ BitVec 8) Bool) column from main__bb54 —
;   a column with zero `select` and zero `store` anywhere in the file — and:
;     ay  ->  unsat   (proved, 23 ms)
;   Put the array back in ANY position (first / middle / last): unknown again.
;   Replace it with a Bool column in the SAME position:          unsat.
;   => the ARRAY SORT is the trigger, not arity, not array COUNT, not the
;      "2 Array-sorted state parameters" heuristic trust-mc's driver reports
;      (trust-mc-driver/src/call_ay/chc/native.rs:103,137) — one inert array
;      column is already enough.
;
; INTERNAL EVIDENCE (ay solve --verbose)
;   Adaptive: BV-native acyclic BMC probe ... Acyclic BMC probe solved the problem
;   Adaptive: BV-native query-only discharge re-proved all 1 query bodies UNSAT
;             on a fresh executor; promoting Safe via CheckedQueryOnlyDischarge
;   PDR: verify_model: clause 7 implication failed
;     body=(= _main_95 (_ bv3 8))
;     head=(= _main_1_fld2 (_ bv3 8))
;     model={"_main_95": BitVec(3, 8), "_main_1_fld2": BitVec(0, 8)}
;   Clause 7 is `(main__bb54 _main_1_fld2 _main_1_fld3 _main_95) => (main__bb2 _main_1_fld2)`.
;   Under a correct substitution this is a tautology: bb2's single parameter is
;   bb54's argument #0. The validator instead compares the constraint on
;   argument #2 with the constraint on argument #0 and reports a violation.
;   Gate: ay/crates/ay/src/chc_runner.rs:283 chc_safe_invariant_discharges
;         -> ay-chc/src/lib.rs:679 external_invariant_model_excludes_error
;         -> ay-chc/src/pdr/verification/model.rs:258 verify_model_query_only
;   (budget there is hard-capped at 10 s: chc_runner.rs:290 `.min(Duration::from_secs(10))`,
;    so a larger user --timeout cannot help even when the check is merely slow.)
;
; WHY THIS SHAPE COMES OUT OF RUST
;   trust-mc gives every basic-block relation the whole function state as
;   columns, including whole-memory arrays (Array BV64 -> BV192 for the
;   Vec<u32> heap, Array BV32 -> Bool for object validity, ...). Most blocks
;   never touch them; they are pass-through columns exactly like the one below.
;   So this gate fires on essentially every trust-mc CHC harness that models
;   memory — which is the `unknown` bucket.
;
; SHAPE OF THIS PROBLEM
;   acyclic (cycles=false), linear (one body predicate per rule), 10 predicates,
;   dag depth 10, no loops, no recursion, no quantifiers, no datatypes,
;   BV8 + Bool + one Array(BV8 -> Bool) column, no select, no store.
;   By hand: bb53(3) -> bb54(3,arr,3) -> bb2(3) -> bb14(*) -> bb50(0)
;            -> bb17(b,w) with b = (0 <u k), w = ite(0 <u k, 0, *)
;            -> guard forces b, hence w = 0 -> bb48(0)
;            -> error needs 0 >u 0x7f : unreachable. SAFE.
;
; REDUCTION PROVENANCE
;   Delta-debugged from the real VC with a two-sided oracle: every step had to
;   keep (a) z3 deciding the problem and (b) ay answering `unknown` for a
;   CAPABILITY reason (steps whose `unknown` was merely `:reason-unknown
;   "timeout"` were rejected, so nothing here is budget-bound).
; ============================================================================

(set-logic HORN)
(declare-var _main_1_fld2 (_ BitVec 8))
(declare-var _main_1_fld2__out (_ BitVec 8))
(declare-var _main_1_fld3 (Array (_ BitVec 8) Bool))
(declare-var _main_1_fld3__out (Array (_ BitVec 8) Bool))
(declare-var _main_26_fld0 (_ BitVec 8))
(declare-var _main_26_fld0__out (_ BitVec 8))
(declare-var _main_26_fld1 (_ BitVec 8))
(declare-var _main_27_fld0 Bool)
(declare-var _main_27_fld0__out Bool)
(declare-var _main_27_fld1 (_ BitVec 8))
(declare-var _main_27_fld1__out (_ BitVec 8))
(declare-var _main_90 (_ BitVec 8))
(declare-var _main_90__out (_ BitVec 8))
(declare-var _main_95 (_ BitVec 8))
(declare-var _main_95__out (_ BitVec 8))
(declare-rel error ())
(declare-rel error_p3 ())
(declare-rel main__bb14 ((_ BitVec 8)))
(declare-rel main__bb17 (Bool (_ BitVec 8)))
(declare-rel main__bb19 ((_ BitVec 8)))
(declare-rel main__bb2 ((_ BitVec 8)))
(declare-rel main__bb48 ((_ BitVec 8)))
(declare-rel main__bb50 ((_ BitVec 8)))
(declare-rel main__bb53 ((_ BitVec 8)))
(declare-rel main__bb54 ((_ BitVec 8) (Array (_ BitVec 8) Bool) (_ BitVec 8)))
(rule (=> error_p3 error))
(rule (=> (and (main__bb48 _main_90) (not (bvule _main_90 #x7f))) error_p3))
(rule (=> (and (main__bb19 _main_27_fld1) (= _main_90__out _main_27_fld1)) (main__bb48 _main_90__out)))
(rule (=> (and (main__bb17 _main_27_fld0 _main_27_fld1) _main_27_fld0) (main__bb19 _main_27_fld1)))
(rule (=> (and (main__bb50 _main_26_fld0) (= _main_27_fld0__out (bvult _main_26_fld0 _main_26_fld1)) (= _main_27_fld1__out (ite (bvult _main_26_fld0 _main_26_fld1) _main_26_fld0 _main_27_fld1))) (main__bb17 _main_27_fld0__out _main_27_fld1__out)))
(rule (=> (and (main__bb14 _main_27_fld1) (= _main_26_fld0__out #x00)) (main__bb50 _main_26_fld0__out)))
(rule (=> (main__bb2 _main_1_fld2) (main__bb14 _main_27_fld1)))
(rule (=> (main__bb54 _main_1_fld2 _main_1_fld3 _main_95) (main__bb2 _main_1_fld2)))
(rule (=> (and (main__bb53 _main_95) (= _main_1_fld2__out _main_95)) (main__bb54 _main_1_fld2__out _main_1_fld3__out _main_95)))
(rule (=> (= _main_95__out #x03) (main__bb53 _main_95__out)))
(query error)
