; ============================================================================
; repro_dyn_struct.smt2  --  ay CHC reproducer  (key: dyn_struct)
; ============================================================================
;
; SOURCE HARNESS
;   <repo>/target/kani-domination/kani/tests/kani/Drop/dyn_struct_member.rs
;   harness `check_drop_dyn`, flags: (none)
;   Real VC produced by:
;     trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=15s dyn_struct_member.rs
;   -> dyn_struct_member__RNvCsfrKlYLh7uYy_17dyn_struct_member14check_drop_dyn.symtab.smt2
;      (237 lines / 132,830 bytes; 51 relations, 55 rules, arities up to 61)
;   This file is that VC reduced by delta-debugging to 14 lines / 532 bytes.
;
; AY VERDICT ON THIS FILE  (ay 0.5.0+build.6947.610856d76)
;     $ ay solve --timeout 60000 repro_dyn_struct.smt2
;     [AY SOUNDNESS GATE] caught an INVALID model -- a theory-search path
;         returned a model that falsifies an assertion.  logic: QF_AUFBV
;     c !! MODEL-UNCONFIRMED ... SAT degraded to Unknown
;     unknown
;     (:reason-unknown "incomplete: CHC portfolio exhausted all strategies within budget")
;   EXPECTED: sat.  In the (declare-rel/rule/query) Horn dialect `(query error)`
;   answers `sat` when `error` is derivable.  Here `error` is derivable in two
;   trivial steps: the single non-fact rule's body is a pair of definitional
;   equations that are satisfiable by inspection (they merely name `obj_valid__out`
;   and the 256-bit word), so `error_p5`, hence `error`, follows.  ay answers
;   `unknown`.  Not budget-bound: still `unknown` at 60 s and at 120 s, and the
;   original harness is still `unknown` at a 180 s budget.
;
; WHAT AY CANNOT DO  (one sentence)
;   When a Horn rule body contains BOTH an Array-sorted equation AND an equation
;   over a bitvector wider than 128 bits, ay's theory search builds a model that
;   its own model-validation oracle rejects, and it fail-closes to `unknown`
;   instead of deciding the (trivially satisfiable) query.
;
; ISOLATION -- measured, each line is a separate ay run on a hand-built variant
;   (baseline body = one Array equation + one wide-BV equation; expected `sat`)
;
;     Array eq alone .................................... sat      (correct)
;     wide-BV eq alone (no Array anywhere) .............. sat      (correct)
;     Array eq + BV eq at width 126 / 127 / 128 ......... sat      (correct)
;     Array eq + BV eq at width 129 ..................... unknown  <-- BREAKS
;     ... and every width tested above 128 (130,132,136,144,
;         160,192,224,240,248,256,264,320,384,512) ...... unknown
;     Array eq + BV256 declared but NOT constrained ..... sat      (correct)
;     Int eq   + BV256 eq ............................... sat      (correct)
;     Bool eq  + BV256 eq ............................... sat      (correct)
;     BV64 eq  + BV256 eq ............................... sat      (correct)
;     (Array (BV 8) Bool)  + BV256 eq ................... unknown  (index width irrelevant)
;     (Array (BV 32) (BV 8)) + BV256 eq ................. unknown  (element sort irrelevant)
;     `store` vs plain array equality ................... irrelevant (both break)
;     `select` only (no Array-sorted term) + BV256 eq ... sat      (correct)
;     wide term built by concat / bvadd / a constant .... unknown  (all break)
;     the two equations split across two rules .......... unknown  (still breaks)
;
;   So the trigger is exactly: an Array-SORTED term coexisting with a bitvector
;   term of width > 128 in the same CHC query.  The 128-bit cliff is sharp
;   (128 ok, 129 not), which points at a 128-bit limb/word assumption in the
;   BV layer that the array-aware path does not honour.
;
; WHY THE HARNESS HITS IT
;   `Wrapper<T: ?Sized> { w_id: u128, inner: DummyImpl { id: u128 } }` lowers to a
;   256-bit memory word (`concat` of the two u128 fields), and trust-mc threads a
;   per-object validity map `obj_valid : (Array (BitVec 32) Bool)` through every
;   block relation.  Every Rust type with >128 bits of scalar payload reaching a
;   VC that also carries the object-validity array lands in this hole.
;
; NOTE ON A RELATED SIGNAL (not required to reproduce this file)
;   Per-rule alpha-renaming of `declare-var` names -- semantics-preserving, since
;   Horn rule variables are implicitly universally quantified per rule -- changes
;   ay's behaviour on the 37-rule intermediate reduction (the invalid-model gate
;   stops firing, though the answer stays `unknown`).  That suggests the flattening
;   pass keys on variable NAMES across rules.  Worth a look, separately.
;
; PROVENANCE OF THE REDUCTION (each step re-ran ay and kept only what still failed)
;   132,830 B  original VC (51 rels / 55 rules / 1797 predicate columns)
;    13,972 B  after rule ddmin + column ddmin (1797 -> 2 columns)
;     9,906 B  after contracting the 37-block acyclic chain to 2 rules
;     1,007 B  after conjunct ddmin
;       532 B  after dropping the unused datatype declarations  <-- this file
;
;   `obj_valid` is the ONLY array in the whole original VC, so the driver's
;   ">=2 Array-sorted state parameters" label (trust-mc-driver/src/call_ay/chc/
;   native.rs:103,137) does not even apply to this harness -- and array-param
;   COUNT is not the cause in any case.
; ============================================================================

(set-logic HORN)

(declare-var obj_valid       (Array (_ BitVec 32) Bool))
(declare-var obj_valid__out  (Array (_ BitVec 32) Bool))
(declare-var _check_drop_dyn_mem_Wrapper_DummyImpl_at_0x300000000_bv64__out (_ BitVec 256))

(declare-rel error ())
(declare-rel error_p5 ())

; the object-validity map gains object 0x29, and the 256-bit Wrapper<DummyImpl>
; word is defined as concat(w_id = 0u128, inner.id = 1u128).
; Both conjuncts are plainly satisfiable, so error_p5 is derivable.
(rule (=> (and (= obj_valid__out (store obj_valid #x00000029 true))
               (= _check_drop_dyn_mem_Wrapper_DummyImpl_at_0x300000000_bv64__out
                  (concat #x00000000000000000000000000000000
                          #x00000000000000000000000000000001)))
          error_p5))

(rule (=> error_p5 error))

(query error)
