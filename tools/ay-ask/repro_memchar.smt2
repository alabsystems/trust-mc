; ============================================================================
; repro_memchar.smt2  --  minimal ay CHC reproducer
; ============================================================================
;
; SOURCE HARNESS
;   kani/tests/expected/loop-contract/memchar_naive.rs :: memchar_naive_harness
;   (trust-mc, flags: --ay-chc -Z unstable-options -Z loop-contracts,
;    harness timeout 15s).  Expected result: VERIFICATION SUCCESSFUL.
;   Actual: [AY:UNKNOWN] CHC verification: solver returned unknown
;           [AY:UNKNOWN_REASON:SolverError]
;
; AY VERDICT ON THIS FILE
;   $ ay solve --timeout 300000 repro_memchar.smt2
;   unknown
;   (:reason-unknown "incomplete: CHC portfolio exhausted all strategies
;                     within budget")            [gave up after 285 s]
;   Same verdict at 60 s, with --no-validate, and with --competition.
;   z3 -T:60 fp.engine=spacer repro_memchar.smt2   ->  unsat   in 0.00 s
;   (z3 also solves the FULL unreduced 461 KB VC in 0.07 s.)
;
; WHAT AY CANNOT DO  (one sentence)
;   ay cannot propagate a constant through a chain of uninterpreted Horn
;   predicates: this system is ACYCLIC (no recursion, no invariant to infer)
;   and the only fact needed is "x3 = 0 flows B1 -> B29 -> B26 -> B39 -> B40",
;   which kills the two guarded edges and forces x5 = true at B25 -- yet no
;   engine in ay's CHC portfolio derives it, while ay itself decides the very
;   same problem in 0.3 s once the intermediate predicates are eliminated by
;   resolution.
;
; ---------------------------------------------------------------------------
; THE PROOF, IN FULL (this is all that is required)
;   B0  is total.  B0 -> B1 sets x3 = 0.
;   B1 -> B29 -> B26 -> B39 -> B40 -> B42 all pass x3 through unchanged.
;   Therefore at B39:  (bvule x3 #x..05) holds, so the B41 edge, guarded by
;     (not (bvule x3 #x..05)), is infeasible.
;   Therefore at B40:  x3 = 0, so the B43 edge, guarded by (not (= x3 #x..00)),
;     is infeasible -- and with it B44, B45.
;   The only surviving path is B40 -> B42 -> B46, which sets x5 = true.
;   B46 -> B47 -> B25 carries x5 = true, so the B25 -> B17 edge, guarded by
;     (not x5), is infeasible.  B17, error_p3 and error are unreachable.
;
;   A witnessing model is a one-liner:
;     B0 = true
;     B1 = B29 = B26 = B39 = B40 = B42 := (= x3 #x0000000000000000)
;     B41 = B43 = B44 = B45 := false
;     B46 = B47 := x5      B25 := x5
;     B17 = error_p3 = error := false
;
; FEATURE PROFILE  (what is NOT in here)
;   no arrays, no quantifiers, no algebraic datatypes, no uninterpreted
;   functions, no multiplication/division, no recursion.  Theory content is
;   exactly: =, and, not, bvule, bvult over one BitVec 64 and two Bool
;   columns.  19 rules, 17 predicates, max arity 3, DAG depth 11.
;
; MINIMALITY (each checked by re-running ay after the edit)
;   * 1-minimal in RULES: deleting ANY one of the 19 rules makes ay answer
;     unsat in < 1 s.
;   * 1-minimal in COLUMNS: deleting x3, x5 or x65 makes ay answer in < 2 s
;     (x65 is especially telling -- it is a Bool column that is *written once*
;     on the B39 -> B40 edge and *never read*; deleting it flips ay to unsat).
;   * 1-minimal in CONJUNCTS: 47 of the 55 original body conjuncts were
;     already deleted; each of the remaining 8 is load-bearing.
;   * Width is irrelevant: rewriting BitVec 64 -> BitVec 8 keeps the unknown.
;
; PROVENANCE OF THE REDUCTION
;   Full VC: 362 lines / 461,062 bytes, 57 predicates of arity 88-95,
;   95 rules, 15 proof obligations (error_p0..error_p14).  The VC is ACYCLIC:
;   trust-mc's loop-contract lowering leaves NO cycle in the predicate graph,
;   so this is bounded model checking presented in Horn form, not invariant
;   inference.  Slicing to one obligation at a time, only error_p3 (a
;   memory-safety check) is unknown; the other 14 are decided in 0.04-20 s.
;   Delta-debugging that slice (columns, then conjuncts, then columns again)
;   gives the 19 rules below.
;
; CONTROL EXPERIMENT (the key datum for a solver engineer)
;   Eliminating the 15 intermediate predicates by linear Horn resolution --
;   a purely syntactic unfold of this DAG, 3 constraint-only rules -- turns
;   this into a problem ay solves instantly:
;     ay solve  <inlined>  ->  unsat  in 0.27 s, with an ay-chc SAFE
;                              certificate.
;   The same holds for the unreduced VC: inlined, ay answers unsat in 1.5 s;
;   as Horn clauses, ay answers unknown at 60 s.  So the gap is not the
;   bit-vector reasoning and not the budget -- it is that ay's CHC portfolio
;   never reduces an acyclic (loop-free) Horn system to the trivial
;   BMC/unfolding query it actually is.
; ============================================================================

(set-logic HORN)
(declare-var x3 (_ BitVec 64))
(declare-var x3_o (_ BitVec 64))
(declare-var x5 Bool)
(declare-var x5_o Bool)
(declare-var x65 Bool)
(declare-var x65_o Bool)
(declare-rel B0 ((_ BitVec 64) Bool Bool))
(declare-rel B1 ((_ BitVec 64) Bool Bool))
(declare-rel B17 ((_ BitVec 64) Bool))
(declare-rel B25 ((_ BitVec 64) Bool))
(declare-rel B26 ((_ BitVec 64) Bool Bool))
(declare-rel B29 ((_ BitVec 64) Bool Bool))
(declare-rel B39 ((_ BitVec 64) Bool Bool))
(declare-rel B40 ((_ BitVec 64) Bool Bool))
(declare-rel B41 ((_ BitVec 64) Bool Bool))
(declare-rel B42 ((_ BitVec 64) Bool Bool))
(declare-rel B43 ((_ BitVec 64) Bool Bool))
(declare-rel B44 ((_ BitVec 64) Bool Bool))
(declare-rel B45 ((_ BitVec 64) Bool Bool))
(declare-rel B46 ((_ BitVec 64) Bool Bool))
(declare-rel B47 ((_ BitVec 64) Bool Bool))
(declare-rel error ())
(declare-rel error_p3 ())
(rule (=> true
          (B0 x3 x5 x65)))
(rule (=> (and (B0 x3 x5 x65)
               (= x3_o #x0000000000000000))
          (B1 x3_o x5 x65)))
(rule (=> (B1 x3 x5 x65)
          (B29 x3 x5_o x65)))
(rule (=> (B29 x3 x5 x65)
          (B26 x3 x5 x65)))
(rule (=> (B26 x3 x5 x65)
          (B39 x3 x5 x65)))
(rule (=> (and (B39 x3 x5 x65)
               (not (bvule x3 #x0000000000000005)))
          (B41 x3 x5 x65_o)))
(rule (=> (and (B39 x3 x5 x65)
               (= x65_o (bvule x3 #x0000000000000005)))
          (B40 x3 x5 x65_o)))
(rule (=> (B40 x3 x5 x65)
          (B42 x3 x5 x65)))
(rule (=> (and (B40 x3 x5 x65)
               (not (= x3 #x0000000000000000)))
          (B43 x3 x5 x65)))
(rule (=> (B41 x3 x5 x65)
          (B47 x3 x5_o x65)))
(rule (=> (and (B42 x3 x5 x65)
               (= x5_o true))
          (B46 x3 x5_o x65)))
(rule (=> (and (B43 x3 x5 x65)
               (not (bvult x3 #x0000000000000001)))
          (B44 x3 x5 x65)))
(rule (=> (B44 x3 x5 x65)
          (B45 x3 x5 x65)))
(rule (=> (B45 x3 x5 x65)
          (B46 x3 x5_o x65)))
(rule (=> (B46 x3 x5 x65)
          (B47 x3 x5 x65)))
(rule (=> (B47 x3 x5 x65)
          (B25 x3 x5)))
(rule (=> (and (B25 x3 x5)
               (not x5))
          (B17 x3 x5)))
(rule (=> error_p3
          error))
(rule (=> (B17 x3 x5)
          error_p3))
(query error)
