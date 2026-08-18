; ============================================================================
; repro_from_raw_parts.smt2 — minimal ay CHC reproducer
;
; SOURCE HARNESS
;   target/kani-domination/kani/tests/kani/Quantifiers/from_raw_parts.rs
;   (kani-flags: -Z quantifiers)   harness `main`
;   Real VC: from_raw_parts__RNvCs6IclyHBw5rk_14from_raw_parts4main.symtab.smt2
;            2430 lines / 527,459 bytes / 77 relations (arity 122-142) / 109 rules
;   This file: 13 non-comment lines / 3 rules / 2 relations.
;
; AY VERDICT (this file, verbatim, ay 0.5.0+build.6947.610856d76)
;   $ ay solve --timeout 60000 repro_from_raw_parts.smt2
;   c !! MODEL-UNCONFIRMED [UNCONFIRMED/published] (not a refutation - see
;        [AY SOUNDNESS GATE] for caught invalid models) model validation violated:
;        SmtGroundAssertion: Assertion 0 violated: (= v0_1 1) evaluates to false
;   c !! MODEL-UNCONFIRMED ... Assertion 3 violated:
;        (or (not (= v1_1 0)) (not (= v0_1 0))) evaluates to false
;   unknown
;   (:reason-unknown "incomplete: CHC portfolio exhausted all strategies within budget")
;   exit.code=0 wall_time_ms=1252 -- it gives up in ~1 s, not at the 60 s budget.
;   The correct answer is `sat` (the query relation IS reachable); z3 -T:60
;   fp.engine=spacer answers `sat` on this exact file in 0.019 s.
;   NOTE the MODEL-UNCONFIRMED lines are the same failure the full 2430-line VC
;   emits ("Assertion 452 violated: (= _main_32_fld0__mid_bb22
;   _main_32_fld0__mid_bb35) evaluates to false") -- a candidate model that ay's
;   own ground-assertion evaluator cannot satisfy, hence no publishable answer.
;
; WHAT AY CANNOT DO — ONE SENTENCE
;   ay cannot confirm a satisfying model for a CHC whose constraints contain a
;   `concat` term WIDER THAN 128 BITS used as an array element or array index, so
;   its mandatory model-validation gate rejects the witness and silently demotes
;   the Unsafe it already derived to `unknown`.
;
; MECHANISM (ay's own --verbose trace, identical at every scale)
;   BMC: exact acyclic branch 0 was not discharged
;   cex-replay: no confirmed witness at depth 8 / 16 / 32 / 64
;   c !! MODEL-UNCONFIRMED ... strict model-validation oracle
;        arrays-read-conflict-uneval rejected assertion 108
;   PDR: witness-free counterexample replay inconclusive; returning Unknown
;   Adaptive: final validation demoted Unsafe -> Unknown
;             (stage=unsafe_rejected_by_final_verification, witness=false, head=[])
;   i.e. the SEARCH succeeds and the CONFIRMATION fails.  This is a model-
;   reconstruction / witness-completion gap, NOT a search-power or budget gap.
;
; EXACT BOUNDARY — measured, both directions
;   array element width  120 -> sat   128 -> sat   129 -> UNKNOWN   130,136,144,
;                        160,192,256,320 -> UNKNOWN        (threshold is 128 = u128)
;   Trigger needs the array AND the concat together:
;     (store g k (concat f0 f1))   elem BV192   -> unknown
;     (select g k) = (concat f0 f1)             -> unknown    (index side too:
;     (store g (concat f0 f1) v)   Array BV192 BV32 -> unknown)
;     (store g k v)      v a free BV192 var     -> sat        (no concat)
;     (store g k (bvnot v)) / (bvadd v v), BV192-> sat        (not concat)
;     go = (concat (concat f0 f1) f2), BV192, NO array        -> sat
;   UNSAT / Safe direction is UNAFFECTED: ay proves `unsat` correctly with the
;   same >128-bit concat present.  Only counterexample confirmation is broken.
;
; CAUSALITY PROVED ON THE FULL 2430-LINE VC (not just on this reduction)
;   full VC                                    ay: unknown  (60 s budget)
;   full VC, >128-bit array traffic ablated    ay: sat      in 0.62 s   <-- cause
;   full VC, narrow BV32-array stores ablated  ay: unknown  <-- negative control
;
; WHY THIS MATTERS TO trust-mc
;   The term below is verbatim trust-mc output.  trust-mc models a `Vec<u32>`
;   (ptr,len,cap) as ONE 192-bit memory cell built by concat of three 64-bit
;   fields.  Every Rust value wider than 128 bits stored to memory — Vec, String,
;   any 3-word struct, fat pointers with metadata — emits this shape.  Note also
;   that the driver's "≥2 Array-sorted state parameters (#4259)" label is a
;   trust-mc-side guess, not an ay limit; array-param COUNT is a correlate of the
;   real cause, which is array ELEMENT WIDTH > 128 under a concat.
;
; CONTROL THAT AY SOLVES (change 192 -> 128 and drop one field): flip the two
; `192` widths to `128` and use `(concat _main_14_fld0 _main_14_fld1)` — ay: sat.
; ============================================================================

(set-logic HORN)

; the trust-mc heap for `std::vec::Vec<u32, std::alloc::Global>`:
; address (BV64) -> one packed 192-bit cell holding (ptr, len, cap)
(declare-var _main_mem_std_vec_Vec_u32_std_alloc_Global      (Array (_ BitVec 64) (_ BitVec 192)))
(declare-var _main_mem_std_vec_Vec_u32_std_alloc_Global__out (Array (_ BitVec 64) (_ BitVec 192)))
(declare-var _main_14_fld0 (_ BitVec 64))   ; Vec.ptr
(declare-var _main_14_fld1 (_ BitVec 64))   ; Vec.len
(declare-var _main_14_fld2 (_ BitVec 64))   ; Vec.cap
(declare-var _main_89      (_ BitVec 64))   ; surviving scalar state column

(declare-rel main__bb13 ((_ BitVec 64)))
(declare-rel error ())

; bb13: `let mut v = mem::ManuallyDrop::new(v);` — write the 3-word Vec header
; to memory as a single 192-bit cell.  THIS RULE IS THE WHOLE REPRODUCER.
(rule (=> (= _main_mem_std_vec_Vec_u32_std_alloc_Global__out
              (store _main_mem_std_vec_Vec_u32_std_alloc_Global
                     (concat #x0000000e #x00000000)
                     (concat (concat _main_14_fld0 _main_14_fld1) _main_14_fld2)))
          (main__bb13 _main_89)))

(rule (=> (main__bb13 _main_89) error))

(query error)
