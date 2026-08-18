; ===========================================================================
; repro_boxslice2.smt2   --   ay CHC capability gap: NESTED DATATYPES kill SAT
; ===========================================================================
;
; SOURCE HARNESS
;   <repo>/target/kani-domination/kani/tests/kani/FatPointers/boxslice2.rs
;   (trust-mc key `boxslice2`, no extra flags; VC emitted by trust-mc-driver
;    --ay-chc as boxslice2__RNvCsaierRFLeFQO_9boxslice24main.symtab.smt2, 88 lines)
;
; AY VERDICT ON THIS FILE
;   unknown   (:reason-unknown "incomplete: CHC portfolio exhausted all strategies within budget")
;   preceded by 8x
;     c !! MODEL-UNCONFIRMED ... model validation violated: SmtGroundAssertion:
;         Assertion 1 violated: (or (and (= v0 0) (= v1 0) (= v0_1 1) (= v1_1 0))
;                                   (and (= v1 0) (= v0 1) (= v1_1 1) (= v0_1 0)
;                                        (not (= v3 #xf0)))) evaluates to false
;   wall_time_ms = 16.   Z3/Spacer answers `sat` on this file instantly.
;   NOT budget-bound: ay gives up in 16 ms; the same failure holds at --timeout 180000.
;
; WHAT AY CANNOT DO (one sentence)
;   ay's CHC engine cannot produce a *validatable* counterexample model -- and so
;   downgrades a plainly-`sat` Horn query to `unknown` -- as soon as any datatype
;   occurring in the rules has a constructor field whose sort is itself a datatype
;   (algebraic nesting depth >= 2); its ground-SMT model reconstruction returns an
;   assignment that fails ay's own model validator on the transition assertion.
;
; ---------------------------------------------------------------------------
; MEASURED EVIDENCE (every line below was run; ay build
;   0.5.0+build.6947.610856d76bccd061e169458a1df1720ba4c84f05)
; ---------------------------------------------------------------------------
;   file / shape                                              ay        z3
;   -------------------------------------------------------   -------   -----
;   full 88-line boxslice2 VC, verbatim                        unknown   sat
;   same VC, ONLY change: (Err_field_0 Utf8Error)
;                      -> (Err_field_0 (_ BitVec 64))          sat       sat   <-- ONE EDIT FIXES IT
;   this file (distilled, depth-3 nesting)                     unknown   sat
;   this file with Err payload flattened to a bitvector        sat       sat
;
;   synthetic ladder (each is a 10-line Horn problem, one free datatype
;   parameter plus one BV8 parameter, error reachable iff bv8 != #xf0):
;     P(Inner, bv8),      Inner = (Inner_mk (fld bv64))        sat       sat   depth 1 struct  OK
;     P(Outer, bv8),      Outer = (A bv8) | (B bv64)           sat       sat   depth 1 sum     OK
;     P(A1, B1, bv8),     two independent depth-1 datatypes    sat       sat   count is NOT the issue
;     P(Outer, bv8),      Outer = (Outer_mk (b Inner))         unknown   sat   depth 2         BREAKS
;     P(Outer, bv8),      Outer = (A) | (B Inner)              unknown   sat   depth 2         BREAKS
;     P(Outer, bv8),      Outer = (Outer_mk (b E)), E=(E1)|(E2) unknown  sat   nested *enum*   BREAKS
;     P(I2,  bv8),        I2 -> I1 -> I0 -> bv64               unknown   sat   depth 3         BREAKS
;
;   scope of the defect, pinned by further probes:
;     * NOT the relation signature. A nested datatype that appears only inside a
;       rule BODY (never as a relation parameter) fails identically.
;     * NOT mere declaration. A nested datatype declared but never mentioned in
;       any rule solves fine -- it must actually occur in the Horn system.
;     * NOT the SMT core. The same nested datatypes in a plain (set-logic ALL)
;       (check-sat) query with a two-level selector chain return `sat` correctly.
;       The bug is in the CHC/BMC lowering + model reconstruction layer only.
;     * NOT the unsat direction. Making the same nested-datatype system UNSAT
;       (guard x = #xf0 on entry) yields a correct `unsat` from ay.
;       So the gap is exactly: SAT/counterexample production under nested datatypes.
;     * NOT arrays. The 88-line boxslice2 VC contains ZERO Array-sorted relation
;       parameters -- the driver's ">=2 Array-sorted state parameters" label
;       (trust-mc-driver/src/call_ay/chc/native.rs:103,137) is a wrong guess here.
;     * NOT bitvector width. Shrinking the 128-bit fat-pointer field to 8 bits
;       changes nothing; keeping it while flattening the nested field fixes it.
;
; WHY THIS MATTERS FOR TRUST-MC
;   Every Rust enum/struct that wraps another aggregate lowers to a nested SMT
;   datatype. Here it is `Result<&str, Utf8Error>` where `Utf8Error` itself holds
;   an `Option<u8>`. That shape is pervasive (Result, Option-of-struct, nested
;   structs, Vec<T> of aggregate), so this single defect converts an entire class
;   of decidable counterexample queries into `unknown`.
;
; ---------------------------------------------------------------------------
; THE PROBLEM (distilled from the boxslice2 VC; datatype shapes are verbatim
; from the real VC, the control flow is collapsed to the single rule that
; reaches `error`). Expected answer: sat -- `_main_10_fld1` is a completely
; unconstrained BitVec 8, so `error` is trivially reachable.
; `_main_5` is dead weight: it is never constrained and never inspected. Its
; mere presence, with `Utf8Error` nested inside it, is what breaks ay.
; ---------------------------------------------------------------------------

(set-logic HORN)

(declare-datatype Option_u8
  ((None_Option_u8)
   (Some_Option_u8 (value_Option_u8 (_ BitVec 8)))))

(declare-datatype Utf8Error
  ((Utf8Error_mk (fld_valid_up_to (_ BitVec 64))
                 (fld_error_len   Option_u8))))          ; <-- nesting level 2

(declare-datatype Result_ref_str_std_str_Utf8Error
  ((Ok_Result_ref_str_std_str_Utf8Error  (Ok_field_0  (_ BitVec 128)))
   (Err_Result_ref_str_std_str_Utf8Error (Err_field_0 Utf8Error))))   ; <-- nesting level 1
                                                          ;     REPLACE Utf8Error
                                                          ;     BY (_ BitVec 64)
                                                          ;     AND AY RETURNS sat

(declare-var _main_5       Result_ref_str_std_str_Utf8Error)
(declare-var _main_10_fld1 (_ BitVec 8))

(declare-rel main__bb10 (Result_ref_str_std_str_Utf8Error (_ BitVec 8)))
(declare-rel error ())

; entry: both state columns unconstrained
(rule (main__bb10 _main_5 _main_10_fld1))

; the Rust assertion `assert!(b == 240)` -- violated when the byte is not 0xf0
(rule (=> (and (main__bb10 _main_5 _main_10_fld1)
               (not (= _main_10_fld1 #xf0)))
          error))

(query error)
