// SOUNDNESS DUAL (missed-bug tripwire) — CHC block-relation slot misalignment.
//
// EXPECTED VERDICT: VERIFICATION:- FAILED. A SUCCESSFUL verdict means the
// emit-time optimization pipeline is again shipping a frame whose applications
// disagree on which state variable occupies a column.
//
// Mechanism this guards (see block_relation_slot_names_consistent in
// chc/translate.rs): the producer and consumer of a block relation both
// SORT-conform, so neither the sort net nor canonicalize_block_relation_apps
// touches them, but the consumer is one column short inside a run of
// identically-sorted slots and the arity fixup pads at the TAIL:
//
//   (declare-rel f__bb2 (Bool Bool Bool (_ BitVec 32) x3))
//   producer: (f__bb2 _6 _8 true #x00000001 e0 e1 e2)          <- slot 3 = Option payload
//   consumer: (f__bb2 _6 _8 _10_fld0 e0 e1 e2 __pad_f__bb2_7)  <- payload column missing
//
// Every array column shifts left one, so the consumer's own constraints
// e0=1 /\ e1=2 /\ e2=3 bind against (payload,e0,e1) and demand 1=2 and 2=3.
// The body is UNSATISFIABLE => the successor block is unreachable => the error
// edge is underivable => UNSAT => "proven". Nothing is flagged: no fallback
// reason, no demotion, no CTREX category.
//
// The check must run BEFORE the straightline discharge, which replaces every
// rule with `(=> false error)` and would leave nothing to detect.
//
// Truth: a fresh 3-element iterator's first next() is Some(1), so is_none() is
// FALSE. Never delete, never weaken.
#[kani::proof]
#[kani::unwind(6)]
fn dual_slot_misalign_is_none_must_fail() {
    let a = [1u32, 2u32, 3u32];
    let s: &[u32] = &a;
    let mut it = s.iter();
    assert!(it.next().is_none(), "FALSE: first next() is Some(1)");
}
