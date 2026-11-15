// Oracle: MUST be SUCCESSFUL.
//
// The non-vacuity twin of `unreachable_multi_edge_dual.rs`: the same multi-edge
// `unreachable` shapes with no bug in them. A SUCCESSFUL here witnesses that the
// twin's FAILED comes from its assertion being refuted, not from every harness
// with an unreachable arm failing wholesale.
//
// These are the recall cases the encoding fix exists for. `safe_empty_vec_loop`
// is `kani/Vectors/issue-763.rs` verbatim in shape: its ONLY check is an
// `unreachable` on the loop header's otherwise arm. Registered with no rule it
// was INCONCLUSIVE ([AY:UNKNOWN_REASON:LostErrorRules]); credited by the
// whole-VC encode-time discharge it was SUCCESSFUL with no solver run
// (`[AY:PROOF] property proven (false error obligation)`, measured on main
// 2026-09-18). Neither is a proof of the check. With the per-block obligation
// emitted, a solver decides it.

enum MyError {
    _Val1,
    Val2,
}

fn foo(x: u32) -> Result<(), MyError> {
    if x > 10 { Err(MyError::Val2) } else { Ok(()) }
}

fn bar(x: u32) -> Result<u32, MyError> {
    foo(x)?;
    Ok(x)
}

/// `kani/Vectors/issue-763.rs` verbatim in shape, and deliberately BARE: measured
/// on pristine main, adding a counter and an assertion to this body changes the
/// MIR enough that the `unreachable` property stops being registered at all
/// (the harness then reports two `assertion` checks). Only the bare loop keeps
/// "one registered check, an `unreachable`" — the exact recall case.
#[kani::proof]
fn safe_empty_vec_loop_bare() {
    let v = Vec::<i32>::new();
    for _ in v {}
}

#[kani::proof]
fn safe_empty_vec_loop() {
    let v = Vec::<i32>::new();
    let mut seen = 0u32;
    for _ in v {
        seen += 1;
    }
    assert!(seen == 0);
}

#[kani::proof]
fn safe_niche_question_mark() {
    let x: u32 = kani::any();
    kani::assume(x <= 10);
    let r = bar(x);
    assert!(r.is_ok());
}
