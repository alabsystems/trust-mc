// Oracle: MUST FAIL.
//
// WHY THIS FILE EXISTS
//
// The `unreachable` obligation is per BLOCK, and the blocks that carry it here
// are entered by SEVERAL edges: `for _ in vec` lowers to a loop header switching
// on `Iterator::next`, reached both from entry and from the back edge, whose
// `otherwise` arm is a MIR `Unreachable`; `?` on a `Result` switches on a niche
// discriminant the same way. Those are the shapes that actually register
// `unreachable` properties (measured on the corpus: `kani/Vectors/issue-763.rs`
// registers `main.unreachable.0`, `kani/Enum/niche.rs` two of them).
//
// Each harness below ALSO carries a real, refutable bug in the same body. That
// is the hazard this stands in front of: the encoder records the dead
// unreachable edge's obligation, and if that record is ever allowed to speak for
// the whole VC — the wholesale `false => error` discharge, which main reports as
// `[AY:PROOF] property proven (false error obligation)` with NO solver run — the
// live assertion goes with it and a real bug comes back proved in milliseconds.
// That is how 852fecece and 1a3b1a0f6 both failed; this file is the verdict-level
// wall in front of the same mistake for the per-block obligation.
//
// The complementary case — an `unreachable` that control genuinely REACHES —
// cannot be written in safe Rust (rustc emits `Unreachable` only where it proves
// control cannot arrive); it is reached through `unreachable_unchecked`, which
// trust-mc encodes as a memory-safety hook, and it already has its own
// tripwires: `unreachable_discharge_dual.rs::bug_reachable_unreachable` and
// `obligation_free_walk_dual.rs::bug_unreachable_unchecked_one_deep`, both of
// which MUST stay FAILED.
//
// Twin: `unreachable_multi_edge_dual_safe.rs`, the same shapes with no bug, which
// must be SUCCESSFUL — and whose proof must come from a solver.

enum MyError {
    _Val1,
    Val2,
}

fn foo(x: u32) -> Result<(), MyError> {
    if x > 10 { Err(MyError::Val2) } else { Ok(()) }
}

fn bar(x: u32) -> Result<u32, MyError> {
    // `?` on a niche-optimised Result: a discriminant switch whose otherwise arm
    // is an `Unreachable` block.
    foo(x)?;
    Ok(x)
}

/// The empty-`Vec` loop of `kani/Vectors/issue-763.rs` (its only check is an
/// `unreachable`), plus an assertion that is FALSE and must be refuted.
#[kani::proof]
fn bug_empty_vec_loop_with_real_assertion() {
    let v = Vec::<i32>::new();
    let mut seen = 0u32;
    for _ in v {
        seen += 1;
    }
    // The loop body never runs, so `seen == 0`. This claim is false.
    assert!(seen == 1);
}

/// The niche `?` shape, plus an assertion that is FALSE and must be refuted.
#[kani::proof]
fn bug_niche_question_mark_with_real_assertion() {
    let x: u32 = kani::any();
    kani::assume(x <= 10);
    let r = bar(x);
    // `x <= 10` means `foo` returns Ok and `bar` returns `Ok(x)`, so `is_err()`
    // is false. This claim is false.
    assert!(r.is_err());
}
