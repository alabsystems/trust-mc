// Oracle: MUST FAIL.
//
// `ConstantIndex { from_end: true }` on a SLICE. Every assertion below is FALSE
// and must be refuted. Each one was PROVED before the fix.
//
// WHY THIS FILE EXISTS — a FALSE PROOF, not a false positive:
//
//     assert!(a[0] == 99)   FALSE  ->  PROVED (then demoted chc_fallback=1)
//     assert!(a[3] == 99)   TRUE   ->  refuted with a counterexample
//
// Both directions wrong is the signature of a WRONG CELL, not a dropped write.
// `constant_index_offset` (codegen_stmt_projection/projection_path.rs) computed
// `min_length.saturating_sub(offset)`, but `min_length` is the PATTERN's minimum
// length, never the slice's runtime length. MIR settles it:
//
//     match a { [.., x] => .. }      a: &mut [i64]     ->  (*_1)[-1 of 1]
//     match a { [_, .., x] => .. }   a: &mut [i64]     ->  (*_1)[-1 of 2]
//     match a { [.., x] => .. }      a: &mut [i64; 4]  ->  (*_1)[3 of 4]
//
// ARRAYS lower to a DIRECT index and never take the `from_end` branch, so the
// branch is wrong on 100% of its reachable inputs. Probing an array shows
// correct behaviour and proves NOTHING about this path — it exercises the
// `else` arm. That mistake was made and corrected; do not repeat it.
//
// THREE ARITIES ARE REQUIRED. The buggy index tracks `min_length - offset`, so
// it is 0, 1, 2 for the three patterns while the correct answer is always
// `len - 1 == 3`. A single arity cannot distinguish "wrong cell" from
// "projection silently dropped": for `[.., x]` both predict index 0.
//
// Containment was ACCIDENTAL: the co-located read-lane refusal
// (memory_impl_addr.rs `get_array_length` returns None for RigidTy::Slice)
// raised the chc_fallback=1 that masked this. Fixing the read lane alone
// removes the mask. If this file ever reports SUCCESSFUL, the store lane is
// trusting `min_length` again.

fn set_last(a: &mut [i64]) {
    match a {
        [.., x] => *x = 99,
        _ => {}
    }
}

fn set_last_skip1(a: &mut [i64]) {
    match a {
        [_, .., x] => *x = 99,
        _ => {}
    }
}

fn set_last_skip2(a: &mut [i64]) {
    match a {
        [_, _, .., x] => *x = 99,
        _ => {}
    }
}

#[kani::proof]
fn bug_from_end_arity1_writes_cell0() {
    let mut a: [i64; 4] = [1, 2, 3, 4];
    set_last(&mut a);
    assert!(a[0] == 99);
}

#[kani::proof]
fn bug_from_end_arity2_writes_cell1() {
    let mut a: [i64; 4] = [1, 2, 3, 4];
    set_last_skip1(&mut a);
    assert!(a[1] == 99);
}

#[kani::proof]
fn bug_from_end_arity3_writes_cell2() {
    let mut a: [i64; 4] = [1, 2, 3, 4];
    set_last_skip2(&mut a);
    assert!(a[2] == 99);
}

/// CONFLICTING UNSIZE LENGTHS.
///
/// The slice length for `from_end` is recovered by scanning MIR for the
/// `Unsize` cast that produced the local. When ONE local is unsized from arrays
/// of DIFFERENT lengths, answering with either is arbitrary and wrong on the
/// other branch.
///
/// Taking the FIRST match (the obvious implementation, and what
/// `try_resolve_len_from_unsize` did) PROVED the assertion below with
/// `[AY:PROOF_QUALIFIERS:clean]`: it computed `len - 1 == 3` for BOTH branches,
/// so the `a8` case read cell 3 (value 4) instead of cell 7 (value 8). Caught
/// by this twin before it shipped.
///
/// `*x` is 4 when `a4` is chosen and 8 when `a8` is chosen, so `*x == 4` is
/// FALSE for half the inputs and must be refuted. If this reports SUCCESSFUL,
/// the length scan is guessing again instead of failing closed on a conflict.
#[kani::proof]
fn bug_conflicting_unsize_lengths() {
    let a4: [i64; 4] = [1, 2, 3, 4];
    let a8: [i64; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    let c: bool = kani::any();
    let s: &[i64] = if c { &a4 } else { &a8 };
    match s {
        [.., x] => assert!(*x == 4),
        _ => assert!(false),
    }
}

/// MOVE/COPY PREBINDING MUST NOT ERASE THE CONFLICT.
///
/// This is deliberately distinct from `bug_conflicting_unsize_lengths`: each
/// Unsize cast first initializes its own local, and the join local receives only
/// Move/Copy assignments. A resolver that scans only direct casts, or takes the
/// first resolvable Move/Copy predecessor, can still manufacture length 4 here.
#[kani::proof]
fn bug_conflicting_prebound_slice_lengths() {
    let a4: [i64; 4] = [1, 2, 3, 4];
    let a8: [i64; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    let s4: &[i64] = &a4;
    let s8: &[i64] = &a8;
    let c: bool = kani::any();
    let s: &[i64] = if c { s4 } else { s8 };
    match s {
        [.., x] => assert!(*x == 4),
        _ => assert!(false),
    }
}
