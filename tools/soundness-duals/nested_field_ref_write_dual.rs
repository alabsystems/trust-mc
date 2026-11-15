// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (KNOWN-RED missed-bug tracker) -- a write to a NESTED field
//! through a reference (`r.inner.a = 7` with `r: &mut P`), then a read of the
//! owner's field. No dyn dispatch and no inline walker: this is the statement
//! path.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3; see the manifest entry):
//!   bug_stmt_nested_write            -> VERIFICATION:- FAILED  ('assertion failed: o.inner.a == 0')
//!   safe_stmt_nested_write           -> VERIFICATION:- SUCCESSFUL
//!   bug_helper_nested_write          -> VERIFICATION:- FAILED  ('assertion failed: o.inner.a == 0')
//!   safe_helper_nested_write         -> VERIFICATION:- SUCCESSFUL
//!   bug_helper_nested1_write         -> VERIFICATION:- FAILED  ('assertion failed: o.inner.a == 0')
//!   safe_helper_nested1_write        -> VERIFICATION:- SUCCESSFUL
//!   bug_ref_read_after_nested_write  -> VERIFICATION:- FAILED  ('assertion failed: rd_ref(&o.inner) == 0')
//!   safe_ref_read_after_nested_write -> VERIFICATION:- SUCCESSFUL
//!   bug_flat_write_control           -> VERIFICATION:- FAILED  ('assertion failed: q.a == 0'; control)
//!   bug_top_field_write_control      -> VERIFICATION:- FAILED  ('assertion failed: o.c == 0'; control)
//!   bug_stmt_nested_xor_same_block          -> FAILED ('assertion failed: o.inner.a == 7')
//!   safe_stmt_nested_xor_same_block         -> SUCCESSFUL
//!   bug_stmt_nested_read_between_writes     -> FAILED ('assertion failed: y == 9')
//!   safe_stmt_nested_read_between_writes    -> SUCCESSFUL
//!   bug_direct_nested_xor_same_block        -> FAILED ('assertion failed: o.inner.a == 7')
//!   safe_direct_nested_xor_same_block       -> SUCCESSFUL
//!   bug_direct_nested_read_between_writes   -> FAILED ('assertion failed: y == 9')
//!   safe_direct_nested_read_between_writes  -> SUCCESSFUL
//!   bug_top_field_after_multi_leaf_sibling  -> FAILED ('assertion failed: o.c == 0')
//!   safe_top_field_after_multi_leaf_sibling -> SUCCESSFUL
//!   bug_sub_struct_store                    -> FAILED ('assertion failed: o.inner.b == 0')
//!   safe_sub_struct_store                   -> SUCCESSFUL
//!   bug_three_level_write                   -> FAILED ('assertion failed: o.p.inner.a == 0')
//!   safe_three_level_write                  -> SUCCESSFUL
//!   bug_interior_tuple1_write_r1_read_y     -> FAILED ('assertion failed: o.a.0.y == v')
//!   bug_interior_tuple1_write               -> FAILED ('assertion failed: o.a.0.y == 0')
//!   safe_interior_tuple1_write              -> SUCCESSFUL
//!   bug_interior_tuple1_helper              -> FAILED ('assertion failed: o.a.0.y == 0')
//!   safe_interior_tuple1_helper             -> SUCCESSFUL
//!   bug_closure_fnmut_interior_tuple        -> FAILED ('assertion failed: got == 0')
//!   bug_ref_write_read_interior_tuple       -> FAILED ('assertion failed: got == 0')
//!   bug_env_write_read_interior_tuple       -> FAILED ('assertion failed: got == 0')
//!   bug_env_helper_interior_tuple           -> FAILED ('assertion failed: got == 0')
//!
//! Measured 2026-09-24 at ay 5d900fd2f (CHC lane), identical on the branch
//! bundle 328b4a952027 and the main bundle 72090d76d40a: every bug_ row except
//! the controls is SUCCESSFUL clean (a missed bug), every safe_ row is FAILED
//! Genuine on its own assertion (a false certificate), and both controls FAIL
//! Genuine on Kani's message.
//!
//! MECHANISM (pre-existing, outside the walker; main and the walker branch
//! agreed before the fix): the owner `o: P` is a flattened local (one scalar
//! state var per leaf field). A store through a reference into it at depth
//! two, `(*r).inner.a = 7`, is written to memory, and
//! `mirror_scalar_ref_store` (`stmt/codegen_stmt_store/deref_mem_mirror.rs`)
//! must mirror it into the flattened scalar. A nested field projection on a
//! flattened struct (two field projections, no enum downcast) reaches its last
//! arm, which only warned "CHC: unsupported nested flattened field mirror for
//! Mem-level Deref store" and recorded no fail-close reason. The later read of
//! `o.inner.a` (directly, or through `&o.inner`) read the flattened scalar,
//! which kept 0. Every bug_ row logged that warning under --debug on the branch
//! bundle; bug_top_field_write_control did not. A one-level write (a field of
//! a flat struct, or a top-level field of `P`) is mirrored and caught.
//!
//! FAIL-CLOSED after the R0 change alone (measured 2026-09-24 at ay f28345ff1
//! on compiler 804ecdaa4fd1): that last arm recorded the FailClose reason
//! `deref_mirror_flat_path_unresolved`, gave every flattened slot of the
//! owner its free output variable and dropped the owner's cached values. Every
//! bug_ row was FAILED OverApproximation (a match; the three helper rows get
//! there from a demoted [AY:PROOF], because emit-time constant propagation
//! read an unconstrained `__out` slot whose input is a constant as an
//! identity pass-through; that reading is gone since 2026-09-25, see
//! `const_prop_havoc_dual.rs`), every safe_ row was FAILED OverApproximation (a
//! known-red false failure), and both controls still FAILED Genuine.
//!
//! PRECISE since the resolver change (measured 2026-09-24 at ay f28345ff1 on
//! compiler 58c4145b9bb6): a Field path into a flattened struct owner is
//! resolved to its leaf slots by `resolve_flat_struct_path`
//! (`expr/codegen_expr_flat_struct_path.rs`) and mirrored exactly
//! (`stmt/codegen_stmt_store/deref_mem_mirror_struct.rs`), or fails closed.
//! Every row below matches Kani: each bug_ row FAILS Genuine on Kani's
//! message and each safe_ row is SUCCESSFUL clean.
//!
//! The rows after the controls were added with the resolver, each checked
//! against the corpus-rev Kani 4c0fce8c3 (Kani 0.67.0) on 2026-09-24:
//! - `*_xor_same_block` / `*_read_between_writes` keep two writes and a read
//!   of one nested field in ONE block. Read case C of
//!   `translate_flattened_place` used to return the block's final `__out`
//!   instead of the value last written (critique R1): `^=` then emitted an
//!   UNSAT transition. On the main bundle e709ca52f59f both direct `xor`
//!   rows were SUCCESSFUL clean (a vacuous proof) and the direct
//!   `read_between` bug row was SUCCESSFUL clean.
//! - `*_top_field_after_multi_leaf_sibling`: a one-level write `p.c = 7`
//!   after a two-leaf sibling. The old one-level mirror wrote the raw field
//!   index (slot 1, `inner.b`) instead of the leaf offset (slot 2): the bug_
//!   row was SUCCESSFUL clean on main and after the fail-closed change.
//! - `*_sub_struct_store`: `p.inner = Q2 { .. }` through the reference (a
//!   two-leaf span), also SUCCESSFUL clean on main and after the fail-closed
//!   change, because the one-level mirror wrote the datatype into slot 0.
//! - `*_three_level_write`: `r.p.inner.a = 7`, SUCCESSFUL clean on main.
//!
//! The `*interior_tuple1*` rows came from the soundness review of the
//! resolver (2026-09-24), each checked against the corpus-rev Kani 4c0fce8c3.
//! `translate_ty((QT,))` is QT's sort, so the step `.0` into `a: (QT,)` has
//! no sort level. The resolver peeled it at any depth and wrote the exact
//! slot, but read case C peeled only a ROOT `(T,)` and walked the remaining
//! MIR indices over the sort tree, landing on another leaf: on compiler
//! 58c4145b9bb6 every bug_ row here was SUCCESSFUL clean (a false proof, and
//! `bug_interior_tuple1_write_r1_read_y` was FAILED Genuine on main). The
//! resolver now peels only leading steps and refuses an interior one (fail
//! closed), and read case C refuses the path too (`flat_nested_path_refusal`).
//! The bug_ rows FAIL; the safe_ rows are known-red false failures; and
//! `bug_closure_fnmut_interior_tuple` FAILS only through a demoted
//! [AY:PROOF]: its assertion check is proved under the FailClose reason.
//! Measured 2026-09-25 (ay 4378d73a4), that is not the unbound-`__out` hole
//! in the R0 note: with the emit-time passes fixed (`const_prop_havoc_dual.rs`)
//! nothing is re-bound in this harness. The assertion's error obligation is
//! already `false` when it is emitted ("property proven (false error
//! obligation)"), with or without the translate-time straight-line discharge
//! (`TRUST_MC_NO_STRAIGHTLINE_DISCHARGE=1` gives the same proof): the encoding
//! reads the closure's result, loaded through the Mem-level Deref of the
//! captured owner, as the constant 0. Still a known-red missed bug.
//!
//! FIXED on fix/chc-lost-writes (2026-09-26). The read went through the
//! stack Deref+Field lane (`try_stack_deref_field_expr`,
//! `expr/codegen_expr_deref_field_offset.rs`), which read the owner's
//! flattened INPUT variables whatever the block had written, and selected the
//! path's leaf by walking the MIR indices over the sort tree, which past the
//! interior `(QT,)` names `x.r1`. The lane now reads the value the block last
//! wrote, requires the pointer to be the owner's own address with the owner's
//! type, and refuses a path with no faithful slot
//! (`flat_nested_path_refusal`): the read then comes from memory, where the
//! store through the pointer went, and records
//! `stack_deref_field_path_unfaithful` (FailClose). The three rows after it
//! were added with the fix (checked against the corpus-rev Kani 4c0fce8c3):
//! the same write-then-read through a reference, through a wrapper, and in a
//! helper; on the integration baseline a15de6272 each proved its assertion
//! check from a false error obligation (FAILED only through the demotion).
//!
//! Promoted from the 2026-09-24 walker drop-certificate verification (probes
//! p5_alias_min.rs and p6_alias_shape.rs); the safe twins of the statement and
//! one-field rows are new.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s nested_field_ref_write_dual.rs

pub struct Q {
    a: u8,
}
pub struct P {
    inner: Q,
    c: u8,
}
pub struct P1 {
    inner: Q,
}

#[inline(never)]
fn wr_nested(p: &mut P) {
    p.inner.a = 7;
}
#[inline(never)]
fn wr_nested1(p: &mut P1) {
    p.inner.a = 7;
}
#[inline(never)]
fn wr_flat(q: &mut Q) {
    q.a = 7;
}
#[inline(never)]
fn wr_top(p: &mut P) {
    p.c = 7;
}
#[inline(never)]
fn rd_ref(q: &Q) -> u8 {
    q.a
}

// The write through the reference, as a statement in the harness body.
#[kani::proof]
fn bug_stmt_nested_write() {
    let mut o = P { inner: Q { a: 0 }, c: 0 };
    let r = &mut o;
    r.inner.a = 7;
    assert!(o.inner.a == 0);
}

#[kani::proof]
fn safe_stmt_nested_write() {
    let mut o = P { inner: Q { a: 0 }, c: 0 };
    let r = &mut o;
    r.inner.a = 7;
    assert!(o.inner.a == 7);
}

// The write in a helper that takes &mut P.
#[kani::proof]
fn bug_helper_nested_write() {
    let mut o = P { inner: Q { a: 0 }, c: 0 };
    wr_nested(&mut o);
    assert!(o.inner.a == 0);
}

#[kani::proof]
fn safe_helper_nested_write() {
    let mut o = P { inner: Q { a: 0 }, c: 0 };
    wr_nested(&mut o);
    assert!(o.inner.a == 7);
}

// The same with a one-field outer struct.
#[kani::proof]
fn bug_helper_nested1_write() {
    let mut o = P1 { inner: Q { a: 0 } };
    wr_nested1(&mut o);
    assert!(o.inner.a == 0);
}

#[kani::proof]
fn safe_helper_nested1_write() {
    let mut o = P1 { inner: Q { a: 0 } };
    wr_nested1(&mut o);
    assert!(o.inner.a == 7);
}

// The read through a reference to the inner field.
#[kani::proof]
fn bug_ref_read_after_nested_write() {
    let mut o = P { inner: Q { a: 0 }, c: 0 };
    wr_nested(&mut o);
    assert!(rd_ref(&o.inner) == 0);
}

#[kani::proof]
fn safe_ref_read_after_nested_write() {
    let mut o = P { inner: Q { a: 0 }, c: 0 };
    wr_nested(&mut o);
    assert!(rd_ref(&o.inner) == 7);
}

// Controls: a one-level write (flat struct, top-level field) is kept.
#[kani::proof]
fn bug_flat_write_control() {
    let mut q = Q { a: 0 };
    wr_flat(&mut q);
    assert!(q.a == 0);
}

#[kani::proof]
fn bug_top_field_write_control() {
    let mut o = P { inner: Q { a: 0 }, c: 0 };
    wr_top(&mut o);
    assert!(o.c == 0);
}

// ---- Added with the resolver: same-block reads (R1), raw-index slot,
// ---- sub-struct span, three levels.

pub struct Q2 {
    a: u8,
    b: u8,
}
pub struct P2 {
    inner: Q2,
    c: u8,
}
pub struct R {
    p: P,
    d: u8,
}

#[inline(never)]
fn wr_top2(p: &mut P2) {
    p.c = 7;
}
#[inline(never)]
fn wr_inner2(p: &mut P2) {
    p.inner = Q2 { a: 1, b: 2 };
}
#[inline(never)]
fn wr_deep(r: &mut R) {
    r.p.inner.a = 7;
}

// Two writes of the same nested field in ONE block (no overflow check on ^).
#[kani::proof]
fn bug_stmt_nested_xor_same_block() {
    let mut o = P { inner: Q { a: 0 }, c: 0 };
    let r = &mut o;
    r.inner.a = 7;
    r.inner.a ^= 1;
    assert!(o.inner.a == 7);
}

#[kani::proof]
fn safe_stmt_nested_xor_same_block() {
    let mut o = P { inner: Q { a: 0 }, c: 0 };
    let r = &mut o;
    r.inner.a = 7;
    r.inner.a ^= 1;
    assert!(o.inner.a == 6);
}

// A read between two writes in one block binds the value at that point.
#[kani::proof]
fn bug_stmt_nested_read_between_writes() {
    let mut o = P { inner: Q { a: 0 }, c: 0 };
    let r = &mut o;
    r.inner.a = 7;
    let y = r.inner.a;
    r.inner.a = 9;
    assert!(y == 9);
}

#[kani::proof]
fn safe_stmt_nested_read_between_writes() {
    let mut o = P { inner: Q { a: 0 }, c: 0 };
    let r = &mut o;
    r.inner.a = 7;
    let y = r.inner.a;
    r.inner.a = 9;
    assert!(y == 7 && o.inner.a == 9);
}

// The same two shapes as direct writes, no reference.
#[kani::proof]
fn bug_direct_nested_xor_same_block() {
    let mut o = P { inner: Q { a: 0 }, c: 0 };
    o.inner.a = 7;
    o.inner.a ^= 1;
    assert!(o.inner.a == 7);
}

#[kani::proof]
fn safe_direct_nested_xor_same_block() {
    let mut o = P { inner: Q { a: 0 }, c: 0 };
    o.inner.a = 7;
    o.inner.a ^= 1;
    assert!(o.inner.a == 6);
}

#[kani::proof]
fn bug_direct_nested_read_between_writes() {
    let mut o = P { inner: Q { a: 0 }, c: 0 };
    o.inner.a = 7;
    let y = o.inner.a;
    o.inner.a = 9;
    assert!(y == 9);
}

#[kani::proof]
fn safe_direct_nested_read_between_writes() {
    let mut o = P { inner: Q { a: 0 }, c: 0 };
    o.inner.a = 7;
    let y = o.inner.a;
    o.inner.a = 9;
    assert!(y == 7 && o.inner.a == 9);
}

// One level after a sibling with two leaves.
#[kani::proof]
fn bug_top_field_after_multi_leaf_sibling() {
    let mut o = P2 { inner: Q2 { a: 0, b: 0 }, c: 0 };
    wr_top2(&mut o);
    assert!(o.c == 0);
}

#[kani::proof]
fn safe_top_field_after_multi_leaf_sibling() {
    let mut o = P2 { inner: Q2 { a: 0, b: 0 }, c: 0 };
    wr_top2(&mut o);
    assert!(o.c == 7 && o.inner.b == 0);
}

// A whole sub-struct stored through the reference (a span of two leaves).
#[kani::proof]
fn bug_sub_struct_store() {
    let mut o = P2 { inner: Q2 { a: 0, b: 0 }, c: 0 };
    wr_inner2(&mut o);
    assert!(o.inner.b == 0);
}

#[kani::proof]
fn safe_sub_struct_store() {
    let mut o = P2 { inner: Q2 { a: 0, b: 0 }, c: 0 };
    wr_inner2(&mut o);
    assert!(o.inner.a == 1 && o.inner.b == 2 && o.c == 0);
}

// Three levels deep.
#[kani::proof]
fn bug_three_level_write() {
    let mut o = R { p: P { inner: Q { a: 0 }, c: 0 }, d: 0 };
    wr_deep(&mut o);
    assert!(o.p.inner.a == 0);
}

#[kani::proof]
fn safe_three_level_write() {
    let mut o = R { p: P { inner: Q { a: 0 }, c: 0 }, d: 0 };
    wr_deep(&mut o);
    assert!(o.p.inner.a == 7 && o.p.c == 0 && o.d == 0);
}

// ---- An interior single-element tuple on the path (review of the resolver,
// 2026-09-24). `translate_ty((QT,))` is QT's sort, so the step `.0` into
// `a: (QT,)` has no sort level. The resolver peeled it and wrote the exact
// slot, but the readers that walk the MIR indices over the sort tree land on
// another leaf there, so the write was read back from the wrong slot.
pub struct R2 {
    r0: u8,
    r1: u8,
}
pub struct QT {
    x: R2,
    y: u8,
}
pub struct PT {
    a: (QT,),
    c: u8,
}
pub struct QT1 {
    t: (QT,),
    k: u8,
}
fn mk_pt() -> PT {
    PT { a: (QT { x: R2 { r0: 0, r1: 0 }, y: 0 },), c: 0 }
}
#[inline(never)]
fn wr_pt(p: &mut PT, v: u8) {
    p.a.0.y = v;
}

// Write r1 through the reference, read y: the resolver's exact write landed on
// r1's slot and read case C read y from the same slot.
#[kani::proof]
fn bug_interior_tuple1_write_r1_read_y() {
    let mut o = mk_pt();
    let v: u8 = kani::any();
    kani::assume(v != 0);
    let r = &mut o;
    r.a.0.x.r1 = v;
    assert!(o.a.0.y == v);
}

#[kani::proof]
fn bug_interior_tuple1_write() {
    let mut o = mk_pt();
    let v: u8 = kani::any();
    kani::assume(v != 0);
    let r = &mut o;
    r.a.0.y = v;
    assert!(o.a.0.y == 0);
}

#[kani::proof]
fn safe_interior_tuple1_write() {
    let mut o = mk_pt();
    let v: u8 = kani::any();
    let r = &mut o;
    r.a.0.y = v;
    assert!(o.a.0.y == v);
}

#[kani::proof]
fn bug_interior_tuple1_helper() {
    let mut o = mk_pt();
    let v: u8 = kani::any();
    kani::assume(v != 0);
    wr_pt(&mut o, v);
    assert!(o.a.0.y == 0);
}

#[kani::proof]
fn safe_interior_tuple1_helper() {
    let mut o = mk_pt();
    let v: u8 = kani::any();
    wr_pt(&mut o, v);
    assert!(o.a.0.y == v);
}

// A `move` FnMut closure that captured the owner writes and reads the field.
#[kani::proof]
fn bug_closure_fnmut_interior_tuple() {
    let mut o = QT1 { t: (QT { x: R2 { r0: 0, r1: 0 }, y: 0 },), k: 0 };
    let v: u8 = kani::any();
    kani::assume(v != 0);
    let mut f = move |w: u8| {
        o.t.0.y = w;
        o.t.0.y
    };
    let got = f(v);
    assert!(got == 0);
}

// The same write-then-read without a closure: through a reference to the
// owner, through a wrapper around it, and in a helper.
pub struct EnvT {
    o: QT1,
}
fn mk_qt1() -> QT1 {
    QT1 { t: (QT { x: R2 { r0: 0, r1: 0 }, y: 0 },), k: 0 }
}
#[inline(never)]
fn wr_rd_env(e: &mut EnvT, v: u8) -> u8 {
    e.o.t.0.y = v;
    e.o.t.0.y
}

#[kani::proof]
fn bug_ref_write_read_interior_tuple() {
    let mut o = mk_qt1();
    let v: u8 = kani::any();
    kani::assume(v != 0);
    let r = &mut o;
    r.t.0.y = v;
    let got = r.t.0.y;
    assert!(got == 0);
}

#[kani::proof]
fn bug_env_write_read_interior_tuple() {
    let mut e = EnvT { o: mk_qt1() };
    let v: u8 = kani::any();
    kani::assume(v != 0);
    let r = &mut e;
    r.o.t.0.y = v;
    let got = r.o.t.0.y;
    assert!(got == 0);
}

#[kani::proof]
fn bug_env_helper_interior_tuple() {
    let mut e = EnvT { o: mk_qt1() };
    let v: u8 = kani::any();
    kani::assume(v != 0);
    let got = wr_rd_env(&mut e, v);
    assert!(got == 0);
}
