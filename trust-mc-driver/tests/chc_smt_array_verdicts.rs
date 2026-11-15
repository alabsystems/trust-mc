// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Engine verdicts over the SMT-array model of fixed-size arrays.
//!
//! Arrays reach the native typed CHC/PDR solver as one SMT array per element
//! leaf — `const_array` for a splat, `store` for an element write, `select` for
//! a read, `(Array (_ BitVec 64) S)` relation columns — never one variable per
//! lane. These tests ask the ENGINE (the acyclic direct-SMT decision, then PDR)
//! for verdicts on the shapes that used to need the retired N-field model, at
//! lengths that model could not represent at all, and pin that the verdict does
//! not change with the length.
//!
//! The lengths compared are small on purpose, from 4 to 4097 (past the retired
//! model's 256-lane and 4096-leaf bounds): the translation is constant in the
//! length (`trust-mc-trust-bmc/src/translate_chc_smt_array_tests.rs`), and a
//! regression that sized something by the length then fails cheaply instead of
//! allocating toward a huge one under a parallel test runner.

#![cfg(all(feature = "native-typed-chc-pdr", feature = "native-trust-ir-bundle"))]

use std::time::Duration;

use trust_ir::Module;
use trust_ir::inst::{BinOp, ICmpOp};
use trust_ir::ty::Ty;
use trust_ir::value::FuncId;
use trust_ir_build::ModuleBuilder;
use trust_mc_core::{
    ChcPdrSolveOptions, ChcPdrSolveRequest, FullVerificationVerdict, MirChcPdrObligation,
    MirObligationKind,
};
use trust_mc_trust_bmc::{TranslateOptions, trust_ir_function_to_chc_translation_output};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Proved,
    Refuted,
    Unknown,
}

/// The engine's own verdict for `function`, before proof-grade admission (which
/// needs the private consumer replay this lane does not run): the question here
/// is what the CHC means.
fn solve(module: &Module, function: FuncId) -> Verdict {
    let output =
        trust_ir_function_to_chc_translation_output(module, function, &TranslateOptions::default())
            .expect("fixture function translates");
    assert!(
        output.diagnostics.is_empty(),
        "every array operation is modeled: {:?}",
        output.diagnostics
    );
    let name = module.function_by_id(function).map_or("?", |f| f.name.as_str()).to_owned();
    let obligation = MirChcPdrObligation::new(
        format!("smt-array-{}", function.index()),
        name,
        MirObligationKind::Assertion,
        output.vc,
    );
    if obligation.validate().is_err() {
        return Verdict::Unknown;
    }
    let request = ChcPdrSolveRequest::new(obligation)
        .with_options(ChcPdrSolveOptions::default().with_timeout(Duration::from_secs(20)));
    match trust_mc_driver::solve_typed_chc_pdr_full_verification(request) {
        Ok(solved) => match solved.verdict {
            FullVerificationVerdict::Proved { .. } => Verdict::Proved,
            FullVerificationVerdict::Failed { .. } => Verdict::Refuted,
            _ => Verdict::Unknown,
        },
        Err(_) => Verdict::Unknown,
    }
}

/// Lengths from tiny to past both of the retired per-lane model's bounds.
const LENGTHS: [u64; 4] = [4, 5, 257, 4097];

/// The `tests/ui/codegen/huge-stacks.rs` shape:
/// `let mut x = [0u8; n]; x[2] = 123; assert!(x[2] == expected)`.
fn huge_stacks(n: u64, expected: i128) -> Module {
    let mut mb = ModuleBuilder::new("huge_stacks");
    let u8_id = mb.add_type(Ty::U8);
    let arr = Ty::Array(u8_id, n);
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("huge_stacks", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let zero = fb.iconst(Ty::U8, 0);
    let x0 = fb.array_splat(arr.clone(), zero);
    let two = fb.iconst(Ty::U64, 2);
    let value = fb.iconst(Ty::U8, 123);
    let x1 = fb.insert_element(arr, x0, two, value);
    let read = fb.extract_element(Ty::U8, x1, two);
    let want = fb.iconst(Ty::U8, expected);
    let cond = fb.icmp(ICmpOp::Eq, Ty::U8, read, want);
    fb.assert(cond);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn the_huge_stacks_shape_is_proved_at_every_length() {
    for n in LENGTHS {
        assert_eq!(solve(&huge_stacks(n, 123), FuncId::new(0)), Verdict::Proved, "n = {n}");
        assert_eq!(solve(&huge_stacks(n, 124), FuncId::new(0)), Verdict::Refuted, "n = {n}");
    }
}

/// `f(i, y) { if i < n { a = [0; n]; a[i] = y; assert(a[i] == y) } }` — a write
/// and a read at the same SYMBOLIC lane, under the source-level bounds guard.
fn symbolic_lane(n: u64, guarded: bool) -> Module {
    let mut mb = ModuleBuilder::new("symbolic_lane");
    let u32_id = mb.add_type(Ty::U32);
    let arr = Ty::Array(u32_id, n);
    let ft = mb.add_func_type(vec![Ty::U64, Ty::U32], vec![]);
    let mut fb = mb.function("symbolic_lane", ft);
    let entry = fb.create_block();
    let body = fb.create_block();
    let done = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let i = fb.add_block_param(entry, Ty::U64);
    let y = fb.add_block_param(entry, Ty::U32);
    if guarded {
        let len = fb.iconst(Ty::U64, i128::from(n));
        let ok = fb.icmp(ICmpOp::Ult, Ty::U64, i, len);
        fb.condbr(ok, body, vec![], done, vec![]);
    } else {
        fb.br(body, vec![]);
    }
    fb.switch_to_block(body);
    let zero = fb.iconst(Ty::U32, 0);
    let a0 = fb.array_splat(arr.clone(), zero);
    let a1 = fb.insert_element(arr, a0, i, y);
    let read = fb.extract_element(Ty::U32, a1, i);
    let cond = fb.icmp(ICmpOp::Eq, Ty::U32, read, y);
    fb.assert(cond);
    fb.br(done, vec![]);
    fb.switch_to_block(done);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn a_symbolic_lane_write_then_read_is_proved_and_its_bounds_are_checked() {
    for n in LENGTHS {
        assert_eq!(solve(&symbolic_lane(n, true), FuncId::new(0)), Verdict::Proved, "n = {n}");
        // Unguarded, the write can be out of bounds: undefined behaviour, refuted.
        assert_eq!(solve(&symbolic_lane(n, false), FuncId::new(0)), Verdict::Refuted, "n = {n}");
    }
}

/// The loop shapes: `a = [x; n]; i = 0; while i < bound { <body>; i += 1 }`.
#[derive(Clone, Copy, Debug)]
enum LoopBody {
    /// `_ = a[i]` — a read whose only obligation is its bounds.
    Read,
    /// `a[i] = 7` — a write whose only obligation is its bounds. (The written
    /// value is a constant made in the body: writing the entry parameter `x`
    /// instead threads one more, unused, 32-bit column through the loop, and the
    /// engine at the pinned revision answers that array-free problem
    /// Inconclusive — a solver sensitivity measured on the emitted CHC, not an
    /// array question.)
    Write,
}

/// Every block a cycle of the CFG reaches carries its arrays SHAPE-ONLY (the
/// native engine at the pinned ay revision answers Inconclusive for an array term
/// reachable from a loop), but every access keeps its bounds obligation. So the
/// loop's reads and writes are PROVED in bounds when `bound <= n`, at every
/// length, and one lane past the end (`bound == n + 1`) they are NEVER proved.
/// (That case is not pinned as Refuted: the engine does not refute the scalar
/// analog `while i < 5 { assert!(i < 4) }` on this lane either — measured
/// Unknown at the pinned revision — so it is a property of cyclic refutation, not
/// of arrays.)
fn loop_access(n: u64, bound: u64, body_kind: LoopBody) -> Module {
    let mut mb = ModuleBuilder::new("loop_access");
    let u32_id = mb.add_type(Ty::U32);
    let arr = Ty::Array(u32_id, n);
    let ft = mb.add_func_type(vec![Ty::U32], vec![]);
    let mut fb = mb.function("loop_access", ft);
    let entry = fb.create_block();
    let head = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let x = fb.add_block_param(entry, Ty::U32);
    let a0 = fb.array_splat(arr.clone(), x);
    let start = fb.iconst(Ty::U64, 0);
    fb.br(head, vec![a0, start]);
    fb.switch_to_block(head);
    let a = fb.add_block_param(head, arr.clone());
    let i = fb.add_block_param(head, Ty::U64);
    let limit = fb.iconst(Ty::U64, i128::from(bound));
    let more = fb.icmp(ICmpOp::Ult, Ty::U64, i, limit);
    // The head's parameters reach the body as block arguments (the translator
    // threads entry parameters and instruction results across blocks, not a later
    // block's parameters).
    fb.condbr(more, body, vec![a, i], exit, vec![]);
    fb.switch_to_block(body);
    let a = fb.add_block_param(body, arr.clone());
    let i = fb.add_block_param(body, Ty::U64);
    let a1 = match body_kind {
        LoopBody::Read => {
            let _read = fb.extract_element(Ty::U32, a, i);
            a
        }
        LoopBody::Write => {
            let seven = fb.iconst(Ty::U32, 7);
            fb.insert_element(arr, a, i, seven)
        }
    };
    let one = fb.iconst(Ty::U64, 1);
    let i1 = fb.binop(BinOp::Add, Ty::U64, i, one);
    fb.br(head, vec![a1, i1]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn loop_element_accesses_are_decided_by_their_bounds_at_every_length() {
    for body in [LoopBody::Read, LoopBody::Write] {
        for n in LENGTHS {
            assert_eq!(
                solve(&loop_access(n, n.min(8), body), FuncId::new(0)),
                Verdict::Proved,
                "{body:?} n = {n}: in-bounds loop accesses"
            );
        }
        for n in [4, 5] {
            assert_ne!(
                solve(&loop_access(n, n + 1, body), FuncId::new(0)),
                Verdict::Proved,
                "{body:?} n = {n}: an access one lane past the end must never be proved"
            );
        }
    }
}

/// `f(p: u8) { assume(p == 200); a = [0u32; 256]; b = a[p := 5]; assert(b[200] ==
/// expected) }`. An unsigned `u8` of 200 names lane 200 (trust-ir
/// `runtime_index`); its top bit is not a sign.
fn narrow_unsigned_index(expected: i128) -> Module {
    let mut mb = ModuleBuilder::new("narrow_unsigned_index");
    let u32_id = mb.add_type(Ty::U32);
    let arr = Ty::Array(u32_id, 256);
    let ft = mb.add_func_type(vec![Ty::U8], vec![]);
    let mut fb = mb.function("narrow_unsigned_index", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let p = fb.add_block_param(entry, Ty::U8);
    let two_hundred = fb.iconst(Ty::U8, 200);
    let is = fb.icmp(ICmpOp::Eq, Ty::U8, p, two_hundred);
    fb.assume(is);
    let zero = fb.iconst(Ty::U32, 0);
    let a = fb.array_splat(arr.clone(), zero);
    let five = fb.iconst(Ty::U32, 5);
    let b = fb.insert_element(arr, a, p, five);
    let lane = fb.iconst(Ty::U64, 200);
    let read = fb.extract_element(Ty::U32, b, lane);
    let want = fb.iconst(Ty::U32, expected);
    let cond = fb.icmp(ICmpOp::Eq, Ty::U32, read, want);
    fb.assert(cond);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn a_narrow_unsigned_index_is_decided_by_its_lane() {
    assert_eq!(solve(&narrow_unsigned_index(5), FuncId::new(0)), Verdict::Proved);
    assert_eq!(solve(&narrow_unsigned_index(0), FuncId::new(0)), Verdict::Refuted);
}

/// `f() { slot = alloca [u32; 4]; *slot = [5; 4]; *gep(slot, 1) = 9;
/// assert(*gep(slot, 1) == expected); i = 0; loop { i += 1; if i >= 4 break } }` —
/// a stack array cell round-tripped through a constant GEP lane in the entry
/// block, with a loop AFTER it. No cycle reaches the entry, so its array content
/// is modeled there and the engine decides the assertion; the loop's blocks carry
/// no array term. (A counting loop, because the engine at the pinned revision
/// answers Inconclusive for the array-free `while c {}` over a threaded `bool`.)
fn stack_lane_before_a_loop(expected: i128) -> Module {
    let mut mb = ModuleBuilder::new("stack_lane_before_a_loop");
    let u32_id = mb.add_type(Ty::U32);
    let arr = Ty::Array(u32_id, 4);
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("stack_lane_before_a_loop", ft);
    let entry = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let slot = fb.alloca(arr.clone());
    let five = fb.iconst(Ty::U32, 5);
    let splat = fb.array_splat(arr.clone(), five);
    fb.store(arr, slot, splat);
    let lane = fb.iconst(Ty::I64, 1);
    let lane_ptr = fb.gep(Ty::U32, slot, vec![lane]);
    let nine = fb.iconst(Ty::U32, 9);
    fb.store(Ty::U32, lane_ptr, nine);
    let lane_ptr = fb.gep(Ty::U32, slot, vec![lane]);
    let read = fb.load(Ty::U32, lane_ptr);
    let want = fb.iconst(Ty::U32, expected);
    let cond = fb.icmp(ICmpOp::Eq, Ty::U32, read, want);
    fb.assert(cond);
    let start = fb.iconst(Ty::U64, 0);
    fb.br(body, vec![start]);
    fb.switch_to_block(body);
    let i = fb.add_block_param(body, Ty::U64);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.binop(BinOp::Add, Ty::U64, i, one);
    let four = fb.iconst(Ty::U64, 4);
    let more = fb.icmp(ICmpOp::Ult, Ty::U64, next, four);
    fb.condbr(more, body, vec![next], exit, vec![]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn a_stack_lane_round_trip_before_a_loop_is_decided() {
    assert_eq!(solve(&stack_lane_before_a_loop(9), FuncId::new(0)), Verdict::Proved);
    assert_ne!(
        solve(&stack_lane_before_a_loop(5), FuncId::new(0)),
        Verdict::Proved,
        "a false lane claim before a loop is never proved"
    );
}
