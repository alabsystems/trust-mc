// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The SMT-array model of fixed-size arrays (`ArrayValue`).
//!
//! Three properties are pinned here:
//!
//! * SIZE. A `[e; n]` value is one SMT array per scalar leaf of `e`, so the
//!   encoding of every array shape — splat, constant splat, list literal, element
//!   write and read at constant and symbolic indices, a loop-carried array, a
//!   stack cell written through a GEP lane, an array of structs, a nested array
//!   and an array through a call summary — is IDENTICAL at every length: same
//!   variables, rules, relation signatures and expression nodes. The lengths
//!   compared are SMALL (2 to 4097, across the retired model's 256-lane and
//!   4096-leaf bounds): equal encodings there already show that nothing grows
//!   per lane, and a regression that did grow per lane fails as a cheap
//!   `assert_eq!` instead of allocating toward a huge length under a parallel
//!   test runner.
//! * THE JUNK-LANE INVARIANT. Lanes outside `[0, len)` never decide anything: no
//!   rule equates two array-sorted terms, a proof never rests on a junk lane (an
//!   out-of-bounds read is an error with memory checks on and a havoc with them
//!   off), and a counterexample never reads one (every counterexample through an
//!   access is either the access's own bounds violation or reads a real lane).
//! * WHAT A CYCLE REACHES IS ARRAY-FREE. The native CHC engine at the pinned ay
//!   revision answers Inconclusive for an array term reachable from a loop, so
//!   every block a cycle of the CFG reaches carries its arrays SHAPE-ONLY
//!   (length, no content) — chosen by the CFG, never by a length — and keeps
//!   every bounds obligation; the blocks before the first loop keep the full
//!   model.
//! * NO LENGTH DECIDES THE GATE'S CELL LANES. The translator promotes an array
//!   cell of any length, and the proof-authority lanes 2 and 4 admit it at any
//!   length (decision TMC-2 retired the frozen extent they applied before).
//!
//! Verdicts that need the CHC engine (loops) are in
//! `trust-mc-driver/tests/chc_smt_array_verdicts.rs`; everything here is either a
//! structural fact about the emitted VC or a solver question over single-block
//! rule bodies.

use std::collections::{BTreeMap, BTreeSet};

use ay_bindings::{Expr, Sort};
use trust_ir::inst::{BinOp, ICmpOp};
use trust_ir::ty::Ty;
use trust_ir::value::FuncId;
use trust_ir::{Constant, Module};
use trust_ir_build::ModuleBuilder;
use trust_mc_core::chc::ChcVc;

use super::*;
use crate::TranslateOptions;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

pub(super) fn translate_with(
    module: &Module,
    function: FuncId,
    options: &TranslateOptions,
) -> ChcTranslationOutput {
    trust_ir_function_to_chc_translation_output(module, function, options)
        .expect("fixture function translates")
}

pub(super) fn translate(module: &Module, function: FuncId) -> ChcTranslationOutput {
    translate_with(module, function, &TranslateOptions::default())
}

pub(super) fn unchecked() -> TranslateOptions {
    TranslateOptions { check_memory_bounds: false, ..TranslateOptions::default() }
}

/// Distinct expression nodes over every rule (body constraints, body and head
/// relation arguments), shared subterms counted once.
pub(super) fn distinct_expr_nodes(vc: &ChcVc) -> usize {
    let mut seen: BTreeSet<*const ay_bindings::ExprValue> = BTreeSet::new();
    let mut stack: Vec<&Expr> = Vec::new();
    for rule in &vc.rules {
        stack.extend(rule.body.constraints.iter());
        if let Some(app) = &rule.body.relation {
            stack.extend(app.args.iter());
        }
        stack.extend(rule.head.args.iter());
    }
    while let Some(expr) = stack.pop() {
        if seen.insert(std::ptr::from_ref(expr.value())) {
            stack.extend(expr.children());
        }
    }
    seen.len()
}

/// Everything a length-dependent encoding would grow: declared variables,
/// rules, every relation's signature, and the expression DAG.
#[derive(Debug, PartialEq, Eq)]
pub(super) struct VcSize {
    vars: usize,
    rules: usize,
    relations: Vec<(String, usize)>,
    nodes: usize,
}

pub(super) fn vc_size(output: &ChcTranslationOutput) -> VcSize {
    VcSize {
        vars: output.vc.vars().len(),
        rules: output.vc.rules.len(),
        relations: output
            .vc
            .relations
            .iter()
            .map(|relation| (relation.name.to_string(), relation.arity()))
            .collect(),
        nodes: distinct_expr_nodes(&output.vc),
    }
}

/// Is the conjunction satisfiable (in-process AY, arrays and bit-vectors)?
pub(super) fn satisfiable(vc: &ChcVc, constraints: &[Expr]) -> bool {
    let mut program = ay_bindings::AYProgram::new();
    program.set_logic("QF_ABV");
    for var in vc.vars() {
        let _ = program.declare_const(var.name.to_string(), var.sort.clone());
    }
    for constraint in constraints {
        program.assert(constraint.clone());
    }
    program.check_sat();
    match ay_bindings::execute_direct::execute(&program)
        .expect("in-process AY execution should succeed")
    {
        ay_bindings::execute_direct::ExecuteResult::Counterexample { .. } => true,
        ay_bindings::execute_direct::ExecuteResult::Verified => false,
        other => panic!("unexpected solver outcome: {other:?}"),
    }
}

/// Is the conjunction PROVABLY unsatisfiable? (`false` for a satisfiable one and
/// for a solver `Unknown` — never proved.)
pub(super) fn unsatisfiable(vc: &ChcVc, constraints: &[Expr]) -> bool {
    let mut program = ay_bindings::AYProgram::new();
    program.set_logic("QF_ABV");
    for var in vc.vars() {
        let _ = program.declare_const(var.name.to_string(), var.sort.clone());
    }
    for constraint in constraints {
        program.assert(constraint.clone());
    }
    program.check_sat();
    matches!(
        ay_bindings::execute_direct::execute(&program)
            .expect("in-process AY execution should succeed"),
        ay_bindings::execute_direct::ExecuteResult::Verified
    )
}

pub(super) fn error_rule_bodies(vc: &ChcVc) -> Vec<Vec<Expr>> {
    vc.rules
        .iter()
        .filter(|rule| rule.head.name.as_str() == "error")
        .map(|rule| rule.body.constraints.iter().cloned().collect())
        .collect()
}

/// Can any `error` rule fire? (Single-block fixtures: the entry relation is
/// unconstrained, so a satisfiable body is a reachable error.)
pub(super) fn error_reachable(output: &ChcTranslationOutput) -> bool {
    error_rule_bodies(&output.vc).iter().any(|body| satisfiable(&output.vc, body))
}

/// The declared variable named exactly `name` (an entry-block parameter is
/// `bb0_v<value index>`).
pub(super) fn var_named(output: &ChcTranslationOutput, name: &str) -> Expr {
    let var = output
        .vc
        .vars()
        .iter()
        .find(|var| &*var.name == name)
        .unwrap_or_else(|| panic!("no variable `{name}`"));
    Expr::var(var.name.to_string(), var.sort.clone())
}

// ---------------------------------------------------------------------------
// Fixtures: every array shape the translator models, parametrized by length
// ---------------------------------------------------------------------------

/// The lengths every size test compares: tiny, the retired N-field model's
/// per-dimension bound and one past it, and one past its 4096-leaf bound. All
/// small on purpose (see the module doc): equal encodings at these lengths show
/// that nothing is sized by the length.
const LENGTHS: [u64; 5] = [2, 3, 256, 257, 4097];

#[derive(Clone, Copy, Debug)]
enum Shape {
    /// `a = [x; n]; b = a[i := y]; z = b[j]; assert(z != x ^ y ^ 1)`.
    RegisterSplatSymbolic,
    /// `a = const [3; n]; b = a[1 := 9]; z = b[1]; assert(z == 9)`.
    ConstSplatConstantLanes,
    /// `a = const [5, 6]` padded to `n` by a splat: `[5, 6]` only fits `n == 2`, so
    /// this is `b = [5; n]` rewritten as a two-element write chain on `[0; n]`.
    WriteChain,
    /// A loop that writes `a[i] = x` for `i < k`, then reads `a[0]`.
    LoopCarried,
    /// `slot = alloca [u32; n]; *slot = [5; n]; *gep(slot, 1) = 9; assert(slot[1] == 9)`.
    StackCellLane,
    /// `[(u32, bool); n]` splat, read at a symbolic lane, field 0 compared.
    ArrayOfPairs,
    /// `[[7u8; n]; n]`, read at two symbolic lanes.
    Nested,
    /// `g(a: [u32; n]) -> [u32; n] { a }`; `f(x) { b = g([x; n]); assert(b[0] == x) }`.
    ThroughACallSummary,
}

const SHAPES: [Shape; 8] = [
    Shape::RegisterSplatSymbolic,
    Shape::ConstSplatConstantLanes,
    Shape::WriteChain,
    Shape::LoopCarried,
    Shape::StackCellLane,
    Shape::ArrayOfPairs,
    Shape::Nested,
    Shape::ThroughACallSummary,
];

/// The module for `shape` at length `n`, and the function to translate.
fn fixture(shape: Shape, n: u64) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new(format!("smt_array_{shape:?}"));
    let u32_id = mb.add_type(Ty::U32);
    let arr = Ty::Array(u32_id, n);
    match shape {
        Shape::RegisterSplatSymbolic => {
            let ft = mb.add_func_type(vec![Ty::U32, Ty::U32, Ty::U64, Ty::U64], vec![]);
            let mut fb = mb.function("f", ft);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let seed = fb.add_block_param(entry, Ty::U32);
            let written = fb.add_block_param(entry, Ty::U32);
            let idx = fb.add_block_param(entry, Ty::U64);
            let jdx = fb.add_block_param(entry, Ty::U64);
            let arr_v = fb.array_splat(arr.clone(), seed);
            let arr_w = fb.insert_element(arr, arr_v, idx, written);
            let lane_v = fb.extract_element(Ty::U32, arr_w, jdx);
            let xy = fb.binop(BinOp::BXor, Ty::U32, seed, written);
            let one = fb.iconst(Ty::U32, 1);
            let other = fb.binop(BinOp::BXor, Ty::U32, xy, one);
            let cond = fb.icmp(ICmpOp::Ne, Ty::U32, lane_v, other);
            fb.assert(cond);
            fb.ret(vec![]);
            fb.build();
        }
        Shape::ConstSplatConstantLanes => {
            let ft = mb.add_func_type(vec![], vec![]);
            let mut fb = mb.function("f", ft);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let arr_v = fb.const_value(arr.clone(), Constant::splat(Constant::Int(3), n));
            let one = fb.iconst(Ty::U64, 1);
            let nine = fb.iconst(Ty::U32, 9);
            let arr_w = fb.insert_element(arr, arr_v, one, nine);
            let lane_v = fb.extract_element(Ty::U32, arr_w, one);
            let cond = fb.icmp(ICmpOp::Eq, Ty::U32, lane_v, nine);
            fb.assert(cond);
            fb.ret(vec![]);
            fb.build();
        }
        Shape::WriteChain => {
            let ft = mb.add_func_type(vec![], vec![]);
            let mut fb = mb.function("f", ft);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let zero = fb.iconst(Ty::U32, 0);
            let arr_v = fb.array_splat(arr.clone(), zero);
            let lane0 = fb.iconst(Ty::U64, 0);
            let lane1 = fb.iconst(Ty::U64, 1);
            let five = fb.iconst(Ty::U32, 5);
            let six = fb.iconst(Ty::U32, 6);
            let arr_w = fb.insert_element(arr.clone(), arr_v, lane0, five);
            let cv = fb.insert_element(arr, arr_w, lane1, six);
            let lane_v = fb.extract_element(Ty::U32, cv, lane0);
            let cond = fb.icmp(ICmpOp::Eq, Ty::U32, lane_v, five);
            fb.assert(cond);
            fb.ret(vec![]);
            fb.build();
        }
        Shape::LoopCarried => {
            let ft = mb.add_func_type(vec![Ty::U32, Ty::U64], vec![]);
            let mut fb = mb.function("f", ft);
            let entry = fb.create_block();
            let head = fb.create_block();
            let body = fb.create_block();
            let exit = fb.create_block();
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let seed = fb.add_block_param(entry, Ty::U32);
            let limit = fb.add_block_param(entry, Ty::U64);
            let a0 = fb.array_splat(arr.clone(), seed);
            let start = fb.iconst(Ty::U64, 0);
            fb.br(head, vec![a0, start]);
            fb.switch_to_block(head);
            let arr_v = fb.add_block_param(head, arr.clone());
            let idx = fb.add_block_param(head, Ty::U64);
            let more = fb.icmp(ICmpOp::Ult, Ty::U64, idx, limit);
            fb.condbr(more, body, vec![arr_v, idx], exit, vec![arr_v]);
            fb.switch_to_block(body);
            let arr_v = fb.add_block_param(body, arr.clone());
            let idx = fb.add_block_param(body, Ty::U64);
            let a1 = fb.insert_element(arr.clone(), arr_v, idx, seed);
            let one = fb.iconst(Ty::U64, 1);
            let i1 = fb.binop(BinOp::Add, Ty::U64, idx, one);
            fb.br(head, vec![a1, i1]);
            fb.switch_to_block(exit);
            let arr_v = fb.add_block_param(exit, arr);
            let zero = fb.iconst(Ty::U64, 0);
            let lane_v = fb.extract_element(Ty::U32, arr_v, zero);
            let cond = fb.icmp(ICmpOp::Eq, Ty::U32, lane_v, seed);
            fb.assert(cond);
            fb.ret(vec![]);
            fb.build();
        }
        Shape::StackCellLane => {
            let ft = mb.add_func_type(vec![], vec![]);
            let mut fb = mb.function("f", ft);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let slot = fb.alloca(arr.clone());
            let five = fb.iconst(Ty::U32, 5);
            let splat = fb.array_splat(arr.clone(), five);
            fb.store(arr.clone(), slot, splat);
            let lane = fb.iconst(Ty::I64, 1);
            let lane_ptr = fb.gep(Ty::U32, slot, vec![lane]);
            let nine = fb.iconst(Ty::U32, 9);
            fb.store(Ty::U32, lane_ptr, nine);
            let whole = fb.load(arr, slot);
            let lane_v = fb.extract_element(Ty::U32, whole, lane);
            let cond = fb.icmp(ICmpOp::Eq, Ty::U32, lane_v, nine);
            fb.assert(cond);
            fb.ret(vec![]);
            fb.build();
        }
        Shape::ArrayOfPairs => {
            let pair = Ty::Tuple(vec![Ty::U32, Ty::Bool]);
            let pair_id = mb.add_type(pair.clone());
            let pairs = Ty::Array(pair_id, n);
            let ft = mb.add_func_type(vec![Ty::U32, Ty::U64], vec![]);
            let mut fb = mb.function("f", ft);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let seed = fb.add_block_param(entry, Ty::U32);
            let idx = fb.add_block_param(entry, Ty::U64);
            let flag = fb.const_value(Ty::Bool, Constant::Bool(true));
            let blank =
                fb.const_value(pair.clone(), Constant::Aggregate(vec![Constant::Uninit; 2]));
            let first = fb.insert_field(pair.clone(), blank, 0, seed);
            let element = fb.insert_field(pair.clone(), first, 1, flag);
            let arr_v = fb.array_splat(pairs, element);
            let read = fb.extract_element(pair, arr_v, idx);
            let lane_v = fb.extract_field(Ty::U32, read, 0);
            let cond = fb.icmp(ICmpOp::Eq, Ty::U32, lane_v, seed);
            fb.assert(cond);
            fb.ret(vec![]);
            fb.build();
        }
        Shape::Nested => {
            let u8_id = mb.add_type(Ty::U8);
            let row = Ty::Array(u8_id, n);
            let row_id = mb.add_type(row.clone());
            let grid = Ty::Array(row_id, n);
            let ft = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![]);
            let mut fb = mb.function("f", ft);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let idx = fb.add_block_param(entry, Ty::U64);
            let jdx = fb.add_block_param(entry, Ty::U64);
            let arr_v =
                fb.const_value(grid, Constant::splat(Constant::splat(Constant::Int(7), n), n));
            let row_v = fb.extract_element(row, arr_v, idx);
            let cv = fb.extract_element(Ty::U8, row_v, jdx);
            let seven = fb.iconst(Ty::U8, 7);
            let cond = fb.icmp(ICmpOp::Eq, Ty::U8, cv, seven);
            fb.assert(cond);
            fb.ret(vec![]);
            fb.build();
        }
        Shape::ThroughACallSummary => {
            let g_ty = mb.add_func_type(vec![arr.clone()], vec![arr.clone()]);
            let g_id = mb.peek_next_func_id().expect("peek_next_func_id: test fixture");
            {
                let mut g = mb.function("g", g_ty);
                let entry = g.create_block();
                g.switch_to_block(entry);
                g.set_entry(entry);
                let arr_v = g.add_block_param(entry, arr.clone());
                g.ret(vec![arr_v]);
                g.build();
            }
            let ft = mb.add_func_type(vec![Ty::U32], vec![]);
            let mut fb = mb.function("f", ft);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let seed = fb.add_block_param(entry, Ty::U32);
            let arr_v = fb.array_splat(arr, seed);
            let arr_w = fb.call(g_id, vec![arr_v]);
            let zero = fb.iconst(Ty::U64, 0);
            let lane_v = fb.extract_element(Ty::U32, arr_w, zero);
            let cond = fb.icmp(ICmpOp::Eq, Ty::U32, lane_v, seed);
            fb.assert(cond);
            fb.ret(vec![]);
            fb.build();
            let module = mb.build().expect("ModuleBuilder::build: test fixture");
            let f = FuncId::new(1);
            return (module, f);
        }
    }
    (mb.build().expect("ModuleBuilder::build: test fixture"), FuncId::new(0))
}

#[test]
fn original_array_of_pairs_undef_seed_is_runtime_ub_and_refused() {
    let (mut module, function) = fixture(Shape::ArrayOfPairs, 4);
    let source = module.functions.iter_mut().find(|source| source.id == function).unwrap();
    let seed = source
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.body)
        .find(|node| {
            matches!(&node.inst, Inst::Const { value: Constant::Aggregate(fields), .. }
            if fields.iter().all(|field| matches!(field, Constant::Uninit)))
        })
        .unwrap();
    let Inst::Const { ty, .. } = &seed.inst else { unreachable!() };
    seed.inst = Inst::Undef { ty: ty.clone() };
    let error = trust_ir::interpret::Interpreter::with_module(&module)
        .execute_func(
            function,
            [
                trust_ir::interpret::InterpretValue::int(Ty::U32, 7).unwrap(),
                trust_ir::interpret::InterpretValue::int(Ty::U64, 0).unwrap(),
            ],
        )
        .unwrap_err();
    assert_eq!(error.code, trust_ir::interpret::InterpretErrorCode::UndefinedBehavior);
    let output = translate(&module, function);
    assert!(
        output
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.reason == TrustIrChcUnsupportedReason::OperandConsumption)
    );
    assert!(error_reachable(&output));
}

// ---------------------------------------------------------------------------
// Size: constant in the length
// ---------------------------------------------------------------------------

#[test]
fn every_array_shape_has_the_same_encoding_at_every_length() {
    for shape in SHAPES {
        let sizes: Vec<(u64, VcSize, usize)> = LENGTHS
            .iter()
            .map(|&n| {
                let (module, f) = fixture(shape, n);
                let output = translate(&module, f);
                (n, vc_size(&output), output.diagnostics.len())
            })
            .collect();
        let (_, first, first_diagnostics) = &sizes[0];
        for (n, size, diagnostics) in &sizes[1..] {
            assert_eq!(size, first, "{shape:?}: the encoding at n = {n} differs from n = 2");
            assert_eq!(diagnostics, first_diagnostics, "{shape:?}: diagnostics depend on n = {n}");
        }
        assert_eq!(*first_diagnostics, 0, "{shape:?}: every array operation here is modeled");
    }
}

/// An array column is ONE relation argument per element leaf, of the lifted
/// sort `(Array BV64 S)`: a `[u32; n]` carried across a diamond join is one
/// column, and `[[u8; n]; n]` as an entry parameter is one column of sort
/// `(Array BV64 (Array BV64 BV8))` — at `n = 4097`, past both retired bounds.
#[test]
fn an_array_column_is_one_lifted_sort_per_element_leaf() {
    let mut mb = ModuleBuilder::new("diamond_column");
    let u32_id = mb.add_type(Ty::U32);
    let arr = Ty::Array(u32_id, 4097);
    let ft = mb.add_func_type(vec![Ty::U32, Ty::Bool], vec![]);
    let mut fb = mb.function("f", ft);
    let (entry, left, right, join) =
        (fb.create_block(), fb.create_block(), fb.create_block(), fb.create_block());
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let seed = fb.add_block_param(entry, Ty::U32);
    let cv = fb.add_block_param(entry, Ty::Bool);
    let arr_v = fb.array_splat(arr.clone(), seed);
    fb.condbr(cv, left, vec![], right, vec![]);
    fb.switch_to_block(left);
    let zero = fb.iconst(Ty::U64, 0);
    let arr_w = fb.insert_element(arr.clone(), arr_v, zero, seed);
    fb.br(join, vec![arr_w]);
    fb.switch_to_block(right);
    fb.br(join, vec![arr_v]);
    fb.switch_to_block(join);
    let merged = fb.add_block_param(join, arr);
    let zero = fb.iconst(Ty::U64, 0);
    let lane_v = fb.extract_element(Ty::U32, merged, zero);
    let cond = fb.icmp(ICmpOp::Eq, Ty::U32, lane_v, seed);
    fb.assert(cond);
    fb.ret(vec![]);
    fb.build();
    // Per block: the test reads the join's own relation.
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let output = super::translate_function_per_block(
        &module.functions[0],
        &module,
        &TranslateOptions::default(),
    );
    let join = output
        .vc
        .relations
        .iter()
        .find(|relation| relation.name.as_str() == "bb3")
        .expect("the join relation");
    let array_columns: Vec<_> = join.arg_sorts.iter().filter(|sort| sort.is_array()).collect();
    assert_eq!(array_columns.len(), 1, "the join carries the array as one column");
    let expected = lifted_sort(ay_bindings::Sort::bitvec(32), 1);
    assert!(sort_matches(array_columns[0], &expected), "{:?}", array_columns[0]);

    // A nested array: one leaf, two levels of array sort.
    let mut mb = ModuleBuilder::new("nested_column");
    let u8_id = mb.add_type(Ty::U8);
    let row_id = mb.add_type(Ty::Array(u8_id, 4097));
    let grid = Ty::Array(row_id, 4097);
    let ft = mb.add_func_type(vec![grid.clone()], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let _a = fb.add_block_param(entry, grid);
    fb.ret(vec![]);
    fb.build();
    // Per block: the test reads the join's own relation.
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let output = super::translate_function_per_block(
        &module.functions[0],
        &module,
        &TranslateOptions::default(),
    );
    let entry_relation = output
        .vc
        .relations
        .iter()
        .find(|relation| relation.name.as_str() == "bb0")
        .expect("the entry relation");
    assert_eq!(entry_relation.arg_sorts.len(), 1);
    assert!(sort_matches(
        &entry_relation.arg_sorts[0],
        &lifted_sort(ay_bindings::Sort::bitvec(8), 2)
    ));
}

// ---------------------------------------------------------------------------
// Cyclic functions: arrays keep only their shape
// ---------------------------------------------------------------------------

/// `array_content_blocks` is every block no cycle of the CFG reaches: all of an
/// acyclic function, the blocks before the first loop of a cyclic one, and
/// nothing when the loop runs back to the entry.
#[test]
fn array_content_blocks_are_the_blocks_no_cycle_reaches() {
    let build = |edges: &[(usize, usize)], blocks: usize| {
        let mut mb = ModuleBuilder::new("cfg_shape");
        let ft = mb.add_func_type(vec![Ty::Bool], vec![]);
        let mut fb = mb.function("f", ft);
        let ids: Vec<_> = (0..blocks).map(|_| fb.create_block()).collect();
        fb.set_entry(ids[0]);
        let cv = fb.add_block_param(ids[0], Ty::Bool);
        for (block, id) in ids.iter().enumerate() {
            fb.switch_to_block(*id);
            let targets: Vec<usize> =
                edges.iter().filter(|(from, _)| *from == block).map(|(_, to)| *to).collect();
            match targets.as_slice() {
                [] => fb.ret(vec![]),
                [only] => fb.br(ids[*only], vec![]),
                [then, other] => fb.condbr(cv, ids[*then], vec![], ids[*other], vec![]),
                _ => unreachable!("at most two successors"),
            }
        }
        fb.build();
        (mb.build().expect("ModuleBuilder::build: test fixture"), ids)
    };
    let content = |edges: &[(usize, usize)], blocks: usize| -> Vec<usize> {
        let (module, ids) = build(edges, blocks);
        let set = array_content_blocks(module.function_by_id(FuncId::new(0)).expect("declared"));
        (0..blocks).filter(|index| set.contains(&ids[*index])).collect()
    };
    assert_eq!(content(&[], 1), vec![0], "straight line");
    assert_eq!(content(&[(0, 1), (0, 2), (1, 3), (2, 3)], 4), vec![0, 1, 2, 3], "diamond");
    assert_eq!(content(&[(0, 1), (1, 2), (1, 3), (2, 1)], 4), vec![0], "loop: only the entry");
    assert_eq!(content(&[(0, 1), (1, 1), (1, 2)], 3), vec![0], "self-loop");
    assert_eq!(
        content(&[(0, 1), (1, 2), (2, 0)], 3),
        Vec::<usize>::new(),
        "back edge to the entry"
    );
    assert_eq!(
        content(&[(0, 1), (0, 2), (1, 3), (2, 3), (3, 4), (4, 4), (4, 5)], 6),
        vec![0, 1, 2, 3],
        "a diamond before a loop keeps its content; the loop and after do not"
    );
}

/// Does any term of `rule` (body constraints, body and head arguments) have an
/// array sort?
fn rule_has_array_term(rule: &trust_mc_core::chc::Rule) -> bool {
    let mut seen: BTreeSet<*const ay_bindings::ExprValue> = BTreeSet::new();
    let mut stack: Vec<&Expr> = rule
        .body
        .constraints
        .iter()
        .chain(rule.head.args.iter())
        .chain(rule.body.relation.iter().flat_map(|app| app.args.iter()))
        .collect();
    while let Some(expr) = stack.pop() {
        if seen.insert(std::ptr::from_ref(expr.value())) {
            if expr.sort().is_array() {
                return true;
            }
            stack.extend(expr.children());
        }
    }
    false
}

/// The native CHC engine at the pinned ay revision answers Inconclusive for any
/// array term reachable from a loop, so every block a cycle reaches carries its
/// arrays SHAPE-ONLY: its relation has no array column and no rule leaving it has
/// an array term — while every element access keeps its in-bounds obligation (an
/// error rule over the index and the length alone). Here the entry block, which
/// no cycle reaches, builds the splat; the loop head, body and exit carry it
/// shape-only.
#[test]
fn blocks_a_cycle_reaches_are_array_free_and_keep_their_bounds_obligations() {
    let (module, f) = fixture(Shape::LoopCarried, 4097);
    let output = translate(&module, f);
    assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
    let cyclic = ["bb1", "bb2", "bb3"];
    for relation in &output.vc.relations {
        if cyclic.contains(&relation.name.as_str()) {
            assert!(
                relation.arg_sorts.iter().all(|sort| !sort.is_array()),
                "{} is reached by the loop: no array column",
                relation.name
            );
        }
    }
    for rule in &output.vc.rules {
        let leaves_the_loop =
            rule.body.relation.as_ref().is_some_and(|app| cyclic.contains(&app.name.as_str()));
        if leaves_the_loop {
            assert!(!rule_has_array_term(rule), "an array term in a clause the loop reaches");
        }
    }
    // The loop's write `a[i] = x` keeps its bounds obligation `i <u 4097`.
    let bound = Expr::bitvec_const(4097u64, 64);
    let has_bounds_rule = error_rule_bodies(&output.vc).iter().any(|body| {
        let mut seen: BTreeSet<*const ay_bindings::ExprValue> = BTreeSet::new();
        let mut stack: Vec<&Expr> = body.iter().collect();
        while let Some(expr) = stack.pop() {
            if !seen.insert(std::ptr::from_ref(expr.value())) {
                continue;
            }
            if let ay_bindings::ExprValue::BvULt(_, limit) = expr.value()
                && *limit == bound
            {
                return true;
            }
            stack.extend(expr.children());
        }
        false
    });
    assert!(has_bounds_rule, "the loop's element write keeps its in-bounds rule");
}

// ---------------------------------------------------------------------------
// The junk-lane invariant
// ---------------------------------------------------------------------------

/// No translation of any fixture, at any length or check setting, equates two
/// array-sorted terms — and the detector does see one when it is there.
#[test]
fn no_translation_equates_array_terms() {
    for shape in SHAPES {
        for n in [2, 257] {
            let (module, f) = fixture(shape, n);
            for options in [TranslateOptions::default(), unchecked()] {
                let output = translate_with(&module, f, &options);
                assert!(
                    !output_equates_array_terms(&output),
                    "{shape:?} n = {n}: a rule equates array terms"
                );
            }
        }
    }

    // Positive control: a hand-built rule that asserts `a == const_array(0)`.
    let mut vc = ChcVc::new();
    let sort = lifted_sort(ay_bindings::Sort::bitvec(8), 1);
    let arr_v = vc.declare_var("a".to_string(), sort);
    let zeros = Expr::const_array(array_index_sort(), Expr::bitvec_const(0u64, 8));
    vc.add_relation(trust_mc_core::chc::RelationDecl::nullary("error"));
    vc.add_rule(trust_mc_core::chc::Rule::new(
        trust_mc_core::chc::RuleBody::new(None, vec![arr_v.eq(zeros)]),
        trust_mc_core::chc::RelationApp::nullary("error"),
    ));
    assert!(vc_equates_array_terms(&vc), "the detector must see an array equality");
}

/// `[7; 4][i] == 7` holds on every in-bounds lane AND — because a constant array
/// pins them — on every junk lane. So it is exactly the claim a junk lane could
/// falsely prove if an out-of-bounds read returned the junk:
///
/// * memory checks ON: not proved — the read's own bounds rule fires for
///   `i >= 4`, and it is the ONLY way `error` is reachable (the assertion itself
///   is dead: the path continues only under `i < 4`);
/// * memory checks OFF: not proved either — the out-of-bounds read is a havoc,
///   never the pinned junk, so the ASSERTION can fail, and only for `i >= 4`;
/// * with `assume(i < 4)`: PROVED under both settings.
#[test]
fn a_junk_lane_never_proves_an_assertion() {
    let probe = |bounded: bool| {
        let mut mb = ModuleBuilder::new("junk_proof");
        let u32_id = mb.add_type(Ty::U32);
        let arr = Ty::Array(u32_id, 4);
        let ft = mb.add_func_type(vec![Ty::U64], vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let idx = fb.add_block_param(entry, Ty::U64);
        if bounded {
            let four = fb.iconst(Ty::U64, 4);
            let in_bounds = fb.icmp(ICmpOp::Ult, Ty::U64, idx, four);
            fb.assume(in_bounds);
        }
        let arr_v = fb.const_value(arr, Constant::splat(Constant::Int(7), 4));
        let lane_v = fb.extract_element(Ty::U32, arr_v, idx);
        let seven = fb.iconst(Ty::U32, 7);
        let cond = fb.icmp(ICmpOp::Eq, Ty::U32, lane_v, seven);
        fb.assert(cond);
        fb.ret(vec![]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    let unbounded = probe(false);
    let bounded = probe(true);
    for options in [TranslateOptions::default(), unchecked()] {
        let open = translate_with(&unbounded, FuncId::new(0), &options);
        assert!(open.diagnostics.is_empty(), "{:?}", open.diagnostics);
        assert!(
            error_reachable(&open),
            "check_memory_bounds = {}: `[7; 4][i] == 7` must NOT be proved for an unbounded i",
            options.check_memory_bounds
        );
        // Every way to `error` is an out-of-bounds `i`: never an in-bounds lane.
        let idx = var_named(&open, "bb0_v0");
        let four = Expr::bitvec_const(4u64, 64);
        for body in error_rule_bodies(&open.vc) {
            let mut in_bounds = body.clone();
            in_bounds.push(idx.clone().bvult(four.clone()));
            assert!(
                !satisfiable(&open.vc, &in_bounds),
                "check_memory_bounds = {}: an in-bounds lane of `[7; 4]` must never reach \
                 `error`",
                options.check_memory_bounds
            );
        }

        let proved = translate_with(&bounded, FuncId::new(0), &options);
        assert!(
            !error_reachable(&proved),
            "check_memory_bounds = {}: `[7; 4][i] == 7` under `i < 4` must be PROVED",
            options.check_memory_bounds
        );
    }
}

/// COUNTEREXAMPLE SOUNDNESS. `p` is an unconstrained `[u32; 4]` whose four real
/// lanes are all written `7` — its junk lanes stay FREE, so a junk read could be
/// anything. `assert(p[i] == 7)` then fails on NO real execution: the only real
/// error is the read's bounds violation. A model that let a junk lane reach the
/// assertion would hand back a "counterexample" `i = 9, p[9] = 0` that no Rust
/// execution realizes. With memory checks on:
///
/// * the assertion's error rule is UNSATISFIABLE (the path continues only under
///   `i < 4`, where every lane is 7);
/// * the bounds rule's every model has `i >= 4` — a genuine out-of-bounds read.
///
/// And the other direction — junk must not HIDE a real failure: writing `9` to
/// lane 2 instead makes the assertion's error rule satisfiable, by exactly
/// `i == 2`.
#[test]
fn every_counterexample_through_an_access_reads_a_real_lane() {
    let probe = |lane_two: i128| {
        let mut mb = ModuleBuilder::new("junk_counterexample");
        let u32_id = mb.add_type(Ty::U32);
        let arr = Ty::Array(u32_id, 4);
        let ft = mb.add_func_type(vec![arr.clone(), Ty::U64], vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let param = fb.add_block_param(entry, arr.clone());
        let idx = fb.add_block_param(entry, Ty::U64);
        let mut arr_v = param;
        for (lane, value) in [(0, 7), (1, 7), (2, lane_two), (3, 7)] {
            let lane = fb.iconst(Ty::U64, lane);
            let value = fb.iconst(Ty::U32, value);
            arr_v = fb.insert_element(arr.clone(), arr_v, lane, value);
        }
        let lane_v = fb.extract_element(Ty::U32, arr_v, idx);
        let seven = fb.iconst(Ty::U32, 7);
        let cond = fb.icmp(ICmpOp::Eq, Ty::U32, lane_v, seven);
        fb.assert(cond);
        fb.ret(vec![]);
        fb.build();
        translate(&mb.build().expect("ModuleBuilder::build: test fixture"), FuncId::new(0))
    };
    let all_seven = probe(7);
    assert!(all_seven.diagnostics.is_empty(), "{:?}", all_seven.diagnostics);
    let idx = var_named(&all_seven, "bb0_v1");
    let four = Expr::bitvec_const(4u64, 64);
    let bodies = error_rule_bodies(&all_seven.vc);
    assert_eq!(bodies.len(), 2, "one bounds rule and one assertion rule");
    let (reachable, dead): (Vec<_>, Vec<_>) =
        bodies.into_iter().partition(|body| satisfiable(&all_seven.vc, body));
    assert_eq!(dead.len(), 1, "the assertion can never fail on a real lane");
    assert_eq!(reachable.len(), 1, "the read's bounds rule is reachable");
    for body in reachable {
        let mut in_bounds = body.clone();
        in_bounds.push(idx.clone().bvult(four.clone()));
        assert!(
            !satisfiable(&all_seven.vc, &in_bounds),
            "the bounds rule's every model is out of bounds"
        );
    }

    let lane_two_is_nine = probe(9);
    let idx = var_named(&lane_two_is_nine, "bb0_v1");
    let failing: Vec<_> = error_rule_bodies(&lane_two_is_nine.vc)
        .into_iter()
        .filter(|body| {
            let mut in_bounds = body.clone();
            in_bounds.push(idx.clone().bvult(four.clone()));
            satisfiable(&lane_two_is_nine.vc, &in_bounds)
        })
        .collect();
    assert_eq!(failing.len(), 1, "the real failure is reachable in bounds");
    let mut not_lane_two = failing[0].clone();
    not_lane_two.push(idx.clone().eq(Expr::bitvec_const(2u64, 64)).not());
    assert!(
        !satisfiable(&lane_two_is_nine.vc, &not_lane_two),
        "the only in-bounds counterexample is the lane that really holds 9"
    );
}

/// Write coverage counts only distinct in-range lanes, and an earlier poison
/// write is never hidden by a later one. The coverage rule is observable only
/// where the entry array does not itself supply the lane, so the duplicate-lane
/// and poison controls run on `[(u32,); 3]`, whose root parameter the value-domain
/// rule does not admit. On `[u32; 3]` the root parameter ranges over `[u32; 3]`
/// VALUES (trust-ir SPEC_RATIFICATIONS §13), so the unwritten lane 2 of mode 1 is
/// an in-domain input lane and the read is defined; an embedder-built argument
/// whose lanes are `PartialBytes` lies outside that domain. Mode 2's poison write
/// is refused on both element types.
#[test]
fn finite_array_write_coverage_cannot_count_duplicate_lanes_or_hide_poison() {
    use trust_ir::interpret::{
        ArrayValue, InterpretErrorCode, InterpretValue, InterpretValueKind, Interpreter,
    };
    for tuple_lanes in [true, false] {
        for mode in 0..3 {
            let mut builder = ModuleBuilder::new("finite_array_initialization");
            let lane_ty = if tuple_lanes { Ty::Tuple(vec![Ty::U32]) } else { Ty::U32 };
            let element = builder.add_type(lane_ty.clone());
            let ty = Ty::Array(element, 3);
            let signature = builder.add_func_type(vec![ty.clone()], vec![Ty::U32]);
            let mut function = builder.function("writes_then_reads", signature);
            let entry = function.create_block();
            function.set_entry(entry);
            function.switch_to_block(entry);
            let mut array = function.add_block_param(entry, ty.clone());
            let seven = function.iconst(Ty::U32, 7);
            let seven = if tuple_lanes {
                function.make_aggregate(lane_ty.clone(), vec![seven])
            } else {
                seven
            };
            if mode == 2 {
                let zero = function.iconst(Ty::U64, 0);
                let poison = function.undef(Ty::U32);
                let poison = if tuple_lanes {
                    function.make_aggregate(lane_ty.clone(), vec![poison])
                } else {
                    poison
                };
                array = function.insert_element(ty.clone(), array, zero, poison);
            }
            for lane in if mode == 1 { [0, 1, 1] } else { [0, 1, 2] } {
                let index = function.iconst(Ty::U64, lane);
                array = function.insert_element(ty.clone(), array, index, seven);
            }
            let last = function.iconst(Ty::U64, 2);
            let value = function.extract_element(lane_ty.clone(), array, last);
            let value = if tuple_lanes { function.extract_field(Ty::U32, value, 0) } else { value };
            function.ret(vec![value]);
            function.build();
            let module = builder.build().unwrap();
            assert!(trust_ir_build::validate_module(&module).is_empty());
            let lane = |kind: InterpretValueKind| {
                let scalar = InterpretValue { ty: Ty::U32, kind };
                if tuple_lanes {
                    InterpretValue {
                        ty: lane_ty.clone(),
                        kind: InterpretValueKind::Aggregate(vec![scalar]),
                    }
                } else {
                    scalar
                }
            };
            let input = |lanes: Vec<InterpretValue>| InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::Array(ArrayValue::from_vec(lanes)),
            };
            let poison_input =
                input(vec![lane(InterpretValueKind::PartialBytes(vec![None; 4])); 3]);
            let domain_input = input(
                (100..103)
                    .map(|value| lane(InterpretValue::int(Ty::U32, value).unwrap().kind))
                    .collect(),
            );
            let run = |argument| {
                Interpreter::with_module(&module).execute_func(FuncId::new(0), [argument])
            };
            let output = translate(&module, FuncId::new(0));
            let label = format!("tuple_lanes {tuple_lanes}, mode {mode}");
            let seven = vec![InterpretValue::int(Ty::U32, 7).unwrap()];
            match (tuple_lanes, mode) {
                (_, 0) => {
                    assert_eq!(run(poison_input).unwrap().returns, seven, "{label}");
                    assert_eq!(run(domain_input).unwrap().returns, seven, "{label}");
                    assert!(output.diagnostics.is_empty(), "{label}: {:?}", output.diagnostics);
                }
                (false, 1) => {
                    // The unwritten lane is the in-domain input lane 2.
                    assert_eq!(
                        run(domain_input).unwrap().returns,
                        vec![InterpretValue::int(Ty::U32, 102).unwrap()],
                        "{label}"
                    );
                    assert_eq!(
                        run(poison_input).unwrap_err().code,
                        InterpretErrorCode::UndefinedBehavior,
                        "{label}: the out-of-domain argument stays UB"
                    );
                    assert!(output.diagnostics.is_empty(), "{label}: {:?}", output.diagnostics);
                }
                _ => {
                    assert_eq!(
                        run(poison_input).unwrap_err().code,
                        InterpretErrorCode::UndefinedBehavior,
                        "{label}"
                    );
                    assert!(
                        output.diagnostics.iter().any(|diagnostic| diagnostic.reason
                            == TrustIrChcUnsupportedReason::OperandConsumption),
                        "{label}: {:?}",
                        output.diagnostics
                    );
                    assert!(error_reachable(&output), "{label}");
                }
            }
        }
    }
}

/// A symbolic write followed by a read of the same lane is exact, and one of a
/// different lane keeps the old value: `b = a[i := y]` then `b[i] == y` is
/// proved and `b[j] == a[j]` for `j != i` is proved, under in-bounds indices.
#[test]
fn a_symbolic_write_is_read_back_exactly() {
    let build = |same_lane: bool, initialized: bool| {
        let mut mb = ModuleBuilder::new("symbolic_write");
        let u32_id = mb.add_type(Ty::U32);
        let arr = Ty::Array(u32_id, 4097);
        let ft = mb.add_func_type(
            vec![if initialized { Ty::U32 } else { arr.clone() }, Ty::U64, Ty::U64, Ty::U32],
            vec![],
        );
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let initial = fb.add_block_param(entry, if initialized { Ty::U32 } else { arr.clone() });
        let idx = fb.add_block_param(entry, Ty::U64);
        let jdx = fb.add_block_param(entry, Ty::U64);
        let written = fb.add_block_param(entry, Ty::U32);
        let arr_v = if initialized { fb.array_splat(arr.clone(), initial) } else { initial };
        let n = fb.iconst(Ty::U64, 4097);
        let i_ok = fb.icmp(ICmpOp::Ult, Ty::U64, idx, n);
        fb.assume(i_ok);
        let j_ok = fb.icmp(ICmpOp::Ult, Ty::U64, jdx, n);
        fb.assume(j_ok);
        let arr_w = fb.insert_element(arr, arr_v, idx, written);
        let cond = if same_lane {
            let read = fb.extract_element(Ty::U32, arr_w, idx);
            fb.icmp(ICmpOp::Eq, Ty::U32, read, written)
        } else {
            let distinct = fb.icmp(ICmpOp::Ne, Ty::U64, idx, jdx);
            fb.assume(distinct);
            let new = fb.extract_element(Ty::U32, arr_w, jdx);
            let old = fb.extract_element(Ty::U32, arr_v, jdx);
            fb.icmp(ICmpOp::Eq, Ty::U32, new, old)
        };
        fb.assert(cond);
        fb.ret(vec![]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    };
    // Preserve the original generic array program. An embedder-built argument
    // with poison lanes is UB in the interpreter, but it lies outside the
    // `[u32; 4097]` value domain the root parameter ranges over (trust-ir
    // SPEC_RATIFICATIONS §13): an in-domain argument runs, and the program is
    // PROVED. The poison-entry negative control lives on an element type the
    // value-domain rule does not admit
    // (`finite_array_write_coverage_cannot_count_duplicate_lanes_or_hide_poison`,
    // `root_array_parameters_outside_the_value_domain_rule_keep_the_refusal`).
    let original = build(false, false);
    {
        use trust_ir::interpret::{
            ArrayValue, InterpretErrorCode, InterpretValue, InterpretValueKind, Interpreter,
        };
        let array_ty = original.func_types[original.functions[0].ty.as_usize()].params[0].clone();
        let partial =
            InterpretValue { ty: Ty::U32, kind: InterpretValueKind::PartialBytes(vec![None; 4]) };
        let values = |poison| InterpretValue {
            ty: array_ty.clone(),
            kind: InterpretValueKind::Array(ArrayValue::from_vec(
                (0..4097)
                    .map(|lane| {
                        if poison {
                            partial.clone()
                        } else {
                            InterpretValue::int(Ty::U32, lane).unwrap()
                        }
                    })
                    .collect(),
            )),
        };
        let arguments = |poison| {
            [
                values(poison),
                InterpretValue::int(Ty::U64, 0).unwrap(),
                InterpretValue::int(Ty::U64, 1).unwrap(),
                InterpretValue::int(Ty::U32, 7).unwrap(),
            ]
        };
        assert_eq!(
            Interpreter::with_module(&original)
                .execute_func(FuncId::new(0), arguments(true))
                .unwrap_err()
                .code,
            InterpretErrorCode::UndefinedBehavior
        );
        Interpreter::with_module(&original).execute_func(FuncId::new(0), arguments(false)).unwrap();
    }
    let original_output = translate(&original, FuncId::new(0));
    assert!(original_output.diagnostics.is_empty(), "{:?}", original_output.diagnostics);
    assert!(!error_reachable(&original_output), "the original program must be PROVED");
    for same_lane in [true, false] {
        // Same-index read preserves the original arbitrary array parameter:
        // the actual write supplies that lane's initialization. The unrelated
        // read uses an explicitly initialized unknown source, not a premise.
        let module = build(same_lane, !same_lane);
        let output = translate(&module, FuncId::new(0));
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert!(!error_reachable(&output), "same_lane = {same_lane}: must be PROVED");
    }
}

/// The element of a root array parameter in [`root_array_read`].
#[derive(Debug, Clone)]
enum RootLane {
    /// `[t; 7]`, the lane read directly.
    Scalar(Ty),
    /// `[[t; 2]; 7]`, the lane read down to its first scalar.
    Nested(Ty),
    /// `[(t,); 7]`, the lane read down to its only field.
    Tuple(Ty),
}

/// `pick(a: [e; 7], i: u64) -> t { a[i]… }` translated as the ROOT, with an
/// optional `assume(i < 7)`; the read descends to the element's scalar `t`.
fn root_array_read(lane: &RootLane, guarded: bool) -> Module {
    let mut mb = ModuleBuilder::new("root_array_read");
    let (element, scalar) = match lane {
        RootLane::Scalar(ty) => (ty.clone(), ty.clone()),
        RootLane::Nested(ty) => (Ty::Array(mb.add_type(ty.clone()), 2), ty.clone()),
        RootLane::Tuple(ty) => (Ty::Tuple(vec![ty.clone()]), ty.clone()),
    };
    let array = Ty::Array(mb.add_type(element.clone()), 7);
    let ft = mb.add_func_type(vec![array.clone(), Ty::U64], vec![scalar.clone()]);
    let mut fb = mb.function("pick", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let a = fb.add_block_param(entry, array);
    let i = fb.add_block_param(entry, Ty::U64);
    if guarded {
        let seven = fb.iconst(Ty::U64, 7);
        let in_bounds = fb.icmp(ICmpOp::Ult, Ty::U64, i, seven);
        fb.assume(in_bounds);
    }
    let read = fb.extract_element(element, a, i);
    let read = match lane {
        RootLane::Scalar(_) => read,
        RootLane::Nested(_) => {
            let zero = fb.iconst(Ty::U64, 0);
            fb.extract_element(scalar, read, zero)
        }
        RootLane::Tuple(_) => fb.extract_field(scalar, read, 0),
    };
    fb.ret(vec![read]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    module
}

/// BMC-LANE-1: a root parameter ranges over its type's value domain (trust-ir
/// SPEC_RATIFICATIONS §13), so a lane read of a root `[e; n]` parameter whose
/// element is an integer, `Bool`, float or such an array is defined. The read's
/// bounds rule stays: unguarded, it is reachable and its every model is out of
/// bounds; under `assume(i < 7)` the function is PROVED.
#[test]
fn a_root_value_domain_array_parameter_lane_read_is_defined() {
    let lanes = [
        RootLane::Scalar(Ty::I32),
        RootLane::Scalar(Ty::U8),
        RootLane::Scalar(Ty::Usize),
        RootLane::Scalar(Ty::I128),
        RootLane::Scalar(Ty::Bool),
        RootLane::Scalar(Ty::F64),
        RootLane::Nested(Ty::I32),
    ];
    for lane in lanes {
        let unguarded = translate(&root_array_read(&lane, false), FuncId::new(0));
        assert!(unguarded.diagnostics.is_empty(), "{lane:?}: {:?}", unguarded.diagnostics);
        assert!(error_reachable(&unguarded), "{lane:?}: the unguarded read is out of bounds");
        let index = var_named(&unguarded, "bb0_v1");
        let seven = Expr::bitvec_const(7u64, 64);
        for body in error_rule_bodies(&unguarded.vc) {
            let mut in_bounds = body.clone();
            in_bounds.push(index.clone().bvult(seven.clone()));
            assert!(
                !satisfiable(&unguarded.vc, &in_bounds),
                "{lane:?}: every reachable error model reads out of bounds"
            );
        }
        let guarded = translate(&root_array_read(&lane, true), FuncId::new(0));
        assert!(guarded.diagnostics.is_empty(), "{lane:?}: {:?}", guarded.diagnostics);
        assert!(!error_reachable(&guarded), "{lane:?}: the guarded read must be PROVED");
    }
}

/// The value-domain rule is narrow: a root array whose element is a `char` (a
/// 32-bit carrier wider than its domain), a pointer, or a tuple, or an array of
/// those, keeps the definedness refusal, guarded or not.
#[test]
fn root_array_parameters_outside_the_value_domain_rule_keep_the_refusal() {
    let lanes = [
        RootLane::Scalar(Ty::Char),
        RootLane::Nested(Ty::Char),
        RootLane::Scalar(Ty::Ptr),
        RootLane::Tuple(Ty::U32),
    ];
    for lane in lanes {
        for guarded in [false, true] {
            let output = translate(&root_array_read(&lane, guarded), FuncId::new(0));
            assert!(
                output.diagnostics.iter().any(|diagnostic| diagnostic.reason
                    == TrustIrChcUnsupportedReason::OperandConsumption),
                "{lane:?}, guarded {guarded}: {:?}",
                output.diagnostics
            );
            assert!(error_reachable(&output), "{lane:?}, guarded {guarded}");
        }
    }
}

/// `f(i) { a = [0; 4]; _ = a[index] }` for a constant out-of-bounds `index`
/// or the unconstrained parameter `i`.
fn oob_read(constant_index: bool) -> Module {
    let mut mb = ModuleBuilder::new("oob_read");
    let u32_id = mb.add_type(Ty::U32);
    let arr = Ty::Array(u32_id, 4);
    let ft = mb.add_func_type(vec![Ty::U64], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let idx = fb.add_block_param(entry, Ty::U64);
    let index = if constant_index { fb.iconst(Ty::U64, 4) } else { idx };
    let zero = fb.iconst(Ty::U32, 0);
    let arr_v = fb.array_splat(arr, zero);
    let _z = fb.extract_element(Ty::U32, arr_v, index);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A static invalid index refuses canonical input regardless of memory options.
/// A valid dynamic index reaches error through its runtime bounds rule only
/// with memory checks on; with them off it is havoc, never an error.
#[test]
fn an_out_of_bounds_read_reaches_error() {
    for constant_index in [true, false] {
        let module = oob_read(constant_index);
        if constant_index {
            crate::tests::assert_canonical_refusal(
                &module,
                "constant lane index 4 is out of range for 4 lanes",
            );
            continue;
        }
        assert!(trust_ir_build::validate_module(&module).is_empty());
        let checked = translate(&module, FuncId::new(0));
        assert!(checked.diagnostics.is_empty(), "{:?}", checked.diagnostics);
        assert!(error_reachable(&checked), "constant = {constant_index}: an OOB read is an error");
        let unchecked_output = translate_with(&module, FuncId::new(0), &unchecked());
        assert!(
            unchecked_output.vc.rules.iter().all(|rule| rule.head.name.as_str() != "error"),
            "constant = {constant_index}: with memory checks off the read adds no error rule"
        );
    }
}

/// A stack cell of a length far past the retired bound, written whole and then
/// through a constant GEP lane, reads back the lane write and the splat
/// elsewhere — the cell is tracked at any length.
#[test]
fn a_long_array_stack_cell_is_tracked_through_its_lanes() {
    let probe = |read_lane: i128, expected: i128| {
        let mut mb = ModuleBuilder::new("long_cell");
        let u32_id = mb.add_type(Ty::U32);
        let arr = Ty::Array(u32_id, 4097);
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let slot = fb.alloca(arr.clone());
        let five = fb.iconst(Ty::U32, 5);
        let splat = fb.array_splat(arr.clone(), five);
        fb.store(arr.clone(), slot, splat);
        let lane = fb.iconst(Ty::I64, 3000);
        let lane_ptr = fb.gep(Ty::U32, slot, vec![lane]);
        let nine = fb.iconst(Ty::U32, 9);
        fb.store(Ty::U32, lane_ptr, nine);
        let whole = fb.load(arr, slot);
        let read = fb.iconst(Ty::I64, read_lane);
        let lane_v = fb.extract_element(Ty::U32, whole, read);
        let want = fb.iconst(Ty::U32, expected);
        let cond = fb.icmp(ICmpOp::Eq, Ty::U32, lane_v, want);
        fb.assert(cond);
        fb.ret(vec![]);
        fb.build();
        translate(&mb.build().expect("ModuleBuilder::build: test fixture"), FuncId::new(0))
    };
    for (lane, expected, holds) in [(3000, 9, true), (3, 5, true), (3000, 5, false), (3, 9, false)]
    {
        let output = probe(lane, expected);
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert_eq!(
            !error_reachable(&output),
            holds,
            "lane {lane} == {expected} must be {}",
            if holds { "PROVED" } else { "REFUTED" }
        );
    }
}

/// A list-spelled array literal is fresh lanes pinned by one definitional
/// equality per element (`define_array_lanes`): every lane reads back exactly,
/// and the literal costs one equality per element WRITTEN.
#[test]
fn a_list_literal_is_exact_lane_by_lane() {
    let probe = |lane: i128, expected: i128| {
        let mut mb = ModuleBuilder::new("list_literal");
        let u32_id = mb.add_type(Ty::U32);
        let arr = Ty::Array(u32_id, 3);
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let arr_v = fb.const_value(
            arr,
            Constant::Array(vec![Constant::Int(4), Constant::Int(5), Constant::Int(6)]),
        );
        let index = fb.iconst(Ty::U64, lane);
        let lane_v = fb.extract_element(Ty::U32, arr_v, index);
        let want = fb.iconst(Ty::U32, expected);
        let cond = fb.icmp(ICmpOp::Eq, Ty::U32, lane_v, want);
        fb.assert(cond);
        fb.ret(vec![]);
        fb.build();
        translate(&mb.build().expect("ModuleBuilder::build: test fixture"), FuncId::new(0))
    };
    for (lane, value) in [(0, 4), (1, 5), (2, 6)] {
        assert!(!error_reachable(&probe(lane, value)), "lane {lane} == {value} is PROVED");
        assert!(
            error_reachable(&probe(lane, value + 1)),
            "lane {lane} == {} is REFUTED",
            value + 1
        );
    }
}

// ---------------------------------------------------------------------------
// The gate's stack-cell lanes admit an array cell of any length (TMC-2)
// ---------------------------------------------------------------------------

/// The cell types the frozen extent (`gate_array_extent_is_legacy_admitted`,
/// deleted by decision TMC-2) refused, and the ones it admitted: every one is a
/// promotable cell, and nothing about it is sized by a length.
fn cell_types_across_the_retired_extent(mb: &mut ModuleBuilder) -> Vec<(&'static str, Ty)> {
    let u8_id = mb.add_type(Ty::U8);
    let row_64 = mb.add_type(Ty::Array(u8_id, 64));
    let row_65 = mb.add_type(Ty::Array(u8_id, 65));
    vec![
        ("[u8; 256]", Ty::Array(u8_id, 256)),
        ("[u8; 257]", Ty::Array(u8_id, 257)),
        ("[u8; 4097]", Ty::Array(u8_id, 4097)),
        // The largest length a type can carry (this module's and
        // `tests/v50_array_splat.rs`'s convention): a regression that walked or
        // allocated per lane would fail at once on a capacity overflow instead of
        // reserving toward a huge but grantable length.
        ("[u8; u64::MAX]", Ty::Array(u8_id, u64::MAX)),
        ("[[u8; 64]; 64] = 4096 retired leaves", Ty::Array(row_64, 64)),
        ("[[u8; 65]; 64] = 4160 retired leaves", Ty::Array(row_65, 64)),
        ("(u8, [u8; 300])", Ty::Tuple(vec![Ty::U8, Ty::Array(u8_id, 300)])),
    ]
}

/// Lane 2 (promoted cell): a cross-block `slot = alloca T; *slot = v; …; _ = *slot`
/// cell is promoted by the translator and admitted by the gate at every length —
/// the lengths the retired extent refused (past 256 lanes, past 4096 flattened
/// leaves) included. Before TMC-2 the long ones were refused as
/// `array_extent_pending_decision`.
#[test]
fn a_promoted_array_cell_is_admitted_by_the_gate_at_every_length() {
    let mut mb = ModuleBuilder::new("promoted_cells");
    let cases = cell_types_across_the_retired_extent(&mut mb);
    let mut cells = Vec::new();
    for (index, (label, ty)) in cases.iter().enumerate() {
        let ft = mb.add_func_type(vec![ty.clone()], vec![]);
        let mut fb = mb.function(&format!("f{index}"), ft);
        let entry = fb.create_block();
        let next = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let value = fb.add_block_param(entry, ty.clone());
        let slot = fb.alloca(ty.clone());
        fb.store(ty.clone(), slot, value);
        fb.br(next, vec![]);
        fb.switch_to_block(next);
        let _whole = fb.load(ty.clone(), slot);
        fb.ret(vec![]);
        fb.build();
        cells.push((*label, ty.clone(), slot));
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    for (index, (label, ty, slot)) in cells.into_iter().enumerate() {
        let function = module.function_by_id(FuncId::new(index as u32)).expect("declared");
        let (promoted, _) = compute_promotable_cells_of(&module, function);
        assert!(
            promoted.iter().any(|(cell, _)| *cell == slot),
            "{label}: the translator promotes the cell"
        );
        assert_eq!(
            promoted_cell_alloca_reject(&module, function, slot, &ty),
            None,
            "{label}: lane 2 admits it"
        );
        assert!(single_cell_alloca_is_admissible(&module, function, slot, &ty), "{label}");
    }
}

/// Lane 4 (initialized block-local borrow): `slot = alloca T; *slot = v; r = &slot;
/// _ = *r` in one block is admitted at every length, as it is at 256 lanes.
#[test]
fn a_borrowed_block_local_array_cell_is_admitted_by_the_gate_at_every_length() {
    let mut mb = ModuleBuilder::new("borrowed_cells");
    let cases = cell_types_across_the_retired_extent(&mut mb);
    let mut borrows = Vec::new();
    for (index, (label, ty)) in cases.iter().enumerate() {
        let ft = mb.add_func_type(vec![ty.clone()], vec![]);
        let mut fb = mb.function(&format!("g{index}"), ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let value = fb.add_block_param(entry, ty.clone());
        let slot = fb.alloca(ty.clone());
        fb.store(ty.clone(), slot, value);
        let shared = fb.borrow(slot);
        let _whole = fb.load(ty.clone(), shared);
        fb.ret(vec![]);
        fb.build();
        borrows.push((*label, shared));
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    for (index, (label, shared)) in borrows.into_iter().enumerate() {
        let function = module.function_by_id(FuncId::new(index as u32)).expect("declared");
        assert!(
            initialized_local_borrow_is_admissible(&module, function, shared),
            "{label}: lane 4 admits the borrow"
        );
    }
}

// ---------------------------------------------------------------------------
// Element index signedness
// ---------------------------------------------------------------------------

/// `f(p) { a = [0u32; 256]; b = a[idx := 5]; assert(b[lane] == expected) }` where
/// `idx` has the bit pattern `bits` at `index_ty`: a constant or, `symbolic`, the
/// parameter `p: index_ty` under `assume(p == bits)`. `lane` is a `u64`.
fn index_write(index_ty: &Ty, bits: i128, symbolic: bool, lane: i128, expected: i128) -> Module {
    let mut mb = ModuleBuilder::new("index_write");
    let u32_id = mb.add_type(Ty::U32);
    let arr = Ty::Array(u32_id, 256);
    let ft = mb.add_func_type(vec![index_ty.clone()], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let param = fb.add_block_param(entry, index_ty.clone());
    let idx = if symbolic {
        let want = fb.iconst(index_ty.clone(), bits);
        let is = fb.icmp(ICmpOp::Eq, index_ty.clone(), param, want);
        fb.assume(is);
        param
    } else {
        fb.iconst(index_ty.clone(), bits)
    };
    let zero = fb.iconst(Ty::U32, 0);
    let a = fb.array_splat(arr.clone(), zero);
    let five = fb.iconst(Ty::U32, 5);
    let b = fb.insert_element(arr, a, idx, five);
    let lane = fb.iconst(Ty::U64, lane);
    let read = fb.extract_element(Ty::U32, b, lane);
    let want = fb.iconst(Ty::U32, expected);
    let cond = fb.icmp(ICmpOp::Eq, Ty::U32, read, want);
    fb.assert(cond);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// An UNSIGNED index narrower than `usize` with its top bit set is an ordinary
/// in-bounds index: a `u8` of 200 names lane 200 of a `[u32; 256]` (trust-ir
/// `runtime_index`). So `b[200] == 5` after `b = a[200u8 := 5]` is PROVED and
/// `b[200] == 0` is REFUTED — a clean refutation, with no diagnostic — with memory
/// checks on and off, for a constant and for a symbolic index. (Reading its top
/// bit as a sign once dropped this write with checks off — a false proof of
/// `b[200] == 0` — and refuted the correct program with checks on.)
#[test]
fn a_narrow_unsigned_index_names_its_lane() {
    for symbolic in [false, true] {
        for options in [TranslateOptions::default(), unchecked()] {
            let label = format!("symbolic = {symbolic}, checks = {}", options.check_memory_bounds);
            let holds = translate_with(
                &index_write(&Ty::U8, 200, symbolic, 200, 5),
                FuncId::new(0),
                &options,
            );
            assert!(holds.diagnostics.is_empty(), "{label}: {:?}", holds.diagnostics);
            assert!(!error_reachable(&holds), "{label}: b[200] == 5 must be PROVED");
            let fails = translate_with(
                &index_write(&Ty::U8, 200, symbolic, 200, 0),
                FuncId::new(0),
                &options,
            );
            assert!(fails.diagnostics.is_empty(), "{label}: {:?}", fails.diagnostics);
            assert!(error_reachable(&fails), "{label}: b[200] == 0 must be REFUTED");
        }
    }
}

/// A SIGNED index with the same bits, `-56i8`, is negative: undefined behaviour,
/// never lane 200. With memory checks on, the write's bounds rule is the one
/// reachable error (the path does not continue past it). With them off, the
/// write havocs the array, so neither `b[200] == 5` (the wrapped reading) nor
/// `b[200] == 0` (a dropped write) is proved.
#[test]
fn a_negative_signed_index_is_undefined_behaviour_not_a_wrapped_lane() {
    for symbolic in [false, true] {
        let label = format!("symbolic = {symbolic}");
        for expected in [5, 0] {
            let module = index_write(&Ty::I8, -56, symbolic, 200, expected);
            let checked = translate(&module, FuncId::new(0));
            assert!(checked.diagnostics.is_empty(), "{label}: {:?}", checked.diagnostics);
            let reachable = error_rule_bodies(&checked.vc)
                .iter()
                .filter(|body| satisfiable(&checked.vc, body))
                .count();
            assert_eq!(reachable, 1, "{label}: only the write's bounds rule is reachable");
            let unchecked_output = translate_with(&module, FuncId::new(0), &unchecked());
            assert!(
                error_reachable(&unchecked_output),
                "{label}: b[200] == {expected} must not be proved through a negative index"
            );
        }
    }
}

/// `translate`, but with no declared type for any element operand: every index
/// is of UNKNOWN signedness (the defensive path of `array_lane_access`).
fn translate_without_index_types(
    module: &Module,
    options: &TranslateOptions,
) -> ChcTranslationOutput {
    let func = module.function_by_id(FuncId::new(0)).expect("declared");
    let mut translator = ChcFuncTranslator::new(func, module, options);
    translator.element_operand_tys.clear();
    translator.translate()
}

/// An index whose declared type is unknown is read only where both readings
/// agree. Bits 100 (top bit clear) are exact: `b[100] == 5` is PROVED. Bits 200
/// (top bit set, below the length) name lane 200 unsigned and UB signed: with
/// memory checks on the access fails closed with an `UnmodeledElementIndex`
/// diagnostic (never a clean verdict), and with them off the write havocs, so
/// neither reading's claim is proved.
#[test]
fn an_index_of_unknown_signedness_fails_closed_where_its_readings_disagree() {
    for symbolic in [false, true] {
        let label = format!("symbolic = {symbolic}");
        for options in [TranslateOptions::default(), unchecked()] {
            // (A symbolic index carries the ambiguous-region rule whatever it is
            // assumed to be; under `p == 100` that rule is unreachable.)
            let agree = translate_without_index_types(
                &index_write(&Ty::U8, 100, symbolic, 100, 5),
                &options,
            );
            if !symbolic {
                assert!(agree.diagnostics.is_empty(), "{label}: {:?}", agree.diagnostics);
            }
            assert!(!error_reachable(&agree), "{label}: bits 100 are lane 100 either way");
        }
        for expected in [5, 0] {
            let module = index_write(&Ty::U8, 200, symbolic, 200, expected);
            let checked = translate_without_index_types(&module, &TranslateOptions::default());
            assert!(
                checked
                    .diagnostics
                    .iter()
                    .any(|d| d.reason == TrustIrChcUnsupportedReason::UnmodeledElementIndex),
                "{label}: {:?}",
                checked.diagnostics
            );
            let unchecked_output = translate_without_index_types(&module, &unchecked());
            assert!(
                unchecked_output.diagnostics.is_empty(),
                "{label}: {:?}",
                unchecked_output.diagnostics
            );
            assert!(
                error_reachable(&unchecked_output),
                "{label}: b[200] == {expected} is not proved"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Array literals: flat, exact, constant depth
// ---------------------------------------------------------------------------

/// The deepest term over every rule of `vc` (body constraints, body and head
/// arguments), computed iteratively so a deep term cannot overflow the test.
fn max_term_depth(vc: &ChcVc) -> usize {
    let mut depth: BTreeMap<*const ay_bindings::ExprValue, usize> = BTreeMap::new();
    let mut deepest = 0;
    for rule in &vc.rules {
        let roots = rule
            .body
            .constraints
            .iter()
            .chain(rule.head.args.iter())
            .chain(rule.body.relation.iter().flat_map(|app| app.args.iter()));
        for root in roots {
            let mut stack: Vec<(&Expr, bool)> = vec![(root, false)];
            while let Some((expr, expanded)) = stack.pop() {
                let key = std::ptr::from_ref(expr.value());
                if depth.contains_key(&key) {
                    continue;
                }
                if expanded {
                    let below = expr
                        .children()
                        .map(|child| {
                            depth.get(&std::ptr::from_ref(child.value())).copied().unwrap_or(0)
                        })
                        .max()
                        .unwrap_or(0);
                    depth.insert(key, below + 1);
                    deepest = deepest.max(below + 1);
                } else {
                    stack.push((expr, true));
                    for child in expr.children() {
                        stack.push((child, false));
                    }
                }
            }
        }
    }
    deepest
}

/// `f() { a = const [0, 1, 2, …, n-1 (mod 1000)] : [u32; n]; assert(a[3] == 3) }`.
fn long_list_literal(n: usize) -> Module {
    let mut mb = ModuleBuilder::new("long_list_literal");
    let u32_id = mb.add_type(Ty::U32);
    let arr = Ty::Array(u32_id, u64::try_from(n).expect("fits"));
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let elems =
        (0..n).map(|lane| Constant::Int(i128::try_from(lane % 1000).expect("fits"))).collect();
    let arr_v = fb.const_value(arr, Constant::Array(elems));
    let three = fb.iconst(Ty::U64, 3);
    let lane_v = fb.extract_element(Ty::U32, arr_v, three);
    let want = fb.iconst(Ty::U32, 3);
    let cond = fb.icmp(ICmpOp::Eq, Ty::U32, lane_v, want);
    fb.assert(cond);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A list literal is FLAT: its terms are as deep at 2^15 elements as at 4, so
/// no recursive consumer (the solver, `Drop` of the term) meets a deep term —
/// a store chain as long as the literal overflowed the in-process solver's stack
/// at 2^14 elements and aborted the process. The literal of 2^14 elements
/// translates, solves (PROVED) and drops.
#[test]
fn a_long_list_literal_is_flat_and_solves() {
    let short = translate(&long_list_literal(4), FuncId::new(0));
    let long = translate(&long_list_literal(1 << 15), FuncId::new(0));
    assert!(long.diagnostics.is_empty(), "{:?}", long.diagnostics);
    assert_eq!(
        max_term_depth(&long.vc),
        max_term_depth(&short.vc),
        "depth does not grow with the literal"
    );
    drop(long);
    let solved = translate(&long_list_literal(1 << 14), FuncId::new(0));
    assert!(!error_reachable(&solved), "a[3] == 3 is PROVED");
}

/// `f() { a = const <value> : [elem; len]; assert(a[lane] == expected) }`.
fn literal_read(len: u64, value: Constant, elem: Ty, lane: i128, expected: i128) -> Module {
    let mut mb = ModuleBuilder::new("literal_read");
    let elem_id = mb.add_type(elem.clone());
    let arr = Ty::Array(elem_id, len);
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let arr_v = fb.const_value(arr, value);
    let index = fb.iconst(Ty::U64, lane);
    let lane_v = fb.extract_element(elem.clone(), arr_v, index);
    let want = fb.iconst(elem.clone(), expected);
    let cond = fb.icmp(ICmpOp::Eq, elem, lane_v, want);
    fb.assert(cond);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The other list spellings of an array literal are exact lane by lane too: a
/// byte string at `[u8; n]` and the legacy `Aggregate` spelling at an array type
/// (trust-ir executes both as the listed elements).
#[test]
fn byte_string_and_aggregate_array_literals_are_exact() {
    let bytes = || Constant::Bytes { data: b"abc".to_vec(), utf8: false };
    for (lane, byte) in [(0, b'a'), (1, b'b'), (2, b'c')] {
        let byte = i128::from(byte);
        let proved = translate(&literal_read(3, bytes(), Ty::U8, lane, byte), FuncId::new(0));
        assert!(proved.diagnostics.is_empty(), "{:?}", proved.diagnostics);
        assert!(!error_reachable(&proved), "bytes lane {lane} == {byte} is PROVED");
        let refuted = translate(&literal_read(3, bytes(), Ty::U8, lane, byte + 1), FuncId::new(0));
        assert!(error_reachable(&refuted), "bytes lane {lane} == {} is REFUTED", byte + 1);
    }
    let aggregate =
        || Constant::Aggregate(vec![Constant::Int(4), Constant::Int(5), Constant::Int(6)]);
    for (lane, value) in [(0, 4), (1, 5), (2, 6)] {
        let proved = translate(&literal_read(3, aggregate(), Ty::U32, lane, value), FuncId::new(0));
        assert!(proved.diagnostics.is_empty(), "{:?}", proved.diagnostics);
        assert!(!error_reachable(&proved), "aggregate lane {lane} == {value} is PROVED");
        let refuted =
            translate(&literal_read(3, aggregate(), Ty::U32, lane, value + 1), FuncId::new(0));
        assert!(error_reachable(&refuted), "aggregate lane {lane} == {} is REFUTED", value + 1);
    }
}

/// A list literal of ARRAYS — `[[1, 2, 3], [0; 3]]`, a nested list and a nested
/// splat — is exact: its nested lanes are pinned by definitional array-sorted
/// equalities `select(L, k) = e_k`, which the junk-lane checker admits (every
/// debug translation runs it) because `L` is fresh and each lane is defined once.
#[test]
fn a_nested_array_literal_is_exact() {
    let probe = |row: i128, column: i128, expected: i128| {
        let mut mb = ModuleBuilder::new("nested_literal");
        let u8_id = mb.add_type(Ty::U8);
        let row_ty = Ty::Array(u8_id, 3);
        let row_id = mb.add_type(row_ty.clone());
        let grid = Ty::Array(row_id, 2);
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let value = Constant::Array(vec![
            Constant::Array(vec![Constant::Int(1), Constant::Int(2), Constant::Int(3)]),
            Constant::splat(Constant::Int(0), 3),
        ]);
        let grid_v = fb.const_value(grid, value);
        let row_index = fb.iconst(Ty::U64, row);
        let row_v = fb.extract_element(row_ty, grid_v, row_index);
        let column_index = fb.iconst(Ty::U64, column);
        let cell = fb.extract_element(Ty::U8, row_v, column_index);
        let want = fb.iconst(Ty::U8, expected);
        let cond = fb.icmp(ICmpOp::Eq, Ty::U8, cell, want);
        fb.assert(cond);
        fb.ret(vec![]);
        fb.build();
        translate(&mb.build().expect("ModuleBuilder::build: test fixture"), FuncId::new(0))
    };
    for (row, column, value) in [(0, 0, 1), (0, 2, 3), (1, 1, 0)] {
        let proved = probe(row, column, value);
        assert!(proved.diagnostics.is_empty(), "{:?}", proved.diagnostics);
        assert!(!error_reachable(&proved), "[{row}][{column}] == {value} is PROVED");
        // The in-process solver cannot always validate a model over nested array
        // sorts (it answers `incomplete`, fail-closed), so the other direction is
        // pinned as NEVER PROVED rather than as a validated counterexample.
        let wrong = probe(row, column, value + 1);
        assert!(
            error_rule_bodies(&wrong.vc).iter().any(|body| !unsatisfiable(&wrong.vc, body)),
            "[{row}][{column}] == {} is never proved",
            value + 1
        );
    }
}

/// `MakeAggregate` at an array type, one operand per lane, is exact (the flat
/// encoding of its operands): `a = [x, y]; a[1] == y` is PROVED and `a[1] == x`
/// is REFUTED, with no diagnostic.
#[test]
fn make_aggregate_over_an_array_is_exact() {
    let probe = |read_y: bool| {
        let mut mb = ModuleBuilder::new("make_array");
        let u32_id = mb.add_type(Ty::U32);
        let arr = Ty::Array(u32_id, 2);
        let ft = mb.add_func_type(vec![Ty::U32, Ty::U32], vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let x = fb.add_block_param(entry, Ty::U32);
        let y = fb.add_block_param(entry, Ty::U32);
        let arr_v = fb.make_aggregate(arr, vec![x, y]);
        let one = fb.iconst(Ty::U64, 1);
        let lane_v = fb.extract_element(Ty::U32, arr_v, one);
        let cond = fb.icmp(ICmpOp::Eq, Ty::U32, lane_v, if read_y { y } else { x });
        fb.assert(cond);
        fb.ret(vec![]);
        fb.build();
        translate(&mb.build().expect("ModuleBuilder::build: test fixture"), FuncId::new(0))
    };
    let proved = probe(true);
    assert!(proved.diagnostics.is_empty(), "{:?}", proved.diagnostics);
    assert!(!error_reachable(&proved), "a[1] == y is PROVED");
    assert!(error_reachable(&probe(false)), "a[1] == x is REFUTED");
}

// ---------------------------------------------------------------------------
// Arrays with no binding of their own still carry their bounds
// ---------------------------------------------------------------------------

/// An array-typed `Select` is `ite` on the lanes: `select(c, [1; 4], [2; 4])[i]`
/// is exact (`== 1` PROVED under `c` and `i < 4`) and, unguarded, its bounds rule
/// is the way `error` is reached — only by an out-of-bounds `i`.
#[test]
fn an_array_select_carries_its_lanes_and_its_bounds() {
    let probe = |guarded: bool| {
        let mut mb = ModuleBuilder::new("array_select");
        let u32_id = mb.add_type(Ty::U32);
        let arr = Ty::Array(u32_id, 4);
        let ft = mb.add_func_type(vec![Ty::Bool, Ty::U64], vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let cv = fb.add_block_param(entry, Ty::Bool);
        let idx = fb.add_block_param(entry, Ty::U64);
        let ones = fb.const_value(arr.clone(), Constant::splat(Constant::Int(1), 4));
        let twos = fb.const_value(arr.clone(), Constant::splat(Constant::Int(2), 4));
        let picked = fb.select(arr, cv, ones, twos);
        if guarded {
            fb.assume(cv);
            let four = fb.iconst(Ty::U64, 4);
            let ok = fb.icmp(ICmpOp::Ult, Ty::U64, idx, four);
            fb.assume(ok);
        }
        let lane_v = fb.extract_element(Ty::U32, picked, idx);
        if guarded {
            let one = fb.iconst(Ty::U32, 1);
            let is_one = fb.icmp(ICmpOp::Eq, Ty::U32, lane_v, one);
            fb.assert(is_one);
        }
        fb.ret(vec![]);
        fb.build();
        translate(&mb.build().expect("ModuleBuilder::build: test fixture"), FuncId::new(0))
    };
    let proved = probe(true);
    assert!(proved.diagnostics.is_empty(), "{:?}", proved.diagnostics);
    assert!(!error_reachable(&proved), "select(c, [1; 4], [2; 4])[i] == 1 under c, i < 4");
    let open = probe(false);
    assert!(error_reachable(&open), "an unbounded i reaches the read's bounds rule");
    let idx = var_named(&open, "bb0_v1");
    for body in error_rule_bodies(&open.vc) {
        let mut in_bounds = body.clone();
        in_bounds.push(idx.clone().bvult(Expr::bitvec_const(4u64, 64)));
        assert!(!satisfiable(&open.vc, &in_bounds), "only an out-of-bounds i reaches error");
    }
}

/// An array whose ELEMENT this model does not track (`[Seq<u8>; 4]`) has no lanes
/// of its own, but it has a declared length: a read at an unbounded index still
/// carries its bounds rule, and under `i < 4` no error is reachable.
#[test]
fn an_untracked_element_array_keeps_its_bounds_rule() {
    let probe = |guarded: bool| {
        let mut mb = ModuleBuilder::new("untracked_element");
        let u8_id = mb.add_type(Ty::U8);
        let seq = Ty::Sequence(u8_id);
        let seq_id = mb.add_type(seq.clone());
        let arr = Ty::Array(seq_id, 4);
        let ft = mb.add_func_type(vec![arr.clone(), Ty::U64], vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let arr_v = fb.add_block_param(entry, arr);
        let idx = fb.add_block_param(entry, Ty::U64);
        if guarded {
            let four = fb.iconst(Ty::U64, 4);
            let ok = fb.icmp(ICmpOp::Ult, Ty::U64, idx, four);
            fb.assume(ok);
        }
        let _read = fb.extract_element(seq, arr_v, idx);
        fb.ret(vec![]);
        fb.build();
        translate(&mb.build().expect("ModuleBuilder::build: test fixture"), FuncId::new(0))
    };
    assert!(error_reachable(&probe(false)), "an unbounded read of [Seq<u8>; 4] is an error");
    assert!(!error_reachable(&probe(true)), "an in-bounds read of [Seq<u8>; 4] is not");
}

// ---------------------------------------------------------------------------
// Blocks before a loop keep the full model
// ---------------------------------------------------------------------------

/// `slot = alloca [u32; 4]; *slot = [5; 4]; *gep(slot, 1) = 9; v = *gep(slot, 1);
/// assert(v == expected)` in the entry block, `in_loop` inside a loop body, else
/// before a loop that follows it.
fn stack_lane_round_trip(in_loop: bool, expected: i128) -> Module {
    let mut mb = ModuleBuilder::new("stack_lane_round_trip");
    let u32_id = mb.add_type(Ty::U32);
    let arr = Ty::Array(u32_id, 4);
    let ft = mb.add_func_type(vec![Ty::Bool], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let cv = fb.add_block_param(entry, Ty::Bool);
    let round_trip = |fb: &mut trust_ir_build::builder::FunctionBuilder<'_>| {
        let slot = fb.alloca(arr.clone());
        let five = fb.iconst(Ty::U32, 5);
        let splat = fb.array_splat(arr.clone(), five);
        fb.store(arr.clone(), slot, splat);
        let lane = fb.iconst(Ty::I64, 1);
        let lane_ptr = fb.gep(Ty::U32, slot, vec![lane]);
        let nine = fb.iconst(Ty::U32, 9);
        fb.store(Ty::U32, lane_ptr, nine);
        let lane_ptr = fb.gep(Ty::U32, slot, vec![lane]);
        let read = fb.load(Ty::U32, lane_ptr);
        let want = fb.iconst(Ty::U32, expected);
        let cond = fb.icmp(ICmpOp::Eq, Ty::U32, read, want);
        fb.assert(cond);
    };
    if !in_loop {
        round_trip(&mut fb);
    }
    fb.br(body, vec![]);
    fb.switch_to_block(body);
    if in_loop {
        round_trip(&mut fb);
    }
    fb.condbr(cv, body, vec![], exit, vec![]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A stack array cell written whole and through a constant GEP lane, then read
/// back through the lane, in the entry block of a function with a loop AFTER it:
/// no cycle reaches the entry, so the cell's content is modeled — `v == 9` is
/// PROVED and `v == 5` REFUTED, with no diagnostic. (A whole-function "has a
/// cycle" choice made this read fail closed.) The same round trip INSIDE the loop
/// is where this model is still imprecise: the block's arrays are shape-only, so
/// the lane load — a valid access to owned stack memory at an admitted lane —
/// reads a fresh value with no memory error, and `v == 9` is not proved there
/// until the engine decides array terms in a loop (the retired per-lane model
/// proved it for up to 256 lanes).
#[test]
fn a_stack_lane_round_trip_before_a_loop_is_exact() {
    let proved = translate(&stack_lane_round_trip(false, 9), FuncId::new(0));
    assert!(proved.diagnostics.is_empty(), "{:?}", proved.diagnostics);
    assert!(!error_reachable(&proved), "v == 9 is PROVED before the loop");
    let refuted = translate(&stack_lane_round_trip(false, 5), FuncId::new(0));
    assert!(refuted.diagnostics.is_empty(), "{:?}", refuted.diagnostics);
    assert!(error_reachable(&refuted), "v == 5 is REFUTED before the loop");

    let in_loop = translate(&stack_lane_round_trip(true, 9), FuncId::new(0));
    assert!(in_loop.diagnostics.is_empty(), "an in-bounds owned access: {:?}", in_loop.diagnostics);
    assert!(error_reachable(&in_loop), "inside the loop the lane read is a fresh value");
}

// ---------------------------------------------------------------------------
// The junk-lane checker sees every term
// ---------------------------------------------------------------------------

/// `vc_equates_array_terms_beyond` walks body constraints, body relation
/// arguments and head arguments; it admits a definitional lane equality of a
/// listed fresh lane variable exactly once per lane, and nothing else.
#[test]
fn the_array_equality_checker_sees_every_term_of_every_rule() {
    use trust_mc_core::chc::{RelationApp, RelationDecl, Rule, RuleBody};
    let sort = lifted_sort(ay_bindings::Sort::bitvec(8), 1);
    let zeros = Expr::const_array(array_index_sort(), Expr::bitvec_const(0u64, 8));
    let with_rule = |rule: Rule| {
        let mut vc = ChcVc::new();
        let _ = vc.declare_var("a".to_string(), sort.clone());
        vc.add_relation(RelationDecl::new("p", vec![ay_bindings::Sort::bool()]));
        vc.add_relation(RelationDecl::nullary("error"));
        vc.add_rule(rule);
        vc
    };
    let arr_v = Expr::var("a".to_string(), sort.clone());
    let equal = arr_v.clone().eq(zeros.clone());
    // In a head argument and in a body relation argument.
    let in_head = with_rule(Rule::new(
        RuleBody::new(None, vec![]),
        RelationApp::new("p", vec![equal.clone()]),
    ));
    assert!(vc_equates_array_terms(&in_head), "an array equality in a head argument");
    let in_body = with_rule(Rule::new(
        RuleBody::new(Some(RelationApp::new("p", vec![equal])), vec![]),
        RelationApp::nullary("error"),
    ));
    assert!(vc_equates_array_terms(&in_body), "an array equality in a body relation argument");

    // A definitional lane of a listed fresh variable, once: admitted.
    let lanes_sort = lifted_sort(ay_bindings::Sort::bitvec(8), 2);
    let lanes = Expr::var("L".to_string(), lanes_sort.clone());
    let lane = |k: u64| lanes.clone().select(Expr::bitvec_const(k, 64));
    let listed: BTreeSet<String> = ["L".to_string()].into_iter().collect();
    let define = |constraints: Vec<Expr>| {
        let mut vc = ChcVc::new();
        let _ = vc.declare_var("L".to_string(), lanes_sort.clone());
        vc.add_relation(RelationDecl::nullary("error"));
        vc.add_rule(Rule::new(RuleBody::new(None, constraints), RelationApp::nullary("error")));
        vc
    };
    let no_columns = BTreeSet::new();
    let once = define(vec![lane(0).eq(zeros.clone()), lane(1).eq(zeros.clone())]);
    assert!(!vc_equates_array_terms_beyond(&once, &listed, &no_columns), "one definition per lane");
    assert!(vc_equates_array_terms(&once), "not admitted for an unlisted variable");
    let ones = Expr::const_array(array_index_sort(), Expr::bitvec_const(1u64, 8));
    let twice = define(vec![lane(0).eq(zeros.clone()), lane(0).eq(ones.clone())]);
    assert!(vc_equates_array_terms_beyond(&twice, &listed, &no_columns), "a lane defined twice");

    // A large-block definitional variable is defined by ONE unconditional
    // equality, and only its defining term is walked: a second definition — a
    // hypothesis on two array terms — and an array equality inside the
    // defining term are still reported.
    let column_sort = ones.sort().clone();
    let column = Expr::var("bb3_lbe_c0".to_string(), column_sort);
    let columns: BTreeSet<String> = ["bb3_lbe_c0".to_string()].into_iter().collect();
    let s1 = Expr::var("s1".to_string(), Sort::bool());
    let defined =
        define(vec![column.clone().eq(Expr::ite(s1.clone(), zeros.clone(), ones.clone()))]);
    assert!(!vc_equates_array_terms_beyond(&defined, &BTreeSet::new(), &columns));
    assert!(vc_equates_array_terms(&defined), "not admitted for an unlisted column");
    let redefined = define(vec![
        column.clone().eq(Expr::ite(s1.clone(), zeros.clone(), ones.clone())),
        column.clone().eq(zeros.clone()),
    ]);
    assert!(
        vc_equates_array_terms_beyond(&redefined, &BTreeSet::new(), &columns),
        "a definitional variable defined twice"
    );
    let nested = define(vec![column.eq(Expr::ite(zeros.clone().eq(ones.clone()), zeros, ones))]);
    assert!(
        vc_equates_array_terms_beyond(&nested, &BTreeSet::new(), &columns),
        "an array equality inside a column's defining term"
    );
}

// ---------------------------------------------------------------------------
// An element read inside a summarized callee
// ---------------------------------------------------------------------------

/// `f(i) { a = [7; 4]; _ = g(a, i) }` with `g(a, i) = a[i]` summarized into `f`'s
/// CHC: the callee's out-of-bounds read reaches `f`'s `error` — as its index's
/// declared type reads it — exactly where it is out of bounds, and the read is
/// the exact lane (`g(a, i) == x` is proved under the guard). Before TMC-1 the
/// summary read a fresh value with no bounds condition, so an unguarded call
/// left `f` safe.
#[test]
fn a_summarized_callee_read_carries_its_bounds_obligation() {
    // `guard` is `None` (no guard), `Some((signed_lower, upper))`: `assume(i <
    // upper)` (signed for a signed index), and also `assume(0 <= i)` when
    // `signed_lower`.
    let probe = |index_ty: Ty, guard: Option<(bool, i128)>, assert_lane: bool| {
        let mut mb = ModuleBuilder::new("summarized_read");
        let u32_id = mb.add_type(Ty::U32);
        let arr = Ty::Array(u32_id, 4);
        let caller_ty = mb.add_func_type(vec![index_ty.clone(), Ty::U32], vec![]);
        let callee_ty = mb.add_func_type(vec![arr.clone(), index_ty.clone()], vec![Ty::U32]);
        {
            let mut fb = mb.function("f", caller_ty);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let i = fb.add_block_param(entry, index_ty.clone());
            let x = fb.add_block_param(entry, Ty::U32);
            if let Some((signed_lower, upper)) = guard {
                let bound = fb.iconst(index_ty.clone(), upper);
                let op = if index_ty.is_signed() { ICmpOp::Slt } else { ICmpOp::Ult };
                let below = fb.icmp(op, index_ty.clone(), i, bound);
                fb.assume(below);
                if signed_lower {
                    let zero = fb.iconst(index_ty.clone(), 0);
                    let non_negative = fb.icmp(ICmpOp::Sge, index_ty.clone(), i, zero);
                    fb.assume(non_negative);
                }
            }
            let a = fb.array_splat(arr.clone(), x);
            let read = fb.call(FuncId::new(1), vec![a, i]);
            if assert_lane {
                let same = fb.icmp(ICmpOp::Eq, Ty::U32, read, x);
                fb.assert(same);
            }
            fb.ret(vec![]);
            fb.build();
        }
        {
            let mut fb = mb.function("g", callee_ty);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let a = fb.add_block_param(entry, arr);
            let i = fb.add_block_param(entry, index_ty);
            let read = fb.extract_element(Ty::U32, a, i);
            fb.ret(vec![read]);
            fb.build();
        }
        let output =
            translate(&mb.build().expect("ModuleBuilder::build: test fixture"), FuncId::new(0));
        assert!(
            output.diagnostics.is_empty(),
            "the call is summarized, not refused: {:?}",
            output.diagnostics
        );
        error_reachable(&output)
    };
    assert!(probe(Ty::U64, None, false), "an unguarded callee read can be out of bounds");
    assert!(!probe(Ty::U64, Some((false, 4)), false), "under i < 4 it cannot");
    assert!(probe(Ty::U64, Some((false, 5)), false), "under i < 5 it can (i = 4)");
    assert!(probe(Ty::I8, Some((false, 4)), false), "a negative i8 is out of bounds");
    assert!(!probe(Ty::I8, Some((true, 4)), false), "0 <= i8 < 4 is in bounds");
    assert!(!probe(Ty::U64, Some((false, 4)), true), "the read is the exact lane: g(a, i) == x");
}

/// A caller `f(i: u64, x: u32)` that reads `g(splat(x), i)` with `g(a, i) = a[i]`
/// over `[u32; 4]`, optionally under `assume(i < 4)`, optionally asserting that the
/// read is `x`; translated with `options`.
fn summarized_read_of_a_splat(
    guarded: bool,
    assert_lane: bool,
    options: &TranslateOptions,
) -> ChcTranslationOutput {
    let mut mb = ModuleBuilder::new("summarized_read_of_a_splat");
    let u32_id = mb.add_type(Ty::U32);
    let arr = Ty::Array(u32_id, 4);
    let caller_ty = mb.add_func_type(vec![Ty::U64, Ty::U32], vec![]);
    let callee_ty = mb.add_func_type(vec![arr.clone(), Ty::U64], vec![Ty::U32]);
    {
        let mut fb = mb.function("f", caller_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let i = fb.add_block_param(entry, Ty::U64);
        let x = fb.add_block_param(entry, Ty::U32);
        if guarded {
            let four = fb.iconst(Ty::U64, 4);
            let below = fb.icmp(ICmpOp::Ult, Ty::U64, i, four);
            fb.assume(below);
        }
        let a = fb.array_splat(arr.clone(), x);
        let read = fb.call(FuncId::new(1), vec![a, i]);
        if assert_lane {
            let same = fb.icmp(ICmpOp::Eq, Ty::U32, read, x);
            fb.assert(same);
        }
        fb.ret(vec![]);
        fb.build();
    }
    {
        let mut fb = mb.function("g", callee_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let a = fb.add_block_param(entry, arr);
        let i = fb.add_block_param(entry, Ty::U64);
        let read = fb.extract_element(Ty::U32, a, i);
        fb.ret(vec![read]);
        fb.build();
    }
    let output = translate_with(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        FuncId::new(0),
        options,
    );
    assert!(output.diagnostics.is_empty(), "summarized: {:?}", output.diagnostics);
    output
}

/// With memory checks OFF a summarized callee's read states no rule, as
/// `discharge_element_bounds` states none in a block, and outside the bounds it
/// is a fresh value, never a modeled lane: the two models of one read agree in
/// every lane, not only the proof-grade one (TMC-1 review).
#[test]
fn a_summarized_callee_read_honors_unchecked_memory_bounds() {
    assert!(
        error_reachable(&summarized_read_of_a_splat(false, false, &TranslateOptions::default())),
        "checked: an unguarded read can be out of bounds"
    );
    assert!(
        !error_reachable(&summarized_read_of_a_splat(false, false, &unchecked())),
        "unchecked: the read itself states no rule"
    );
    assert!(
        error_reachable(&summarized_read_of_a_splat(false, true, &unchecked())),
        "unchecked: outside the bounds the value is fresh, so `g(a, i) == x` can fail"
    );
    assert!(
        !error_reachable(&summarized_read_of_a_splat(true, true, &unchecked())),
        "unchecked: inside the bounds it is the exact lane"
    );
}

/// The summary takes the selected lane only when its sort is EXACTLY the result
/// type's — the bar `translate_extract_element` sets — never a width-normalized
/// one: `g` reads a `u32` lane as `u8` (trust-ir's validator lets a refinement on
/// either side through), so the read is a fresh `u8`, not the lane truncated, and
/// `g(splat(zext x), i) == x` is not provable (TMC-1 review).
#[test]
fn a_summarized_read_of_a_mismatched_element_is_a_fresh_value() {
    let mut mb = ModuleBuilder::new("summarized_mismatched_read");
    let u32_id = mb.add_type(Ty::U32);
    let arr = Ty::Array(u32_id, 4);
    let caller_ty = mb.add_func_type(vec![Ty::U64, Ty::U8], vec![]);
    let callee_ty = mb.add_func_type(vec![arr.clone(), Ty::U64], vec![Ty::U8]);
    {
        let mut fb = mb.function("f", caller_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let i = fb.add_block_param(entry, Ty::U64);
        let x = fb.add_block_param(entry, Ty::U8);
        let four = fb.iconst(Ty::U64, 4);
        let below = fb.icmp(ICmpOp::Ult, Ty::U64, i, four);
        fb.assume(below);
        let wide = fb.cast(trust_ir::inst::CastOp::ZExt, Ty::U8, Ty::U32, x);
        let a = fb.array_splat(arr.clone(), wide);
        let read = fb.call(FuncId::new(1), vec![a, i]);
        let same = fb.icmp(ICmpOp::Eq, Ty::U8, read, x);
        fb.assert(same);
        fb.ret(vec![]);
        fb.build();
    }
    {
        let mut fb = mb.function("g", callee_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let a = fb.add_block_param(entry, arr);
        let i = fb.add_block_param(entry, Ty::U64);
        let read = fb.extract_element(Ty::U8, a, i);
        fb.ret(vec![read]);
        fb.build();
    }
    let output =
        translate(&mb.build().expect("ModuleBuilder::build: test fixture"), FuncId::new(0));
    assert!(output.diagnostics.is_empty(), "summarized: {:?}", output.diagnostics);
    assert!(error_reachable(&output), "a fresh u8, not the truncated lane");
}

/// The summary interpreter does not narrow its path by a read's in-bounds
/// condition, so `n` reads in one callee block add a constant amount to the CHC
/// each: the expression DAG grows LINEARLY in `n` (the TMC-1 review measured the
/// narrowed form at 1,424 / 5,349 / 20,699 edges for n = 50 / 100 / 200 — one
/// flat conjunction per later obligation, copying every earlier condition). The
/// growth per read is checked to be exactly constant.
#[test]
fn reads_in_a_summarized_callee_grow_the_chc_linearly() {
    let edges = |n: usize| {
        let mut mb = ModuleBuilder::new("summarized_reads");
        let u32_id = mb.add_type(Ty::U32);
        let arr = Ty::Array(u32_id, 4);
        let caller_ty = mb.add_func_type(vec![Ty::U64, Ty::U32], vec![]);
        let callee_ty = mb.add_func_type(vec![arr.clone(), Ty::U64], vec![Ty::U32]);
        {
            let mut fb = mb.function("f", caller_ty);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let i = fb.add_block_param(entry, Ty::U64);
            let x = fb.add_block_param(entry, Ty::U32);
            let a = fb.array_splat(arr.clone(), x);
            let _ = fb.call(FuncId::new(1), vec![a, i]);
            fb.ret(vec![]);
            fb.build();
        }
        {
            let mut fb = mb.function("g", callee_ty);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let a = fb.add_block_param(entry, arr);
            let i = fb.add_block_param(entry, Ty::U64);
            let mut last = None;
            for _ in 0..n {
                last = Some(fb.extract_element(Ty::U32, a, i));
            }
            fb.ret(vec![last.expect("n > 0")]);
            fb.build();
        }
        let output =
            translate(&mb.build().expect("ModuleBuilder::build: test fixture"), FuncId::new(0));
        assert!(output.diagnostics.is_empty(), "n = {n}: summarized: {:?}", output.diagnostics);
        let mut seen: BTreeSet<*const ay_bindings::ExprValue> = BTreeSet::new();
        let mut stack: Vec<&Expr> = Vec::new();
        for rule in &output.vc.rules {
            stack.extend(rule.body.constraints.iter());
            if let Some(app) = &rule.body.relation {
                stack.extend(app.args.iter());
            }
            stack.extend(rule.head.args.iter());
        }
        let mut edges = 0usize;
        while let Some(expr) = stack.pop() {
            if seen.insert(std::ptr::from_ref(expr.value())) {
                let children: Vec<&Expr> = expr.children().collect();
                edges += children.len();
                stack.extend(children);
            }
        }
        edges
    };
    let measured: Vec<usize> = [4, 8, 12, 16].into_iter().map(edges).collect();
    let steps: Vec<usize> = measured.windows(2).map(|pair| pair[1] - pair[0]).collect();
    assert!(steps.iter().all(|step| *step == steps[0]), "edges {measured:?}: steps {steps:?}");
}

/// A summarized callee's element operand types are gathered ONCE per translation,
/// however many call sites reach it (`ChcTranslationWork::callee_operand_type_passes`):
/// the work is linear in the distinct callees' sizes, not in the call sites
/// (TMC-1 review).
#[test]
fn a_callees_element_operand_types_are_gathered_once_per_translation() {
    let passes = |call_sites: usize, second_reader: bool| {
        let mut mb = ModuleBuilder::new("operand_type_passes");
        let u32_id = mb.add_type(Ty::U32);
        let arr = Ty::Array(u32_id, 4);
        let caller_ty = mb.add_func_type(vec![Ty::U64, Ty::U32], vec![]);
        let callee_ty = mb.add_func_type(vec![arr.clone(), Ty::U64], vec![Ty::U32]);
        {
            let mut fb = mb.function("f", caller_ty);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let i = fb.add_block_param(entry, Ty::U64);
            let x = fb.add_block_param(entry, Ty::U32);
            let four = fb.iconst(Ty::U64, 4);
            let below = fb.icmp(ICmpOp::Ult, Ty::U64, i, four);
            fb.assume(below);
            let a = fb.array_splat(arr.clone(), x);
            for _ in 0..call_sites {
                let _ = fb.call(FuncId::new(1), vec![a, i]);
            }
            if second_reader {
                let _ = fb.call(FuncId::new(2), vec![a, i]);
            }
            fb.ret(vec![]);
            fb.build();
        }
        for name in ["g", "h"] {
            let mut fb = mb.function(name, callee_ty);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let a = fb.add_block_param(entry, arr.clone());
            let i = fb.add_block_param(entry, Ty::U64);
            let read = fb.extract_element(Ty::U32, a, i);
            fb.ret(vec![read]);
            fb.build();
        }
        let output =
            translate(&mb.build().expect("ModuleBuilder::build: test fixture"), FuncId::new(0));
        assert!(output.diagnostics.is_empty(), "summarized: {:?}", output.diagnostics);
        output.work.callee_operand_type_passes
    };
    assert_eq!(passes(1, false), 1);
    assert_eq!(passes(5, false), 1, "five call sites of one reader: one pass");
    assert_eq!(passes(5, true), 2, "two distinct readers: one pass each");
}

/// A SIMD vector's read states the bounds rule of its lane count — the same rule
/// the summary interpreter states for it — though its lanes are not modeled
/// (trust-ir makes an out-of-bounds vector read undefined behaviour, as an
/// array's); a read whose length is unknown (a sequence) fails closed with memory
/// checks on (`UnmodeledElementLength`) instead of being an unconstrained value
/// with no obligation (TMC-1 review).
#[test]
fn a_vector_read_is_bounded_and_a_read_of_unknown_length_fails_closed() {
    let vector_read = |guarded: bool, options: &TranslateOptions| {
        let mut mb = ModuleBuilder::new("vector_read");
        let vector = Ty::Vector(Box::new(Ty::U32), 4);
        let ft = mb.add_func_type(vec![vector.clone(), Ty::U32], vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let v = fb.add_block_param(entry, vector);
        let i = fb.add_block_param(entry, Ty::U32);
        if guarded {
            let four = fb.iconst(Ty::U32, 4);
            let below = fb.icmp(ICmpOp::Ult, Ty::U32, i, four);
            fb.assume(below);
        }
        let _ = fb.extract_element(Ty::U32, v, i);
        fb.ret(vec![]);
        fb.build();
        translate_with(
            &mb.build().expect("ModuleBuilder::build: test fixture"),
            FuncId::new(0),
            options,
        )
    };
    let checked = TranslateOptions::default();
    assert!(error_reachable(&vector_read(false, &checked)), "lane 4 and past are out of bounds");
    assert!(!error_reachable(&vector_read(true, &checked)), "below 4 is in bounds");
    assert!(!error_reachable(&vector_read(false, &unchecked())), "no rule when unchecked");

    let sequence_read = |options: &TranslateOptions| {
        let mut mb = ModuleBuilder::new("sequence_read");
        let u8_id = mb.add_type(Ty::U8);
        let seq = Ty::Sequence(u8_id);
        let ft = mb.add_func_type(vec![seq.clone(), Ty::U64], vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let s = fb.add_block_param(entry, seq);
        let i = fb.add_block_param(entry, Ty::U64);
        let _ = fb.extract_element(Ty::U8, s, i);
        fb.ret(vec![]);
        fb.build();
        translate_with(
            &mb.build().expect("ModuleBuilder::build: test fixture"),
            FuncId::new(0),
            options,
        )
    };
    let reasons = |output: &ChcTranslationOutput| {
        output.diagnostics.iter().map(|diagnostic| diagnostic.reason).collect::<Vec<_>>()
    };
    assert!(
        reasons(&sequence_read(&checked))
            .contains(&TrustIrChcUnsupportedReason::UnmodeledElementLength),
        "checked: the read fails closed"
    );
    assert!(
        !reasons(&sequence_read(&unchecked()))
            .contains(&TrustIrChcUnsupportedReason::UnmodeledElementLength),
        "unchecked: no rule"
    );
}

// ---------------------------------------------------------------------------
// The proof-authority gate's view of array element reads (TMC-1)
// ---------------------------------------------------------------------------

/// `ProofGradeElementReads` admits a read exactly when the translator reads
/// SMT-array lanes under the access's own bounds obligation, and names every
/// other case — including the two that validated IR never reaches (an operand
/// with no declared type), which it refuses rather than assumes away.
#[test]
fn the_gate_view_admits_exactly_the_smt_modeled_reads() {
    use trust_ir::value::ValueId;

    let mut mb = ModuleBuilder::new("gate_view");
    let u8_id = mb.add_type(Ty::U8);
    let u32_id = mb.add_type(Ty::U32);
    let seq = Ty::Sequence(u8_id);
    let seq_id = mb.add_type(seq.clone());
    let row = Ty::Array(u8_id, 3);
    let row_id = mb.add_type(row.clone());
    // (label, operand type, element type, index type, expected kind or None)
    let straight: Vec<(&str, Ty, Ty, Ty, Option<&str>)> = vec![
        ("[u32; 4] by u32", Ty::Array(u32_id, 4), Ty::U32, Ty::U32, None),
        ("[u8; 4097] by i8", Ty::Array(u8_id, 4097), Ty::U8, Ty::I8, None),
        ("[[u8; 3]; 5] by u128", Ty::Array(row_id, 5), row, Ty::U128, None),
        ("<4 x u32>", Ty::Vector(Box::new(Ty::U32), 4), Ty::U32, Ty::U32, Some("not_an_smt_array")),
        ("Seq<u8>", seq.clone(), Ty::U8, Ty::U64, Some("not_an_smt_array")),
        ("[u32; 0]", Ty::Array(u32_id, 0), Ty::U32, Ty::U32, Some("not_an_smt_array")),
        ("[Seq<u8>; 4]", Ty::Array(seq_id, 4), seq, Ty::U64, Some("not_an_smt_array")),
        ("a Bool index", Ty::Array(u32_id, 4), Ty::U32, Ty::Bool, Some("unmodeled_index")),
        // A result that is not the element type (the validator lets a refinement on
        // either side through; the translator reads any mismatch as a fresh value).
        (
            "[u32; 4] read as u8",
            Ty::Array(u32_id, 4),
            Ty::U8,
            Ty::U32,
            Some("element_type_mismatch"),
        ),
    ];
    let mut reads = Vec::new();
    for (index, (label, operand_ty, element_ty, index_ty, expected)) in
        straight.into_iter().enumerate()
    {
        let ft = mb.add_func_type(vec![operand_ty.clone(), index_ty.clone()], vec![]);
        let mut fb = mb.function(format!("f{index}"), ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let operand = fb.add_block_param(entry, operand_ty);
        let at = fb.add_block_param(entry, index_ty);
        let _ = fb.extract_element(element_ty.clone(), operand, at);
        fb.ret(vec![]);
        fb.build();
        reads.push((label, FuncId::new(index as u32), entry, element_ty, operand, at, expected));
    }
    // Operands no block parameter or typed result defines (malformed IR).
    let ft = mb.add_func_type(vec![Ty::Array(u32_id, 4), Ty::U32], vec![]);
    let mut fb = mb.function("untyped", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let operand = fb.add_block_param(entry, Ty::Array(u32_id, 4));
    let at = fb.add_block_param(entry, Ty::U32);
    let ghost = ValueId::new(9_000);
    let _ = fb.extract_element(Ty::U32, ghost, at);
    let _ = fb.extract_element(Ty::U32, operand, ValueId::new(9_001));
    fb.ret(vec![]);
    let untyped = fb.build();
    reads.push(("an untyped array", untyped, entry, Ty::U32, ghost, at, Some("untyped_array")));
    reads.push((
        "an untyped index",
        untyped,
        entry,
        Ty::U32,
        operand,
        ValueId::new(9_001),
        Some("unmodeled_index"),
    ));
    // Before, in and after a loop: `head <-> body`, `head -> exit`.
    let ft = mb.add_func_type(vec![Ty::Array(u32_id, 4), Ty::U64], vec![]);
    let mut fb = mb.function("looped", ft);
    let entry = fb.create_block();
    let head = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let operand = fb.add_block_param(entry, Ty::Array(u32_id, 4));
    let at = fb.add_block_param(entry, Ty::U64);
    let _ = fb.extract_element(Ty::U32, operand, at);
    fb.br(head, vec![]);
    fb.switch_to_block(head);
    let go = fb.bool_const(true);
    fb.condbr(go, body, vec![], exit, vec![]);
    fb.switch_to_block(body);
    let _ = fb.extract_element(Ty::U32, operand, at);
    fb.br(head, vec![]);
    fb.switch_to_block(exit);
    let _ = fb.extract_element(Ty::U32, operand, at);
    fb.ret(vec![]);
    let looped = fb.build();
    reads.push(("before the loop", looped, entry, Ty::U32, operand, at, None));
    reads.push(("in the loop", looped, body, Ty::U32, operand, at, Some("shape_only_array")));
    reads.push(("after the loop", looped, exit, Ty::U32, operand, at, Some("shape_only_array")));

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    for (label, function, block, result_ty, array, index, expected) in reads {
        let function = module.function_by_id(function).expect("declared");
        let mut view = ProofGradeElementReads::new(&module, function);
        let got = view.rejection(block, &result_ty, array, index);
        assert_eq!(got.as_ref().map(ExtractElementReject::kind), expected, "{label}: {got:?}");
        // The shape decision is memoized per array type: asking again agrees.
        assert_eq!(view.rejection(block, &result_ty, array, index), got, "{label}");
    }
}

/// A summarized callee's read runs in the CALLER's call-site block
/// (`try_direct_call_summary`), so the gate refuses a call that would fold a read
/// into a block a cycle reaches — where the caller carries arrays shape-only and the
/// read would be a fresh value — and admits the same call before the loop, and a
/// call in the loop of a callee that reads nothing. "Reads" is transitive along
/// direct calls: a wrapper that only calls a reader is a reader.
#[test]
fn the_gate_view_refuses_a_callee_read_folded_into_a_block_a_cycle_reaches() {
    let mut mb = ModuleBuilder::new("gate_view_calls");
    let u32_id = mb.add_type(Ty::U32);
    let arr = Ty::Array(u32_id, 4);
    let read_ty = mb.add_func_type(vec![arr.clone(), Ty::U64], vec![Ty::U32]);
    let plain_ty = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let caller_ty = mb.add_func_type(vec![arr.clone(), Ty::U64], vec![]);
    let (reader, wrapper, plain) = (FuncId::new(1), FuncId::new(2), FuncId::new(3));
    let (entry, body, exit);
    {
        let mut fb = mb.function("caller", caller_ty);
        entry = fb.create_block();
        let head = fb.create_block();
        body = fb.create_block();
        exit = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let a = fb.add_block_param(entry, arr.clone());
        let k = fb.add_block_param(entry, Ty::U64);
        let _ = fb.call(reader, vec![a, k]);
        fb.br(head, vec![]);
        fb.switch_to_block(head);
        let go = fb.bool_const(true);
        fb.condbr(go, body, vec![], exit, vec![]);
        fb.switch_to_block(body);
        let _ = fb.call(reader, vec![a, k]);
        let _ = fb.call(wrapper, vec![a, k]);
        let _ = fb.call(plain, vec![k]);
        fb.br(head, vec![]);
        fb.switch_to_block(exit);
        fb.ret(vec![]);
        fb.build();
    }
    {
        let mut fb = mb.function("reader", read_ty);
        let block = fb.create_block();
        fb.switch_to_block(block);
        fb.set_entry(block);
        let a = fb.add_block_param(block, arr.clone());
        let k = fb.add_block_param(block, Ty::U64);
        let read = fb.extract_element(Ty::U32, a, k);
        fb.ret(vec![read]);
        fb.build();
    }
    {
        let mut fb = mb.function("wrapper", read_ty);
        let block = fb.create_block();
        fb.switch_to_block(block);
        fb.set_entry(block);
        let a = fb.add_block_param(block, arr.clone());
        let k = fb.add_block_param(block, Ty::U64);
        let read = fb.call(reader, vec![a, k]);
        fb.ret(vec![read]);
        fb.build();
    }
    {
        let mut fb = mb.function("plain", plain_ty);
        let block = fb.create_block();
        fb.switch_to_block(block);
        fb.set_entry(block);
        let k = fb.add_block_param(block, Ty::U64);
        fb.ret(vec![k]);
        fb.build();
    }
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let readers = ElementReadingFunctions::new(&module);
    assert!(readers.reads(reader), "a function with an ExtractElement");
    assert!(readers.reads(wrapper), "a function that calls one");
    assert!(readers.reads(FuncId::new(0)), "the caller too: summarized, it folds its callees");
    assert!(!readers.reads(plain), "a function that reaches no ExtractElement");
    let caller = module.function_by_id(FuncId::new(0)).expect("declared");
    let view = ProofGradeElementReads::new(&module, caller);
    let callee = |id: FuncId| module.function_by_id(id).expect("declared");
    assert_eq!(view.call_rejection(entry, callee(reader), &readers), None, "before the loop");
    for (id, name) in [(reader, "reader"), (wrapper, "wrapper")] {
        assert_eq!(
            view.call_rejection(body, callee(id), &readers),
            Some(ExtractElementReject::ShapeOnlyArrayInCallee { callee: name.to_string() }),
            "{name} in the loop"
        );
    }
    assert_eq!(
        view.call_rejection(body, callee(plain), &readers),
        None,
        "a callee that reads nothing"
    );
    assert_eq!(view.call_rejection(exit, callee(plain), &readers), None);
}
