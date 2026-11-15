// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! trust-ir v50 `Inst::ArraySplat` / `Constant::Splat` — the constant-size
//! uniform array `[v; n]` — in both trust-mc lanes.
//!
//! * CHC: a splat is one constant SMT array per element leaf,
//!   `((as const (Array BV64 S)) v)`, at EVERY length — there is no trackable
//!   bound any more. A lane read (`ExtractElement`, `select`) is PROVED equal to
//!   the operand (`ArraySplat`) or the element's exact encoding (`Splat`) and
//!   refuted against anything else — a havoc could do neither — and the VC's
//!   size does not depend on `n`, checked by comparing small lengths, the old
//!   bound's neighbourhood (256, 257) and `u64::MAX`.
//! * BMC: one opaque value whatever `n` is (this lane has no aggregate value
//!   model), no unsupported VC, and the same VC at every length.
//!
//! Every "huge" fixture uses `n = u64::MAX`. The fixtures themselves are
//! O(1) in `n` (one element, one length); a regression that sized anything by
//! `n` would fail at once on a capacity overflow rather than walk or allocate
//! toward it.

use ay_bindings::Expr;
use trust_ir::inst::{BinOp, ICmpOp, Inst};
use trust_ir::value::{FuncId, ValueId};
use trust_ir::{Constant, Ty};
use trust_ir_build::ModuleBuilder;
use trust_mc_core::bmc::BmcVc;
use trust_mc_core::decl::Decl;
use trust_mc_core::violation::PropertyKind;
use trust_mc_trust_bmc::{
    ChcTranslationOutput, SemanticsFamily, TranslateOptions, TrustIrChcUnsupportedReason,
    family_for_inst, stack_alloca_pointer_is_non_escaping,
    trust_ir_function_to_chc_translation_output,
    trust_ir_function_to_chc_translation_output_per_block, trust_ir_to_bmc_vc,
};

/// The largest length a `Ty::Array` can carry.
const HUGE: u64 = u64::MAX;
/// The smallest length past the retired N-field model's per-dimension bound
/// (`[T; N <= 256]`); nothing in the SMT-array model treats it specially.
const PAST_THE_OLD_BOUND: u64 = 257;

// ---------------------------------------------------------------------------
// Helpers (in-process AY, as tests/ws3_20_bit_ops_and_bulk_memory.rs)
// ---------------------------------------------------------------------------

fn sat(decls: &[Decl], extra_vars: &[(String, ay_bindings::Sort)], constraints: &[Expr]) -> bool {
    let mut program = ay_bindings::AYProgram::new();
    program.set_logic("QF_ABV");
    for (name, sort) in extra_vars {
        let _ = program.declare_const(name.clone(), sort.clone());
    }
    for decl in decls {
        if let Decl::Const { name, sort } = decl {
            let _ = program.declare_const(name.clone(), sort.clone());
        }
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

/// Is any `error` rule's body satisfiable? Every fixture that asks is a single
/// block with an unconstrained entry, so this is the obligation's reachability.
fn chc_error_reachable(output: &ChcTranslationOutput) -> bool {
    let vars: Vec<(String, ay_bindings::Sort)> =
        output.vc.vars().iter().map(|var| (var.name.to_string(), var.sort.clone())).collect();
    let error_rules: Vec<_> =
        output.vc.rules.iter().filter(|rule| rule.head.name == "error").collect();
    assert!(!error_rules.is_empty(), "the assert must emit an error rule");
    error_rules.iter().any(|rule| {
        let constraints: Vec<Expr> = rule.body.constraints.iter().cloned().collect();
        sat(&output.vc.decls, &vars, &constraints)
    })
}

fn chc_reasons(output: &ChcTranslationOutput) -> Vec<TrustIrChcUnsupportedReason> {
    output.diagnostics.iter().map(|d| d.reason).collect()
}

fn chc(module: &trust_ir::Module) -> ChcTranslationOutput {
    trust_ir_function_to_chc_translation_output(
        module,
        FuncId::new(0),
        &TranslateOptions::default(),
    )
    .expect("fixture function translates")
}

/// `chc` in the per-block encoding: one relation per block, for the tests that
/// read a block's relation (in production an acyclic function is one
/// large-block query over the entry's relation alone).
fn chc_per_block(module: &trust_ir::Module) -> ChcTranslationOutput {
    trust_ir_function_to_chc_translation_output_per_block(
        module,
        FuncId::new(0),
        &TranslateOptions::default(),
    )
    .expect("fixture function translates")
}

fn only_bmc_vc(module: &trust_ir::Module) -> BmcVc {
    let mut vcs = trust_ir_to_bmc_vc(module, &TranslateOptions::default());
    assert_eq!(vcs.len(), 1, "fixture has one function");
    vcs.remove(0)
}

fn bmc_unsupported(vc: &BmcVc) -> Vec<String> {
    vc.violations
        .iter()
        .filter(|v| v.kind == PropertyKind::Other)
        .filter_map(|v| v.message.clone())
        .filter(|m| m.contains("unsupported trust_ir semantics"))
        .collect()
}

/// The size of a CHC translation: what a length-dependent model would grow.
fn chc_shape(output: &ChcTranslationOutput) -> (usize, usize, usize, Vec<usize>) {
    (
        output.vc.vars().len(),
        output.vc.decls.len(),
        output.vc.rules.len(),
        output.vc.relations.iter().map(|rel| rel.arity()).collect(),
    )
}

fn relation_arity(output: &ChcTranslationOutput, block: u32) -> usize {
    let name = format!("bb{block}");
    output
        .vc
        .relations
        .iter()
        .find(|rel| rel.name == name)
        .expect("the block relation is declared")
        .arity()
}

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

/// How the uniform array is spelled.
#[derive(Clone, Copy, Debug)]
enum Spelling {
    /// `a = array_splat [u32 x n] %x` over the parameter `x`.
    Register,
    /// `a = const [u32 x n] splat(7)`; the probe compares with `7`.
    Constant,
}

const ELEMENT: i128 = 7;

/// What the probe asserts about lane `lane`.
#[derive(Clone, Copy, Debug)]
enum Claim {
    /// `a[lane] == element` (the parameter `x`, or the constant 7).
    IsTheElement,
    /// `a[lane] == element ^ 1` — false on every execution.
    IsNotTheElement,
    /// `a[0] == a[lane]` — every lane is the same value.
    EqualsLaneZero,
}

/// `f(x: u32) { a = [element; n]; assert(<claim about a[lane]>) }`, reading the
/// lane with `ExtractElement` at a constant index.
fn lane_probe(spelling: Spelling, n: u64, lane: u64, claim: Claim) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("array_splat_lane_probe");
    let u32_id = mb.add_type(Ty::U32);
    let arr = Ty::Array(u32_id, n);
    let ft = mb.add_func_type(vec![Ty::U32], vec![]);
    let mut fb = mb.function("probe", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let x = fb.add_block_param(entry, Ty::U32);
    let (a, element) = match spelling {
        Spelling::Register => (fb.array_splat(arr, x), x),
        Spelling::Constant => {
            let a = fb.const_value(arr, Constant::splat(Constant::Int(ELEMENT), n));
            (a, fb.iconst(Ty::U32, ELEMENT))
        }
    };
    let lane = fb.iconst(Ty::U64, i128::from(lane));
    let read = fb.extract_element(Ty::U32, a, lane);
    let cond = match claim {
        Claim::IsTheElement => fb.icmp(ICmpOp::Eq, Ty::U32, read, element),
        Claim::IsNotTheElement => {
            // `x ^ 1` differs from `x` on every execution and, unlike `x + 1`,
            // carries no overflow obligation of its own.
            let one = fb.iconst(Ty::U32, 1);
            let flipped = fb.binop(BinOp::BXor, Ty::U32, element, one);
            fb.icmp(ICmpOp::Eq, Ty::U32, read, flipped)
        }
        Claim::EqualsLaneZero => {
            let zero = fb.iconst(Ty::U64, 0);
            let first = fb.extract_element(Ty::U32, a, zero);
            fb.icmp(ICmpOp::Eq, Ty::U32, first, read)
        }
    };
    fb.assert(cond);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `f(x: u32) { a = [element; n]; _ = a[0] }` with an `ExtractElement` read —
/// the shape whose cost must not depend on `n`.
fn opaque_probe(spelling: Spelling, n: u64) -> trust_ir::Module {
    opaque_probe_at(spelling, n, 0)
}

fn opaque_probe_at(spelling: Spelling, n: u64, index: i128) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("array_splat_opaque_probe");
    let u32_id = mb.add_type(Ty::U32);
    let arr = Ty::Array(u32_id, n);
    let ft = mb.add_func_type(vec![Ty::U32], vec![]);
    let mut fb = mb.function("probe", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let x = fb.add_block_param(entry, Ty::U32);
    let a = match spelling {
        Spelling::Register => fb.array_splat(arr, x),
        Spelling::Constant => fb.const_value(arr, Constant::splat(Constant::Int(ELEMENT), n)),
    };
    let index = fb.iconst(Ty::U64, index);
    let _read = fb.extract_element(Ty::U32, a, index);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

// ---------------------------------------------------------------------------
// CHC: a splat is exact at every length
// ---------------------------------------------------------------------------

#[test]
fn every_lane_of_a_splat_is_proved_to_be_the_element_at_every_length() {
    for spelling in [Spelling::Register, Spelling::Constant] {
        // A register splat of one lane is canonical (`[x; 1]`); a constant splat
        // starts at two lanes (one lane is the list `array[ c ]`).
        let lens: &[u64] = match spelling {
            Spelling::Register => &[1, 2, 4, 256, PAST_THE_OLD_BOUND, HUGE],
            Spelling::Constant => &[2, 4, 256, PAST_THE_OLD_BOUND, HUGE],
        };
        for &n in lens {
            // The last lane, or — for a length past 2^63, which no non-ZST Rust
            // array can have — a lane far past every old bound whose top bit is
            // clear (an index with its top bit set is read as out of bounds under
            // either signedness; `array_lane_access`).
            for lane in [0, (n - 1).min(u64::from(u32::MAX))] {
                let what = format!("{spelling:?} [u32; {n}] lane {lane}");
                let proved = chc(&lane_probe(spelling, n, lane, Claim::IsTheElement));
                assert!(proved.diagnostics.is_empty(), "{what}: {:?}", chc_reasons(&proved));
                assert!(!chc_error_reachable(&proved), "{what}: a[lane] == v must be PROVED");

                let same = chc(&lane_probe(spelling, n, lane, Claim::EqualsLaneZero));
                assert!(same.diagnostics.is_empty(), "{what}: {:?}", chc_reasons(&same));
                assert!(!chc_error_reachable(&same), "{what}: a[0] == a[lane] must be PROVED");

                // Non-vacuity: the lane is the element, not an unconstrained value
                // the solver happens to satisfy, and not a value the model invents.
                let refuted = chc(&lane_probe(spelling, n, lane, Claim::IsNotTheElement));
                assert!(refuted.diagnostics.is_empty(), "{what}: {:?}", chc_reasons(&refuted));
                assert!(chc_error_reachable(&refuted), "{what}: a[lane] == v ^ 1 must be REFUTED");
            }
        }
    }
}

/// `[[9u8; 3]; 2]` spelled as a nested constant splat: the inner splat is the
/// outer one's element — one leaf of sort `(Array BV64 (Array BV64 BV8))` — and
/// both levels are read lane-exactly.
#[test]
fn a_nested_constant_splat_is_exact_at_every_level() {
    let probe = |expected: i128| {
        let mut mb = ModuleBuilder::new("nested_splat");
        let u8_id = mb.add_type(Ty::U8);
        let row_id = mb.add_type(Ty::Array(u8_id, 3));
        let grid = Ty::Array(row_id, 2);
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("nested", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let a = fb.const_value(grid, Constant::splat(Constant::splat(Constant::Int(9), 3), 2));
        let one = fb.iconst(Ty::U64, 1);
        let row = fb.extract_element(Ty::Array(u8_id, 3), a, one);
        let two = fb.iconst(Ty::U64, 2);
        let cell = fb.extract_element(Ty::U8, row, two);
        let want = fb.iconst(Ty::U8, expected);
        let cond = fb.icmp(ICmpOp::Eq, Ty::U8, cell, want);
        fb.assert(cond);
        fb.ret(vec![]);
        fb.build();
        chc(&mb.build().expect("ModuleBuilder::build: test fixture"))
    };
    let proved = probe(9);
    assert!(proved.diagnostics.is_empty(), "{:?}", chc_reasons(&proved));
    assert!(!chc_error_reachable(&proved), "grid[1][2] == 9 must be PROVED");
    let refuted = probe(8);
    assert!(chc_error_reachable(&refuted), "grid[1][2] == 8 must be REFUTED");
}

/// A splat followed by an element write: the written lane is the new value, the
/// others keep the splatted one.
#[test]
fn an_element_write_after_a_splat_changes_only_its_lane() {
    let probe = |lane: u64, expect_written: bool| {
        let mut mb = ModuleBuilder::new("splat_then_insert");
        let u32_id = mb.add_type(Ty::U32);
        let arr = Ty::Array(u32_id, 4);
        let ft = mb.add_func_type(vec![Ty::U32, Ty::U32], vec![]);
        let mut fb = mb.function("splat_then_insert", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let x = fb.add_block_param(entry, Ty::U32);
        let y = fb.add_block_param(entry, Ty::U32);
        let a = fb.array_splat(arr.clone(), x);
        let two = fb.iconst(Ty::I64, 2);
        let b = fb.insert_element(arr, a, two, y);
        let lane = fb.iconst(Ty::I64, i128::from(lane));
        let read = fb.extract_element(Ty::U32, b, lane);
        let want = if expect_written { y } else { x };
        let cond = fb.icmp(ICmpOp::Eq, Ty::U32, read, want);
        fb.assert(cond);
        fb.ret(vec![]);
        fb.build();
        chc(&mb.build().expect("ModuleBuilder::build: test fixture"))
    };
    for (lane, written) in [(2, true), (1, false), (3, false), (0, false)] {
        let out = probe(lane, written);
        assert!(out.diagnostics.is_empty(), "lane {lane}: {:?}", chc_reasons(&out));
        assert!(!chc_error_reachable(&out), "lane {lane} must be PROVED");
    }
    // Non-vacuity: the written lane is NOT the old value in general (x != y).
    let stale = probe(2, false);
    assert!(chc_error_reachable(&stale), "lane 2 == x must be REFUTED after the write");
}

/// A splat used in a successor block is threaded as ONE column per element leaf
/// — a single `(Array BV64 BV32)` here — at every length, and the successor's
/// read is still proved from it.
#[test]
fn a_cross_block_splat_threads_one_column_whatever_its_length() {
    let probe = |n: u64| {
        let mut mb = ModuleBuilder::new("splat_cross_block");
        let u32_id = mb.add_type(Ty::U32);
        let arr = Ty::Array(u32_id, n);
        let ft = mb.add_func_type(vec![Ty::U32], vec![]);
        let mut fb = mb.function("cross_block", ft);
        let entry = fb.create_block();
        let next = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let x = fb.add_block_param(entry, Ty::U32);
        let a = fb.array_splat(arr, x);
        fb.br(next, vec![]);
        fb.switch_to_block(next);
        let zero = fb.iconst(Ty::U64, 0);
        let read = fb.extract_element(Ty::U32, a, zero);
        let cond = fb.icmp(ICmpOp::Eq, Ty::U32, read, x);
        fb.assert(cond);
        fb.ret(vec![]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        (chc(&module), chc_per_block(&module))
    };
    let (four, four_per_block) = probe(4);
    // `x` (entry param) and `a` (one SMT array) are what block 1 carries.
    assert_eq!(relation_arity(&four_per_block, 1), 2, "x plus one array column");
    for n in [5, PAST_THE_OLD_BOUND, HUGE] {
        let (out, per_block) = probe(n);
        assert_eq!(chc_shape(&out), chc_shape(&four), "n = {n}: the VC must not depend on n");
        assert_eq!(
            chc_shape(&per_block),
            chc_shape(&four_per_block),
            "n = {n}: the per-block VC must not depend on n"
        );
        assert!(out.diagnostics.is_empty(), "n = {n}: {:?}", chc_reasons(&out));
    }
}

// ---------------------------------------------------------------------------
// CHC + BMC: a splat costs the same at every length
// ---------------------------------------------------------------------------

#[test]
fn a_splat_costs_the_same_at_every_length() {
    for spelling in [Spelling::Register, Spelling::Constant] {
        for n in [2, PAST_THE_OLD_BOUND, HUGE] {
            let errors = trust_ir_build::validate_module(&opaque_probe(spelling, n));
            assert!(errors.is_empty(), "positive cost input must be valid: {errors:?}");
        }
        let bound = chc(&opaque_probe(spelling, PAST_THE_OLD_BOUND));
        let huge = chc(&opaque_probe(spelling, HUGE));
        for (n, out) in [(PAST_THE_OLD_BOUND, &bound), (HUGE, &huge)] {
            assert!(
                out.diagnostics.is_empty(),
                "{spelling:?} n={n}: a splat is pure and total, never an error rule: {:?}",
                chc_reasons(out)
            );
        }
        assert_eq!(chc_shape(&bound), chc_shape(&huge), "{spelling:?}: CHC size depends on n");

        let bmc_bound = only_bmc_vc(&opaque_probe(spelling, PAST_THE_OLD_BOUND));
        let bmc_huge = only_bmc_vc(&opaque_probe(spelling, HUGE));
        let bmc_small = only_bmc_vc(&opaque_probe(spelling, 2));
        for vc in [&bmc_small, &bmc_bound, &bmc_huge] {
            // The ExtractElement read is refused by name; the splat itself is not.
            let unsupported = bmc_unsupported(vc);
            assert!(
                unsupported.iter().all(|m| m.contains("aggregate extraction")),
                "{spelling:?}: only the element read is unmodeled in BMC: {unsupported:?}"
            );
        }
        let bmc_shape = |vc: &BmcVc| (vc.decls.len(), vc.constraints.len(), vc.violations.len());
        assert_eq!(bmc_shape(&bmc_small), bmc_shape(&bmc_huge), "{spelling:?}: BMC depends on n");
        assert_eq!(bmc_shape(&bmc_bound), bmc_shape(&bmc_huge), "{spelling:?}: BMC depends on n");
    }
}

#[test]
fn original_out_of_bounds_small_splat_is_an_input_refusal() {
    for spelling in [Spelling::Register, Spelling::Constant] {
        // Retain the original small comparison input, whose read at 256 lies
        // outside its two-element array. It cannot be a cost-equivalence oracle.
        let original = opaque_probe_at(spelling, 2, 256);
        assert!(!trust_ir_build::validate_module(&original).is_empty());
        let output = chc(&original);
        assert!(output.module_input_refusal.is_some());
        assert!(output.diagnostics.is_empty());
        assert!(chc_error_reachable(&output));
        let vc = only_bmc_vc(&original);
        assert!(vc.decls.is_empty());
        assert!(vc.constraints.is_empty());
        assert_eq!(vc.violations.len(), 1);
        assert_eq!(vc.violations[0].kind, PropertyKind::Other);
        assert_eq!(vc.violations[0].message, output.module_input_refusal);
        assert_eq!(vc.violations[0].condition, Expr::true_());
    }
}

/// BMC has no aggregate value model: the splat is one fresh value, with no
/// unsupported VC of its own.
#[test]
fn bmc_binds_a_register_splat_without_an_unsupported_vc() {
    let mut mb = ModuleBuilder::new("bmc_splat");
    let u32_id = mb.add_type(Ty::U32);
    let ft = mb.add_func_type(vec![Ty::U32], vec![]);
    let mut fb = mb.function("bmc_splat", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let x = fb.add_block_param(entry, Ty::U32);
    let _a = fb.array_splat(Ty::Array(u32_id, HUGE), x);
    let _c = fb.const_value(Ty::Array(u32_id, HUGE), Constant::splat(Constant::Int(ELEMENT), HUGE));
    fb.ret(vec![]);
    fb.build();
    let vc = only_bmc_vc(&mb.build().expect("ModuleBuilder::build: test fixture"));
    assert!(bmc_unsupported(&vc).is_empty(), "{:?}", bmc_unsupported(&vc));
    assert!(
        vc.decls
            .iter()
            .any(|d| matches!(d, Decl::Const { name, .. } if name.starts_with("array_splat_"))),
        "the register splat is bound to a fresh value"
    );
}

// ---------------------------------------------------------------------------
// Operands, escapes, coverage
// ---------------------------------------------------------------------------

/// A pointer splatted into an array has left its cell: the stack-cell
/// analyses must see the use and refuse to keep the cell precise.
#[test]
fn a_splatted_cell_pointer_escapes() {
    let mut mb = ModuleBuilder::new("splat_escape");
    let ptr_id = mb.add_type(Ty::Ptr);
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("splat_escape", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let cell = fb.alloca(Ty::U32);
    let zero = fb.iconst(Ty::U32, 0);
    fb.store(Ty::U32, cell, zero);
    let _pointers = fb.array_splat(Ty::Array(ptr_id, 2), cell);
    fb.ret(vec![]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let function = module.function_by_id(FuncId::new(0)).expect("declared");
    assert!(
        !stack_alloca_pointer_is_non_escaping(function, cell),
        "a pointer copied into every lane of an array escapes its cell"
    );
}

#[test]
fn coverage_places_the_uniform_array_with_the_aggregates() {
    let splat =
        Inst::ArraySplat { ty: Ty::Array(trust_ir::TyId::new(0), HUGE), value: ValueId::new(0) };
    assert_eq!(family_for_inst(&splat), SemanticsFamily::Aggregates);
    let constant = Inst::Const {
        ty: Ty::Array(trust_ir::TyId::new(0), HUGE),
        value: Constant::splat(Constant::Int(0), HUGE),
    };
    assert_eq!(family_for_inst(&constant), SemanticsFamily::Aggregates);
}
