// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! trust-ir WS3.20 (F-057) constructs in both trust-mc lanes.
//!
//! * `BinOp::RotL` / `BinOp::RotR` on integers are TOTAL (the amount is reduced
//!   modulo the width) and are encoded EXACTLY — checked here against Rust's own
//!   `rotate_left` / `rotate_right`, which is the semantics trust-ir names, on a
//!   grid that includes a zero amount, the full width and amounts past it; plus
//!   the symbolic round-trip `rotr(rotl(x, n), n) == x` proved at every width.
//! * `BinOp::FCopySign` and the bit intrinsics `UnOp::{CtLz, CtTz, BSwap,
//!   BitReverse}` have no exact model here and fail CLOSED, by name, in both lanes.
//! * `Inst::MemCopy` / `Inst::MemSet` (dynamic byte count) never drop their write.
//!   Through a pointer with no exact place, a tracked cell the destination could
//!   reach is havocked and the instruction fails closed by name (BMC always; CHC
//!   whenever memory bounds are checked). The invalidation tests are built so
//!   that a DROPPED write would fold the obligation to a constant PROVE — each has
//!   a control showing that it does. A write of one whole stack cell is exact in
//!   BMC (here); the CHC lane's exact model is pinned in
//!   `src/translate_chc_bulk_memory_tests.rs`.

use ay_bindings::Expr;
use trust_ir::inst::{BinOp, ICmpOp, Inst, UnOp};
use trust_ir::value::FuncId;
use trust_ir::{Constant, FieldDef, StructDef, StructRepr, Ty};
use trust_ir_build::ModuleBuilder;
use trust_mc_core::bmc::BmcVc;
use trust_mc_core::chc::ChcVc;
use trust_mc_core::chc_const_prop::eval::try_eval_to_bool;
use trust_mc_core::decl::Decl;
use trust_mc_core::violation::{PropertyKind, Violation};
use trust_mc_trust_bmc::{
    ChcTranslationOutput, SemanticsFamily, SemanticsStatus, TranslateOptions,
    TrustIrChcUnsupportedReason, coverage_for_family, family_for_inst,
    trust_ir_function_to_chc_translation_output, trust_ir_to_bmc_vc,
};

// ---------------------------------------------------------------------------
// Solving helpers (in-process AY)
// ---------------------------------------------------------------------------

fn sat(decls: &[Decl], extra_vars: &[(String, ay_bindings::Sort)], constraints: &[Expr]) -> bool {
    let mut program = ay_bindings::AYProgram::new();
    program.set_logic("QF_BV");
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

/// Is `violation` reachable in the BMC VC `vc` (constraints ∧ condition SAT)?
fn bmc_violation_reachable(vc: &BmcVc, violation: &Violation) -> bool {
    let mut constraints = vc.constraints.clone();
    constraints.push(violation.condition.clone());
    sat(&vc.decls, &[], &constraints)
}

fn bmc_unsupported(vc: &BmcVc) -> Vec<String> {
    vc.violations
        .iter()
        .filter(|v| v.kind == PropertyKind::Other)
        .filter_map(|v| v.message.clone())
        .filter(|m| m.contains("unsupported trust_ir semantics"))
        .collect()
}

fn bmc_assertions(vc: &BmcVc) -> Vec<&Violation> {
    vc.violations.iter().filter(|v| v.kind == PropertyKind::Assertion).collect()
}

/// Is any `error` rule's body satisfiable? The fixtures are single-block with an
/// unconstrained entry, so this is the reachability of the obligation.
fn chc_error_reachable(output: &ChcTranslationOutput) -> bool {
    let vars: Vec<(String, ay_bindings::Sort)> =
        output.vc.vars().iter().map(|var| (var.name.to_string(), var.sort.clone())).collect();
    output.vc.rules.iter().filter(|rule| rule.head.name == "error").any(|rule| {
        let constraints: Vec<Expr> = rule.body.constraints.iter().cloned().collect();
        sat(&output.vc.decls, &vars, &constraints)
    })
}

fn chc_reasons(output: &ChcTranslationOutput) -> Vec<TrustIrChcUnsupportedReason> {
    output.diagnostics.iter().map(|d| d.reason).collect()
}

/// Constant-fold the `error` rules: `Some(true)` reachable on a constant path,
/// `Some(false)` every error path folds to false (PROVED), `None` a constraint
/// stayed symbolic (havoc — the solver decides; sound, never a false proof).
fn chc_error_folds(vc: &ChcVc) -> Option<bool> {
    let mut any_reachable = false;
    let mut saw_error_rule = false;
    for rule in &vc.rules {
        if rule.head.name.as_str() != "error" {
            continue;
        }
        saw_error_rule = true;
        let mut conjunction = Some(true);
        for constraint in rule.body.constraints.iter() {
            match try_eval_to_bool(constraint) {
                Some(true) => {}
                Some(false) => {
                    conjunction = Some(false);
                    break;
                }
                None => conjunction = None,
            }
        }
        match conjunction {
            Some(true) => any_reachable = true,
            Some(false) => {}
            None => return None,
        }
    }
    assert!(saw_error_rule, "the assert must emit an error rule");
    Some(any_reachable)
}

fn chc(module: &trust_ir::Module, func: u32, options: &TranslateOptions) -> ChcTranslationOutput {
    trust_ir_function_to_chc_translation_output(module, FuncId::new(func), options)
        .expect("fixture function translates")
}

fn only_bmc_vc(module: &trust_ir::Module) -> BmcVc {
    let mut vcs = trust_ir_to_bmc_vc(module, &TranslateOptions::default());
    assert_eq!(vcs.len(), 1, "fixture has one function");
    vcs.remove(0)
}

// ---------------------------------------------------------------------------
// Rotates
// ---------------------------------------------------------------------------

/// `f(x, n) { assert(rotr(rotl(x, n), n) == x) }` at `ty`.
fn rotate_round_trip_module(ty: &Ty) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("rotate_round_trip");
    let ft = mb.add_func_type(vec![ty.clone(), ty.clone()], vec![]);
    let mut fb = mb.function("round_trip", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let x = fb.add_block_param(entry, ty.clone());
    let n = fb.add_block_param(entry, ty.clone());
    let left = fb.binop(BinOp::RotL, ty.clone(), x, n);
    let back = fb.binop(BinOp::RotR, ty.clone(), left, n);
    let same = fb.icmp(ICmpOp::Eq, ty.clone(), back, x);
    fb.assert(same);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `f() { assert(rot(x, n) == expected) }` over constants.
fn rotate_constant_module(
    ty: &Ty,
    op: BinOp,
    x: u128,
    n: u128,
    expected: u128,
) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("rotate_constant");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("rotate_constant", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let x = fb.uconst(ty.clone(), x);
    let n = fb.uconst(ty.clone(), n);
    let expected = fb.uconst(ty.clone(), expected);
    let rotated = fb.binop(op, ty.clone(), x, n);
    let same = fb.icmp(ICmpOp::Eq, ty.clone(), rotated, expected);
    fb.assert(same);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Proved in BMC (assertion unreachable, nothing unsupported) and in CHC (no
/// diagnostics, error unreachable).
fn assert_proved_in_both_lanes(module: &trust_ir::Module, what: &str) {
    let vc = only_bmc_vc(module);
    assert!(
        bmc_unsupported(&vc).is_empty(),
        "{what}: BMC must model it: {:?}",
        bmc_unsupported(&vc)
    );
    let assertions = bmc_assertions(&vc);
    assert_eq!(assertions.len(), 1, "{what}: one assertion VC");
    assert!(!bmc_violation_reachable(&vc, assertions[0]), "{what}: BMC must PROVE it");

    let out = chc(module, 0, &TranslateOptions::default());
    assert!(out.diagnostics.is_empty(), "{what}: CHC must model it: {:?}", chc_reasons(&out));
    assert!(!chc_error_reachable(&out), "{what}: CHC must PROVE it");
}

/// Refuted in both lanes — the non-vacuity half of every exactness check.
fn assert_refuted_in_both_lanes(module: &trust_ir::Module, what: &str) {
    let vc = only_bmc_vc(module);
    let assertions = bmc_assertions(&vc);
    assert_eq!(assertions.len(), 1, "{what}: one assertion VC");
    assert!(bmc_violation_reachable(&vc, assertions[0]), "{what}: BMC must REFUTE it");
    let out = chc(module, 0, &TranslateOptions::default());
    assert!(chc_error_reachable(&out), "{what}: CHC must REFUTE it");
}

/// Symbolic in both operands, so this is a solver proof over every `(x, n)` — kept
/// to the widths whose shifter circuits bit-blast quickly; 64 and 128 bits are
/// covered exactly by the constant grid below.
#[test]
fn rotate_round_trip_is_proved_symbolically() {
    for ty in [Ty::U8, Ty::U16, Ty::U32, Ty::I8, Ty::I32] {
        assert_proved_in_both_lanes(&rotate_round_trip_module(&ty), &format!("round trip at {ty}"));
    }
}

/// A rotate that is NOT the identity must not be provable as one — the round-trip
/// proof above is not an artifact of a havoc that happens to be unconstrained.
#[test]
fn rotate_is_not_the_identity() {
    let mut mb = ModuleBuilder::new("rotate_not_identity");
    let ft = mb.add_func_type(vec![Ty::U32, Ty::U32], vec![]);
    let mut fb = mb.function("not_identity", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let x = fb.add_block_param(entry, Ty::U32);
    let n = fb.add_block_param(entry, Ty::U32);
    let rotated = fb.binop(BinOp::RotL, Ty::U32, x, n);
    let same = fb.icmp(ICmpOp::Eq, Ty::U32, rotated, x);
    fb.assert(same);
    fb.ret(vec![]);
    fb.build();
    assert_refuted_in_both_lanes(
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        "rotl(x, n) == x",
    );
}

/// Exactness against Rust's `rotate_left` / `rotate_right` (the semantics trust-ir
/// defines `rotl` / `rotr` by) — amounts 0, 1, w-1, w, w+1, past 2w, and an amount
/// with the high bit set, at u8, u32, u64 and u128.
#[test]
fn rotate_matches_rust_rotate_on_a_constant_grid() {
    let mut cases: Vec<(Ty, BinOp, u128, u128, u128)> = Vec::new();
    for x in [0x81u8, 0x5a, 0xff, 0x01] {
        for n in [0u8, 1, 7, 8, 9, 19, 0x83] {
            let n32 = u32::from(n);
            cases.push((Ty::U8, BinOp::RotL, x.into(), n.into(), x.rotate_left(n32).into()));
            cases.push((Ty::U8, BinOp::RotR, x.into(), n.into(), x.rotate_right(n32).into()));
        }
    }
    for x in [0x8000_0001u32, 0xdead_beef] {
        for n in [0u32, 1, 31, 32, 33, 67, 0x8000_0005] {
            cases.push((Ty::U32, BinOp::RotL, x.into(), n.into(), x.rotate_left(n).into()));
            cases.push((Ty::U32, BinOp::RotR, x.into(), n.into(), x.rotate_right(n).into()));
        }
    }
    for x in [0x8000_0000_0000_0001u64, 0x0123_4567_89ab_cdef] {
        for n in [0u64, 1, 63, 64, 65, 131] {
            let n32 = u32::try_from(n).expect("small amount");
            cases.push((Ty::U64, BinOp::RotL, x.into(), n.into(), x.rotate_left(n32).into()));
            cases.push((Ty::U64, BinOp::RotR, x.into(), n.into(), x.rotate_right(n32).into()));
        }
    }
    for x in
        [0x8000_0000_0000_0000_0000_0000_0000_0001u128, 0x0123_4567_89ab_cdef_fedc_ba98_7654_3210]
    {
        for n in [0u128, 1, 127, 128, 129, 300, 1 << 127] {
            let k = u32::try_from(n % 128).expect("reduced amount");
            cases.push((Ty::U128, BinOp::RotL, x, n, x.rotate_left(k)));
            cases.push((Ty::U128, BinOp::RotR, x, n, x.rotate_right(k)));
        }
    }
    for (ty, op, x, n, expected) in cases {
        let what = format!("{op:?} {ty} x={x:#x} n={n:#x}");
        assert_proved_in_both_lanes(&rotate_constant_module(&ty, op, x, n, expected), &what);
        // Non-vacuity: the neighbouring value must be refuted.
        assert_refuted_in_both_lanes(
            &rotate_constant_module(&ty, op, x, n, expected ^ 1),
            &format!("{what} (expected ^ 1)"),
        );
    }
}

// ---------------------------------------------------------------------------
// FCopySign and the bit intrinsics: named fail-closed
// ---------------------------------------------------------------------------

#[test]
fn fcopysign_fails_closed_in_both_lanes() {
    for ty in [Ty::U32, Ty::F64] {
        let mut mb = ModuleBuilder::new("fcopysign");
        let ft = mb.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
        let mut fb = mb.function("copysign", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let a = fb.add_block_param(entry, ty.clone());
        let b = fb.add_block_param(entry, ty.clone());
        let r = fb.binop(BinOp::FCopySign, ty.clone(), a, b);
        fb.ret(vec![r]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");

        let vc = only_bmc_vc(&module);
        let out = chc(&module, 0, &TranslateOptions::default());
        if ty == Ty::U32 {
            // Preserve the original ill-typed floating operation. Canonical
            // validation rejects it before either instruction-level model.
            assert!(!trust_ir_build::validate_module(&module).is_empty());
            assert!(out.module_input_refusal.is_some());
            assert!(out.diagnostics.is_empty());
            assert!(vc.decls.is_empty());
            assert!(vc.constraints.is_empty());
            assert_eq!(vc.violations.len(), 1);
            assert_eq!(vc.violations[0].kind, PropertyKind::Other);
            assert_eq!(vc.violations[0].message, out.module_input_refusal);
            assert!(bmc_violation_reachable(&vc, &vc.violations[0]));
            assert!(chc_error_reachable(&out));
            continue;
        }
        assert!(trust_ir_build::validate_module(&module).is_empty());
        assert!(out.module_input_refusal.is_none());
        assert!(
            bmc_unsupported(&vc).iter().any(|m| m.contains("FCopySign")),
            "BMC must refuse FCopySign on {ty} by name: {:?}",
            bmc_unsupported(&vc)
        );
        assert_eq!(
            chc_reasons(&out),
            vec![TrustIrChcUnsupportedReason::FloatingPointArithmetic],
            "CHC must refuse FCopySign on {ty} as floating-point arithmetic"
        );
        assert!(chc_error_reachable(&out), "the refusal must be a reachable error rule");
    }
}

#[test]
fn bit_intrinsics_fail_closed_in_both_lanes() {
    for op in [UnOp::CtLz, UnOp::CtTz, UnOp::BSwap, UnOp::BitReverse] {
        let mut mb = ModuleBuilder::new("bit_intrinsic");
        let ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
        let mut fb = mb.function("bit_intrinsic", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let x = fb.add_block_param(entry, Ty::U32);
        let r = fb.unop(op, Ty::U32, x);
        fb.ret(vec![r]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");

        let vc = only_bmc_vc(&module);
        assert!(
            bmc_unsupported(&vc).iter().any(|m| m.contains("unary operation")),
            "BMC must refuse {op:?}: {:?}",
            bmc_unsupported(&vc)
        );
        let out = chc(&module, 0, &TranslateOptions::default());
        assert_eq!(
            chc_reasons(&out),
            vec![TrustIrChcUnsupportedReason::UnaryOperation],
            "CHC must refuse {op:?} by name"
        );
    }
}

/// The direct-call summary treats the bit intrinsics like `CtPop`: TOTAL, so the
/// callee is summarized with an unconstrained result instead of being declined
/// (declining would model the call as may-panic). Nothing is PROVED from the
/// havocked value: the caller's `result == 7` assertion stays refutable.
#[test]
fn bit_intrinsic_callee_is_summarized_with_an_unconstrained_result() {
    for op in [UnOp::CtPop, UnOp::CtLz, UnOp::CtTz, UnOp::BSwap, UnOp::BitReverse] {
        let mut mb = ModuleBuilder::new("bit_intrinsic_summary");
        let callee_ty = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
        let callee_id = mb.peek_next_func_id().expect("peek_next_func_id: test fixture");
        {
            let mut cb = mb.function("callee", callee_ty);
            let entry = cb.create_block();
            cb.switch_to_block(entry);
            cb.set_entry(entry);
            let x = cb.add_block_param(entry, Ty::U32);
            let r = cb.unop(op, Ty::U32, x);
            cb.ret(vec![r]);
            cb.build();
        }
        let caller_ty = mb.add_func_type(vec![Ty::U32], vec![]);
        let mut fb = mb.function("caller", caller_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let x = fb.add_block_param(entry, Ty::U32);
        let r = fb.call(callee_id, vec![x]);
        let seven = fb.iconst(Ty::U32, 7);
        let is_seven = fb.icmp(ICmpOp::Eq, Ty::U32, r, seven);
        fb.assert(is_seven);
        fb.ret(vec![]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");

        let out = chc(&module, 1, &TranslateOptions::default());
        assert!(
            !chc_reasons(&out).contains(&TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary),
            "a callee using {op:?} must be summarized, not declined: {:?}",
            chc_reasons(&out)
        );
        assert!(chc_error_reachable(&out), "{op:?}: the havocked result must not prove `r == 7`");
    }
}

/// Every `UnOp`. The match is exhaustive (no wildcard), so a new trust-ir
/// variant is a compile error here as well as in both lanes' dispatch.
fn every_unop() -> Vec<UnOp> {
    let all = [
        UnOp::Neg,
        UnOp::FNeg,
        UnOp::FAbs,
        UnOp::FSqrt,
        UnOp::FFloor,
        UnOp::FCeil,
        UnOp::FTrunc,
        UnOp::Not,
        UnOp::CtPop,
        UnOp::CtLz,
        UnOp::CtTz,
        UnOp::BSwap,
        UnOp::BitReverse,
    ];
    for op in all {
        match op {
            UnOp::Neg
            | UnOp::FNeg
            | UnOp::FAbs
            | UnOp::FSqrt
            | UnOp::FFloor
            | UnOp::FCeil
            | UnOp::FTrunc
            | UnOp::Not
            | UnOp::CtPop
            | UnOp::CtLz
            | UnOp::CtTz
            | UnOp::BSwap
            | UnOp::BitReverse => {}
        }
    }
    all.to_vec()
}

/// Each unary op, through both main lanes, against the coverage matrix: an op
/// BOTH lanes refuse must not sit in a family whose row says `Implemented`, and
/// BMC's refusal names the op (its trust-ir text mnemonic). Measured before the
/// fix: `CtPop`/`CtLz`/`CtTz`/`BSwap`/`BitReverse` were filed under
/// `IntegerArithmetic = Implemented`, and every BMC refusal was the anonymous
/// "unary operation". Since e7f622c0a BMC models integer `Neg` and `Not` exactly,
/// as CHC does, so for those two each lane must accept rather than refuse.
#[test]
fn every_unary_op_is_labelled_by_what_the_lanes_actually_do() {
    let mut unnamed_in_bmc = Vec::new();
    let mut bmc_disagrees = Vec::new();
    let mut chc_disagrees = Vec::new();
    let mut labelled_implemented = Vec::new();
    for op in every_unop() {
        let float = matches!(
            op,
            UnOp::FNeg | UnOp::FAbs | UnOp::FSqrt | UnOp::FFloor | UnOp::FCeil | UnOp::FTrunc
        );
        let ty = if float { Ty::F64 } else { Ty::U32 };
        let mut mb = ModuleBuilder::new("unary");
        let ft = mb.add_func_type(vec![ty.clone()], vec![ty.clone()]);
        let mut fb = mb.function("unary", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let x = fb.add_block_param(entry, ty.clone());
        let r = fb.unop(op, ty.clone(), x);
        fb.ret(vec![r]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");

        // BMC models exactly integer `Neg` / `Not` (e7f622c0a), and must refuse
        // every other op by name.
        let named = format!("unary operation {}", format!("{op:?}").to_lowercase());
        let bmc = bmc_unsupported(&only_bmc_vc(&module));
        if matches!(op, UnOp::Neg | UnOp::Not) {
            if !bmc.is_empty() {
                bmc_disagrees.push(format!("{op:?}: {bmc:?}"));
            }
        } else if !bmc.iter().any(|m| m.contains(&named)) {
            unnamed_in_bmc.push(format!("{op:?}: {bmc:?}"));
        }

        // CHC models exactly integer `Neg` / `Not`, and refuses every other op.
        let out = chc(&module, 0, &TranslateOptions::default());
        let chc_refuses = chc_reasons(&out).contains(&TrustIrChcUnsupportedReason::UnaryOperation);
        if chc_refuses == matches!(op, UnOp::Neg | UnOp::Not) {
            chc_disagrees.push(format!("{op:?}: {:?}", chc_reasons(&out)));
        }

        let inst = Inst::UnOp { op, ty, operand: trust_ir::value::ValueId::new(0) };
        let row = coverage_for_family(family_for_inst(&inst));
        if chc_refuses && row.status == SemanticsStatus::Implemented {
            labelled_implemented.push(format!("{op:?} -> {:?}", row.family));
        }
    }
    assert!(
        unnamed_in_bmc.is_empty()
            && bmc_disagrees.is_empty()
            && chc_disagrees.is_empty()
            && labelled_implemented.is_empty(),
        "BMC refusals that do not name the op: {unnamed_in_bmc:#?}\n\
         BMC unary-op modeling changed: {bmc_disagrees:#?}\n\
         CHC unary-op modeling changed: {chc_disagrees:#?}\n\
         refused by both lanes but filed under an Implemented family: {labelled_implemented:#?}"
    );
}

#[test]
fn coverage_families_place_every_new_variant() {
    let v = trust_ir::value::ValueId::new;
    let binop = |op| Inst::BinOp { op, ty: Ty::U32, lhs: v(0), rhs: v(1) };
    let unop = |op| Inst::UnOp { op, ty: Ty::U32, operand: v(0) };
    assert_eq!(family_for_inst(&binop(BinOp::RotL)), SemanticsFamily::IntegerArithmetic);
    assert_eq!(family_for_inst(&binop(BinOp::RotR)), SemanticsFamily::IntegerArithmetic);
    assert_eq!(family_for_inst(&binop(BinOp::FCopySign)), SemanticsFamily::Floats);
    assert_eq!(family_for_inst(&binop(BinOp::FMin)), SemanticsFamily::Floats);
    for op in [UnOp::CtPop, UnOp::CtLz, UnOp::CtTz, UnOp::BSwap, UnOp::BitReverse] {
        assert_eq!(family_for_inst(&unop(op)), SemanticsFamily::BitIntrinsics);
    }
    assert_eq!(family_for_inst(&unop(UnOp::FSqrt)), SemanticsFamily::Floats);
    assert_eq!(
        family_for_inst(&Inst::MemCopy { dst: v(0), src: v(1), bytes: v(2), overlap: false }),
        SemanticsFamily::MemoryProvenance
    );
    assert_eq!(
        family_for_inst(&Inst::MemSet { dst: v(0), byte: v(1), bytes: v(2) }),
        SemanticsFamily::MemoryProvenance
    );
}

// ---------------------------------------------------------------------------
// Bulk memory
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Bulk {
    None,
    MemSet,
    MemCpy,
    MemMove,
}

/// CHC probe. `s = S { a: 1, b: seed }` lives in a tracked stack cell whose
/// interior address has ESCAPED into `sink(&mut s.a)`. After the call `s` is
/// re-stored EXACTLY (so the cell is precise again: `s.a == 1`), then a bulk
/// write goes through a pointer with no provenance — one that may be the
/// escaped address — and `s.a != 0` is asserted.
///
/// A dropped write would read the re-stored `1` back and PROVE the assertion
/// (the control `Bulk::None` shows exactly that fold); a modeled write havocs
/// the cell, so the obligation cannot fold.
fn escaped_cell_probe(bulk: Bulk, options: &TranslateOptions) -> ChcTranslationOutput {
    chc(&escaped_cell_module(bulk, false), 1, options)
}

fn escaped_cell_module(bulk: Bulk, legacy_undef: bool) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("bulk_memory_escape");
    let struct_id = mb.add_struct(StructDef {
        id: trust_ir::value::StructId::new(0),
        name: "bulk_memory_escape::S".to_string(),
        fields: vec![
            FieldDef { name: "a".into(), ty: Ty::U32, offset: Some(0) },
            FieldDef { name: "b".into(), ty: Ty::U32, offset: Some(4) },
        ],
        size: Some(8),
        align: Some(4),
        repr: StructRepr::Rust,
        origin: None,
    });
    let sty = Ty::Struct(struct_id);
    // `sink` returns nothing, so its direct-call summary SUCCEEDS: the call adds
    // no error rule of its own, and the only effect under test is the escape.
    let sink_ty = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let sink_id = mb.peek_next_func_id().expect("peek_next_func_id: test fixture");
    {
        let mut sink = mb.function("sink", sink_ty);
        let entry = sink.create_block();
        sink.switch_to_block(entry);
        sink.set_entry(entry);
        sink.add_block_param(entry, Ty::Ptr);
        sink.ret(vec![]);
        sink.build();
    }

    let params = if legacy_undef { vec![Ty::U32] } else { vec![Ty::U32, Ty::Ptr, Ty::Ptr] };
    let ft = mb.add_func_type(params, vec![Ty::U32]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let seed = fb.add_block_param(entry, Ty::U32);
    let unknown_pointers = (!legacy_undef)
        .then(|| (fb.add_block_param(entry, Ty::Ptr), fb.add_block_param(entry, Ty::Ptr)));

    let one = fb.const_value(Ty::U32, Constant::Int(1));
    let agg1 = if legacy_undef {
        let undef = fb.undef(sty.clone());
        let agg0 = fb.insert_field(sty.clone(), undef, 0, one);
        fb.insert_field(sty.clone(), agg0, 1, seed)
    } else {
        fb.make_aggregate(sty.clone(), vec![one, seed])
    };
    let slot = fb.alloca(sty.clone());
    fb.store(sty.clone(), slot, agg1);

    // `sink(&mut s.a)`: the interior address escapes.
    let lane = fb.const_value(Ty::I64, Constant::Int(0));
    let field_ptr = fb.gep(Ty::U32, slot, vec![lane]);
    let borrow = fb.borrow_mut(field_ptr);
    fb.call_void(sink_id, vec![borrow]);
    // Re-store `s` exactly: the cell is precise again.
    fb.store(sty.clone(), slot, agg1);

    // The bulk write through a pointer with no provenance into `s`.
    // These are alias-model probes, not evidence that null accesses execute.
    // Keep the original null/Undef program separately as a canonical UB control.
    let unknown_dst =
        unknown_pointers.map(|(destination, _)| destination).unwrap_or_else(|| fb.null_ptr());
    let bytes = fb.const_value(Ty::U64, Constant::Int(4));
    match bulk {
        Bulk::None => {}
        Bulk::MemSet => {
            let zero_byte = fb.const_value(Ty::U8, Constant::Int(0));
            fb.memset(unknown_dst, zero_byte, bytes);
        }
        Bulk::MemCpy | Bulk::MemMove => {
            let unknown_src =
                unknown_pointers.map(|(_, source)| source).unwrap_or_else(|| fb.null_ptr());
            fb.memcopy(unknown_dst, unknown_src, bytes, bulk == Bulk::MemMove);
        }
    }

    let reloaded = fb.load(sty.clone(), slot);
    let a = fb.extract_field(Ty::U32, reloaded, 0);
    let zero = fb.const_value(Ty::U32, Constant::Int(0));
    let is_zero = fb.icmp(ICmpOp::Eq, Ty::U32, a, zero);
    let f = fb.const_value(Ty::Bool, Constant::Bool(false));
    let ok = fb.icmp(ICmpOp::Eq, Ty::Bool, is_zero, f);
    fb.assert(ok);
    fb.ret(vec![a]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn original_bulk_probe_aggregate_undef_is_canonical_ub_and_refused() {
    use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
    for bulk in [Bulk::None, Bulk::MemSet, Bulk::MemCpy, Bulk::MemMove] {
        let original = escaped_cell_module(bulk, true);
        let error = Interpreter::with_module(&original)
            .execute_func(FuncId::new(1), [InterpretValue::int(Ty::U32, 7).unwrap()])
            .expect_err("non-scalar Undef fails before the old bulk/null access");
        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior, "{bulk:?}: {error:?}");
        for options in [TranslateOptions::default(), memory_bounds_unchecked()] {
            let output = chc(&original, 1, &options);
            assert!(
                output.diagnostics.iter().any(|diagnostic| diagnostic.reason
                    == TrustIrChcUnsupportedReason::OperandConsumption)
            );
            assert_ne!(chc_error_folds(&output.vc), Some(false));
        }
    }
}

fn memory_bounds_unchecked() -> TranslateOptions {
    TranslateOptions { check_memory_bounds: false, ..TranslateOptions::default() }
}

/// The control: with no bulk write the re-stored cell is precise and the
/// obligation folds to PROVED. This is what makes the next test load-bearing.
#[test]
fn escaped_cell_probe_control_is_precise() {
    let out = escaped_cell_probe(Bulk::None, &memory_bounds_unchecked());
    assert!(out.diagnostics.is_empty(), "control must translate cleanly: {:?}", chc_reasons(&out));
    assert_eq!(chc_error_folds(&out.vc), Some(false), "control: `s.a == 1` must fold to PROVED");
}

/// THE DROPPED-WRITE ORACLE. With memory bounds unchecked there is no fail-closed
/// error rule to hide behind: only the write's own model stands between the
/// re-stored `s.a == 1` and a false PROVE. The bulk write must havoc the cell.
#[test]
fn bulk_write_through_an_unknown_pointer_invalidates_an_escaped_cell() {
    for bulk in [Bulk::MemSet, Bulk::MemCpy, Bulk::MemMove] {
        let out = escaped_cell_probe(bulk, &memory_bounds_unchecked());
        assert!(
            out.diagnostics.is_empty(),
            "{bulk:?}: with memory bounds unchecked the refusal is gated off: {:?}",
            chc_reasons(&out)
        );
        assert_eq!(
            chc_error_folds(&out.vc),
            None,
            "{bulk:?}: the write may land on `s`, so `s.a` must be havocked, never read stale"
        );
    }
}

/// With memory bounds checked (the proof-grade profile) the bulk write also fails
/// closed by name: its range UB has no byte-granular model.
#[test]
fn bulk_write_fails_closed_by_name_when_memory_bounds_are_checked() {
    for bulk in [Bulk::MemSet, Bulk::MemCpy, Bulk::MemMove] {
        let out = escaped_cell_probe(bulk, &TranslateOptions::default());
        let bulk_diagnostics: Vec<_> = out
            .diagnostics
            .iter()
            .filter(|d| d.reason == TrustIrChcUnsupportedReason::BulkMemoryTransfer)
            .collect();
        assert_eq!(bulk_diagnostics.len(), 1, "{bulk:?}: {:?}", chc_reasons(&out));
        assert_eq!(bulk_diagnostics[0].family, SemanticsFamily::MemoryProvenance);
        assert!(chc_error_reachable(&out), "{bulk:?}: the refusal must be a reachable error");
    }
}

/// BMC: `slot: T = 7; <bulk>(slot, .., bytes); assert(*slot == expected)`, with
/// `other: T = 0` as a copy's source. `T` is `u8` or `u16`.
fn bmc_region_probe(bulk: Bulk, ty: Ty, bytes: i128, expected: i128) -> BmcVc {
    let mut mb = ModuleBuilder::new("bmc_bulk_memory");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("bmc_bulk", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let slot = fb.alloca(ty.clone());
    let seven = fb.iconst(ty.clone(), 7);
    fb.store(ty.clone(), slot, seven);
    let count = fb.const_value(Ty::U64, Constant::Int(bytes));
    match bulk {
        Bulk::None => {}
        Bulk::MemSet => {
            let zero = fb.iconst(Ty::U8, 0);
            fb.memset(slot, zero, count);
        }
        Bulk::MemCpy | Bulk::MemMove => {
            let other = fb.alloca(ty.clone());
            let zero = fb.iconst(ty.clone(), 0);
            fb.store(ty.clone(), other, zero);
            fb.memcopy(slot, other, count, bulk == Bulk::MemMove);
        }
    }
    let loaded = fb.load(ty.clone(), slot);
    let want = fb.iconst(ty.clone(), expected);
    let holds = fb.icmp(ICmpOp::Eq, ty, loaded, want);
    fb.assert(holds);
    fb.ret(vec![]);
    fb.build();
    only_bmc_vc(&mb.build().expect("ModuleBuilder::build: test fixture"))
}

fn bmc_assertion_proved(vc: &BmcVc) -> bool {
    let assertions = bmc_assertions(vc);
    assert_eq!(assertions.len(), 1);
    !bmc_violation_reachable(vc, assertions[0])
}

fn bmc_reachable(vc: &BmcVc, kind: PropertyKind) -> bool {
    vc.violations.iter().filter(|v| v.kind == kind).any(|v| bmc_violation_reachable(vc, v))
}

/// A write of exactly one whole single-cell `Alloca` is exact in the typed array
/// model: the element the copy reads, or the fill byte repeated. No fail-closed
/// VC, and the assertion is decided by the written value alone.
#[test]
fn bmc_whole_cell_bulk_writes_are_exact() {
    let control = bmc_region_probe(Bulk::None, Ty::U8, 1, 7);
    assert!(bmc_unsupported(&control).is_empty(), "control: {:?}", bmc_unsupported(&control));
    assert!(bmc_assertion_proved(&control), "control: the stored 7 is read back exactly");

    for bulk in [Bulk::MemSet, Bulk::MemCpy, Bulk::MemMove] {
        let wrote = bmc_region_probe(bulk, Ty::U8, 1, 0);
        assert!(bmc_unsupported(&wrote).is_empty(), "{bulk:?}: {:?}", bmc_unsupported(&wrote));
        assert!(bmc_assertion_proved(&wrote), "{bulk:?}: the cell holds the written 0");
        let stale = bmc_region_probe(bulk, Ty::U8, 1, 7);
        assert!(!bmc_assertion_proved(&stale), "{bulk:?}: the pre-write 7 is gone");
        let none = bmc_region_probe(bulk, Ty::U8, 0, 7);
        assert!(bmc_unsupported(&none).is_empty(), "{bulk:?}: zero bytes is a no-op");
        assert!(bmc_assertion_proved(&none), "{bulk:?}: zero bytes keeps the 7");
    }
    // A `u16` fill writes the byte into both of its bytes.
    let mut mb = ModuleBuilder::new("bmc_fill_u16");
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("bmc_fill", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let slot = fb.alloca(Ty::U16);
    let byte = fb.iconst(Ty::U8, 0xA5);
    let count = fb.const_value(Ty::U64, Constant::Int(2));
    fb.memset(slot, byte, count);
    let loaded = fb.load(Ty::U16, slot);
    let want = fb.iconst(Ty::U16, 0xA5A5);
    let holds = fb.icmp(ICmpOp::Eq, Ty::U16, loaded, want);
    fb.assert(holds);
    fb.ret(vec![]);
    fb.build();
    let vc = only_bmc_vc(&mb.build().expect("ModuleBuilder::build: test fixture"));
    assert!(bmc_unsupported(&vc).is_empty(), "{:?}", bmc_unsupported(&vc));
    assert!(bmc_assertion_proved(&vc), "memset(u16, 0xA5, 2) == 0xA5A5");
}

/// Undefined behaviour is a genuine violation, not a fail-closed one: past the
/// cell is out of bounds, and a `memcpy` of a cell onto itself overlaps (a
/// `memmove` of it is the identity).
#[test]
fn bmc_bulk_overrun_and_overlap_are_undefined_behaviour() {
    for bulk in [Bulk::MemSet, Bulk::MemCpy, Bulk::MemMove] {
        let vc = bmc_region_probe(bulk, Ty::U8, 2, 0);
        assert!(bmc_unsupported(&vc).is_empty(), "{bulk:?}: {:?}", bmc_unsupported(&vc));
        assert!(bmc_reachable(&vc, PropertyKind::OutOfBounds), "{bulk:?}: 2 bytes into a u8");
        assert!(!bmc_assertion_proved(&vc), "{bulk:?}: an overrun leaves the cell unknown");
    }
    for overlap in [false, true] {
        let mut mb = ModuleBuilder::new("bmc_onto_itself");
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("bmc_onto_itself", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let slot = fb.alloca(Ty::U32);
        let value = fb.iconst(Ty::U32, 7);
        fb.store(Ty::U32, slot, value);
        let count = fb.const_value(Ty::U64, Constant::Int(4));
        fb.memcopy(slot, slot, count, overlap);
        let loaded = fb.load(Ty::U32, slot);
        let holds = fb.icmp(ICmpOp::Eq, Ty::U32, loaded, value);
        fb.assert(holds);
        fb.ret(vec![]);
        fb.build();
        let vc = only_bmc_vc(&mb.build().expect("ModuleBuilder::build: test fixture"));
        assert!(bmc_unsupported(&vc).is_empty(), "{:?}", bmc_unsupported(&vc));
        assert_eq!(bmc_reachable(&vc, PropertyKind::UndefinedBehavior), !overlap);
        if overlap {
            assert!(bmc_assertion_proved(&vc), "memmove onto itself is the identity");
        }
    }
}

/// A range that is not one whole cell — one byte of a `u16`, or any write
/// through a pointer that is not a single-cell `Alloca` — has no reading in the
/// typed array model: the region is havocked and the instruction fails closed
/// by name.
#[test]
fn bmc_bulk_write_without_an_exact_element_fails_closed_and_havocs_the_region() {
    for (bulk, spelling) in
        [(Bulk::MemSet, "memset"), (Bulk::MemCpy, "memcpy"), (Bulk::MemMove, "memmove")]
    {
        let vc = bmc_region_probe(bulk, Ty::U16, 1, 7);
        let unsupported = bmc_unsupported(&vc);
        assert!(
            unsupported.iter().any(|m| m.contains(spelling) && m.contains("not one whole element")),
            "{bulk:?}: BMC must refuse a partial element by name: {unsupported:?}"
        );
        assert!(!bmc_assertion_proved(&vc), "{bulk:?}: the pre-write element is havocked");
    }

    let mut mb = ModuleBuilder::new("bmc_unknown");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![]);
    let mut fb = mb.function("bmc_unknown", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let unknown = fb.add_block_param(entry, Ty::Ptr);
    let byte = fb.iconst(Ty::U8, 0);
    let count = fb.const_value(Ty::U64, Constant::Int(1));
    fb.memset(unknown, byte, count);
    fb.ret(vec![]);
    fb.build();
    let vc = only_bmc_vc(&mb.build().expect("ModuleBuilder::build: test fixture"));
    let unsupported = bmc_unsupported(&vc);
    assert!(
        unsupported.iter().any(|m| m.contains("memset") && m.contains("dynamic byte count")),
        "an unknown destination keeps the old refusal: {unsupported:?}"
    );
}

/// A symbolic count costs one comparison with the cell's size, whatever it is:
/// pinned to the cell's size the fill is exact, pinned to zero it is a no-op,
/// and only a partial count (fail-closed) or an overrun (out of bounds) fails.
#[test]
fn bmc_symbolic_count_is_exact_where_it_names_the_cell() {
    let probe = |pin: Option<i128>, expected: i128| {
        let mut mb = ModuleBuilder::new("bmc_symbolic_fill");
        let ft = mb.add_func_type(vec![Ty::U64], vec![]);
        let mut fb = mb.function("bmc_symbolic_fill", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let n = fb.add_block_param(entry, Ty::U64);
        if let Some(pin) = pin {
            let k = fb.iconst(Ty::U64, pin);
            let pinned = fb.icmp(ICmpOp::Eq, Ty::U64, n, k);
            fb.assume(pinned);
        }
        let slot = fb.alloca(Ty::U32);
        let seven = fb.iconst(Ty::U32, 7);
        fb.store(Ty::U32, slot, seven);
        let byte = fb.iconst(Ty::U8, 0xAB);
        fb.memset(slot, byte, n);
        let loaded = fb.load(Ty::U32, slot);
        let want = fb.iconst(Ty::U32, expected);
        let holds = fb.icmp(ICmpOp::Eq, Ty::U32, loaded, want);
        fb.assert(holds);
        fb.ret(vec![]);
        fb.build();
        only_bmc_vc(&mb.build().expect("ModuleBuilder::build: test fixture"))
    };
    let filled = probe(Some(4), 0xABAB_ABAB);
    assert!(bmc_assertion_proved(&filled), "n == 4 fills the whole u32");
    assert!(!bmc_reachable(&filled, PropertyKind::Other), "no fail-closed VC fires at n == 4");
    assert!(!bmc_reachable(&filled, PropertyKind::OutOfBounds));
    let untouched = probe(Some(0), 7);
    assert!(bmc_assertion_proved(&untouched), "n == 0 is a no-op");
    for (n, kind) in [(2, PropertyKind::Other), (5, PropertyKind::OutOfBounds)] {
        let vc = probe(Some(n), 0xABAB_ABAB);
        assert!(bmc_reachable(&vc, kind), "n == {n}");
    }
    // The encoding is the same whatever the count is pinned to.
    let shape = |vc: &BmcVc| (vc.decls.len(), vc.violations.len(), vc.constraints.len());
    assert_eq!(shape(&probe(Some(4), 0)), shape(&probe(Some(1 << 40), 0)));
}
