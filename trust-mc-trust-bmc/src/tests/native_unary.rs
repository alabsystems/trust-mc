// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Paired AY checks for native BMC unary values, traps and refusal boundaries.

use super::*;
use trust_mc_core::bmc::BmcVc;

fn one_vc(module: &trust_ir::Module, options: &TranslateOptions) -> BmcVc {
    let mut vcs = trust_ir_to_bmc_vc(module, options);
    assert_eq!(vcs.len(), 1);
    vcs.pop().expect("one function")
}

fn one_valid_vc(module: &trust_ir::Module, options: &TranslateOptions) -> BmcVc {
    let report = trust_ir_build::validate_module_report(module);
    assert!(report.is_ok(), "canonical fixture must validate: {:?}", report.errors());
    one_vc(module, options)
}

fn integer_constant(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    ty: &Ty,
    value: i128,
) -> trust_ir::value::ValueId {
    let width = ty.bit_width_with(64).expect("integer width");
    if ty.is_signed() {
        // Spell the wrapped expected value canonically within the signed range.
        let value = if width == 128 { value } else { (value << (128 - width)) >> (128 - width) };
        fb.iconst(ty.clone(), value)
    } else {
        let mask = if width == 128 { u128::MAX } else { (1u128 << width) - 1 };
        fb.uconst(ty.clone(), (value as u128) & mask)
    }
}

fn assert_value_pair(vc: &BmcVc) {
    let assertions: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::Assertion).collect();
    assert_eq!(assertions.len(), 2);
    assert!(!bmc_violation_is_satisfiable(vc, assertions[0]), "correct unary value must hold");
    assert!(bmc_violation_is_satisfiable(vc, assertions[1]), "wrong unary value must fail");
    assert!(
        vc.violations.iter().all(|v| v.kind != PropertyKind::Other),
        "supported unary operations must not leave an unsupported-semantics obligation"
    );
}

#[test]
fn bmc_unary_canonical_boolean_negation_is_exact_for_both_inputs() {
    let mut mb = ModuleBuilder::new("bool_not");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![]);
    let mut fb = mb.function("bool_not", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let x = fb.add_block_param(entry, Ty::Bool);
    let true_value = fb.bool_const(true);
    let result = fb.binop(BinOp::BXor, Ty::Bool, x, true_value);
    let correct = fb.icmp(ICmpOp::Ne, Ty::Bool, result, x);
    fb.assert(correct);
    let wrong = fb.icmp(ICmpOp::Eq, Ty::Bool, result, x);
    fb.assert(wrong);
    fb.ret(vec![]);
    fb.build();
    let vc = one_valid_vc(&mb.build().expect("bool not fixture"), &TranslateOptions::default());
    assert_value_pair(&vc);
    assert_eq!(vc.violations.len(), 2, "NOT is total, with no overflow obligation");
}

#[test]
fn bmc_unary_integer_not_matches_xor_with_all_ones() {
    for ty in [
        Ty::I8,
        Ty::U8,
        Ty::I16,
        Ty::U16,
        Ty::I32,
        Ty::U32,
        Ty::I64,
        Ty::U64,
        Ty::I128,
        Ty::U128,
        Ty::Isize,
        Ty::Usize,
    ] {
        let mut mb = ModuleBuilder::new("integer_not");
        let ft = mb.add_func_type(vec![ty.clone()], vec![]);
        let mut fb = mb.function("integer_not", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let x = fb.add_block_param(entry, ty.clone());
        let result = fb.unop(UnOp::Not, ty.clone(), x);
        let ones = integer_constant(&mut fb, &ty, -1);
        let expected = fb.binop(BinOp::Xor, ty.clone(), x, ones);
        let correct = fb.icmp(ICmpOp::Eq, ty.clone(), result, expected);
        fb.assert(correct);
        let wrong = fb.icmp(ICmpOp::Ne, ty, result, expected);
        fb.assert(wrong);
        fb.ret(vec![]);
        fb.build();
        let vc =
            one_valid_vc(&mb.build().expect("integer not fixture"), &TranslateOptions::default());
        assert_value_pair(&vc);
        assert_eq!(vc.violations.len(), 2, "integer NOT has no overflow obligation");
    }
}

/// Hold the input at a boundary value, assert the correct and wrong wrapped
/// result separately, and leave the overflow obligation independently solvable.
fn neg_case(
    ty: Ty,
    input: i128,
    expected: i128,
    wrapping: bool,
    options: &TranslateOptions,
) -> BmcVc {
    let mut mb = ModuleBuilder::new("integer_neg");
    let ft = mb.add_func_type(vec![ty.clone()], vec![]);
    let mut fb = mb.function("integer_neg", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let x = fb.add_block_param(entry, ty.clone());
    let input = integer_constant(&mut fb, &ty, input);
    let is_input = fb.icmp(ICmpOp::Eq, ty.clone(), x, input);
    fb.assume(is_input);
    let result = fb.unop(UnOp::Neg, ty.clone(), x);
    if wrapping {
        fb.annotate_last(ProofAnnotation::Wrapping).expect("negation instruction");
    }
    let expected = integer_constant(&mut fb, &ty, expected);
    let correct = fb.icmp(ICmpOp::Eq, ty.clone(), result, expected);
    fb.assert(correct);
    let wrong = fb.icmp(ICmpOp::Ne, ty, result, expected);
    fb.assert(wrong);
    fb.ret(vec![]);
    fb.build();
    one_valid_vc(&mb.build().expect("negation fixture"), options)
}

fn assert_neg_case(vc: &BmcVc, overflow: Option<bool>) {
    assert_value_pair(vc);
    let traps: Vec<_> =
        vc.violations.iter().filter(|v| v.kind == PropertyKind::ArithmeticOverflow).collect();
    match overflow {
        Some(expected) => {
            assert_eq!(traps.len(), 1, "non-wrapping negation carries one trap obligation");
            assert_eq!(bmc_violation_is_satisfiable(vc, traps[0]), expected);
        }
        None => assert!(traps.is_empty(), "wrapping/disabled overflow must suppress only the trap"),
    }
}

#[test]
fn bmc_unary_signed_neg_traps_exactly_at_minimum() {
    for ty in [Ty::I8, Ty::I16, Ty::I32, Ty::I64, Ty::I128, Ty::Isize] {
        let width = ty.bit_width_with(64).expect("integer width");
        let min = if width == 128 { i128::MIN } else { -(1i128 << (width - 1)) };
        let max = if width == 128 { i128::MAX } else { (1i128 << (width - 1)) - 1 };
        for input in [min, min + 1, -1, 0, 1, max] {
            let vc = neg_case(
                ty.clone(),
                input,
                input.wrapping_neg(),
                false,
                &TranslateOptions::default(),
            );
            assert_neg_case(&vc, Some(input == min));
        }
    }
}

#[test]
fn bmc_unary_unsigned_neg_traps_exactly_when_nonzero() {
    for ty in [Ty::U8, Ty::U16, Ty::U32, Ty::U64, Ty::U128, Ty::Usize] {
        let width = ty.bit_width_with(64).expect("integer width");
        let max = if width == 128 { u128::MAX } else { (1u128 << width) - 1 };
        for input in [0, 1, max] {
            let vc = neg_case(
                ty.clone(),
                input as i128,
                input.wrapping_neg() as i128,
                false,
                &TranslateOptions::default(),
            );
            assert_neg_case(&vc, Some(input != 0));
        }
    }
}

#[test]
fn bmc_unary_wrapping_and_overflow_policy_keep_exact_negation_values() {
    for (ty, input, expected) in [(Ty::I8, -128, -128), (Ty::U8, 1, 255)] {
        let wrapping = neg_case(ty.clone(), input, expected, true, &TranslateOptions::default());
        assert_neg_case(&wrapping, None);
        let options = TranslateOptions {
            check_signed_overflow: !ty.is_signed(),
            check_unsigned_overflow: ty.is_signed(),
            ..TranslateOptions::default()
        };
        let disabled = neg_case(ty.clone(), input, expected, false, &options);
        assert_neg_case(&disabled, None);
        let other_signedness_disabled = TranslateOptions {
            check_signed_overflow: ty.is_signed(),
            check_unsigned_overflow: !ty.is_signed(),
            ..TranslateOptions::default()
        };
        let enabled = neg_case(ty, input, expected, false, &other_signedness_disabled);
        assert_neg_case(&enabled, Some(true));
    }
}

#[test]
fn bmc_unary_neg_overflow_is_scoped_to_the_executed_branch() {
    let mut mb = ModuleBuilder::new("guarded_neg");
    let ft = mb.add_func_type(vec![Ty::I8], vec![]);
    let mut fb = mb.function("guarded_neg", ft);
    let entry = fb.create_block();
    let negate = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let x = fb.add_block_param(entry, Ty::I8);
    let min = fb.iconst(Ty::I8, -128);
    let safe = fb.icmp(ICmpOp::Ne, Ty::I8, x, min);
    fb.condbr(safe, negate, vec![], exit, vec![]);
    fb.switch_to_block(negate);
    fb.unop(UnOp::Neg, Ty::I8, x);
    fb.br(exit, vec![]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    let vc = one_valid_vc(&mb.build().expect("guarded neg fixture"), &TranslateOptions::default());
    assert_eq!(vc.violations.len(), 1);
    assert_eq!(vc.violations[0].kind, PropertyKind::ArithmeticOverflow);
    assert!(!bmc_violation_is_satisfiable(&vc, &vc.violations[0]));
    assert!(bmc_condition_is_satisfiable(&vc, Expr::true_()), "guard must not erase all paths");
}

#[test]
fn bmc_unary_float_and_bit_intrinsics_remain_named_refusals() {
    for (op, ty) in [
        (UnOp::FNeg, Ty::F32),
        (UnOp::FAbs, Ty::F32),
        (UnOp::FSqrt, Ty::F32),
        (UnOp::FFloor, Ty::F32),
        (UnOp::FCeil, Ty::F32),
        (UnOp::FTrunc, Ty::F32),
        (UnOp::CtPop, Ty::U32),
        (UnOp::CtLz, Ty::U32),
        (UnOp::CtTz, Ty::U32),
        (UnOp::BSwap, Ty::U32),
        (UnOp::BitReverse, Ty::U32),
    ] {
        let mut mb = ModuleBuilder::new("unsupported_unary");
        let ft = mb.add_func_type(vec![ty.clone()], vec![]);
        let mut fb = mb.function("unsupported_unary", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let x = fb.add_block_param(entry, ty.clone());
        fb.unop(op, ty, x);
        fb.ret(vec![]);
        fb.build();
        let vc =
            one_valid_vc(&mb.build().expect("unsupported fixture"), &TranslateOptions::default());
        assert_eq!(vc.violations.len(), 1);
        let refusal = &vc.violations[0];
        assert_eq!(refusal.kind, PropertyKind::Other);
        assert!(
            refusal
                .message
                .as_deref()
                .expect("refusal reason")
                .contains(&format!("unary operation {}", crate::translate::unop_name(op)))
        );
        assert!(bmc_violation_is_satisfiable(&vc, refusal));
    }
}

#[test]
fn bmc_unary_explicit_integer_width_casts_remain_named_refusals() {
    // Valid IR spells transport width changes as explicit casts. This lane
    // still refuses casts by name; no arbitrary cast result may acquire a
    // favorable unary value/trap judgment merely because the module is valid.
    for (operand_ty, ty, input, expected) in [
        (Ty::I16, Ty::I8, 128, -128),
        (Ty::I16, Ty::I8, 257, -1),
        (Ty::I8, Ty::I16, -128, 128),
        (Ty::U8, Ty::U16, 255, -255),
    ] {
        let mut mb = ModuleBuilder::new("normalized_neg");
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("normalized_neg", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let operand = integer_constant(&mut fb, &operand_ty, input);
        let operand = if operand_ty.bit_width().unwrap() > ty.bit_width().unwrap() {
            fb.trunc(operand_ty, ty.clone(), operand)
        } else if operand_ty.is_signed() {
            fb.sext(operand_ty, ty.clone(), operand)
        } else {
            fb.zext(operand_ty, ty.clone(), operand)
        };
        let result = fb.unop(UnOp::Neg, ty.clone(), operand);
        let expected = integer_constant(&mut fb, &ty, expected);
        let correct = fb.icmp(ICmpOp::Eq, ty.clone(), result, expected);
        fb.assert(correct);
        let wrong = fb.icmp(ICmpOp::Ne, ty, result, expected);
        fb.assert(wrong);
        fb.ret(vec![]);
        fb.build();
        let vc =
            one_valid_vc(&mb.build().expect("normalization fixture"), &TranslateOptions::default());
        let refusals =
            vc.violations.iter().filter(|v| v.kind == PropertyKind::Other).collect::<Vec<_>>();
        assert_eq!(refusals.len(), 1);
        let refusal = refusals[0];
        assert!(refusal.message.as_deref().unwrap().contains("cast operation"));
        assert_eq!(refusal.condition, ay_bindings::Expr::true_());
        assert!(bmc_violation_is_satisfiable(&vc, refusal));
    }
}

#[test]
fn bmc_unary_canonical_invalid_operations_and_widths_refuse_before_translation() {
    // Keep every formerly implicit invalid fixture as an explicit module-input
    // refusal. None may acquire unsupported-operation or unary-value semantics.
    for (op, operand_ty, ty) in [
        (UnOp::Not, Ty::Bool, Ty::Bool),
        (UnOp::Not, Ty::F32, Ty::F32),
        (UnOp::Neg, Ty::F32, Ty::F32),
        (UnOp::Neg, Ty::I16, Ty::I8),
        (UnOp::Neg, Ty::I8, Ty::I16),
        (UnOp::Neg, Ty::U8, Ty::U16),
    ] {
        let mut mb = ModuleBuilder::new("canonically_invalid_unary");
        let ft = mb.add_func_type(vec![operand_ty.clone()], vec![]);
        let mut fb = mb.function("canonically_invalid_unary", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let operand = fb.add_block_param(entry, operand_ty);
        fb.unop(op, ty, operand);
        fb.ret(vec![]);
        fb.build();
        let module = mb.build().expect("invalid unary fixture transport");
        assert!(!trust_ir_build::validate_module(&module).is_empty());
        let vc = one_vc(&module, &TranslateOptions::default());
        assert!(vc.decls.is_empty());
        assert!(vc.constraints.is_empty());
        assert_eq!(vc.violations.len(), 1);
        let refusal = &vc.violations[0];
        assert_eq!(refusal.kind, PropertyKind::Other);
        assert!(refusal.message.as_deref().unwrap().starts_with("invalid trust_ir module"));
        assert!(bmc_violation_is_satisfiable(&vc, refusal));
    }
}

#[test]
fn bmc_unary_incompatible_operand_sorts_fail_closed() {
    for (op, operand_ty, ty) in [
        (UnOp::Not, Ty::Bool, Ty::I8),
        (UnOp::Neg, Ty::Bool, Ty::I8),
        (UnOp::Not, Ty::I8, Ty::Bool),
    ] {
        let mut mb = ModuleBuilder::new("ill_sorted_unary");
        let ft = mb.add_func_type(vec![operand_ty.clone()], vec![]);
        let mut fb = mb.function("ill_sorted_unary", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let operand = fb.add_block_param(entry, operand_ty);
        fb.unop(op, ty, operand);
        fb.ret(vec![]);
        fb.build();
        let vc = one_vc(&mb.build().expect("ill-sorted fixture"), &TranslateOptions::default());
        assert_eq!(vc.violations.len(), 1);
        assert_eq!(vc.violations[0].kind, PropertyKind::Other);
        assert!(bmc_violation_is_satisfiable(&vc, &vc.violations[0]));
    }
}

#[test]
fn bmc_unary_canonical_boolean_connectives_have_exact_truth_tables() {
    for op in [BinOp::BAnd, BinOp::BOr, BinOp::BXor] {
        for (left, right) in [(false, false), (false, true), (true, false), (true, true)] {
            let mut mb = ModuleBuilder::new("canonical_boolean_connectives");
            let ft = mb.add_func_type(vec![Ty::Bool, Ty::Bool], vec![]);
            let mut fb = mb.function("canonical_boolean_connectives", ft);
            let entry = fb.create_block();
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let a = fb.add_block_param(entry, Ty::Bool);
            let b = fb.add_block_param(entry, Ty::Bool);
            let left_value = fb.bool_const(left);
            let right_value = fb.bool_const(right);
            let left_assumption = fb.icmp(ICmpOp::Eq, Ty::Bool, a, left_value);
            fb.assume(left_assumption);
            let right_assumption = fb.icmp(ICmpOp::Eq, Ty::Bool, b, right_value);
            fb.assume(right_assumption);
            let expected = match op {
                BinOp::BAnd => left && right,
                BinOp::BOr => left || right,
                BinOp::BXor => left != right,
                _ => unreachable!("only canonical boolean operators"),
            };
            let expected = fb.bool_const(expected);
            let result = fb.binop(op, Ty::Bool, a, b);
            let correct = fb.icmp(ICmpOp::Eq, Ty::Bool, result, expected);
            fb.assert(correct);
            let wrong = fb.icmp(ICmpOp::Ne, Ty::Bool, result, expected);
            fb.assert(wrong);
            fb.ret(vec![]);
            fb.build();
            let vc =
                one_valid_vc(&mb.build().expect("boolean fixture"), &TranslateOptions::default());
            assert_value_pair(&vc);
            assert_eq!(vc.violations.len(), 2);
        }
    }
}

#[test]
fn bmc_unary_canonical_boolean_connectives_refuse_nonboolean_operands() {
    for op in [BinOp::BAnd, BinOp::BOr, BinOp::BXor] {
        let mut mb = ModuleBuilder::new("ill_sorted_boolean_connective");
        let ft = mb.add_func_type(vec![Ty::I8, Ty::Bool], vec![]);
        let mut fb = mb.function("ill_sorted_boolean_connective", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let a = fb.add_block_param(entry, Ty::I8);
        let b = fb.add_block_param(entry, Ty::Bool);
        fb.binop(op, Ty::Bool, a, b);
        fb.ret(vec![]);
        fb.build();
        let vc =
            one_vc(&mb.build().expect("ill-sorted boolean fixture"), &TranslateOptions::default());
        assert_eq!(vc.violations.len(), 1);
        assert_eq!(vc.violations[0].kind, PropertyKind::Other);
        assert!(bmc_violation_is_satisfiable(&vc, &vc.violations[0]));
    }
}

#[test]
fn bmc_unary_pointer_width_integer_comparisons_are_exact_in_both_lanes() {
    // The unary width matrix exposed a missing comparison classification:
    // Isize/Usize already use exact 64-bit carriers, but ICmp on those types
    // was havocked/refused in both lanes. Keep all equality and ordering
    // operators covered at the sign boundary, including both verdicts.
    for ty in [Ty::Isize, Ty::Usize] {
        for (left, right) in [
            (-1, 0),
            (0, 1),
            (i128::from(i64::MIN), i128::from(i64::MAX)),
            (i128::from(i64::MAX), i128::from(i64::MIN)),
            (0, 0),
        ] {
            for op in [
                ICmpOp::Eq,
                ICmpOp::Ne,
                ICmpOp::Ult,
                ICmpOp::Ule,
                ICmpOp::Ugt,
                ICmpOp::Uge,
                ICmpOp::Slt,
                ICmpOp::Sle,
                ICmpOp::Sgt,
                ICmpOp::Sge,
            ] {
                let expected = match op {
                    ICmpOp::Eq => left as u64 == right as u64,
                    ICmpOp::Ne => left as u64 != right as u64,
                    ICmpOp::Ult => (left as u64) < right as u64,
                    ICmpOp::Ule => (left as u64) <= right as u64,
                    ICmpOp::Ugt => (left as u64) > right as u64,
                    ICmpOp::Uge => (left as u64) >= right as u64,
                    ICmpOp::Slt => (left as i64) < right as i64,
                    ICmpOp::Sle => (left as i64) <= right as i64,
                    ICmpOp::Sgt => (left as i64) > right as i64,
                    ICmpOp::Sge => (left as i64) >= right as i64,
                };
                for wrong in [false, true] {
                    let mut mb = ModuleBuilder::new("pointer_width_comparison");
                    let ft = mb.add_func_type(vec![], vec![]);
                    let mut fb = mb.function("pointer_width_comparison", ft);
                    let entry = fb.create_block();
                    fb.switch_to_block(entry);
                    fb.set_entry(entry);
                    let left = integer_constant(&mut fb, &ty, left);
                    let right = integer_constant(&mut fb, &ty, right);
                    let comparison = fb.icmp(op, ty.clone(), left, right);
                    let expected = fb.bool_const(expected != wrong);
                    let assertion = fb.icmp(ICmpOp::Eq, Ty::Bool, comparison, expected);
                    fb.assert(assertion);
                    fb.ret(vec![]);
                    fb.build();
                    let module = mb.build().expect("pointer-width comparison fixture");
                    let vc = one_valid_vc(&module, &TranslateOptions::default());
                    assert_eq!(vc.violations.len(), 1);
                    assert_eq!(vc.violations[0].kind, PropertyKind::Assertion);
                    assert_eq!(bmc_violation_is_satisfiable(&vc, &vc.violations[0]), wrong);
                    let outputs =
                        trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
                    assert_eq!(outputs.len(), 1);
                    assert!(
                        outputs[0].diagnostics.is_empty(),
                        "pointer-width comparisons are precise"
                    );
                    assert_eq!(some_error_rule_is_satisfiable(&outputs[0]), wrong);
                }
            }
        }
    }
}
