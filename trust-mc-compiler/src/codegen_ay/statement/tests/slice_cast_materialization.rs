// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Slice cast materialization tests.

use super::*;
use std::sync::Arc;

const SLICE_COERCION_SOURCE: &str = r#"
pub fn array_to_slice() {
    let arr: [u8; 4] = [1, 2, 3, 4];
    let slice: &[u8] = &arr;
    let _ = slice;
}
"#;

fn find_slice_cast_assign(
    body: &rustc_public::mir::Body,
) -> (Place, Rvalue, Operand, rustc_public::ty::Ty) {
    for bb in &body.blocks {
        for stmt in &bb.statements {
            let StatementKind::Assign(lhs, rvalue) = &stmt.kind else {
                continue;
            };
            if let Rvalue::Cast(_, operand, target_ty) = rvalue
                && StatementCodegen::is_slice_pointer_ty(*target_ty)
            {
                return (lhs.clone(), rvalue.clone(), operand.clone(), *target_ty);
            }
        }
    }
    panic!("expected array-to-slice cast");
}

fn operand_place(operand: &Operand) -> &Place {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place,
        Operand::Constant(_) => panic!("expected place operand for slice cast"),
    }
}

fn seed_u8_array_backing(
    codegen: &mut StatementCodegen<'_, '_, '_>,
    ref_base: &str,
    backing_name: &str,
) -> Expr {
    let array_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(8));
    let mut backing = codegen.ctx.declare_var(backing_name, array_sort);
    for i in 0u128..4 {
        backing = backing.store(Expr::bitvec_const(i, POINTER_WIDTH), Expr::bitvec_const(i + 1, 8));
    }
    codegen.env_update(backing_name.to_string(), backing.clone());
    codegen.ref_pointees.insert(Arc::from(ref_base), Arc::from(backing_name));
    backing
}

fn slice_constructor_args(slice_expr: &Expr) -> &[Expr] {
    let ExprValue::DatatypeConstructor { args, .. } = slice_expr.value() else {
        panic!("expected datatype constructor, got {:?}", slice_expr.value());
    };
    args
}

#[test]
fn test_slice_cast_prefers_env_pointer_over_cached_ref_slot_address() {
    with_test_ay_ctx_for_source(SLICE_COERCION_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_to_slice");
        let body = instance.body().expect("array_to_slice body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        let (_lhs, _rvalue, operand, target_ty) = find_slice_cast_assign(&body);

        let ref_base = codegen.ssa_base_name(operand_place(&operand));
        let env_ptr =
            codegen.ctx.declare_var("env_ref_points_to_array", Sort::bitvec(POINTER_WIDTH));
        let cached_ref_slot_addr =
            codegen.ctx.declare_var("cached_ref_slot_addr", Sort::bitvec(POINTER_WIDTH));
        codegen.env_update(ref_base.clone(), env_ptr.clone());
        codegen.addr_symbols.insert(Arc::from(ref_base.as_str()), cached_ref_slot_addr.clone());
        let expected_backing =
            seed_u8_array_backing(&mut codegen, &ref_base, "env_ptr_preferred_backing");

        let slice_expr = codegen
            .try_construct_slice_datatype_from_cast(&operand, target_ty)
            .expect("slice cast should materialize with tracked pointer and backing");
        let args = slice_constructor_args(&slice_expr);

        assert_eq!(
            args[0].to_string(),
            env_ptr.to_string(),
            "fld_ptr should use pointer-valued env entry, not cached address of the ref slot"
        );
        assert_ne!(
            args[0].to_string(),
            cached_ref_slot_addr.to_string(),
            "cached ref-slot address must not override the source pointer value"
        );
        assert_eq!(
            args[2].to_string(),
            expected_backing.to_string(),
            "fld_data should preserve the tracked backing array"
        );
    });
}

#[test]
fn test_slice_cast_uses_cached_address_for_env_value_backing() {
    with_test_ay_ctx_for_source(SLICE_COERCION_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_to_slice");
        let body = instance.body().expect("array_to_slice body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        let (_lhs, _rvalue, operand, target_ty) = find_slice_cast_assign(&body);
        let ref_base = codegen.ssa_base_name(operand_place(&operand));

        let cached_addr =
            codegen.ctx.declare_var("env_value_array_addr", Sort::bitvec(POINTER_WIDTH));
        codegen.addr_symbols.insert(Arc::from(ref_base.as_str()), cached_addr.clone());

        let array_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(8));
        let mut backing = codegen.ctx.declare_var("env_value_array_backing", array_sort);
        for i in 0u128..4 {
            backing =
                backing.store(Expr::bitvec_const(i, POINTER_WIDTH), Expr::bitvec_const(i + 1, 8));
        }
        codegen.env_update(ref_base, backing.clone());

        let slice_expr = codegen
            .try_construct_slice_datatype_from_cast(&operand, target_ty)
            .expect("env-value array with cached address should construct slice datatype");
        let args = slice_constructor_args(&slice_expr);

        assert_eq!(
            args[0].to_string(),
            cached_addr.to_string(),
            "value-semantics env backing should use cached address as fld_ptr"
        );
        assert_eq!(
            args[2].to_string(),
            backing.to_string(),
            "env-value recovery should preserve the exact backing array"
        );
    });
}

#[test]
fn test_codegen_assign_slice_cast_prefers_env_pointer_over_cached_address() {
    with_test_ay_ctx_for_source(SLICE_COERCION_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "array_to_slice");
        let body = instance.body().expect("array_to_slice body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);
        let (lhs, rvalue, operand, _target_ty) = find_slice_cast_assign(&body);

        let ref_base = codegen.ssa_base_name(operand_place(&operand));
        let lhs_base = codegen.ssa_base_name(&lhs);
        let env_ptr =
            codegen.ctx.declare_var("assign_env_ref_points_to_array", Sort::bitvec(POINTER_WIDTH));
        let cached_ref_slot_addr =
            codegen.ctx.declare_var("assign_cached_ref_slot_addr", Sort::bitvec(POINTER_WIDTH));
        codegen.env_update(ref_base.clone(), env_ptr);
        codegen.addr_symbols.insert(Arc::from(ref_base.as_str()), cached_ref_slot_addr);
        seed_u8_array_backing(&mut codegen, &ref_base, "assign_env_ptr_preferred_backing");

        let constraints_before = codegen.ctx.bmc_vc.constraints.len();
        codegen.codegen_assign(&lhs, &rvalue);

        let assigned = codegen.env_lookup(&lhs_base).expect("slice lhs should be assigned");
        assert!(assigned.sort().is_datatype(), "slice assignment should use datatype sort");

        let added_constraints = codegen.ctx.bmc_vc.constraints[constraints_before..]
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            added_constraints.contains("assign_env_ref_points_to_array"),
            "codegen_assign should constrain the slice constructor with the source pointer: {added_constraints}"
        );
        assert!(
            !added_constraints.contains("assign_cached_ref_slot_addr"),
            "codegen_assign must not use a cached ref-slot address as fld_ptr: {added_constraints}"
        );
    });
}
