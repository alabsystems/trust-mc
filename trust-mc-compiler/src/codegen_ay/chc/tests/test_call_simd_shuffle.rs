// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::common::*;
use crate::codegen_ay::chc::call::chc_call_context::DispatchCallContext;
use crate::codegen_ay::chc::call::codegen_simd_shuffle;
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::{Expr, ExprValue, Sort};

const SIMD_SHUFFLE_SOURCE: &str = r#"
    #![allow(dead_code, unused_variables)]

    #[derive(Clone, Copy)]
    pub struct U32x8([u32; 8]);

    #[derive(Clone, Copy)]
    pub struct U32x4([u32; 4]);

    pub fn probe_swizzle_from_b_narrow(a: U32x8, b: U32x8, idx: U32x4) -> U32x4 {
        U32x4([0, 0, 0, 0])
    }
"#;

fn store_chain_base_and_len(expr: &Expr) -> (&Expr, usize) {
    let mut base = expr;
    let mut len = 0;
    while let ExprValue::Store { array, .. } = base.value() {
        base = array;
        len += 1;
    }
    (base, len)
}

fn is_neutral_bv_array_base(expr: &Expr, elem_width: u32) -> bool {
    let ExprValue::ConstArray { value, .. } = expr.value() else {
        return false;
    };
    let Some(array_sort) = expr.sort().array_sort() else {
        return false;
    };
    if array_sort.index_sort != Sort::bitvec(POINTER_WIDTH)
        || array_sort.element_sort != Sort::bitvec(elem_width)
    {
        return false;
    }
    matches!(
        value.value(),
        ExprValue::BitVecConst { value, width }
            if *width == elem_width && value.to_string() == "0"
    )
}

fn is_neutral_shuffle_store_chain(expr: &Expr) -> bool {
    let (base, store_count) = store_chain_base_and_len(expr);
    store_count == 4
        && is_neutral_bv_array_base(base, 32)
        && constraint_tree_contains(expr, &|e| matches!(e.value(), ExprValue::Ite { .. }))
}

#[test]
fn test_simd_shuffle_narrow_result_uses_neutral_const_array_base() {
    with_test_ay_ctx_for_source(SIMD_SHUFFLE_SOURCE, |ctx| {
        let fn_name = "probe_swizzle_from_b_narrow";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let from_rel = chc_ctx.block_relations.get(&0).expect("source relation").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals = HashSet::new();
        let func = Operand::Copy(Place { local: 0usize, projection: vec![] });
        let args = [
            Operand::Copy(Place { local: 1usize, projection: vec![] }),
            Operand::Copy(Place { local: 2usize, projection: vec![] }),
            Operand::Copy(Place { local: 3usize, projection: vec![] }),
        ];
        let destination = Place { local: 0usize, projection: vec![] };
        let target = 0usize;
        let target_opt = Some(target);
        let dcx = DispatchCallContext {
            bb_idx: 0,
            func: &func,
            args: &args,
            destination: &destination,
            target: &target_opt,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
            callee_path: None,
        };

        let before_fallback = chc_ctx.sound_fallback_count();
        codegen_simd_shuffle(&mut chc_ctx, &dcx, target);
        assert_eq!(chc_ctx.sound_fallback_count(), before_fallback, "shuffle should not fallback");
        assert_has_nontrivial_transition_constraints(&chc_ctx.vc, fn_name);
        let found_neutral_base = chc_ctx
            .vc
            .rules
            .iter()
            .any(|rule| rule_contains_expr(rule, is_neutral_shuffle_store_chain));
        assert!(
            found_neutral_base,
            "{fn_name}: expected simd_shuffle result store-chain to be rooted at \
             const_array(BV{POINTER_WIDTH}, BV32 zero) so source tail lanes cannot leak"
        );
    });
}
