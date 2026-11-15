// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn native_bmc_address_and_comparison_api_paths_do_not_expose_synthetic_heap_ids() {
    for name in ["address_api", "null_api", "compare_api"] {
        with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.body().unwrap();
            ctx.set_current_fn(instance);
            let mut codegen =
                StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
            let root =
                codegen.ctx.heap_alloc(Expr::bitvec_const(4u64, 64), Expr::bitvec_const(4u64, 64));
            codegen.ctx.record_native_box_allocation(root.clone(), 4, 4, None);
            let value = if name == "null_api" {
                root.clone().bvadd(Expr::bitvec_const(0xffff_ffff_fff0_0000u64, 64))
            } else {
                root
            };
            bind_box(&mut codegen, &Operand::Copy(Place::from(1)), value);
            if name == "compare_api" {
                let physical = Expr::bitvec_const(0x100000u64, 64);
                codegen.ctx.record_box_numeric_address(physical.clone());
                bind_box(&mut codegen, &Operand::Copy(Place::from(2)), physical);
            }
            let term = body
                .blocks
                .iter()
                .find_map(|block| {
                    matches!(block.terminator.kind, TerminatorKind::Call { .. })
                        .then_some(&block.terminator)
                })
                .unwrap();
            let _ = codegen.codegen_terminator_with_successors(term);
            let reason =
                if name == "address_api" { "BoxNumericAddress" } else { "BoxPointerComparison" };
            assert!(
                codegen.ctx.unsupported_constructs.contains_key(reason),
                "{name}: {:?}",
                codegen.ctx.unsupported_constructs
            );
        });
    }
}

#[test]
fn native_bmc_numeric_provenance_invalidation_refuses_possible_id_aliases_without_freeing_native_memory()
 {
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        let root = ctx.heap_alloc(Expr::bitvec_const(4u64, 64), Expr::bitvec_const(4u64, 64));
        ctx.record_native_box_allocation(root, 4, 4, None);
        ctx.heap_invalidate_no_provenance(Expr::bitvec_const(0u64, 64));
        assert!(!ctx.unsupported_constructs.contains_key("BoxNumericProvenanceInvalidation"));
        ctx.heap_invalidate_no_provenance(Expr::bitvec_const(0x100000u64, 64));
        assert!(ctx.unsupported_constructs.contains_key("BoxNumericProvenanceInvalidation"));
        check_formula(vec![ctx.native_box_allocation(0).unwrap().alive.clone().unwrap()], true);
    });
}
