// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn native_bmc_box_carrier_pointee_stubs_and_erased_integer_views_remain_refused() {
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "scalar");
        let body = instance.body().unwrap();
        let (operand, target) = actual_cast(&body);
        let narrow = find_instance_by_suffix(ctx.tcx, "narrow").body().unwrap();
        let (_, wrong_target) = actual_cast(&narrow);
        let allocate = find_instance_by_suffix(ctx.tcx, "allocate").body().unwrap();
        let stub = allocate
            .blocks
            .iter()
            .find_map(|b| match &b.terminator.kind {
                TerminatorKind::Call { func, .. } => {
                    match func.ty(allocate.locals()).unwrap().kind() {
                        TyKind::RigidTy(RigidTy::FnDef(def, _)) => Some(def),
                        _ => None,
                    }
                }
                _ => None,
            })
            .unwrap();
        ctx.set_current_fn(instance);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        let pointer =
            codegen.ctx.heap_alloc(Expr::bitvec_const(4u64, 64), Expr::bitvec_const(4u64, 64));
        codegen.ctx.record_native_box_allocation(pointer.clone(), 4, 4, None);
        bind_box(&mut codegen, &operand, pointer.clone());
        assert!(codegen.checked_bmc_box_deref(&operand, target).is_some());
        assert_eq!(
            StatementCodegen::infer_sort_from_ty(target),
            StatementCodegen::infer_sort_from_ty(wrong_target)
        );
        assert!(
            codegen.checked_bmc_box_deref(&operand, wrong_target).is_none(),
            "same pointer sort is not the same pointee"
        );
        {
            let _stubs = crate::kani_middle::transform::UnitStubsTestScope::install(HashMap::from(
                [(stub, stub)],
            ));
            assert!(codegen.checked_bmc_box_deref(&operand, target).is_none());
        }
        let (numeric_source, numeric_target) = body
            .blocks
            .iter()
            .flat_map(|b| &b.statements)
            .find_map(|s| match &s.kind {
                StatementKind::Assign(_, Rvalue::Cast(_, source, target))
                    if matches!(
                        source.ty(body.locals()).unwrap().kind(),
                        TyKind::RigidTy(RigidTy::RawPtr(..))
                    ) && matches!(target.kind(), TyKind::RigidTy(RigidTy::Uint(_))) =>
                {
                    Some((source, *target))
                }
                _ => None,
            })
            .unwrap();
        bind_box(&mut codegen, numeric_source, pointer.clone());
        let erased = codegen.box_cast_transport(numeric_source, numeric_target, pointer).unwrap();
        bind_box(&mut codegen, &operand, erased);
        assert!(codegen.ctx.unsupported_constructs.contains_key("BoxNumericAddress"));
        assert!(
            codegen.checked_bmc_box_deref(&operand, target).is_none(),
            "an asserted numeric equality restores no provenance"
        );
    });
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "custom_carrier");
        let body = instance.body().unwrap();
        let target = body.locals()[2].ty;
        ctx.set_current_fn(instance);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        let pointer =
            codegen.ctx.heap_alloc(Expr::bitvec_const(4u64, 64), Expr::bitvec_const(4u64, 64));
        codegen.ctx.record_native_box_allocation(pointer.clone(), 4, 4, None);
        let operand = Operand::Copy(Place::from(1));
        bind_box(&mut codegen, &operand, pointer);
        assert!(
            codegen.checked_bmc_box_deref(&operand, target).is_none(),
            "a user BoxRaw has no compiler carrier authority"
        );
    });
}

#[test]
fn native_bmc_zst_rewrap_accepts_aligned_live_or_freed_addresses_without_minting_ownership() {
    for freed in [false, true] {
        with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "zst_roundtrip");
            let body = instance.body().unwrap();
            ctx.set_current_fn(instance);
            let mut codegen =
                StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
            let pointer = codegen
                .ctx
                .heap_alloc(Expr::bitvec_const(32u64, 64), Expr::bitvec_const(32u64, 64));
            codegen.ctx.record_native_box_allocation(pointer.clone(), 32, 32, None);
            if freed {
                codegen.ctx.heap_dealloc(
                    pointer.clone(),
                    Expr::bitvec_const(32u64, 64),
                    Expr::bitvec_const(32u64, 64),
                );
            }
            bind_box(&mut codegen, &Operand::Copy(Place::from(1)), pointer);
            let mut handled = 0;
            for block in &body.blocks {
                if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                {
                    assert!(codegen.try_native_box_transfer_call(func, args, destination));
                    handled += 1;
                }
            }
            assert_eq!(handled, 2);
            assert!(
                !codegen.ctx.claim_released_native_box(0, None),
                "a ZST roundtrip releases no nonzero allocation"
            );
            assert!(!codegen.ctx.unsupported_constructs.contains_key("BoxConstructionValidity"));
        });
    }
}

#[test]
fn native_bmc_unmodeled_global_and_custom_allocator_constructors_are_explicitly_refused() {
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        for name in ["global_construct", "system_construct"] {
            let wrapper = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let callee = wrapper
                .blocks
                .iter()
                .find_map(|block| match &block.terminator.kind {
                    TerminatorKind::Call { func, .. } => {
                        match func.ty(wrapper.locals()).unwrap().kind() {
                            TyKind::RigidTy(RigidTy::FnDef(def, args)) => {
                                Instance::resolve(def, &args).ok()
                            }
                            _ => None,
                        }
                    }
                    _ => None,
                })
                .unwrap();
            let body = callee.body().unwrap();
            ctx.set_current_fn(callee);
            let mut codegen =
                StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
            let before = codegen
                .ctx
                .unsupported_constructs
                .get("BoxConstructionAggregate")
                .map_or(0, Vec::len);
            let mut constructors = 0;
            for statement in body.blocks.iter().flat_map(|block| &block.statements) {
                if let StatementKind::Assign(_, Rvalue::Aggregate(kind, operands)) = &statement.kind
                {
                    let _ = codegen.codegen_aggregate(kind, operands);
                    constructors += usize::from(
                        codegen
                            .ctx
                            .unsupported_constructs
                            .get("BoxConstructionAggregate")
                            .map_or(0, Vec::len)
                            > before,
                    );
                }
            }
            assert!(
                constructors > 0,
                "the actual {name} body must encounter its native Box aggregate"
            );
        }
    });
}

#[test]
fn native_bmc_custom_allocator_drop_is_refused_without_changing_liveness() {
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "system_owner");
        let body = instance.body().unwrap();
        ctx.set_current_fn(instance);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        let pointer =
            codegen.ctx.heap_alloc(Expr::bitvec_const(4u64, 64), Expr::bitvec_const(4u64, 64));
        codegen.ctx.record_native_box_allocation(pointer.clone(), 4, 4, None);
        bind_box(&mut codegen, &Operand::Copy(Place::from(1)), pointer);
        assert!(!codegen.try_native_box_drop(&Place::from(1)));
        assert!(codegen.ctx.unsupported_constructs.contains_key("BoxAllocatorMetadata"));
        check_formula(
            vec![codegen.ctx.native_box_allocation(0).unwrap().alive.clone().unwrap()],
            true,
        );
    });
}

#[test]
fn native_bmc_unknown_owner_layout_and_raw_transmute_do_not_invent_ub_claims() {
    for name in ["wrap_raw", "transmute_pointer"] {
        with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.body().unwrap();
            ctx.set_current_fn(instance);
            let mut codegen =
                StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
            // Four readable, aligned bytes exist, but this is not the exact
            // layout/custody admitted by the checked from_raw API path.
            let pointer =
                codegen.ctx.heap_alloc(Expr::bitvec_const(8u64, 64), Expr::bitvec_const(4u64, 64));
            codegen.ctx.record_native_box_allocation(pointer.clone(), 8, 4, None);
            codegen.ctx.release_native_box(&pointer, None);
            bind_box(&mut codegen, &Operand::Copy(Place::from(1)), pointer);
            let before = codegen.ctx.property_violation_names().len();
            if name == "wrap_raw" {
                let target = body.locals()[0].ty;
                assert!(
                    codegen
                        .codegen_box_construction_cast(&Operand::Copy(Place::from(1)), target)
                        .is_none()
                );
            } else {
                let (kind, operand, target) = body
                    .blocks
                    .iter()
                    .flat_map(|b| &b.statements)
                    .find_map(|s| match &s.kind {
                        StatementKind::Assign(_, Rvalue::Cast(kind, operand, target)) => {
                            Some((kind, operand, *target))
                        }
                        _ => None,
                    })
                    .unwrap();
                assert!(codegen.codegen_cast_with_kind(kind, operand, target).is_none());
            }
            assert_eq!(
                codegen.ctx.property_violation_names().len(),
                before,
                "unmodeled admission is refusal, not a synthetic UB failure"
            );
        });
    }
}
