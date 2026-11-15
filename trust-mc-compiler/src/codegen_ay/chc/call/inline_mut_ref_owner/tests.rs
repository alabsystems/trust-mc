// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::codegen_ay::chc::ChcConfig;
use crate::codegen_ay::chc::call::codegen_call_virtual_inline::resolve_mut_ref_value_args;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use ay_bindings::Expr;

const SOURCE: &str = r#"
    #![allow(dead_code, unused_assignments)]
    #[inline(never)] fn consume(a: &mut i32, b: &mut i32) { *a += 1; *b += 2; }
    pub fn host() { let mut x = 7i32; let mut y = 7i32; consume(&mut x, &mut y); }
    pub fn rebind<'a>(mut a: &'a mut i32, b: &'a mut i32) { a = b; *a += 1; }
    pub fn unary(value: &mut i32) { *value += 1; }
    pub fn unsigned(value: &mut u32) { *value += 1; }
    pub fn word(value: &mut u64) { *value += 1; }
    pub fn word_host() { let mut x = 7u64; word(&mut x); }
    pub fn pair<'a>(a: &'a mut i32, b: &'a mut i32) -> (&'a mut i32, &'a mut i32) { (a, b) }
    pub fn reassigned(flag: bool) {
        let mut x = 7i32; let mut y = 7i32;
        let mut r = &mut x;
        if flag { r = &mut y; }
        consume(r, &mut 0);
    }
    fn replace<'a>(r: &mut &'a mut i32, value: &'a mut i32) { *r = value; }
    pub fn escaped() {
        let mut x = 7i32; let mut y = 7i32;
        let mut r = &mut x;
        replace(&mut r, &mut y);
        consume(r, &mut 0);
    }
"#;

fn reference_call_args(body: &Body) -> &[Operand] {
    body.blocks
        .iter()
        .find_map(|block| match &block.terminator.kind {
            TerminatorKind::Call { args, .. } if args.len() == 2 => Some(args.as_slice()),
            _ => None,
        })
        .expect("reference call")
}

#[test]
fn actual_borrow_owners_survive_rustcall_without_sort_guessing() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let host = find_instance_by_suffix(ctx.tcx, "host").body().unwrap();
        let pair = find_instance_by_suffix(ctx.tcx, "pair").body().unwrap();
        let direct = find_instance_by_suffix(ctx.tcx, "consume").body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &host, "owner_host", ChcConfig::default());
        chc.declare_block_relations();
        let args = reference_call_args(&host);
        let a = chc.host_mut_ref_owner(&args[0]).expect("first actual borrow");
        let b = chc.host_mut_ref_owner(&args[1]).expect("second actual borrow");
        assert_ne!(a.local, b.local, "equal i32 values have distinct owners");
        assert_eq!(a.pointee, b.pointee);
        let (destination, rhs) = pair
            .blocks
            .iter()
            .flat_map(|block| &block.statements)
            .find_map(|statement| match &statement.kind {
                StatementKind::Assign(place, rhs @ Rvalue::Aggregate(AggregateKind::Tuple, _)) => {
                    Some((place.local, rhs))
                }
                _ => None,
            })
            .unwrap();
        chc.inline_walk_param_mut_owner_seeds = Some(vec![(1, a.clone()), (2, b.clone())]);
        chc.inline_walk_param_referent_seeds = Some(vec![1, 2]);
        chc.with_inline_walk_frame(&pair, |chc| {
            chc.note_inline_mut_ref_assignment(&pair, destination, Some(rhs));
            let tuple =
                Operand::Copy(rustc_public::mir::Place { local: destination, projection: vec![] });
            let owners = chc.inline_rustcall_mut_ref_args(&tuple);
            let mut values = vec![Expr::bitvec_const(7u32, 32), Expr::bitvec_const(7u32, 32)];
            assert_eq!(
                resolve_mut_ref_value_args(chc, &mut values, &direct, false, &owners),
                Some(vec![(1, a.local), (2, b.local)])
            );
            assert_eq!(values[0], values[1], "ownership never changes a value");
            let before = chc.diagnostics.place_translation_drop.get();
            assert!(resolve_mut_ref_value_args(chc, &mut values, &direct, false, &[]).is_none());
            assert!(
                chc.diagnostics.place_translation_drop.get() > before,
                "unowned values explicitly fail closed despite known same-sort targets"
            );

            // A write after tuple construction makes its value snapshot stale.
            chc.heap_state.note_write();
            assert!(
                resolve_mut_ref_value_args(chc, &mut values, &direct, false, &owners).is_none()
            );
            chc.invalidate_inline_mut_ref_owner_values(a.local);
            assert!(chc.inline_rustcall_mut_ref_args(&tuple).is_empty());
            assert!(!chc.inline_walk_operand_is_referent(&Operand::Copy(
                rustc_public::mir::Place { local: 1, projection: vec![] }
            )));
        });
        assert!(
            chc.inline_operand_mut_ref_owner(&args[0]).is_none(),
            "frame ownership does not escape"
        );
    });
}

#[test]
fn host_reassigned_and_address_exposed_carriers_have_no_owner_authority() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in ["reassigned", "escaped"] {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            chc.declare_block_relations();
            let args = body
                .blocks
                .iter()
                .filter_map(|block| match &block.terminator.kind {
                    TerminatorKind::Call { args, .. } if args.len() == 2 => Some(args),
                    _ => None,
                })
                .last()
                .unwrap();
            assert!(
                chc.host_mut_ref_owner(&args[0]).is_none(),
                "{name}: neither a last points-at edge nor one original assignment establishes the current owner"
            );
        }
    });
}

#[test]
fn address_lane_requires_its_actual_owner_and_refuses_missing_mismatched_or_interior_identity() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let host = find_instance_by_suffix(ctx.tcx, "host").body().unwrap();
        let direct = find_instance_by_suffix(ctx.tcx, "unary").body().unwrap();
        let mut chc = ChcCtx::new(
            ctx.tcx,
            &host,
            "owner_address_host",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc.declare_block_relations();
        let args = reference_call_args(&host);
        let a = chc.host_mut_ref_owner(&args[0]).unwrap();
        let b = chc.host_mut_ref_owner(&args[1]).unwrap();
        let address = chc.get_or_create_local_address(a.local).unwrap();
        chc.build_memory_store(
            crate::codegen_ay::provenance::Loc::of_address(address.clone()),
            Expr::bitvec_const(7u32, 32),
            a.pointee,
        );
        let binding = InlineMutRefArg { owner: a.clone(), referent_value: false, value_mark: None };
        let mut values = vec![address.clone()];
        assert_eq!(
            resolve_mut_ref_value_args(
                &mut chc,
                &mut values,
                &direct,
                false,
                &[Some(binding.clone())]
            ),
            Some(vec![(1, a.local)])
        );
        assert_eq!(values[0].sort().bitvec_width(), Some(32));
        let mut missing = vec![address.clone()];
        assert!(resolve_mut_ref_value_args(&mut chc, &mut missing, &direct, false, &[]).is_none());
        let mut wrong = vec![address.clone()];
        let wrong_owner = InlineMutRefArg { owner: b, ..binding.clone() };
        assert!(
            resolve_mut_ref_value_args(&mut chc, &mut wrong, &direct, false, &[Some(wrong_owner)])
                .is_none()
        );
        let mut interior = vec![address.bvadd(Expr::bitvec_const(1u64, 64))];
        assert!(
            resolve_mut_ref_value_args(&mut chc, &mut interior, &direct, false, &[Some(binding)])
                .is_none()
        );
    });
}

#[test]
fn conflicting_reassignments_and_nested_frames_never_reuse_an_old_owner() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let host = find_instance_by_suffix(ctx.tcx, "host").body().unwrap();
        let rebind = find_instance_by_suffix(ctx.tcx, "rebind").body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &host, "owner_rebind_host", ChcConfig::default());
        chc.declare_block_relations();
        let args = reference_call_args(&host);
        let a = chc.host_mut_ref_owner(&args[0]).unwrap();
        let b = chc.host_mut_ref_owner(&args[1]).unwrap();
        let rhs = rebind
            .blocks
            .iter()
            .flat_map(|block| &block.statements)
            .find_map(|statement| match &statement.kind {
                StatementKind::Assign(place, rhs @ Rvalue::Use(_, ..)) if place.local == 1 => {
                    Some(rhs)
                }
                _ => None,
            })
            .expect("actual reassignment of reference parameter");
        let operand = Operand::Copy(rustc_public::mir::Place { local: 1, projection: vec![] });
        chc.inline_walk_param_mut_owner_seeds = Some(vec![(1, a.clone()), (2, b.clone())]);
        chc.with_inline_walk_frame(&rebind, |chc| {
            assert_eq!(chc.inline_operand_mut_ref_owner(&operand), Some(a));
            chc.note_inline_mut_ref_assignment(&rebind, 1, Some(rhs));
            assert!(chc.inline_operand_mut_ref_owner(&operand).is_none());
            chc.inline_walk_param_mut_owner_seeds = Some(vec![(1, b.clone())]);
            chc.with_inline_walk_frame(&rebind, |chc| {
                assert_eq!(chc.inline_operand_mut_ref_owner(&operand), Some(b));
            });
            assert!(
                chc.inline_operand_mut_ref_owner(&operand).is_none(),
                "nested local 1 cannot reseed caller local 1"
            );
            chc.note_inline_mut_ref_assignment(&rebind, 1, Some(rhs));
            assert!(
                chc.inline_operand_mut_ref_owner(&operand).is_none(),
                "positive assignments never erase conflicting-branch uncertainty"
            );
        });
    });
}

#[test]
fn owner_type_identity_and_pointer_shaped_logical_values_remain_refused() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let host = find_instance_by_suffix(ctx.tcx, "host").body().unwrap();
        let unsigned = find_instance_by_suffix(ctx.tcx, "unsigned").body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &host, "owner_wrong_type_host", ChcConfig::default());
        chc.declare_block_relations();
        let owner = chc.host_mut_ref_owner(&reference_call_args(&host)[0]).unwrap();
        let binding = InlineMutRefArg {
            owner,
            referent_value: true,
            value_mark: Some(chc.heap_state.write_mark()),
        };
        assert!(
            resolve_mut_ref_value_args(
                &mut chc,
                &mut [Expr::bitvec_const(7u32, 32)],
                &unsigned,
                false,
                &[Some(binding)]
            )
            .is_none(),
            "same sort does not equate i32 and u32 owners"
        );

        let host = find_instance_by_suffix(ctx.tcx, "word_host").body().unwrap();
        let word = find_instance_by_suffix(ctx.tcx, "word").body().unwrap();
        let mut chc = ChcCtx::new(ctx.tcx, &host, "owner_word_host", ChcConfig::default());
        chc.declare_block_relations();
        let operand = host
            .blocks
            .iter()
            .find_map(|block| match &block.terminator.kind {
                TerminatorKind::Call { args, .. } if args.len() == 1 => args.first(),
                _ => None,
            })
            .unwrap();
        let owner = chc.host_mut_ref_owner(operand).unwrap();
        let binding = InlineMutRefArg {
            owner,
            referent_value: true,
            value_mark: Some(chc.heap_state.write_mark()),
        };
        assert!(
            resolve_mut_ref_value_args(
                &mut chc,
                &mut [Expr::bitvec_const(7u64, 64)],
                &word,
                false,
                &[Some(binding)]
            )
            .is_none(),
            "owner authority cannot retag pointer-shaped element bits"
        );
    });
}

#[test]
fn copied_owner_recovery_refuses_missing_allocation_identity() {
    use crate::codegen_ay::chc::codegen_ctx::ExactVar;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let host = find_instance_by_suffix(ctx.tcx, "host").body().unwrap();
        let direct = find_instance_by_suffix(ctx.tcx, "unary").body().unwrap();
        let mut chc = ChcCtx::new(
            ctx.tcx,
            &host,
            "owner_missing_storage",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc.declare_block_relations();
        let owner = chc.host_mut_ref_owner(&reference_call_args(&host)[0]).unwrap();
        let _ = chc.get_or_create_local_address(owner.local).unwrap();
        chc.heap_state.local_addresses.remove(&owner.local);
        let local = owner.local;
        let binding = InlineMutRefArg { owner, referent_value: false, value_mark: None };
        let mut values =
            [ExactVar::defined("copied_reference_address".into(), ay_bindings::Sort::bitvec(64))];
        assert!(
            resolve_mut_ref_value_args(&mut chc, &mut values, &direct, false, &[Some(binding)])
                .is_none()
        );
        assert!(
            !chc.heap_state.local_addresses.contains_key(&local),
            "refusal must not invent a replacement allocation"
        );
        assert!(chc.diagnostics.place_translation_drop.get() > 0);
    });
}
