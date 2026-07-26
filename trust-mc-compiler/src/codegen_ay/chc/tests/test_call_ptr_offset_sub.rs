// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for pointer-sub offset metadata propagation.

#![allow(clippy::unwrap_used)]

use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_ptr::CallPtr;
use super::common::*;
use crate::codegen_ay::chc::codegen_ctx::types::RefTarget;
use crate::codegen_ay::emit_chc;
use ay_bindings::Expr;

/// `ptr.sub()` on a pointer to `arr[N]` should preserve the referent metadata
/// while moving the constant-index projection backwards.
#[test]
fn test_ptr_sub_preserves_ref_target_and_constant_offset_metadata() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_sub(arr: &[i32; 4]) -> *const i32 {
            let p = unsafe { arr.as_ptr().add(3) };
            unsafe { p.sub(1) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_sub");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_sub", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
                    == Some(StubKind::PtrSub)
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, args, destination, target) =
            call_site.expect("expected PtrSub call terminator in probe_ptr_sub MIR");
        let src_local = match args.first() {
            Some(Operand::Copy(place) | Operand::Move(place)) if place.projection.is_empty() => {
                place.local
            }
            other => panic!("expected direct pointer source local, got {other:?}"),
        };

        let expected_src_target = RefTarget::with_projections(
            src_local,
            vec![rustc_public::mir::ProjectionElem::ConstantIndex {
                offset: 3,
                min_length: 4,
                from_end: false,
            }],
        );
        let expected_dest_target = RefTarget::with_projections(
            src_local,
            vec![rustc_public::mir::ProjectionElem::ConstantIndex {
                offset: 2,
                min_length: 4,
                from_end: false,
            }],
        );
        chc_ctx.ref_resolution.ref_targets.insert(src_local, expected_src_target);

        let from_rel =
            chc_ctx.block_relations.get(&bb_idx).expect("source relation for call block").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals = HashSet::new();
        let before_rules = chc_ctx.vc.rules.len();
        let cx = ChcCallContext {
            stub: StubKind::PtrSub,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_ptr_memory(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one ptr.sub rule");
        assert_eq!(chc_ctx.sound_fallback_count(), 0, "ptr.sub metadata propagation is precise");

        assert!(
            chc_ctx.ref_resolution.call_forwarded_raw_ptrs.contains(&destination.local),
            "ptr.sub result should be marked call-forwarded for raw-pointer deref resolution"
        );
        let dest_target = chc_ctx
            .ref_resolution
            .ref_targets
            .get(&destination.local)
            .expect("ptr.sub result should preserve ref_target");
        assert_eq!(dest_target.local, expected_dest_target.local);
        assert_eq!(dest_target.projections, expected_dest_target.projections);
        assert!(
            !chc_ctx.ref_resolution.subslice_offset.contains_key(&destination.local),
            "constant-index ref_target shift should not force the Mem-level offset path"
        );
    });
}

/// Pre-declaration metadata seeding must also handle pointer-offset calls because
/// a target block can be encoded before its predecessor call terminator.
#[test]
fn test_pointer_offset_precollection_shifts_ptr_sub_array_element_metadata() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_offset_sub_exact() {
            let array = [0, 1, 2, 3, 4, 5, 6];
            let second_ref = &array[3];
            let second_ptr: *const i32 = &raw const *second_ref;
            unsafe {
                let before = second_ptr.sub(1);
                assert_eq!(*before, 2);
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_offset_sub_exact");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_offset_sub_exact",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();

        let offset_dest_locals: Vec<_> = body
            .blocks
            .iter()
            .filter_map(|block| {
                let rustc_public::mir::TerminatorKind::Call { func, destination, .. } =
                    &block.terminator.kind
                else {
                    return None;
                };
                let is_offset_model = matches!(
                    chc_ctx.detect_kani_model(func),
                    Some(crate::kani_middle::kani_functions::KaniModel::Offset)
                );
                let is_ptr_sub = chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
                    == Some(StubKind::PtrSub);
                (is_offset_model || is_ptr_sub).then_some(destination.local)
            })
            .collect();

        assert!(
            !offset_dest_locals.is_empty(),
            "expected a pointer-offset call in probe_offset_sub_exact MIR"
        );
        let shifted_dest = offset_dest_locals
            .iter()
            .copied()
            .find(|local| {
                chc_ctx.ref_resolution.ref_targets.get(local).is_some_and(|target| {
                    matches!(
                        target.projections.last(),
                        Some(rustc_public::mir::ProjectionElem::ConstantIndex {
                            offset: 2,
                            min_length: 7,
                            from_end: false,
                        })
                    )
                })
            })
            .unwrap_or_else(|| {
                panic!(
                    "ptr.sub precollection should shift arr[3] metadata to arr[2]; dests={:?}, ref_targets={:?}, offsets={:?}, forwarded={:?}",
                    offset_dest_locals,
                    chc_ctx.ref_resolution.ref_targets,
                    chc_ctx.ref_resolution.subslice_offset,
                    chc_ctx.ref_resolution.call_forwarded_raw_ptrs
                )
            });

        assert!(
            chc_ctx.ref_resolution.call_forwarded_raw_ptrs.contains(&shifted_dest),
            "precollected ptr.sub result should be call-forwarded"
        );
        assert!(
            !chc_ctx.ref_resolution.subslice_offset.contains_key(&shifted_dest),
            "constant-index ref_target shift should not also seed a subslice offset"
        );
        let shifted_value = chc_ctx
            .ref_resolution
            .const_ref_values
            .get(&shifted_dest)
            .expect("shifted stack-array pointer should carry the selected element value");
        assert!(
            matches!(
                shifted_value.value(),
                ExprValue::BitVecConst { value, width }
                    if *width == 32 && u64::try_from(value).ok() == Some(2)
            ),
            "expected ptr.sub precollection to seed const element value 2, got {shifted_value}"
        );
    });
}

#[test]
fn test_pointer_offset_sub_deref_assert_full_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(register_tool)]
        #![register_tool(kanitool)]

        mod kani {
            #[kanitool::fn_marker = "AssertHook"]
            pub fn assert(cond: bool, _msg: &str) {
                let _ = cond;
            }
        }

        pub fn probe_offset_sub_assert() {
            let array = [0, 1, 2, 3, 4, 5, 6];
            let second_ptr: *const i32 = &array[3];
            unsafe {
                let before = second_ptr.sub(1);
                kani::assert(*before == 2, "ptr.sub should read arr[2]");
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_offset_sub_assert");
        let body = instance.body().expect("function body");
        let mut vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_offset_sub_assert",
            ChcConfig {
                track_level: crate::args::ChcTrackLevel::Mem,
                extra_pointer_checks: true,
                ..ChcConfig::default()
            },
        );
        vc.propagate_constants();
        vc.prune_orphan_block_rules();
        vc.prune_dead_identity_scalars();
        vc.normalize_free_array_bases();
        crate::codegen_ay::chc::scalarize_vc(&mut vc);
        vc.prune_dead_vars_and_constraints();
        let smt = emit_chc(&vc).to_string();
        assert_z3_result_with_timeout(&smt, "unsat", 10);
    });
}
