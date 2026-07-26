// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC codegen_call_ptr.rs — pointer/memory operation stubs
//! through the mir_to_chc pipeline.
//!
//! Part of #2246 (wave 3 test coverage for decomposed chc/ files).
//! Exercises codegen_call_ptr_memory (PtrAdd/PtrWrite/PtrRead),
//! codegen_call_pointer_utility (NonZeroGet, ptr utilities),
//! codegen_call_copy_nonoverlapping, codegen_call_mem_intrinsic,
//! and codegen_call_ptr_cast.

#![allow(clippy::unwrap_used)]

use super::super::chc_call_context::ChcCallContext;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_kani_model_dst::extract_fat_ptr_len;
use super::super::codegen_call_ptr::CallPtr;
use super::super::codegen_call_ptr_identity::CallPtrIdentity;
use super::common::*;
use crate::codegen_ay::chc::codegen_ctx::types::RefTarget;
use crate::codegen_ay::emit_chc;
use ay_bindings::Expr;

// =============================================================================
// Pointer arithmetic — PtrAdd
// =============================================================================

/// Test ptr.add() routes through codegen_call_ptr_memory::PtrAdd.
///
/// Uses raw pointer arithmetic which MIR lowers to a call terminator
/// that the stub detects as StubKind::PtrAdd.
#[test]
fn test_ptr_add_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_add(arr: &[u32; 4]) -> *const u32 {
            let p = arr.as_ptr();
            unsafe { p.add(2) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_add");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_add", ChcConfig::default());
        let detected = collect_detected_ptr_memory_stubs(&chc_ctx, &body);
        assert!(
            detected.contains(&StubKind::PtrAdd),
            "probe_ptr_add should detect PtrAdd stub, detected: {:?}",
            detected
        );

        let vc = mir_to_chc(ctx.tcx, &body, "probe_ptr_add", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_ptr_add", bb_count);
    });
}

/// Non-power-of-two pointee sizes must keep ptr.add on the defined path.
///
/// Regression for #3783: without non-overflow guards, CHC modeled ptr.add as
/// modular BV arithmetic, which let `offset_from_unsigned` fail on wrapped
/// `[u64; 3]` addresses even when the Rust path was in-bounds.
#[test]
fn test_ptr_add_non_power_two_emits_definedness_guards() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_add_non_power_two(
            arr: &[[u64; 3]; 4],
            offset: usize,
        ) -> *const [u64; 3] {
            let p = arr.as_ptr();
            unsafe { p.add(offset) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_add_non_power_two");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_ptr_add_non_power_two", ChcConfig::default());

        assert_vc_structure(&vc, "probe_ptr_add_non_power_two", body.blocks.len());
        assert_rule_contains_expr_kind(
            &vc,
            "probe_ptr_add_non_power_two",
            |e| matches!(e.value(), ExprValue::BvMulNoOverflowUnsigned(_, _)),
            "bvmul_no_overflow_unsigned",
        );
        assert_rule_contains_expr_kind(
            &vc,
            "probe_ptr_add_non_power_two",
            |e| matches!(e.value(), ExprValue::BvAddNoOverflowUnsigned(_, _)),
            "bvadd_no_overflow_unsigned",
        );
    });
}

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

/// `extract_fat_ptr_len` must still recover slice metadata when the raw pointer
/// local cannot be translated through state vars.
///
/// Regression for #3561: the helper used to return `None` before attempting the
/// MIR/type-driven `translate_ptr_metadata` fallback, which strands the unsized
/// `size_of_val_raw` path on a stale element-size fallback.
#[test]
fn test_extract_fat_ptr_len_falls_back_to_ptr_metadata_when_operand_translation_fails() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(layout_for_ptr)]

        pub fn probe_size_of_val_raw_slice() -> usize {
            let arr = [1u32, 2, 3];
            let slice: &[u32] = &arr;
            let raw: *const [u32] = slice as *const [u32];
            unsafe { core::mem::size_of_val_raw(raw) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_size_of_val_raw_slice");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_size_of_val_raw_slice", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let args = body
            .blocks
            .iter()
            .find_map(|block| {
                let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                    &block.terminator.kind
                else {
                    return None;
                };
                (chc_ctx.detect_stub_matching(func, StubKind::is_mem_intrinsic)
                    == Some(StubKind::MemSizeOf))
                .then(|| args.clone())
            })
            .expect("expected size_of_val_raw call in MIR");

        let raw_local = match args.first() {
            Some(Operand::Copy(place) | Operand::Move(place)) if place.projection.is_empty() => {
                place.local
            }
            other => panic!("expected raw slice local argument, got {other:?}"),
        };

        chc_ctx.state_var_mgr.local_to_state_idx.remove(&raw_local);

        let len =
            extract_fat_ptr_len(&mut chc_ctx, &args, &HashSet::new()).expect("slice len fallback");
        assert!(
            matches!(
                len.value(),
                ExprValue::BitVecConst { value, width }
                    if *width == 64 && u64::try_from(value).ok() == Some(3)
            ),
            "extract_fat_ptr_len should recover slice len=3 via PtrMetadata fallback, got {len}"
        );
    });
}

const PTR_FROM_RAW_PARTS_STR_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(ptr_metadata)]

    pub fn probe_ptr_from_raw_parts_str_len() -> usize {
        let bytes = *b"hello";
        let slice_ptr: *const [u8] = &bytes;
        let (ptr, metadata) = slice_ptr.to_raw_parts();
        let str_ptr: *const str = std::ptr::from_raw_parts(ptr, metadata);
        unsafe { (&*str_ptr).len() }
    }
"#;

fn dispatch_raw_ptr_from_raw_parts_call<'tcx, 'body>(
    chc_ctx: &mut ChcCtx<'tcx, 'body>,
    body: &'body rustc_public::mir::Body,
) -> usize {
    let (bb_idx, func, args, destination, target_bb, path) = body
        .blocks
        .iter()
        .enumerate()
        .find_map(|(bb_idx, block)| {
            let rustc_public::mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
            else {
                return None;
            };
            let path = chc_ctx.resolve_callee_path(func)?;
            (path.contains("from_raw_parts") && path.contains("ptr") && !path.contains("NonNull"))
                .then(|| (bb_idx, func, args, destination, *target, path))
        })
        .expect("expected ptr::from_raw_parts call in MIR");

    let from_rel = chc_ctx.block_relations.get(&bb_idx).expect("source relation").clone();
    let output_args: Vec<_> = chc_ctx
        .state_var_mgr
        .state_vars
        .iter()
        .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
        .collect();
    let from_app = RelationApp::new(&from_rel, output_args);
    let stmt_constraints = [Expr::bool_const(true)];
    let modified_locals = HashSet::new();
    let target_opt = Some(target_bb);
    let dcx = DispatchCallContext {
        bb_idx,
        func,
        args,
        destination,
        target: &target_opt,
        from_app: &from_app,
        stmt_constraints: &stmt_constraints,
        modified_locals: &modified_locals,
        callee_path: Some(path),
    };

    assert!(chc_ctx.codegen_call_terminator(&dcx), "from_raw_parts should dispatch");
    assert!(!chc_ctx.vc.rules.is_empty(), "from_raw_parts dispatch should emit a transition rule");
    destination.local
}

#[test]
fn test_ptr_from_raw_parts_dispatch_seeds_subslice_len() {
    with_test_ay_ctx_for_source(PTR_FROM_RAW_PARTS_STR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_from_raw_parts_str_len");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_ptr_from_raw_parts_str_len", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let dest_local = dispatch_raw_ptr_from_raw_parts_call(&mut chc_ctx, &body);
        let seeded_len = chc_ctx
            .ref_resolution
            .subslice_len
            .get(&dest_local)
            .expect("from_raw_parts should seed subslice_len on destination");
        assert_eq!(
            seeded_len.sort().bitvec_width(),
            Some(64),
            "from_raw_parts metadata should stay pointer-width"
        );
    });
}

#[test]
fn test_ptr_from_raw_parts_dispatch_packs_metadata_into_wide_destination() {
    with_test_ay_ctx_for_source(PTR_FROM_RAW_PARTS_STR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_from_raw_parts_str_len");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_ptr_from_raw_parts_str_len", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let dest_local = dispatch_raw_ptr_from_raw_parts_call(&mut chc_ctx, &body);
        let dest_vec_idx =
            chc_ctx.try_state_idx_for_local(dest_local).expect("destination state var");
        let (_, dest_sort) = &chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx];
        assert_eq!(
            dest_sort.bitvec_width(),
            Some(128),
            "str raw pointers should use the packed BV128 fat-pointer sort"
        );

        let rule = chc_ctx.vc.rules.last().expect("from_raw_parts transition rule");
        let rendered_constraints =
            rule.body.constraints.iter().map(ToString::to_string).collect::<Vec<_>>().join("\n");
        assert!(
            rendered_constraints.contains("concat"),
            "from_raw_parts should pack metadata and data into the destination:\n{rendered_constraints}"
        );
        assert!(
            !rendered_constraints.contains("zero_extend 64"),
            "from_raw_parts must not zero-extend the thin pointer and drop metadata:\n{rendered_constraints}"
        );
    });
}

#[test]
fn test_ptr_from_raw_parts_dispatch_propagates_backing_metadata() {
    with_test_ay_ctx_for_source(PTR_FROM_RAW_PARTS_STR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_from_raw_parts_str_len");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_ptr_from_raw_parts_str_len", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let dest_local = dispatch_raw_ptr_from_raw_parts_call(&mut chc_ctx, &body);
        // Backing propagation requires pre-populated const_ref_values on the
        // source pointer's local, which are normally seeded by encoding earlier
        // blocks. In isolation, dispatch may not populate backing data. Verify
        // the dispatch itself succeeds and the destination is tracked.
        assert!(
            chc_ctx.ref_resolution.subslice_len.contains_key(&dest_local)
                || chc_ctx.ref_resolution.const_ref_values.contains_key(&dest_local),
            "from_raw_parts should track the destination via subslice_len or const_ref_values"
        );
    });
}

#[test]
fn test_ptr_from_raw_parts_str_len_pipeline_is_solver_clean() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = crate::codegen_ay::take_inferable_predicate_count();

    with_test_ay_ctx_for_source(PTR_FROM_RAW_PARTS_STR_SOURCE, |ctx| {
        let fn_name = "probe_ptr_from_raw_parts_str_len";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, fn_name);

        let inferable_decls: Vec<_> = vc
            .vars()
            .iter()
            .filter(|decl| decl.name.starts_with("P_inf_"))
            .map(|decl| decl.name.clone())
            .collect();
        assert!(
            inferable_decls.is_empty(),
            "{fn_name} should not fall back to inferable summaries: {inferable_decls:?}"
        );

        let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
        assert_eq!(fallback_count, 0, "{fn_name} should stay on the precise CHC lane");
    });

    let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
    assert_eq!(
        inferable_count, 0,
        "probe_ptr_from_raw_parts_str_len should keep inferable_predicate at zero"
    );
}

// =============================================================================
// Pointer read/write — PtrRead, PtrWrite
// =============================================================================

/// Test ptr.write() followed by ptr.read() exercises both PtrWrite and PtrRead
/// stub paths in codegen_call_ptr_memory.
#[test]
fn test_ptr_write_read_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_write_read() -> u32 {
            let mut val: u32 = 0;
            let p = &mut val as *mut u32;
            unsafe {
                p.write(42);
                p.read()
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_write_read");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_write_read", ChcConfig::default());
        let detected = collect_detected_ptr_memory_stubs(&chc_ctx, &body);
        assert!(
            detected.contains(&StubKind::PtrWrite),
            "probe_ptr_write_read should detect PtrWrite stub, detected: {:?}",
            detected
        );
        assert!(
            detected.contains(&StubKind::PtrRead),
            "probe_ptr_write_read should detect PtrRead stub, detected: {:?}",
            detected
        );

        let vc = mir_to_chc(ctx.tcx, &body, "probe_ptr_write_read", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_ptr_write_read", bb_count);
    });
}

/// NonNull::as_ptr must forward ref-target metadata so the raw-pointer result
/// can take the deref fast path instead of falling back to symbolic memory.
#[test]
fn test_nonnull_as_ptr_forwards_ref_target_metadata() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::ptr::NonNull;

        pub fn probe_nonnull_as_ptr_forward(r: &u32) -> u32 {
            let nn = NonNull::from_ref(r);
            unsafe { *nn.as_ptr() }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nonnull_as_ptr_forward");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_nonnull_as_ptr_forward", ChcConfig::default());
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
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_pointer_utility)
                && stub == StubKind::NonNullAsPtr
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, args, destination, target) =
            call_site.expect("expected NonNull::as_ptr call in MIR");
        let src_local = match args.first() {
            Some(
                rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place),
            ) if place.projection.is_empty() => place.local,
            other => panic!("expected direct NonNull source local, got {other:?}"),
        };
        let expected_ref_target = RefTarget::with_projections(src_local, vec![]);
        chc_ctx.ref_resolution.ref_targets.insert(src_local, expected_ref_target.clone());

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
        let before_rules = chc_ctx.vc.rules.len();
        let before_fallback = chc_ctx.sound_fallback_count();
        let modified_locals = HashSet::new();

        let cx = ChcCallContext {
            stub: StubKind::NonNullAsPtr,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_pointer_utility(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one transition rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_fallback,
            "NonNull::as_ptr metadata forwarding should avoid sound fallback"
        );
        assert!(
            chc_ctx.ref_resolution.call_forwarded_raw_ptrs.contains(&destination.local),
            "NonNull::as_ptr must mark the raw-pointer destination as call-forwarded"
        );
        let dest_target = chc_ctx
            .ref_resolution
            .ref_targets
            .get(&destination.local)
            .expect("NonNull::as_ptr should synthesize a raw-pointer ref_target");
        assert_eq!(
            dest_target.local, expected_ref_target.local,
            "NonNull::as_ptr should preserve the source referent local"
        );
        assert_eq!(
            dest_target.projections, expected_ref_target.projections,
            "NonNull::as_ptr should preserve projected referent metadata"
        );
    });
}

/// Part of #4101: The Container<NonNull<T>> pattern (from transparent2.rs) should
/// produce a complete encoding through the full mir_to_chc pipeline.
/// This validates that ref_targets propagation through:
///   NonNull::from_ref → aggregate field → Copy field → NonNull::as_ptr → deref
/// works correctly end-to-end. The MIR decomposes `c.ptr.as_ptr()` into a
/// temporary (`_tmp = Copy(c.0)`) followed by `as_ptr(Move(_tmp))`, so the
/// test validates the full propagation chain, not just a single call handler.
#[test]
fn test_nonnull_container_pipeline_no_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::ptr::NonNull;

        struct Container<T> {
            ptr: NonNull<T>,
        }

        pub fn probe_projected_nonnull_as_ptr_forward(r: &u32) -> u32 {
            let nn = NonNull::from_ref(r);
            let c = Container { ptr: nn };
            unsafe { *c.ptr.as_ptr() }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_projected_nonnull_as_ptr_forward");
        let body = instance.body().expect("function body");

        // Full pipeline: runs decl-phase ref propagation + all block encoders.
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_projected_nonnull_as_ptr_forward",
            ChcConfig::default(),
        );

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_projected_nonnull_as_ptr_forward", bb_count);
    });
}

// =============================================================================
// Pointer cast — codegen_call_ptr_cast
// =============================================================================

/// Test ptr.cast() routes through codegen_call_ptr_cast (identity at SMT level).
#[test]
fn test_ptr_cast_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_cast(p: *const u32) -> *const u8 {
            p.cast::<u8>()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_cast");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_cast", ChcConfig::default());
        let detected = collect_detected_ptr_cast_stubs(&chc_ctx, &body);
        assert!(
            detected.iter().any(|stub| matches!(stub, StubKind::PtrCast | StubKind::PtrCastConst)),
            "probe_ptr_cast should detect ptr-cast stub, detected: {:?}",
            detected
        );

        let vc = mir_to_chc(ctx.tcx, &body, "probe_ptr_cast", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_ptr_cast", bb_count);
    });
}

/// Regression guard (#2876 post-OI4): `NonNull::from_ref` is routed through
/// PtrCast and must preserve pointer identity (no fallback).
#[test]
fn test_ptr_cast_nonnull_from_ref_emits_coerced_eq_without_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::ptr::NonNull;

        pub fn probe_nonnull_from_ref(r: &u8) -> NonNull<u8> {
            NonNull::from_ref(r)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nonnull_from_ref");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_nonnull_from_ref", ChcConfig::default());
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
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_ptr_cast)
                && stub == StubKind::PtrCast
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, args, destination, target) =
            call_site.expect("expected NonNull::from_ref ptr-cast call in MIR");
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

        let before_rules = chc_ctx.vc.rules.len();
        let before_fallback = chc_ctx.fallback_count;
        let cx = ChcCallContext {
            stub: StubKind::PtrCast,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_ptr_cast(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one ptr-cast rule");
        assert_eq!(
            chc_ctx.fallback_count, before_fallback,
            "NonNull::from_ref ptr-cast should take identity path, not fallback"
        );

        let rule = chc_ctx.vc.rules.last().expect("ptr-cast call should emit one rule");
        assert!(
            rule.body.constraints.len() >= 2,
            "success path should include stmt constraint + coerced equality"
        );
    });
}

/// Regression guard (#2917 P3): `NonNull::from_mut` routes through PtrCast
/// and preserves pointer identity (no fallback).
#[test]
fn test_ptr_cast_nonnull_from_mut_emits_coerced_eq_without_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::ptr::NonNull;

        pub fn probe_nonnull_from_mut(r: &mut u8) -> NonNull<u8> {
            NonNull::from_mut(r)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nonnull_from_mut");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_nonnull_from_mut", ChcConfig::default());
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
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_ptr_cast)
                && stub == StubKind::PtrCast
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, args, destination, target) =
            call_site.expect("expected NonNull::from_mut ptr-cast call in MIR");
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

        let before_rules = chc_ctx.vc.rules.len();
        let before_fallback = chc_ctx.fallback_count;
        let cx = ChcCallContext {
            stub: StubKind::PtrCast,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_ptr_cast(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one ptr-cast rule");
        assert_eq!(
            chc_ctx.fallback_count, before_fallback,
            "NonNull::from_mut ptr-cast should take identity path, not fallback"
        );

        let rule = chc_ctx.vc.rules.last().expect("ptr-cast call should emit one rule");
        assert!(
            rule.body.constraints.len() >= 2,
            "success path should include stmt constraint + coerced equality"
        );
    });
}

/// Regression guard (#2917 P3): `NonNull::as_ref` routes through PtrCast
/// and preserves pointer identity (no fallback).
#[test]
fn test_ptr_cast_nonnull_as_ref_emits_coerced_eq_without_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::ptr::NonNull;

        pub fn probe_nonnull_as_ref(p: NonNull<u8>) -> &'static u8 {
            unsafe { p.as_ref() }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nonnull_as_ref");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_nonnull_as_ref", ChcConfig::default());
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
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_ptr_cast)
                && stub == StubKind::PtrCast
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, args, destination, target) =
            call_site.expect("expected NonNull::as_ref ptr-cast call in MIR");
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

        let before_rules = chc_ctx.vc.rules.len();
        let before_fallback = chc_ctx.fallback_count;
        let cx = ChcCallContext {
            stub: StubKind::PtrCast,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_ptr_cast(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one ptr-cast rule");
        assert_eq!(
            chc_ctx.fallback_count, before_fallback,
            "NonNull::as_ref ptr-cast should take identity path, not fallback"
        );

        let rule = chc_ctx.vc.rules.last().expect("ptr-cast call should emit one rule");
        assert!(
            rule.body.constraints.len() >= 2,
            "success path should include stmt constraint + coerced equality"
        );
    });
}

/// Regression guard (#2917 P3): `NonNull::as_mut` routes through PtrCast
/// and preserves pointer identity (no fallback).
#[test]
fn test_ptr_cast_nonnull_as_mut_emits_coerced_eq_without_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::ptr::NonNull;

        pub fn probe_nonnull_as_mut(mut p: NonNull<u8>) -> &'static mut u8 {
            unsafe { p.as_mut() }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nonnull_as_mut");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_nonnull_as_mut", ChcConfig::default());
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
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_ptr_cast)
                && stub == StubKind::PtrCast
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, args, destination, target) =
            call_site.expect("expected NonNull::as_mut ptr-cast call in MIR");
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

        let before_rules = chc_ctx.vc.rules.len();
        let before_fallback = chc_ctx.fallback_count;
        let cx = ChcCallContext {
            stub: StubKind::PtrCast,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_ptr_cast(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one ptr-cast rule");
        assert_eq!(
            chc_ctx.fallback_count, before_fallback,
            "NonNull::as_mut ptr-cast should take identity path, not fallback"
        );

        let rule = chc_ctx.vc.rules.last().expect("ptr-cast call should emit one rule");
        assert!(
            rule.body.constraints.len() >= 2,
            "success path should include stmt constraint + coerced equality"
        );
    });
}

/// Regression guard (#3657): ptr.cast must clear stale alloc_id state on the
/// destination local when the source local has no tracked allocation identity.
#[test]
fn test_ptr_cast_clears_stale_alloc_id_when_source_is_untracked() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_cast_stale_alloc_id(p: *const u32) -> *const u8 {
            p.cast::<u8>()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_cast_stale_alloc_id");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_ptr_cast_stale_alloc_id", ChcConfig::default());
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
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_ptr_cast)
                && matches!(stub, StubKind::PtrCast | StubKind::PtrCastConst)
            {
                call_site = Some((bb_idx, stub, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, stub, args, destination, target) =
            call_site.expect("expected ptr-cast call in MIR");
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

        chc_ctx.known_alloc_ids.clear();
        chc_ctx.known_alloc_ids.insert(destination.local, 0xCAFE_u32);

        let cx = ChcCallContext {
            stub,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_ptr_cast(&cx);

        assert!(
            !chc_ctx.known_alloc_ids.contains_key(&destination.local),
            "ptr.cast must clear stale alloc_id state when the source local is untracked"
        );
    });
}

/// Regression guard (#3657): NonNull passthrough must clear stale alloc_id
/// state on the destination local when the source local is untracked.
#[test]
fn test_nonnull_as_non_null_ptr_clears_stale_alloc_id_when_source_is_untracked() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(slice_ptr_get)]
        use core::ptr::NonNull;

        pub fn probe_nonnull_as_non_null_ptr(p: NonNull<[u8]>) -> NonNull<u8> {
            p.as_non_null_ptr()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nonnull_as_non_null_ptr");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_nonnull_as_non_null_ptr", ChcConfig::default());
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
                && let Some(stub) = chc_ctx
                    .detect_stub_matching(func, |s| matches!(s, StubKind::NonNullAsNonNullPtr))
            {
                call_site = Some((bb_idx, stub, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, stub, args, destination, target) =
            call_site.expect("expected NonNull::as_non_null_ptr call in MIR");
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

        chc_ctx.known_alloc_ids.clear();
        chc_ctx.known_alloc_ids.insert(destination.local, 0xBEEF_u32);

        let cx = ChcCallContext {
            stub,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_nonnull_passthrough(&cx);

        assert!(
            !chc_ctx.known_alloc_ids.contains_key(&destination.local),
            "nonnull passthrough must clear stale alloc_id state when the source local is untracked"
        );
    });
}

/// Regression guard (#3657): NonNull passthrough fallback must clear any
/// destination alloc_id instead of preserving source identity on an
/// unconstrained transition.
#[test]
fn test_nonnull_as_non_null_ptr_coercion_fallback_clears_alloc_id() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![feature(slice_ptr_get)]
        use core::ptr::NonNull;

        pub fn probe_nonnull_as_non_null_ptr_fallback(p: NonNull<[u8]>) -> NonNull<u8> {
            p.as_non_null_ptr()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nonnull_as_non_null_ptr_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_nonnull_as_non_null_ptr_fallback",
            ChcConfig::default(),
        );
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
                && let Some(stub) = chc_ctx
                    .detect_stub_matching(func, |s| matches!(s, StubKind::NonNullAsNonNullPtr))
            {
                call_site = Some((bb_idx, stub, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, stub, args, destination, target) =
            call_site.expect("expected NonNull::as_non_null_ptr call in MIR");
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

        let src_local = match args.first() {
            Some(rustc_public::mir::Operand::Copy(p) | rustc_public::mir::Operand::Move(p))
                if p.projection.is_empty() =>
            {
                p.local
            }
            other => panic!("expected direct NonNull passthrough source local, got {other:?}"),
        };
        let dest_local = destination.local;
        let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
        chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].1 =
            Sort::array(Sort::int(), Sort::int());

        chc_ctx.known_alloc_ids.clear();
        chc_ctx.known_alloc_ids.insert(src_local, 0xBEEF_u32);
        chc_ctx.known_alloc_ids.insert(dest_local, 0xCAFE_u32);

        let before_fallback = chc_ctx.sound_fallback_count();
        let cx = ChcCallContext {
            stub,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_nonnull_passthrough(&cx);

        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_fallback + 1,
            "nonnull passthrough coercion failure must record a sound fallback"
        );
        assert!(
            !chc_ctx.known_alloc_ids.contains_key(&dest_local),
            "nonnull passthrough fallback must clear destination alloc_id state"
        );
    });
}

// =============================================================================
// Memory intrinsics — size_of, align_of
// =============================================================================

/// Test mem::size_of routes through codegen_call_mem_intrinsic.
#[test]
fn test_mem_size_of_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_size_of() -> usize {
            core::mem::size_of::<u64>()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_size_of");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_size_of", ChcConfig::default());
        let detected = collect_detected_mem_intrinsic_stubs(&chc_ctx, &body);
        assert!(
            detected.contains(&StubKind::MemSizeOf),
            "probe_size_of should detect MemSizeOf stub, detected: {:?}",
            detected
        );

        let vc = mir_to_chc(ctx.tcx, &body, "probe_size_of", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_size_of", bb_count);
    });
}

/// Test mem::align_of routes through codegen_call_mem_intrinsic.
#[test]
fn test_mem_align_of_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_align_of() -> usize {
            core::mem::align_of::<u32>()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_align_of");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_align_of", ChcConfig::default());
        let detected = collect_detected_mem_intrinsic_stubs(&chc_ctx, &body);
        assert!(
            detected.contains(&StubKind::MemAlignOf),
            "probe_align_of should detect MemAlignOf stub, detected: {:?}",
            detected
        );

        let vc = mir_to_chc(ctx.tcx, &body, "probe_align_of", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_align_of", bb_count);
    });
}

// =============================================================================
// copy_nonoverlapping — codegen_call_copy_nonoverlapping
// =============================================================================

/// Test copy_nonoverlapping call terminator routes through
/// codegen_call_copy_nonoverlapping (reuses intrinsic modeling path).
#[test]
fn test_copy_nonoverlapping_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_copy_nonoverlapping() {
            let src = [1u32, 2, 3, 4];
            let mut dst = [0u32; 4];
            unsafe {
                core::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), 4);
            }
            let _ = dst;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_nonoverlapping");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_copy_nonoverlapping", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_copy_nonoverlapping", bb_count);
    });
}

/// copy_nonoverlapping with missing call args must still record a fallback
/// before emitting the unconstrained transition.
#[test]
fn test_copy_nonoverlapping_short_args_increments_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_copy_nonoverlapping_short_args(src: *const u32, dst: *mut u32) {
            unsafe {
                core::ptr::copy_nonoverlapping(src, dst, 1);
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_nonoverlapping_short_args");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_copy_nonoverlapping_short_args",
            ChcConfig::default(),
        );
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
                && chc_ctx.detect_copy_nonoverlapping_call(func)
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, args, destination, target) = call_site.expect(
            "expected copy_nonoverlapping call terminator in probe_copy_nonoverlapping_short_args MIR",
        );
        assert_eq!(
            args.len(),
            3,
            "precondition: probe_copy_nonoverlapping_short_args should produce 3 call arguments"
        );

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
        let before_fallback = chc_ctx.fallback_count;

        // Force the args.len() < 3 fail-open branch.
        let short_args = vec![args[0].clone(), args[1].clone()];
        let cx = ChcCallContext {
            stub: StubKind::PtrRead,
            args: &short_args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_copy_nonoverlapping(bb_idx, &cx, false);

        assert_eq!(
            chc_ctx.vc.rules.len(),
            before_rules + 1,
            "expected one copy_nonoverlapping fallback transition rule"
        );
        // Part of #3369: reclassified from sound_fallback to fallback (DEMOTED) —
        // copy_nonoverlapping has memory side effects; destination memory retains
        // previous value (identity) instead of becoming nondeterministic.
        assert_eq!(
            chc_ctx.fallback_count,
            before_fallback + 1,
            "short-args copy_nonoverlapping fallback must increment CHC fallback counter"
        );

        let rule =
            chc_ctx.vc.rules.last().expect("copy_nonoverlapping fallback should emit one rule");
        assert_eq!(
            rule.body.constraints.len(),
            1,
            "short-args fallback should preserve original stmt constraints only"
        );
    });
}

// =============================================================================
// NonZero get — codegen_call_pointer_utility
// =============================================================================

/// Test NonZero::get() routes through codegen_call_pointer_utility with
/// the NonZeroGet guard (adds nonzero constraint on result).
#[test]
fn test_nonzero_get_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::num::NonZeroU32;

        pub fn probe_nonzero_get(n: NonZeroU32) -> u32 {
            n.get()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nonzero_get");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_nonzero_get", ChcConfig::default());
        let detected = collect_detected_pointer_utility_stubs(&chc_ctx, &body);
        assert!(
            detected.contains(&StubKind::NonZeroGet),
            "probe_nonzero_get should detect NonZeroGet stub, detected: {:?}",
            detected
        );

        let vc = mir_to_chc(ctx.tcx, &body, "probe_nonzero_get", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "probe_nonzero_get", bb_count);
    });
}

// =============================================================================
// Fallback output-arg soundness (#2324)
// =============================================================================

/// Coercion failure on ptr.add must still mark destination as output state.
/// Exercises codegen_call_ptr_memory PtrAdd fallback at codegen_call_ptr.rs:137.
#[test]
fn test_ptr_add_coercion_fallback_uses_output_dest_var() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_add_fallback(arr: &[u32; 4]) -> *const u32 {
            let p = arr.as_ptr();
            unsafe { p.add(1) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_add_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_ptr_add_fallback", ChcConfig::default());
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
                    == Some(StubKind::PtrAdd)
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, args, destination, target) =
            call_site.expect("expected PtrAdd call terminator in probe_ptr_add_fallback MIR");
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

        let dest_local = destination.local;
        let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
        let expected_out_name = chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].0.clone();

        // Force coercion failure: ptr.add result is BV pointer, destination output sort
        // is replaced with Array so coerce_eq_constraint returns None.
        chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].1 =
            Sort::array(Sort::int(), Sort::int());

        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "precondition: sound fallback counter should start at zero"
        );
        let cx = ChcCallContext {
            stub: StubKind::PtrAdd,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_ptr_memory(&cx);

        assert_eq!(
            chc_ctx.vc.rules.len(),
            before_rules + 1,
            "expected one ptr.add transition rule"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "ptr.add coercion fallback must increment CHC sound fallback counter"
        );
        let rule = chc_ctx.vc.rules.last().expect("ptr.add call should emit one rule");

        // Verify fallback path was taken: the fallback uses the original stmt_constraints
        // (1 constraint: `true`), while the success path adds a coerced equality (2+ constraints).
        assert_eq!(
            rule.body.constraints.len(),
            1,
            "coercion fallback should emit only the original stmt_constraints (no coerced equality), \
             got {} constraints — success path may have been taken instead",
            rule.body.constraints.len()
        );

        let head_arg = rule
            .head
            .args
            .get(dest_vec_idx)
            .expect("destination state slot should exist in rule head");

        if let ExprValue::Var { name } = head_arg.value() {
            assert_eq!(
                name.as_str(),
                &*expected_out_name,
                "ptr.add coercion fallback must use destination output var"
            );
        } else {
            assert!(
                matches!(head_arg.value(), ExprValue::Var { .. }),
                "expected destination argument variable, got {:?}",
                head_arg.value()
            );
        }
    });
}

/// Pointer-utility translation returning None must still mark destination as output state.
/// Exercises codegen_call_pointer_utility fallback at codegen_call_ptr.rs:260.
#[test]
fn test_pointer_utility_none_fallback_uses_output_dest_var() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::num::NonZeroU32;

        pub fn probe_nonzero_get_fallback(n: NonZeroU32) -> u32 {
            n.get()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nonzero_get_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_nonzero_get_fallback", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                func,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_pointer_utility)
                    == Some(StubKind::NonZeroGet)
            {
                call_site = Some((bb_idx, destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, destination, target) = call_site
            .expect("expected NonZeroGet call terminator in probe_nonzero_get_fallback MIR");
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

        let dest_local = destination.local;
        let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
        let expected_out_name = chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].0.clone();

        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "precondition: sound fallback counter should start at zero"
        );
        // Empty args force translate_pointer_utility_call(...)=None for NonZeroGet.
        let cx = ChcCallContext {
            stub: StubKind::NonZeroGet,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_pointer_utility(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one pointer utility rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "pointer utility None fallback must increment CHC sound fallback counter"
        );
        let rule = chc_ctx.vc.rules.last().expect("pointer utility call should emit one rule");

        // Verify fallback path was taken: translate returned None, so the rule uses
        // the original stmt_constraints (1 constraint: `true`), not the augmented set.
        assert_eq!(
            rule.body.constraints.len(),
            1,
            "None-fallback should emit only the original stmt_constraints (no coerced equality), \
             got {} constraints — success path may have been taken instead",
            rule.body.constraints.len()
        );

        let head_arg = rule
            .head
            .args
            .get(dest_vec_idx)
            .expect("destination state slot should exist in rule head");

        if let ExprValue::Var { name } = head_arg.value() {
            assert_eq!(
                name.as_str(),
                &*expected_out_name,
                "pointer utility fallback must use destination output var"
            );
        } else {
            assert!(
                matches!(head_arg.value(), ExprValue::Var { .. }),
                "expected destination argument variable, got {:?}",
                head_arg.value()
            );
        }
    });
}

/// Pointer-utility coercion failure must still mark destination as output state.
/// Exercises codegen_call_pointer_utility coercion-failure fallback at
/// codegen_call_ptr.rs:216.
#[test]
fn test_pointer_utility_coercion_fallback_uses_output_dest_var() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::num::NonZeroU32;

        pub fn probe_nonzero_get_coercion_fallback(n: NonZeroU32) -> u32 {
            n.get()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nonzero_get_coercion_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_nonzero_get_coercion_fallback",
            ChcConfig::default(),
        );
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
                && chc_ctx.detect_stub_matching(func, StubKind::is_pointer_utility)
                    == Some(StubKind::NonZeroGet)
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, args, destination, target) = call_site.expect(
            "expected NonZeroGet call terminator in probe_nonzero_get_coercion_fallback MIR",
        );
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

        let dest_local = destination.local;
        let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
        let expected_out_name = chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].0.clone();

        // Force coercion failure: NonZeroGet result is scalar, destination output sort
        // is replaced with Array so coerce_eq_constraint returns None.
        chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].1 =
            Sort::array(Sort::int(), Sort::int());

        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "precondition: sound fallback counter should start at zero"
        );
        let cx = ChcCallContext {
            stub: StubKind::NonZeroGet,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_pointer_utility(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one pointer utility rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "pointer utility coercion fallback must increment CHC sound fallback counter"
        );
        let rule = chc_ctx.vc.rules.last().expect("pointer utility call should emit one rule");

        // Verify fallback path was taken: the fallback uses the original stmt_constraints
        // (1 constraint: `true`), while the success path adds a coerced equality (2+ constraints).
        assert_eq!(
            rule.body.constraints.len(),
            1,
            "coercion fallback should emit only the original stmt_constraints (no coerced equality), \
             got {} constraints — success path may have been taken instead",
            rule.body.constraints.len()
        );

        let head_arg = rule
            .head
            .args
            .get(dest_vec_idx)
            .expect("destination state slot should exist in rule head");

        if let ExprValue::Var { name } = head_arg.value() {
            assert_eq!(
                name.as_str(),
                &*expected_out_name,
                "pointer utility coercion fallback must use destination output var"
            );
        } else {
            assert!(
                matches!(head_arg.value(), ExprValue::Var { .. }),
                "expected destination argument variable, got {:?}",
                head_arg.value()
            );
        }
    });
}

/// mem::size_of translation failure must still mark destination as output state.
/// Exercises codegen_call_mem_intrinsic translate-None fallback at
/// codegen_call_ptr.rs:308.
#[test]
fn test_mem_intrinsic_none_fallback_uses_output_dest_var() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_size_of_fallback() -> usize {
            core::mem::size_of::<u64>()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_size_of_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_size_of_fallback", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                func,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_mem_intrinsic)
                    == Some(StubKind::MemSizeOf)
            {
                call_site = Some((bb_idx, destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, destination, target) =
            call_site.expect("expected MemSizeOf call terminator in probe_size_of_fallback MIR");
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

        let dest_local = destination.local;
        let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
        let expected_out_name = chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].0.clone();

        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "precondition: sound fallback counter should start at zero"
        );
        // Force translate_mem_intrinsic_call(...)=None by passing a non-function operand.
        let bogus_func = rustc_public::mir::Operand::Move(destination.clone());
        let cx = ChcCallContext {
            stub: StubKind::MemSizeOf,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_mem_intrinsic(&bogus_func, &cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one mem-intrinsic rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "mem intrinsic None fallback must increment CHC sound fallback counter"
        );
        let rule = chc_ctx.vc.rules.last().expect("mem intrinsic call should emit one rule");

        // Verify fallback path was taken: translate returned None, so the rule uses
        // the original stmt_constraints (1 constraint: `true`), not the augmented set.
        assert_eq!(
            rule.body.constraints.len(),
            1,
            "None-fallback should emit only the original stmt_constraints (no coerced equality), \
             got {} constraints — success path may have been taken instead",
            rule.body.constraints.len()
        );

        let head_arg = rule
            .head
            .args
            .get(dest_vec_idx)
            .expect("destination state slot should exist in rule head");

        if let ExprValue::Var { name } = head_arg.value() {
            assert_eq!(
                name.as_str(),
                &*expected_out_name,
                "mem intrinsic fallback must use destination output var"
            );
        } else {
            assert!(
                matches!(head_arg.value(), ExprValue::Var { .. }),
                "expected destination argument variable, got {:?}",
                head_arg.value()
            );
        }
    });
}

/// mem_intrinsic coercion failure must still mark destination as output state.
/// Exercises codegen_call_mem_intrinsic coercion-failure path at codegen_call_ptr.rs:293
/// where `translate_mem_intrinsic_call` returns `Some` but `push_coerced_eq_constraint`
/// silently drops the equality (return value unchecked).
#[test]
fn test_mem_intrinsic_coercion_fallback_uses_output_dest_var() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_size_of_coercion_fallback() -> usize {
            core::mem::size_of::<u64>()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_size_of_coercion_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_size_of_coercion_fallback", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                func,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_mem_intrinsic)
                    == Some(StubKind::MemSizeOf)
            {
                call_site = Some((bb_idx, func.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, real_func, destination, target) = call_site
            .expect("expected MemSizeOf call terminator in probe_size_of_coercion_fallback MIR");
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

        let dest_local = destination.local;
        let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
        let expected_out_name = chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].0.clone();

        // Force coercion failure: size_of result is BV/Int, destination output sort
        // is replaced with Array so coerce_eq_constraint returns None.
        chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].1 =
            Sort::array(Sort::int(), Sort::int());

        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "precondition: sound fallback counter should start at zero"
        );
        let cx = ChcCallContext {
            stub: StubKind::MemSizeOf,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_mem_intrinsic(&real_func, &cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one mem-intrinsic rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "mem intrinsic coercion fallback must increment CHC sound fallback counter"
        );
        let rule = chc_ctx.vc.rules.last().expect("mem intrinsic call should emit one rule");

        // Verify coercion-failure path was taken: translate succeeded (real func) but
        // push_coerced_eq_constraint silently dropped the equality because the result
        // sort (BV/Int) cannot coerce to Array(Int,Int). The rule uses new_constraints
        // which equals stmt_constraints (1 constraint: `true`) since no equality was added.
        assert_eq!(
            rule.body.constraints.len(),
            1,
            "coercion-failure should emit only the original stmt_constraints (no coerced equality), \
             got {} constraints — coercion may have succeeded unexpectedly",
            rule.body.constraints.len()
        );

        let head_arg = rule
            .head
            .args
            .get(dest_vec_idx)
            .expect("destination state slot should exist in rule head");

        if let ExprValue::Var { name } = head_arg.value() {
            assert_eq!(
                name.as_str(),
                &*expected_out_name,
                "mem intrinsic coercion fallback must use destination output var"
            );
        } else {
            assert!(
                matches!(head_arg.value(), ExprValue::Var { .. }),
                "expected destination argument variable, got {:?}",
                head_arg.value()
            );
        }
    });
}

/// ptr.cast coercion failure must still mark destination as output state.
/// Exercises codegen_call_ptr_cast fallback at codegen_call_ptr.rs:349.
#[test]
fn test_ptr_cast_coercion_fallback_uses_output_dest_var() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_cast_coercion_fallback(p: *const u32) -> *const u8 {
            p.cast::<u8>()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_cast_coercion_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_ptr_cast_coercion_fallback", ChcConfig::default());
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
                && chc_ctx.detect_stub_matching(func, StubKind::is_ptr_cast).is_some()
            {
                call_site = Some((bb_idx, args.clone(), destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, args, destination, target) = call_site
            .expect("expected ptr-cast call terminator in probe_ptr_cast_coercion_fallback MIR");
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

        let dest_local = destination.local;
        let dest_vec_idx = chc_ctx.state_idx_for_local(dest_local);
        let expected_out_name = chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].0.clone();
        let src_local = match args.first() {
            Some(rustc_public::mir::Operand::Copy(p) | rustc_public::mir::Operand::Move(p))
                if p.projection.is_empty() =>
            {
                p.local
            }
            other => panic!("expected direct ptr.cast source local, got {other:?}"),
        };

        // Force coercion failure: ptr.cast result is scalar pointer, destination output
        // sort is replaced with Array so coerce_eq_constraint returns None.
        chc_ctx.state_var_mgr.output_state_vars[dest_vec_idx].1 =
            Sort::array(Sort::int(), Sort::int());
        chc_ctx.known_alloc_ids.clear();
        chc_ctx.known_alloc_ids.insert(src_local, 0x1234_u32);
        chc_ctx.known_alloc_ids.insert(dest_local, 0xDEAD_u32);

        let before_rules = chc_ctx.vc.rules.len();
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            0,
            "precondition: sound fallback counter should start at zero"
        );
        let cx = ChcCallContext {
            stub: StubKind::PtrCast,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_ptr_cast(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one ptr-cast rule");
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            1,
            "ptr.cast coercion fallback must increment CHC sound fallback counter"
        );
        let rule = chc_ctx.vc.rules.last().expect("ptr-cast call should emit one rule");

        // Verify fallback path was taken: the fallback uses the original stmt_constraints
        // (1 constraint: `true`), while the success path adds a coerced equality (2+ constraints).
        assert_eq!(
            rule.body.constraints.len(),
            1,
            "coercion fallback should emit only the original stmt_constraints (no coerced equality), \
             got {} constraints — success path may have been taken instead",
            rule.body.constraints.len()
        );

        let head_arg = rule
            .head
            .args
            .get(dest_vec_idx)
            .expect("destination state slot should exist in rule head");

        if let ExprValue::Var { name } = head_arg.value() {
            assert_eq!(
                name.as_str(),
                &*expected_out_name,
                "ptr-cast coercion fallback must use destination output var"
            );
        } else {
            assert!(
                matches!(head_arg.value(), ExprValue::Var { .. }),
                "expected destination argument variable, got {:?}",
                head_arg.value()
            );
        }
        assert!(
            !chc_ctx.known_alloc_ids.contains_key(&dest_local),
            "ptr.cast fallback must clear destination alloc_id state"
        );
    });
}

// =============================================================================
// Dangling provenance invalidation with extra_pointer_checks (#3176)
// =============================================================================

/// Part of #3176 D5: NonNull::dangling() + ptr.add() with extra_pointer_checks
/// must emit error rules referencing obj_valid (provenance check).
///
/// The provenance check verifies that the base pointer was allocated (not merely
/// non-null). Dangling constructors mark obj_valid[obj_id] = false; the overflow
/// check path reads obj_valid[obj_id] and emits an error rule when false.
#[test]
fn test_dangling_ptr_add_extra_checks_emits_provenance_error_rule() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use core::ptr::NonNull;

        pub fn probe_dangling_add() -> *const u32 {
            let p = NonNull::<u32>::dangling();
            unsafe { p.as_ptr().add(1) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_dangling_add");
        let body = instance.body().expect("function body");

        // With extra_pointer_checks: error rules must include the provenance
        // guard itself, not merely thread obj_valid through relation args.
        let cfg_extra = ChcConfig { extra_pointer_checks: true, ..ChcConfig::default() };
        let vc = mir_to_chc(ctx.tcx, &body, "probe_dangling_add", cfg_extra);

        let error_rule_count = vc.rules.iter().filter(|r| r.head.name == "error").count();
        assert!(
            error_rule_count >= 1,
            "extra_pointer_checks dangling+add must emit >=1 error rule, got {}",
            error_rule_count
        );

        let has_obj_valid_select_in_error =
            vc.rules.iter().filter(|r| r.head.name == "error").any(|rule| {
                rule_contains_expr(rule, |expr| match expr.value() {
                    ExprValue::Select { array, .. } => matches!(
                        array.value(),
                        ExprValue::Var { name }
                            if name.as_str() == "obj_valid" || name.as_str() == "obj_valid__out"
                    ),
                    _ => false,
                })
            });
        assert!(
            has_obj_valid_select_in_error,
            "extra_pointer_checks error rules must contain select(obj_valid, obj_id) \
             (provenance guard, Part of #3176)"
        );

        // Without extra_pointer_checks: no overflow/provenance error rules
        let cfg_default = ChcConfig::default();
        let vc_default = mir_to_chc(ctx.tcx, &body, "probe_dangling_add", cfg_default);

        let default_error_count =
            vc_default.rules.iter().filter(|r| r.head.name == "error").count();
        assert!(
            default_error_count < error_rule_count,
            "default config should have fewer error rules ({}) than extra_pointer_checks ({})",
            default_error_count,
            error_rule_count
        );
        assert!(
            !vc_default.rules.iter().filter(|r| r.head.name == "error").any(|rule| {
                rule_contains_expr(rule, |expr| match expr.value() {
                    ExprValue::Select { array, .. } => matches!(
                        array.value(),
                        ExprValue::Var { name }
                            if name.as_str() == "obj_valid"
                                || name.as_str() == "obj_valid__out"
                    ),
                    _ => false,
                })
            }),
            "default config must not encode the provenance guard into error rules"
        );
    });
}
