// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for codegen_call_alloc.rs — heap allocation call handling.
//!
//! Verifies that codegen_call_alloc produces structurally correct CHC VCs
//! including safety check error rules and heap state constraints for
//! Box::new / alloc / dealloc paths.
//!
//! Part of #2296 (chc/ test coverage gaps).

#![allow(clippy::unwrap_used)]

use std::collections::HashSet;

use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_alloc::CallAlloc;
use super::common::*;

fn find_box_new_call_site(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
) -> (usize, Vec<rustc_public::mir::Operand>, rustc_public::mir::Place, usize) {
    body.blocks
        .iter()
        .enumerate()
        .find_map(|(bb_idx, block)| {
            if let rustc_public::mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
                && chc_ctx.detect_alloc_stub(func) == Some(StubKind::BoxNew)
            {
                Some((bb_idx, args.clone(), destination.clone(), *target))
            } else {
                None
            }
        })
        .expect("expected BoxNew call terminator in MIR")
}

// =============================================================================
// Box::new — allocation via __rust_alloc
// =============================================================================

/// Box::new(value) triggers the allocation stub path. The pipeline should produce
/// a VC with rules for the allocation and proper heap state metadata.
#[test]
fn test_box_new_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_box_new(x: u32) -> Box<u32> {
            Box::new(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_new");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_box_new", ChcConfig::default());

        assert_vc_structure(&vc, "probe_box_new", body.blocks.len());

        // Should have rules (allocation creates transition rules)
        let has_transition = vc.rules.iter().any(|r| r.body.relation.is_some());
        assert!(has_transition, "Box::new should produce transition rules (allocation path)");
    });
}

/// Box::new with a larger type (u64) to exercise width-dependent allocation.
#[test]
fn test_box_new_u64_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_box_new_u64(x: u64) -> Box<u64> {
            Box::new(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_new_u64");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_box_new_u64", ChcConfig::default());

        assert_vc_structure(&vc, "probe_box_new_u64", body.blocks.len());
    });
}

/// Box::new([T; N]) must mirror element stores into flat heap memory arrays.
///
/// Regression for #3766: direct array payloads bypass the struct decomposition
/// path, so BoxNew must still bridge `[u32; 4]` into `mem_u32[addr + offset]`
/// stores or later deref/index reads become unconstrained.
#[test]
fn test_box_new_array_payload_mirrors_flat_heap_elements() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_box_new_array_read() -> u32 {
            let boxed = Box::new([11u32, 22u32, 33u32, 44u32]);
            boxed[2]
        }
    "#;

    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_new_array_read");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_box_new_array_read",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_box_new_array_read", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_box_new_array_read");
        assert!(
            vc_rules_contain_var(&vc, "mem_u32__out"),
            "Box::new([u32; 4]) should constrain the u32 heap output array"
        );
        assert!(
            any_constraint_str(&vc, |constraint| {
                constraint.contains("store")
                    && constraint.contains("mem_u32")
                    && (constraint.contains("#x0000000b")
                        || constraint.contains("#x00000016")
                        || constraint.contains("#x0000002c"))
            }),
            "Box::new([u32; 4]) should mirror concrete array element stores into mem_u32"
        );

        let fallback_count =
            get_chc_fallback_counts().get("probe_box_new_array_read").copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "Box::new([u32; 4]) should not increment CHC fallback count, got {fallback_count}"
        );

        let translation_drops = take_translation_drop_by_fn();
        let translation_drop_count =
            translation_drops.get("probe_box_new_array_read").copied().unwrap_or(0);
        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let site_reasons = translation_sites.get("probe_box_new_array_read");
        assert!(
            translation_drop_count <= 3,
            "Box::new([u32; 4]) translation-drop count should be minimal, got {translation_drop_count}, \
             site_reasons={site_reasons:?}"
        );
    });
}

const PTR_COMPARISON_REAL_FILE: &str =
    include_str!("../../../../../tests/trust_mc/PointerComparison/ptr_comparison.rs");

fn strip_ptr_comparison_for_unit_ctx(source: &str) -> String {
    let mut result = String::with_capacity(
        source.len()
            + "#![allow(dead_code)]\n#![allow(ambiguous_wide_pointer_comparisons)]\n".len(),
    );
    result.push_str("#![allow(dead_code)]\n");
    result.push_str("#![allow(ambiguous_wide_pointer_comparisons)]\n");
    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("#[cfg_attr(kani,") || trimmed.starts_with("// kani-expect:") {
            continue;
        }
        result.push_str(line);
        result.push('\n');
    }
    result
}

/// Mem-level exact-file localizer for `tests/trust_mc/PointerComparison/ptr_comparison.rs`.
///
/// Part of #4030: standalone compiletest runs Mem-level CHC, while the earlier
/// exact-file unit probe in `test_call_slice_range` used `ChcConfig::default()`
/// (Reg). This reproducer keeps the real committed source but matches the
/// standalone track level so translator-vs-compiletest drift is visible in one
/// unit-test lane.
#[test]
fn test_ptr_comparison_real_file_mem_level_localizer() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    let source = strip_ptr_comparison_for_unit_ctx(PTR_COMPARISON_REAL_FILE);
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_edition(&source, "2021", |ctx| {
        for fn_name in
            ["check_box_comparison", "check_slice_data_ptr", "check_slice_len", "check_thin_ptr"]
        {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(
                ctx.tcx,
                &body,
                fn_name,
                ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
            );
            let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
            let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
            let fn_sites = translation_sites.get(fn_name).cloned().unwrap_or_default();
            let call_dispatch_fallbacks = fn_sites
                .iter()
                .filter(|(reason, _)| *reason == "call_dispatch_fallback")
                .map(|(_, count)| *count)
                .sum::<usize>();
            let smt = crate::codegen_ay::emit_chc(&vc).to_string();
            let z3_result =
                run_z3_on_smt2_with_timeout(&smt, 30).unwrap_or_else(|err| format!("error:{err}"));

            assert_vc_structure(&vc, fn_name, body.blocks.len());
            eprintln!(
                "[ptr_comparison mem exact-file] {fn_name}: diagnostics_fallback_count={}, \
                 call_dispatch_fallback={call_dispatch_fallbacks}, z3_result={z3_result}, \
                 fn_sites={fn_sites:?}, translation_sites={translation_sites:?}",
                diagnostics.fallback_count.get(),
            );
        }
    });
}

#[test]
fn test_ptr_comparison_real_file_mem_level_after_inline_localizer() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    let source = strip_ptr_comparison_for_unit_ctx(PTR_COMPARISON_REAL_FILE);
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_edition(&source, "2021", |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "check_box_comparison");
        let body = instance.body().expect("function body");

        let mut pass = crate::kani_middle::transform::inline::FunctionInlinePass::new(
            crate::kani_middle::transform::inline::InlineConfig::default(),
        );
        let (_, inlined_body) =
            pass.transform_with_body_provider(ctx.tcx, body, instance, |callee_instance| {
                if !callee_instance.has_body() {
                    return None;
                }
                let callee_name = callee_instance.name();
                if crate::kani_middle::reachability::is_prefix_abstracted(&callee_name) {
                    return None;
                }
                callee_instance.body()
            });

        let mut probe_ctx = ChcCtx::new(
            ctx.tcx,
            &inlined_body,
            "check_box_comparison",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        probe_ctx.declare_block_relations();
        let block_order = {
            let cfg = crate::codegen_ay::loop_unroll::Cfg::from_body(&inlined_body);
            let topo_set: HashSet<usize> = cfg.topo_order.iter().copied().collect();
            let mut order = cfg.topo_order;
            for bb in 0..inlined_body.blocks.len() {
                if !topo_set.contains(&bb) {
                    order.push(bb);
                }
            }
            order
        };
        for bb_idx in block_order {
            let (_stmt_constraints, _output_args, modified_locals, _safety_checks) =
                probe_ctx.encode_block_statements(bb_idx);
            let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &inlined_body.blocks[bb_idx].terminator.kind
            else {
                continue;
            };
            let Some(callee_name) =
                func.ty(inlined_body.locals()).ok().and_then(|ty| match ty.kind() {
                    rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(def, _)) => {
                        Some(def.0.name())
                    }
                    _ => None,
                })
            else {
                continue;
            };
            if callee_name != "std::ops::Index::index" && callee_name != "core::ops::Index::index" {
                continue;
            }
            let (slice_arg, idx_arg) = probe_ctx.split_chc_slice_index_args(args);
            let slice_backing = probe_ctx.resolve_slice_backing(slice_arg, &modified_locals);
            let slice_ty = slice_arg.ty(inlined_body.locals()).ok().map(|ty| format!("{ty:?}"));
            let idx_ty = idx_arg
                .and_then(|arg| arg.ty(inlined_body.locals()).ok())
                .map(|ty| format!("{ty:?}"));
            let slice_local = match slice_arg {
                Operand::Copy(place) | Operand::Move(place) => {
                    Some((place.local, place.projection.clone()))
                }
                Operand::Constant(_) => None,
            };
            let idx_local = idx_arg.and_then(|arg| match arg {
                Operand::Copy(place) | Operand::Move(place) => {
                    Some((place.local, place.projection.clone()))
                }
                Operand::Constant(_) => None,
            });
            let slice_def = slice_local.as_ref().and_then(|(local, _)| {
                inlined_body.blocks.iter().flat_map(|block| block.statements.iter()).find_map(
                    |stmt| {
                        let rustc_public::mir::StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                            return None;
                        };
                        (lhs.local == *local && lhs.projection.is_empty())
                            .then(|| format!("{rhs:?}"))
                    },
                )
            });
            eprintln!(
                "[ptr_comparison after-inline index] bb={bb_idx}, callee={callee_name}, \
                 slice_local={slice_local:?}, slice_ty={slice_ty:?}, idx_local={idx_local:?}, \
                 idx_ty={idx_ty:?}, slice_def={slice_def:?}, modified_locals={modified_locals:?}, \
                 backing_resolved={}, backing_sort={:?}",
                slice_backing.is_some(),
                slice_backing.as_ref().map(|backing| backing.data.sort()),
            );
        }

        let call_names: Vec<_> = inlined_body
            .blocks
            .iter()
            .filter_map(|block| {
                let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                else {
                    return None;
                };
                let ty = func.ty(inlined_body.locals()).ok()?;
                let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(def, _)) =
                    ty.kind()
                else {
                    return None;
                };
                Some(def.0.name())
            })
            .collect();

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &inlined_body,
            "check_box_comparison",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let fn_sites = translation_sites.get("check_box_comparison").cloned().unwrap_or_default();
        let call_dispatch_fallbacks = fn_sites
            .iter()
            .filter(|(reason, _)| *reason == "call_dispatch_fallback")
            .map(|(_, count)| *count)
            .sum::<usize>();
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        let z3_result =
            run_z3_on_smt2_with_timeout(&smt, 30).unwrap_or_else(|err| format!("error:{err}"));

        assert_vc_structure(&vc, "check_box_comparison", inlined_body.blocks.len());
        eprintln!(
            "[ptr_comparison mem after-inline] diagnostics_fallback_count={}, \
             call_dispatch_fallback={call_dispatch_fallbacks}, z3_result={z3_result}, \
             call_names={call_names:?}, fn_sites={fn_sites:?}, translation_sites={translation_sites:?}",
            diagnostics.fallback_count.get(),
        );
    });
}

#[test]
fn test_check_box_comparison_range_backing_recovers_without_ref_targets() {
    let source = strip_ptr_comparison_for_unit_ctx(PTR_COMPARISON_REAL_FILE);
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_edition(&source, "2021", |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "check_box_comparison");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "check_box_comparison",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();

        let range_slice_args: Vec<_> = body
            .blocks
            .iter()
            .filter_map(|block| match &block.terminator.kind {
                rustc_public::mir::TerminatorKind::Call { func, args, .. }
                    if matches!(
                        chc_ctx.detect_stub(func),
                        Some(StubKind::IndexIndex | StubKind::SliceIndexIndex)
                    ) =>
                {
                    Some(args.clone())
                }
                _ => None,
            })
            .collect();

        assert_eq!(
            range_slice_args.len(),
            2,
            "check_box_comparison should contain exactly the two box subslice Range index calls"
        );

        let mut raw_ptr_locals = Vec::new();
        for args in &range_slice_args {
            let (slice_arg, _) = chc_ctx.split_chc_slice_index_args(&args);
            let slice_local = match slice_arg {
                Operand::Copy(place) | Operand::Move(place) => place.local,
                Operand::Constant(_) => panic!("slice receiver should be a local operand"),
            };

            assert!(
                !chc_ctx.ref_resolution.const_ref_values.contains_key(&slice_local),
                "precondition: box subslice receiver should not rely on const_ref_values"
            );
            assert!(
                !chc_ctx.ref_resolution.const_ref_slice_views.contains_key(&slice_local),
                "precondition: box subslice receiver should not rely on const_ref_slice_views"
            );

            let borrowed_place = body
                .blocks
                .iter()
                .flat_map(|block| block.statements.iter())
                .find_map(|stmt| {
                    let rustc_public::mir::StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                        return None;
                    };
                    if lhs.local != slice_local || !lhs.projection.is_empty() {
                        return None;
                    }
                    match rhs {
                        rustc_public::mir::Rvalue::Ref(_, _, place)
                        | rustc_public::mir::Rvalue::AddressOf(_, place) => Some(place.clone()),
                        _ => None,
                    }
                })
                .expect("slice receiver should have a defining ref assignment");
            assert!(
                matches!(
                    borrowed_place.projection.first(),
                    Some(rustc_public::mir::ProjectionElem::Deref)
                ),
                "box subslice receiver should borrow from a deref place, got {:?}",
                borrowed_place
            );
            raw_ptr_locals.push(borrowed_place.local);
        }

        for (idx, raw_ptr_local) in raw_ptr_locals.into_iter().enumerate() {
            chc_ctx.known_alloc_ids.insert(raw_ptr_local, 0xABCD_u32 + idx as u32);
        }
        chc_ctx.ref_resolution.ref_targets.clear();

        for args in range_slice_args {
            let (slice_arg, _) = chc_ctx.split_chc_slice_index_args(&args);
            let backing = chc_ctx
                .resolve_slice_backing(slice_arg, &HashSet::new())
                .expect("range receiver should recover backing from &_raw_ptr deref");

            assert!(
                backing.data.sort().is_array(),
                "range receiver backing should recover an Array-sort source, got {:?}",
                backing.data.sort()
            );
            assert!(
                ChcCtx::is_zero_pointer_width_bitvec(&backing.offset),
                "box subslice receiver should start from zero offset before range rebasing"
            );
            match backing.len.value() {
                ExprValue::BitVecConst { value, .. } => {
                    assert_eq!(
                        u64::try_from(value).ok(),
                        Some(2),
                        "box subslice receiver should retain fixed array len=2"
                    );
                }
                other => panic!("expected concrete len=2 for box subslice receiver, got {other:?}"),
            }
        }
    });
}

/// Regression for #3871: exact `double_coercion`-shaped nested BoxNew payloads
/// must preserve the dyn-trait payload through the outer allocation path.
#[test]
fn test_box_new_double_dyn_payload_solver_produces_proof() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        use std::boxed::Box;
        use std::ops::Deref;

        trait Identity {
            fn id(&self) -> u16;
        }

        struct Inner {
            id: u8,
        }

        impl Identity for Inner {
            fn id(&self) -> u16 {
                self.id.into()
            }
        }

        fn id_from_coerce<T>(identity: T) -> u16
        where
            T: Deref<Target = dyn Identity>,
        {
            identity.id()
        }

        pub fn probe_box_new_double_dyn_payload(id: u8) {
            let inner: Box<Box<dyn Identity>> = Box::new(Box::new(Inner { id }));
            assert!(inner.id() == id.into());
            assert!(id_from_coerce(*inner) == id.into());
        }
    "#;

    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_new_double_dyn_payload");
        let body = instance.body().expect("function body");

        let vc =
            mir_to_chc(ctx.tcx, &body, "probe_box_new_double_dyn_payload", ChcConfig::default());

        assert_vc_structure(&vc, "probe_box_new_double_dyn_payload", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_box_new_double_dyn_payload");

        let translation_drops = take_translation_drop_by_fn();
        let translation_drop_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let deref_below_mem = translation_drop_sites
            .get("probe_box_new_double_dyn_payload")
            .and_then(|reasons| reasons.get("deref_below_mem_level"))
            .copied()
            .unwrap_or(0);
        let unresolved_deref_loads = translation_drop_sites
            .get("probe_box_new_double_dyn_payload")
            .and_then(|reasons| reasons.get("rvalue_deref_load_unresolved"))
            .copied()
            .unwrap_or(0);
        assert_eq!(
            deref_below_mem, 0,
            "probe_box_new_double_dyn_payload should not fall back below Mem for heap-backed derefs, map={translation_drops:?}, sites={translation_drop_sites:?}"
        );
        assert_eq!(
            unresolved_deref_loads, 0,
            "probe_box_new_double_dyn_payload should not leave deref loads unresolved, map={translation_drops:?}, sites={translation_drop_sites:?}"
        );

        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        assert_z3_result(&smt, "unsat");
    });
}

/// Regression for dyn_fn_mut: Box::new on a promoted `&fn item` payload must
/// stay solver-visible through the BoxNew heap-store path.
#[test]
fn test_box_new_dyn_fn_mut_promoted_ref_solver_produces_proof() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn takes_dyn_fun(mut fun: Box<dyn FnMut(&mut i32)>, x_ptr: &mut i32) {
            fun(x_ptr)
        }

        fn mut_i32_ptr(x: &mut i32) {
            *x = x.wrapping_add(1);
        }

        pub fn probe_box_new_dyn_fn_mut_promoted_ref() {
            let mut x = 1;
            takes_dyn_fun(Box::new(&mut_i32_ptr), &mut x);
            assert!(x == 2);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_new_dyn_fn_mut_promoted_ref");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_box_new_dyn_fn_mut_promoted_ref",
            ChcConfig::default(),
        );

        assert_vc_structure(&vc, "probe_box_new_dyn_fn_mut_promoted_ref", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_box_new_dyn_fn_mut_promoted_ref");

        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        assert_z3_result(&smt, "unsat");
    });
}

/// Regression for #4000: wrapper-forwarded Box<dyn FnMut> must produce PROOF
/// at Mem track level (the default for compiletest/driver). The Reg-level test
/// above passes because Reg havoces loads through references, but the actual
/// compiletest uses Mem which requires correct store/select resolution for the
/// `&mut i32` argument bridging in fn_trait_dispatch.
#[test]
fn test_box_new_dyn_fn_mut_wrapper_mem_level_proof() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn takes_dyn_fun(mut fun: Box<dyn FnMut(&mut i32)>, x_ptr: &mut i32) {
            fun(x_ptr)
        }

        fn mut_i32_ptr(x: &mut i32) {
            *x = x.wrapping_add(1);
        }

        pub fn probe_dyn_fn_mut_wrapper_mem() {
            let mut x = 1;
            takes_dyn_fun(Box::new(&mut_i32_ptr), &mut x);
            assert!(x == 2);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_dyn_fn_mut_wrapper_mem");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_dyn_fn_mut_wrapper_mem",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_dyn_fn_mut_wrapper_mem", body.blocks.len());

        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        assert_z3_result(&smt, "unsat");
    });
}

/// Regression for #3975: predecessor-block BoxNew dyn payload must still
/// resolve through the shared normalization helper when `find_local_defining_rvalue_in_block`
/// cannot recover the source rvalue from the BoxNew block itself.
#[test]
fn test_box_new_predecessor_dyn_payload_solver_produces_proof() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        use std::boxed::Box;

        trait Identity {
            fn id(&self) -> u16;
        }

        struct Inner {
            id: u8,
        }

        impl Identity for Inner {
            fn id(&self) -> u16 {
                self.id.into()
            }
        }

        pub fn probe_box_new_predecessor_dyn_payload(flag: bool, id: u8, alt: u8) {
            let payload: Box<dyn Identity> = if flag {
                Box::new(Inner { id })
            } else {
                Box::new(Inner { id: alt })
            };
            let outer = Box::new(payload);
            let observed = outer.id();
            assert!(if flag { observed == id.into() } else { observed == alt.into() });
        }
    "#;

    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_new_predecessor_dyn_payload");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_box_new_predecessor_dyn_payload",
            ChcConfig::default(),
        );

        assert_vc_structure(&vc, "probe_box_new_predecessor_dyn_payload", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_box_new_predecessor_dyn_payload");

        let translation_drops = take_translation_drop_by_fn();
        let translation_drop_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let deref_below_mem = translation_drop_sites
            .get("probe_box_new_predecessor_dyn_payload")
            .and_then(|reasons| reasons.get("deref_below_mem_level"))
            .copied()
            .unwrap_or(0);
        let unresolved_deref_loads = translation_drop_sites
            .get("probe_box_new_predecessor_dyn_payload")
            .and_then(|reasons| reasons.get("rvalue_deref_load_unresolved"))
            .copied()
            .unwrap_or(0);
        assert_eq!(
            deref_below_mem, 0,
            "predecessor-block payload should not fall back below Mem, map={translation_drops:?}, sites={translation_drop_sites:?}"
        );
        assert_eq!(
            unresolved_deref_loads, 0,
            "predecessor-block payload should not leave deref loads unresolved, map={translation_drops:?}, sites={translation_drop_sites:?}"
        );
        let fallback_count = get_chc_fallback_counts()
            .get("probe_box_new_predecessor_dyn_payload")
            .copied()
            .unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "predecessor-block payload should not increment CHC fallback count, got {fallback_count}"
        );

        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        assert_z3_result(&smt, "unsat");
    });
}

/// BoxNew call handlers must drain pending checks instead of clearing them.
///
/// Regression for self-audit of #3589: `emit_boxnew_value_stores` can now
/// translate fallback operands that perform source-memory loads. Those checks
/// must become `error()` rules, not be silently discarded.
#[test]
fn test_box_new_call_handler_drains_pending_checks() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_box_new_drain_pending_checks(x: u32) -> Box<u32> {
            Box::new(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_new_drain_pending_checks");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_box_new_drain_pending_checks", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, args, destination, target) = find_box_new_call_site(&chc_ctx, &body);
        let from_rel =
            chc_ctx.block_relations.get(&bb_idx).expect("source relation for BoxNew block").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals: HashSet<usize> = HashSet::new();

        chc_ctx.heap_state.pending_checks.push(Expr::bool_const(false));
        let error_rules_before = chc_ctx.vc.rules.iter().filter(|r| r.head.name == "error").count();

        let cx = ChcCallContext {
            stub: StubKind::BoxNew,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_alloc(bb_idx, &cx);

        let error_rules_after = chc_ctx.vc.rules.iter().filter(|r| r.head.name == "error").count();
        assert!(
            error_rules_after > error_rules_before,
            "BoxNew call handler must emit error rules for pending checks"
        );
        assert!(
            chc_ctx.heap_state.pending_checks.is_empty(),
            "pending checks must be drained after BoxNew call handling"
        );
    });
}

// =============================================================================
// Drop-triggered deallocation
// =============================================================================

/// Dropping a Box triggers dealloc. The pipeline should handle the dealloc stub.
#[test]
fn test_box_drop_dealloc_pipeline() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_box_drop(x: Box<u32>) {
            drop(x);
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_drop");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_box_drop", ChcConfig::default());

        assert_vc_structure(&vc, "probe_box_drop", body.blocks.len());
    });
}

// =============================================================================
// Alloc stub detection
// =============================================================================

/// Part of #4169: Localizer for `alloc_zeroed_to_slice` CTREX.
/// The harness calls `alloc_zeroed(layout)`, writes bytes via `ptr.add(N)`,
/// then creates slices via `from_raw_parts`. Both the write and read paths must
/// resolve through the alloc heap pointer without sound fallbacks.
#[test]
fn test_alloc_zeroed_to_slice_localizer() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_alloc_zeroed_to_slice() -> u8 {
            use std::alloc::{Layout, alloc_zeroed};
            use std::slice::from_raw_parts;
            let layout = Layout::from_size_align(32, 8).unwrap();
            unsafe {
                let ptr = alloc_zeroed(layout);
                *ptr = 0x41;
                *ptr.add(1) = 0x42;
                *ptr.add(16) = 0x00;
                let _slice1 = from_raw_parts(ptr, 16);
                let _slice2 = from_raw_parts(ptr.add(16), 16);
                *ptr
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_name = "probe_alloc_zeroed_to_slice";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        let (vc, _, diagnostics) = chc_ctx.translate_with_diagnostics();
        assert_vc_structure(&vc, fn_name, body.blocks.len());
        let fb = diagnostics.fallback_count.get();
        assert_eq!(
            fb, 0,
            "alloc_zeroed_to_slice localizer: {fb} sound fallback(s) detected. \
             alloc_zeroed ptr writes/reads should resolve precisely, not overapprox."
        );
    });
}

/// Verify alloc stub detection on Box::new source.
#[test]
fn test_detect_alloc_stub_box_new() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_detect_alloc(x: u32) -> Box<u32> {
            Box::new(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_detect_alloc");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_detect_alloc", ChcConfig::default());

        let stubs: Vec<_> = body
            .blocks
            .iter()
            .filter_map(|block| {
                if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                {
                    chc_ctx.detect_alloc_stub(func)
                } else {
                    None
                }
            })
            .collect();
        assert_mir_pattern_found(!stubs.is_empty(), "alloc stub call in probe_detect_alloc MIR");
        // Fix #2736: BoxNew is now detected at ALL track levels (including Reg)
        // so that obj_valid/obj_size constraints are emitted for dealloc safety.
        assert!(
            stubs.iter().all(|s| matches!(
                s,
                StubKind::BoxNew
                    | StubKind::RustAlloc
                    | StubKind::RustAllocZeroed
                    | StubKind::RustDealloc
                    | StubKind::RustRealloc
            )),
            "unexpected alloc stub kinds: {:?}",
            stubs
        );
    });
}

// =============================================================================
// Shape B: boxnew_payload_store_drop marker accuracy
// =============================================================================

/// Shape B: `Box::new(x)` where the payload is a moved local with no defining
/// `Assign` statement (here: a function argument — the same shape as a call
/// result like `Box::new(kani::any())`). The primary path stores the whole
/// u32 payload verbatim, so the `boxnew_payload_store_drop` SoundHavoc marker
/// must NOT be recorded (it previously fired spuriously because the
/// aggregate-scan fallback ran unconditionally).
#[test]
fn test_box_new_moved_arg_scalar_payload_records_no_boxnew_drop() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_box_new_arg_scalar(x: u32) -> u32 {
            let b = Box::new(x);
            *b
        }
    "#;

    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_new_arg_scalar");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_box_new_arg_scalar",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_box_new_arg_scalar", body.blocks.len());
        // NOTE: the mem_u32__out lane-presence assertion is deliberately NOT
        // made here — the corpus unit ctx has a pre-existing lane redness
        // (test_box_new_array_payload_mirrors_flat_heap_elements fails the
        // same assertion at HEAD with the unmodified emitter). Lane presence
        // for this shape is exercised end-to-end by the driver (Box::new
        // read-back roundtrip proofs); this test pins the MARKER contract.

        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let boxnew_drops = translation_sites
            .get("probe_box_new_arg_scalar")
            .and_then(|reasons| reasons.get("boxnew_payload_store_drop"))
            .copied()
            .unwrap_or(0);
        assert_eq!(
            boxnew_drops, 0,
            "exact whole-value u32 payload store must not record \
             boxnew_payload_store_drop, got {boxnew_drops} (sites: {translation_sites:?})"
        );
    });
}

/// Shape B: `Box::new(a)` with a moved `[i64; 5]` argument. The #4099
/// decomposition stores every element verbatim, so no drop marker.
#[test]
fn test_box_new_moved_arg_array_payload_records_no_boxnew_drop() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_box_new_arg_array(a: [i64; 5]) -> i64 {
            let b = Box::new(a);
            b[2]
        }
    "#;

    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_new_arg_array");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_box_new_arg_array",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_box_new_arg_array", body.blocks.len());
        // NOTE: no mem_i64__out lane assertion — see the scalar test above
        // (pre-existing corpus-ctx lane redness); this test pins the MARKER
        // contract for the #4099 fully-decomposed array shape.

        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let boxnew_drops = translation_sites
            .get("probe_box_new_arg_array")
            .and_then(|reasons| reasons.get("boxnew_payload_store_drop"))
            .copied()
            .unwrap_or(0);
        assert_eq!(
            boxnew_drops, 0,
            "fully-decomposed [i64; 5] payload store must not record \
             boxnew_payload_store_drop, got {boxnew_drops} (sites: {translation_sites:?})"
        );
    });
}

/// Shape B fail-closed guard: a `[u8; 100]` payload exceeds the #4099
/// per-element decomposition bound (64), so the whole-array lane routes the
/// value through a fresh symbolic (aggregate gap). The exactness detector
/// must NOT claim this shape, and the audited SoundHavoc drop marker must
/// still be recorded.
#[test]
fn test_box_new_large_array_payload_keeps_boxnew_drop() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_box_new_large_array(a: [u8; 100]) -> u8 {
            let b = Box::new(a);
            b[7]
        }
    "#;

    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_new_large_array");
        let body = instance.body().expect("function body");

        let _vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_box_new_large_array",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let boxnew_drops = translation_sites
            .get("probe_box_new_large_array")
            .and_then(|reasons| reasons.get("boxnew_payload_store_drop"))
            .copied()
            .unwrap_or(0);
        assert!(
            boxnew_drops >= 1,
            "inexact [u8; 100] payload store must keep the fail-closed \
             boxnew_payload_store_drop marker (sites: {translation_sites:?})"
        );
    });
}
