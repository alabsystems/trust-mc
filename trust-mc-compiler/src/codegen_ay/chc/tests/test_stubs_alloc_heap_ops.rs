// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for `stubs_alloc_heap_ops.rs`.
//!
//! These tests target the extracted heap-op translators directly:
//! - `translate_rust_alloc`
//! - `translate_rust_dealloc`
//! - `translate_rust_realloc`
//!
//! Part of #2921.

#![allow(clippy::unwrap_used)]

use super::common::*;

const HEAP_OPS_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::alloc::{alloc, dealloc, realloc, Layout};

    pub fn probe_seed(x: u64) -> u64 {
        x.wrapping_add(1)
    }

    pub unsafe fn probe_dealloc_call() {
        let layout = Layout::new::<u64>();
        let ptr = unsafe { alloc(layout) };
        unsafe { dealloc(ptr, layout); }
    }

    pub unsafe fn probe_realloc_call() -> *mut u8 {
        let layout = Layout::new::<u64>();
        let ptr = unsafe { alloc(layout) };
        unsafe { realloc(ptr, layout, 32) }
    }

    pub unsafe fn probe_alloc_call() -> *mut u8 {
        let layout = Layout::new::<u64>();
        unsafe { alloc(layout) }
    }
"#;

const FORWARDED_CHECKED_LAYOUT_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::alloc::{alloc, realloc, Layout};

    pub unsafe fn probe_forwarded_checked_realloc() -> *mut u8 {
        let size = core::hint::black_box(16usize);
        let align = core::hint::black_box(8usize);
        let layout0 = Layout::from_size_align(size, align).unwrap();
        let layout1 = layout0;
        let layout2 = layout1;
        let ptr = unsafe { alloc(layout0) };
        unsafe { realloc(ptr, layout2, 32) }
    }
 "#;

const STALE_POINTER_CHECKED_LAYOUT_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::alloc::{alloc, realloc, Layout};

    pub unsafe fn probe_stale_pointer_checked_realloc() {
        let layout0 = Layout::from_size_align(16, 8).unwrap();
        let layout1 = layout0;
        let old_ptr = unsafe { alloc(layout0) };

        if !old_ptr.is_null() {
            unsafe { *old_ptr = 0xAB };
            let _new_ptr = unsafe { realloc(old_ptr, layout1, 32) };
            let _stale_read = unsafe { core::ptr::read_volatile(old_ptr) };
        }
    }
"#;

#[test]
fn test_translate_rust_alloc_empty_args_returns_symbolic_pointer() {
    with_test_ay_ctx_for_source(HEAP_OPS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_seed");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_seed", ChcConfig::default());

        let result = chc_ctx
            .translate_rust_alloc(StubKind::RustAlloc, &[], &HashSet::new())
            .expect("translate_rust_alloc should return symbolic result for empty args");

        let ptr = result.result.expect("alloc translation should return a pointer expression");
        assert_eq!(ptr.sort().bitvec_width(), Some(64), "alloc result pointer should be BV64");
        assert_eq!(
            result.heap_constraints.len(),
            2,
            "symbolic alloc should still emit obj_valid/obj_size store constraints"
        );
        assert!(
            result.safety_checks.is_empty(),
            "symbolic alloc fallback should skip resolved-arg safety checks; got {:?}",
            result.safety_checks
        );

        assert!(
            result.heap_constraints.iter().any(|c| constraint_tree_contains(c,
                &|e: &Expr| matches!(e.value(), ExprValue::Var { name } if name.contains("obj_valid__out")))),
            "alloc constraints should update obj_valid__out"
        );
        assert!(
            result.heap_constraints.iter().any(|c| constraint_tree_contains(c,
                &|e: &Expr| matches!(e.value(), ExprValue::Var { name } if name.contains("obj_size__out")))),
            "alloc constraints should update obj_size__out"
        );
    });
}

#[test]
fn test_translate_rust_dealloc_fail_open_returns_unit_result() {
    with_test_ay_ctx_for_source(HEAP_OPS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_dealloc_call");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_dealloc_call",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let modified_locals = HashSet::new();
        let mut dealloc_calls = 0usize;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && let Some(StubKind::RustDealloc) = chc_ctx.detect_alloc_stub(func)
            {
                dealloc_calls += 1;
                let result = chc_ctx.translate_rust_dealloc(args, &modified_locals);
                assert!(
                    result.is_some(),
                    "RustDealloc should fail open to Some(unit result), not None"
                );
                assert!(
                    result.expect("checked above").result.is_none(),
                    "RustDealloc translation should return unit result"
                );
            }
        }

        assert!(dealloc_calls > 0, "MIR should contain at least one RustDealloc call");
    });
}

#[test]
fn test_translate_rust_realloc_overflow_fails_closed() {
    with_test_ay_ctx_for_source(HEAP_OPS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_realloc_call");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_realloc_call",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let modified_locals = HashSet::new();

        // First pass: translate alloc calls to seed heap state for realloc.
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_alloc_stub(func)
                && matches!(stub, StubKind::RustAlloc | StubKind::RustAllocZeroed)
            {
                let _ = chc_ctx.translate_rust_alloc(stub, args, &modified_locals);
            }
        }

        // Force allocation-ID exhaustion before realloc translation.
        chc_ctx.heap_state.set_next_alloc_id(u32::MAX);

        // Second pass: realloc should fail closed under overflow.
        let mut saw_realloc_stub = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && let Some(StubKind::RustRealloc) = chc_ctx.detect_alloc_stub(func)
            {
                saw_realloc_stub = true;
                let result = chc_ctx.translate_rust_realloc(args, &modified_locals);
                assert!(
                    result.is_none(),
                    "RustRealloc should fail closed (None) when alloc IDs overflow"
                );
            }
        }

        assert!(saw_realloc_stub, "MIR should contain at least one RustRealloc call");
    });
}

#[test]
fn test_translate_rust_realloc_missing_new_size_fails_closed() {
    with_test_ay_ctx_for_source(HEAP_OPS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_alloc_call");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_alloc_call",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let mut alloc_args: Option<Vec<Operand>> = None;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_alloc_stub(func)
                && matches!(stub, StubKind::RustAlloc | StubKind::RustAllocZeroed)
            {
                alloc_args = Some(args.clone());
                break;
            }
        }

        let alloc_args = alloc_args.expect("MIR should contain a RustAlloc call");
        let result = chc_ctx.translate_rust_realloc(&alloc_args, &HashSet::new());
        assert!(
            result.is_none(),
            "realloc must fail closed when required new_size argument is missing"
        );
    });
}

#[test]
fn test_trace_arg_to_layout_pair_finds_cached_layout() {
    // Part of #3641: verify that trace_arg_to_layout_pair resolves a realloc
    // layout argument through MIR Copy chains to a known_layout_sizes entry.
    // This is the mechanism that enables checked Layout::from_size_align()
    // (which caches in known_layout_sizes via layout_semantic.rs) to propagate
    // to downstream realloc calls.
    with_test_ay_ctx_for_source(HEAP_OPS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_realloc_call");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_realloc_call",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Find the RustRealloc call and its layout argument.
        let mut realloc_layout_arg = None;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && let Some(StubKind::RustRealloc) = chc_ctx.detect_alloc_stub(func)
            {
                // The layout argument is typically args[1] (after ptr).
                realloc_layout_arg = args.get(1).cloned();
            }
        }
        let layout_arg = realloc_layout_arg.expect("MIR should have a RustRealloc with args");

        // Without cache: trace_arg_to_layout_pair should return None.
        assert!(
            chc_ctx.trace_arg_to_layout_pair(&layout_arg).is_none(),
            "trace_arg_to_layout_pair should return None when known_layout_sizes is empty"
        );

        // Populate known_layout_sizes for the layout argument's source local.
        if let Operand::Copy(place) | Operand::Move(place) = &layout_arg {
            chc_ctx.known_layout_sizes.insert(place.local, (8, 8));
        }

        // With cache populated: trace should succeed.
        let pair = chc_ctx.trace_arg_to_layout_pair(&layout_arg);
        assert!(
            pair.is_some(),
            "trace_arg_to_layout_pair should return Some((size, align)) when \
             the argument's local is in known_layout_sizes"
        );
        let (size, align) = pair.unwrap();
        assert_eq!(size, 8, "traced size should match cached value");
        assert_eq!(align, 8, "traced align should match cached value");
    });
}

#[test]
fn test_trace_arg_to_layout_pair_follows_forwarding_chain() {
    // Part of #3641: the real realloc harness forwards the checked Layout
    // through multiple locals before the call. The tracer must chase those
    // Copy/Move hops back to the cached source local.
    with_test_ay_ctx_for_source(FORWARDED_CHECKED_LAYOUT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_forwarded_checked_realloc");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_forwarded_checked_realloc",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let mut alloc_layout_local = None;
        let mut realloc_layout_arg = None;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
            {
                match chc_ctx.detect_alloc_stub(func) {
                    Some(StubKind::RustAlloc | StubKind::RustAllocZeroed) => {
                        if let Some(Operand::Copy(place) | Operand::Move(place)) = args.first() {
                            alloc_layout_local = Some(place.local);
                        }
                    }
                    Some(StubKind::RustRealloc) => {
                        realloc_layout_arg = args.get(1).cloned();
                    }
                    _ => {}
                }
            }
        }

        let alloc_layout_local =
            alloc_layout_local.expect("MIR should contain alloc(layout) for the checked source");
        let realloc_layout_arg =
            realloc_layout_arg.expect("MIR should contain realloc(ptr, layout, new_size)");

        chc_ctx.known_layout_sizes.insert(alloc_layout_local, (16, 8));
        assert_eq!(
            chc_ctx.trace_arg_to_layout_pair(&realloc_layout_arg),
            Some((16, 8)),
            "trace_arg_to_layout_pair should follow forwarded layout locals back to the cached source"
        );
    });
}

#[test]
fn test_mir_checked_layout_stale_pointer_realloc_avoids_generic_fallback() {
    // Part of #3641: the compiletest stale-pointer harness uses constant checked
    // Layout construction plus local forwarding. The CHC VC must use the precise
    // realloc model (`realloc_moved_*`) and avoid the generic fallback model
    // (`realloc_fallback_moved_*`).
    with_test_ay_ctx_for_source(STALE_POINTER_CHECKED_LAYOUT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_stale_pointer_checked_realloc");
        let body = instance.body().expect("function body");

        let saw_realloc = body.blocks.iter().any(|block| {
            matches!(
                &block.terminator.kind,
                rustc_public::mir::TerminatorKind::Call { func, .. }
                    if matches!(
                        ChcCtx::new(
                            ctx.tcx,
                            &body,
                            "probe_stale_pointer_checked_realloc",
                            ChcConfig::default(),
                        )
                        .detect_alloc_stub(func),
                        Some(StubKind::RustRealloc)
                    )
            )
        });
        assert_mir_pattern_found(saw_realloc, "RustRealloc call in checked stale-pointer MIR");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_stale_pointer_checked_realloc",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // #3728: Always-moved model — confirmed by obj_valid output presence,
        // and absence of generic fallback variable.
        // After scalarization, obj_valid__out may become obj_valid_at_0xN_bv32__out.
        assert!(
            vc_rules_contain_var_scalarized(&vc, "obj_valid", "__out"),
            "checked-layout stale-pointer realloc should reach the precise realloc model (always-moved #3728)"
        );
        assert!(
            !vc_rules_contain_var(&vc, "realloc_fallback_moved"),
            "checked-layout stale-pointer realloc should not route through the generic realloc fallback"
        );
    });
}

#[test]
fn test_mir_checked_layout_stale_pointer_realloc_splits_transition_rules() {
    // Part of #3728: the always-moved realloc model should emit a single
    // transition rule (no nondeterministic moved/in-place split) and should
    // not use ITE on metadata arrays.
    with_test_ay_ctx_for_source(STALE_POINTER_CHECKED_LAYOUT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_stale_pointer_checked_realloc");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_stale_pointer_checked_realloc",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // #3728: Always-moved model — no realloc_moved_* variable at all.
        assert!(
            !vc_rules_contain_var(&vc, "realloc_moved_"),
            "always-moved realloc model should NOT contain nondeterministic realloc_moved variable"
        );

        // obj_valid and obj_size outputs must be updated (unconditional invalidation + new size).
        // After scalarization, these may become per-index scalar variables.
        assert!(
            vc_rules_contain_var_scalarized(&vc, "obj_valid", "__out"),
            "always-moved realloc must update obj_valid output"
        );
        assert!(
            vc_rules_contain_var_scalarized(&vc, "obj_size", "__out"),
            "always-moved realloc must update obj_size output"
        );

        // No ITE on metadata arrays — the always-moved model writes directly.
        // After scalarization, store-chains become scalar equalities, so ITE
        // on metadata is structurally impossible. Check for ITE on constraints
        // that mention obj_valid or obj_size output variables (any form).
        let metadata_ite = vc.rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|constraint| {
                let s = constraint.to_string();
                let mentions_realloc_metadata = (s.contains("obj_valid") && s.contains("__out"))
                    || (s.contains("obj_size") && s.contains("__out"));
                mentions_realloc_metadata
                    && constraint_tree_contains(constraint, &|expr| {
                        matches!(expr.value(), ExprValue::Ite { .. })
                    })
            })
        });
        assert!(
            !metadata_ite,
            "realloc metadata updates should not use ITE (always-moved model #3728)"
        );
    });
}

// =============================================================================
// #3841: Dealloc size-mismatch false-PROOF regression at Ptr track level
// =============================================================================

/// Source for probe_dealloc_size_mismatch: alloc 64 bytes, dealloc with 32.
/// Matches the exact shape of `tests/ay/memory_safety_size_mismatch_fail.rs`.
const DEALLOC_SIZE_MISMATCH_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::alloc::{Layout, alloc, dealloc};

    pub unsafe fn probe_dealloc_size_mismatch() {
        let layout_alloc = Layout::from_size_align(64, 8).unwrap();
        let ptr = alloc(layout_alloc);
        if !ptr.is_null() {
            let layout_dealloc = Layout::from_size_align(32, 8).unwrap();
            dealloc(ptr, layout_dealloc);
        }
    }

    pub unsafe fn probe_dealloc_size_mismatch_with_store() {
        let layout_alloc = Layout::from_size_align(64, 8).unwrap();
        let ptr = alloc(layout_alloc);
        if !ptr.is_null() {
            *ptr = 42;
            let layout_dealloc = Layout::from_size_align(32, 8).unwrap();
            dealloc(ptr, layout_dealloc);
        }
    }
"#;

fn reset_dealloc_size_mismatch_translation_metadata() {
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_place_translation_drop_count();
    let _ = crate::codegen_ay::take_constant_translation_drop_count();
}

#[test]
fn test_dealloc_size_mismatch_at_ptr_level_emits_error_rule() {
    // Part of #3841: The compiletest harness `memory_safety_size_mismatch_fail.rs`
    // uses `--ay-chc-track=ptr` and expects CTREX but gets PROOF. If the error rule
    // with the obj_size size-match check is missing at Ptr level, the solver sees
    // no error condition and trivially returns PROOF (vacuous safety).
    with_test_ay_ctx_for_source(DEALLOC_SIZE_MISMATCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_dealloc_size_mismatch");
        let body = instance.body().expect("function body");

        // Use Ptr track level — matching the failing compiletest harness.
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_dealloc_size_mismatch",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "VC should have rules for dealloc size-mismatch probe");

        // Error relation must exist — dealloc safety checks produce error rules.
        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(
            has_error,
            "#3841: dealloc at Ptr level must generate error relation for safety checks"
        );

        // The size-match check requires obj_size in error-targeting rules.
        let has_obj_size_in_error = vc
            .rules
            .iter()
            .filter(|r| r.head.name == "error")
            .any(|rule| {
                rule.body.constraints.iter().any(|c| {
                    constraint_tree_contains(c, &|e: &Expr| {
                        matches!(e.value(), ExprValue::Var { name, .. } if name.contains("obj_size"))
                    })
                })
            });
        assert!(
            has_obj_size_in_error,
            "#3841: dealloc error rules must reference obj_size for size-match check at Ptr level"
        );

        // The VC must contain concrete size values (64 and 32).
        // Check Debug format: BitVecConst { value: 64, ... }
        let vc_str = format!("{:?}", vc);
        let has_concrete_64 = vc_str.contains("value: 64");
        let has_concrete_32 = vc_str.contains("value: 32");
        assert!(
            has_concrete_64 && has_concrete_32,
            "#3841: VC must contain BOTH concrete size constants (64 and 32) for dealloc \
             size-mismatch detection. has_64={has_concrete_64}, has_32={has_concrete_32}"
        );
    });
}

#[test]
fn test_dealloc_size_mismatch_at_mem_level_emits_error_rule() {
    // Baseline: same probe at Mem level should work (existing behavior).
    with_test_ay_ctx_for_source(DEALLOC_SIZE_MISMATCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_dealloc_size_mismatch");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_dealloc_size_mismatch",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let has_error = vc.relations.iter().any(|r| r.name == "error");
        assert!(has_error, "dealloc at Mem level must generate error relation");

        let has_obj_size_in_error = vc
            .rules
            .iter()
            .filter(|r| r.head.name == "error")
            .any(|rule| {
                rule.body.constraints.iter().any(|c| {
                    constraint_tree_contains(c, &|e: &Expr| {
                        matches!(e.value(), ExprValue::Var { name, .. } if name.contains("obj_size"))
                    })
                })
            });
        assert!(
            has_obj_size_in_error,
            "dealloc error rules must reference obj_size at Mem level (baseline)"
        );
    });
}

#[test]
fn test_dealloc_size_mismatch_ptr_vs_mem_concrete_sizes() {
    // Part of #3841: Compare VC output at Ptr vs Mem to diagnose the gap.
    // At Mem level, concrete sizes (64, 32) appear in obj_size Store constraints.
    // At Ptr level, they don't — the alloc/dealloc stubs fall back to symbolic sizes.
    with_test_ay_ctx_for_source(DEALLOC_SIZE_MISMATCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_dealloc_size_mismatch");
        let body = instance.body().expect("function body");

        let vc_ptr = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_dealloc_size_mismatch",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        let vc_mem = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_dealloc_size_mismatch",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Count rules containing concrete BV32 constants 64 (#x00000040) and 32 (#x00000020).
        let count_concrete = |vc: &ChcVc, hex: &str| -> usize {
            vc.rules.iter().filter(|r| format!("{:?}", r).contains(hex)).count()
        };

        // Check multiple formats for size constants
        let ptr_64 = count_concrete(&vc_ptr, "value: 64");
        let ptr_32 = count_concrete(&vc_ptr, "value: 32");
        let mem_64 = count_concrete(&vc_mem, "value: 64");
        let mem_32 = count_concrete(&vc_mem, "value: 32");

        // Both levels must see concrete size constants (64 and 32).
        assert!(ptr_64 > 0, "Ptr level must have concrete size 64");
        assert!(ptr_32 > 0, "Ptr level must have concrete size 32");
        assert!(mem_64 > 0, "Mem level must have concrete size 64");
        assert!(mem_32 > 0, "Mem level must have concrete size 32");

        // Neither level should fall back to symbolic size variables.
        let ptr_fallback = vc_ptr.rules.iter().any(|r| {
            let s = format!("{:?}", r);
            s.contains("__alloc_size") || s.contains("__dealloc_size")
        });
        let mem_fallback = vc_mem.rules.iter().any(|r| {
            let s = format!("{:?}", r);
            s.contains("__alloc_size") || s.contains("__dealloc_size")
        });
        assert!(!ptr_fallback, "Ptr level should not use symbolic alloc/dealloc size fallback");
        assert!(!mem_fallback, "Mem level should not use symbolic alloc/dealloc size fallback");

        // Both levels must produce identical rule and error-rule counts.
        assert_eq!(
            vc_ptr.rules.len(),
            vc_mem.rules.len(),
            "Ptr and Mem levels must produce same rule count for this harness"
        );
    });
}

#[test]
fn test_dealloc_size_mismatch_ptr_level_replays_layout_without_const_ref_drop() {
    reset_dealloc_size_mismatch_translation_metadata();

    with_test_ay_ctx_for_source(DEALLOC_SIZE_MISMATCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_dealloc_size_mismatch");
        let body = instance.body().expect("function body");

        let mut decl_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_dealloc_size_mismatch",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );
        decl_ctx.declare_block_relations();
        let (layout_arr_name, _) = decl_ctx
            .heap_state
            .type_arrays
            .get("std_alloc_Layout")
            .cloned()
            .expect("Ptr-level declaration should predeclare std_alloc_Layout");
        let layout_arr_out_name = crate::codegen_ay::names::out_name(&layout_arr_name);

        let translate_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_dealloc_size_mismatch",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );
        let (vc, _, diagnostics) = translate_ctx.translate_with_diagnostics();

        assert!(
            diagnostics.place_translation_drop.get() <= 2,
            "Ptr-level size-mismatch probe place drops should be minimal, got {}",
            diagnostics.place_translation_drop.get()
        );
        assert!(
            diagnostics.const_translation_drop.get() <= 2,
            "Ptr-level size-mismatch probe const drops should be minimal, got {}",
            diagnostics.const_translation_drop.get()
        );

        let translation_drops = take_translation_drop_by_fn();
        let drop_count = translation_drops.get("probe_dealloc_size_mismatch").copied().unwrap_or(0);
        assert!(
            drop_count <= 2,
            "probe_dealloc_size_mismatch translation drops should be minimal, got {drop_count}, map={translation_drops:?}"
        );

        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let has_const_ref_drop = translation_sites
            .get("probe_dealloc_size_mismatch")
            .is_some_and(|sites| sites.contains_key("const_ref_array_unregistered"));
        assert!(
            !has_const_ref_drop,
            "probe_dealloc_size_mismatch should not record const_ref_array_unregistered, sites={translation_sites:?}"
        );

        let vc_str = format!("{:?}", vc);
        assert!(
            vc_str.contains(layout_arr_out_name.as_str()),
            "Ptr-level translation should replay the promoted Layout array into bb0 store chains, missing {layout_arr_out_name} in VC"
        );
    });
}

#[test]
fn test_dealloc_size_mismatch_with_deref_store_emits_error_rule() {
    // Part of #3841: The compiletest harness has `*ptr = 42` before dealloc.
    // This triggers Mem promotion. Does the error rule survive the deref store?
    with_test_ay_ctx_for_source(DEALLOC_SIZE_MISMATCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_dealloc_size_mismatch_with_store");
        let body = instance.body().expect("function body");

        // At Mem level (the effective level after auto-promotion from Ptr).
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_dealloc_size_mismatch_with_store",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert!(!vc.rules.is_empty(), "VC should have rules");

        let error_rules: Vec<_> = vc.rules.iter().filter(|r| r.head.name == "error").collect();
        assert!(
            !error_rules.is_empty(),
            "#3841: dealloc with *ptr=42 must still generate error rules at Mem level"
        );

        let has_obj_size_in_error = error_rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|c| {
                constraint_tree_contains(c, &|e: &Expr| {
                    matches!(e.value(), ExprValue::Var { name, .. } if name.contains("obj_size"))
                })
            })
        });
        assert!(
            has_obj_size_in_error,
            "#3841: error rules must reference obj_size even with *ptr=42 deref store"
        );
        let has_concrete_obj_size_index_in_error = error_rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|c| {
                constraint_tree_contains(c, &|e: &Expr| match e.value() {
                    ExprValue::Select { array, index } => {
                        constraint_tree_contains(array, &|inner| {
                            matches!(inner.value(), ExprValue::Var { name, .. } if name.contains("obj_size"))
                        }) && matches!(index.value(), ExprValue::BitVecConst { width, .. } if *width == 32)
                            && !constraint_tree_contains(index, &|inner| {
                                matches!(inner.value(), ExprValue::BvExtract { .. })
                            })
                    }
                    _ => false,
                })
            })
        });
        assert!(
            has_concrete_obj_size_index_in_error,
            "#3841: dealloc error rules must index obj_size with a concrete alloc id, \
             not only a raw pointer extract"
        );

        // Verify concrete sizes (64 and 32) are present.
        let vc_str = format!("{:?}", vc);
        assert!(vc_str.contains("value: 64"), "Must have concrete size 64");
        assert!(vc_str.contains("value: 32"), "Must have concrete size 32");

        let total_rules = vc.rules.len();
        let error_count = error_rules.len();
        assert!(
            total_rules >= 3,
            "#3841: expected at least 3 rules, got {total_rules} (error_rules={error_count})"
        );
    });
}

fn expr_selects_array_at_obj_id(expr: &Expr, array_name: &str, obj_id: u32) -> bool {
    constraint_tree_contains(expr, &|node| match node.value() {
        ExprValue::Select { array, index } => {
            constraint_tree_contains(
                array,
                &|inner| matches!(inner.value(), ExprValue::Var { name, .. } if name.contains(array_name)),
            ) && matches!(
                index.value(),
                ExprValue::BitVecConst { value, width }
                    if *width == 32 && *value == obj_id.into()
            )
        }
        _ => false,
    })
}

fn expr_stores_bool_to_array_at_obj_id(
    expr: &Expr,
    array_name: &str,
    obj_id: u32,
    expected: bool,
) -> bool {
    constraint_tree_contains(expr, &|node| match node.value() {
        ExprValue::Store { array, index, value } => {
            constraint_tree_contains(
                array,
                &|inner| matches!(inner.value(), ExprValue::Var { name, .. } if name.contains(array_name)),
            ) && matches!(
                index.value(),
                ExprValue::BitVecConst { value: idx, width }
                    if *width == 32 && *idx == obj_id.into()
            ) && matches!(value.value(), ExprValue::BoolConst(actual) if *actual == expected)
        }
        _ => false,
    })
}

fn expr_uses_bv_extract_index(expr: &Expr, array_name: &str) -> bool {
    constraint_tree_contains(expr, &|node| match node.value() {
        ExprValue::Select { array, index } => {
            constraint_tree_contains(
                array,
                &|inner| matches!(inner.value(), ExprValue::Var { name, .. } if name.contains(array_name)),
            ) && constraint_tree_contains(index, &|inner| {
                matches!(inner.value(), ExprValue::BvExtract { .. })
            })
        }
        ExprValue::Store { array, index, .. } => {
            constraint_tree_contains(
                array,
                &|inner| matches!(inner.value(), ExprValue::Var { name, .. } if name.contains(array_name)),
            ) && constraint_tree_contains(index, &|inner| {
                matches!(inner.value(), ExprValue::BvExtract { .. })
            })
        }
        _ => false,
    })
}

#[test]
fn test_dealloc_size_mismatch_ptr_uses_alloc_obj_id() {
    // Part of #3841: translating the alloc call first must let dealloc recover
    // the same concrete allocation id for obj_size checks and obj_valid invalidation.
    with_test_ay_ctx_for_source(DEALLOC_SIZE_MISMATCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_dealloc_size_mismatch_with_store");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_dealloc_size_mismatch_with_store",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations(); // state vars needed for operand translation

        let modified_locals = HashSet::new();
        let mut alloc_obj_id = None;
        let mut dealloc_result = None;

        for block in &body.blocks {
            let rustc_public::mir::TerminatorKind::Call { func, args, destination, .. } =
                &block.terminator.kind
            else {
                continue;
            };

            match chc_ctx.detect_alloc_stub(func) {
                Some(stub @ (StubKind::RustAlloc | StubKind::RustAllocZeroed)) => {
                    let result = chc_ctx
                        .translate_rust_alloc(stub, args, &modified_locals)
                        .expect("alloc translation should succeed");
                    let obj_id =
                        result.alloc_obj_id.expect("alloc should assign a concrete obj_id");
                    chc_ctx.record_alloc_dest(destination.local, Some(obj_id));
                    alloc_obj_id = Some(obj_id);
                }
                Some(StubKind::RustDealloc) => {
                    dealloc_result = Some(chc_ctx.translate_rust_dealloc(args, &modified_locals));
                }
                _ => {}
            }
        }

        let alloc_obj_id = alloc_obj_id.expect("probe must contain a tracked alloc call");
        let dealloc_result = dealloc_result
            .expect("probe must contain a RustDealloc call")
            .expect("dealloc translation should succeed");

        assert!(
            dealloc_result.safety_checks.iter().any(|expr| expr_selects_array_at_obj_id(
                expr,
                "obj_size",
                alloc_obj_id
            )),
            "#3841: dealloc safety checks must select obj_size using alloc obj_id {alloc_obj_id}"
        );
        assert!(
            dealloc_result.heap_constraints.iter().any(|expr| {
                expr_stores_bool_to_array_at_obj_id(expr, "obj_valid", alloc_obj_id, false)
            }),
            "#3841: dealloc heap constraints must invalidate obj_valid at alloc obj_id {alloc_obj_id}"
        );
        assert!(
            !dealloc_result
                .safety_checks
                .iter()
                .any(|expr| expr_uses_bv_extract_index(expr, "obj_size")),
            "#3841: obj_size selects should not rely on raw BvExtract indices once alloc id is known"
        );
        assert!(
            !dealloc_result
                .heap_constraints
                .iter()
                .any(|expr| expr_uses_bv_extract_index(expr, "obj_valid")),
            "#3841: obj_valid invalidation should not rely on raw BvExtract indices once alloc id is known"
        );
    });
}

#[test]
fn test_dealloc_size_mismatch_with_store_z3_returns_sat() {
    // Part of #3841: End-to-end solver test. The VC has error rules for
    // dealloc size mismatch (64 != 32). Z3 PDR should return "sat"
    // (counterexample found = error is reachable). If Z3 returns "unsat",
    // the false PROOF is in the SMT2 encoding, not the solver.
    with_test_ay_ctx_for_source(DEALLOC_SIZE_MISMATCH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_dealloc_size_mismatch_with_store");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_dealloc_size_mismatch_with_store",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let smt = crate::codegen_ay::emit_chc(&vc).to_string();

        // Dump SMT for manual inspection on failure.
        let error_rule_count = vc.rules.iter().filter(|r| r.head.name == "error").count();
        let total_rules = vc.rules.len();

        match run_z3_on_smt2_with_timeout(&smt, 30) {
            Ok(result) => {
                assert_eq!(
                    result,
                    "sat",
                    "#3841: Z3 should return 'sat' (CTREX) for dealloc size mismatch \
                     (64 != 32). Got '{result}'. \
                     total_rules={total_rules}, error_rules={error_rule_count}. \
                     SMT ({} bytes):\n{}",
                    smt.len(),
                    &smt[..smt.len().min(2000)]
                );
            }
            Err(e) => {
                panic!(
                    "#3841: Z3 execution failed: {e}. \
                     total_rules={total_rules}, error_rules={error_rule_count}"
                );
            }
        }
    });
}
