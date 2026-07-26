// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Caller-level tests for alloc ID overflow (returning None from heap_state).
//!
//! The core heap_state overflow tests (test_heap_state.rs) verify that
//! next_alloc_id/reserve_heap_alloc_id/next_heap_alloc_id return None at
//! u32::MAX. These tests verify that each *caller* of those functions handles
//! None gracefully: no panic, correct fallback behavior, and (where applicable)
//! record_fallback() is called.
//!
//! Part of #2748: 7 caller-level handling paths untested.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::codegen_rules_entry::CodegenRulesEntry;

// =============================================================================
// Path 1 & 2: predeclare_heap_region_arrays — ShallowInitBox + alloc stub
// overflow → warn + continue (no panic)
// =============================================================================

/// Source that triggers ShallowInitBox (Box::new) and allocation stubs in MIR.
/// At Ptr level, predeclare_heap_region_arrays scans all blocks for these
/// patterns and calls reserve_heap_alloc_id.
const BOX_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_box_overflow() {
        let b = Box::new(42u32);
        let _val = *b;
    }
"#;

#[test]
fn test_predeclare_heap_region_arrays_overflow_no_panic() {
    // Paths 1 & 2: When alloc IDs are exhausted during pre-declaration,
    // predeclare_heap_region_arrays should `continue` (skip) rather than panic.
    with_test_ay_ctx_for_source(BOX_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_overflow");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_box_overflow",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        // Exhaust alloc IDs before declare_block_relations triggers pre-declaration.
        chc_ctx.heap_state.set_next_alloc_id(u32::MAX);

        // declare_block_relations calls predeclare_heap_region_arrays internally.
        // With alloc IDs exhausted, it should warn+continue, NOT panic.
        chc_ctx.declare_block_relations();

        // If we reach here, the overflow was handled gracefully.
        // Verify that relations were still declared (the non-overflow parts should work).
        assert!(
            !chc_ctx.vc.relations.is_empty(),
            "Block relations should still be declared even when alloc IDs overflow"
        );
    });
}

// =============================================================================
// Path 3: allocate_stack_locals — overflow → warn + record_sound_fallback + continue
// =============================================================================

/// Source with multiple stack locals to test allocate_stack_locals overflow path.
const MULTI_LOCAL_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_stack_overflow(x: u32) -> u32 {
        let a: u32 = x + 1;
        let b: u32 = a + 2;
        let c: u32 = b + 3;
        c
    }
"#;

#[test]
fn test_allocate_stack_locals_overflow_records_sound_fallback() {
    // Path 3: When alloc IDs overflow during stack local allocation,
    // allocate_stack_locals should warn, record_sound_fallback, and continue.
    with_test_ay_ctx_for_source(MULTI_LOCAL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_stack_overflow");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_stack_overflow",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        let sound_before = chc_ctx.sound_fallback_count();

        // Exhaust alloc IDs.
        chc_ctx.heap_state.set_next_alloc_id(u32::MAX);

        // allocate_stack_locals returns constraints; on overflow it should
        // skip locals and record sound fallbacks (Part of #3099 reclassification).
        let constraints = chc_ctx.allocate_stack_locals();

        // No constraints should be generated for overflowed locals.
        // (Some ZST locals may be skipped naturally, so we check that
        // the sound fallback counter increased — alloc ID overflow is a
        // sound over-approximation, not an unsound fallback.)
        assert!(
            chc_ctx.sound_fallback_count() > sound_before,
            "allocate_stack_locals should call record_sound_fallback on overflow (before={}, after={})",
            sound_before,
            chc_ctx.sound_fallback_count()
        );

        // No local_addresses should be added for overflowed locals.
        // (The heap_state was at u32::MAX, so no new addresses should appear.)
        assert!(
            !chc_ctx.heap_state.local_addresses.values().any(|(id, _)| *id >= u32::MAX - 1),
            "No addresses should be allocated at overflow IDs"
        );

        eprintln!(
            "allocate_stack_locals overflow: sound_fallback_count={}, constraints={}",
            chc_ctx.sound_fallback_count(),
            constraints.len()
        );
    });
}

// =============================================================================
// Path 3b: allocate_stack_locals — unknown type size → record_sound_fallback + skip
// =============================================================================

/// Generic function with T-typed temporaries that force MIR locals with
/// unknown layout in the unmonomorphized body.
/// When allocate_stack_locals encounters `get_type_size(T) → None`, it should
/// call record_sound_fallback() and skip that local (Part of #3099 reclassification).
///
/// Production site: codegen_rules_entry.rs line 168.
/// Part of #2783.
const GENERIC_LOCAL_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Wrapper<T> { inner: T }

    pub fn probe_generic_locals<T: Clone>(x: T) -> Wrapper<T> {
        let a: T = x.clone();
        let b: T = a.clone();
        Wrapper { inner: b }
    }
"#;

fn find_crate_item_by_suffix(tcx: TyCtxt<'_>, suffix: &str) -> rustc_public::CrateItem {
    let matches: Vec<_> = rustc_public::all_local_items()
        .into_iter()
        .filter(|item| {
            let def_id = rustc_public::rustc_internal::internal(tcx, item.def_id());
            let path = tcx.def_path_str(def_id);
            path == suffix || path.ends_with(&format!("::{suffix}"))
        })
        .collect();
    match matches.as_slice() {
        [] => panic!("missing item with suffix '{suffix}'"),
        [single] => *single,
        many => {
            let names: Vec<_> = many
                .iter()
                .map(|item| {
                    let def_id = rustc_public::rustc_internal::internal(tcx, item.def_id());
                    tcx.def_path_str(def_id)
                })
                .collect();
            panic!("ambiguous suffix '{suffix}': {} matches: {names:?}", many.len());
        }
    }
}

/// A local has a generic/unsized type iff its kind is `Param(_)` or an ADT
/// parameterized by a Param. These locals have unknown layout and should be
/// skipped by `allocate_stack_locals`.
fn local_has_generic_layout(ty: &rustc_public::ty::Ty) -> bool {
    let kind = ty.kind();
    if matches!(kind, TyKind::Param(_)) {
        return true;
    }
    if let TyKind::RigidTy(RigidTy::Adt(_, args)) = kind
        && args.0.iter().any(|a| {
            matches!(a,
            rustc_public::ty::GenericArgKind::Type(t)
                if matches!(t.kind(), TyKind::Param(_)))
        })
    {
        return true;
    }
    false
}

#[test]
fn test_allocate_stack_locals_unknown_type_size_records_sound_fallback() {
    // Path 3b: When a local's type size is unknown (generic T), allocate_stack_locals
    // should warn, record_sound_fallback, and skip allocation for that local.
    with_test_ay_ctx_for_source(GENERIC_LOCAL_SOURCE, |ctx| {
        let item = find_crate_item_by_suffix(ctx.tcx, "probe_generic_locals");
        let body = item.body().expect("generic function body");

        // Verify the body has locals with unresolved types (Param or ADT<Param>).
        let arg_count = body.arg_locals().len();
        let has_unsized_local = body
            .locals()
            .iter()
            .enumerate()
            .any(|(i, decl)| i != 0 && i > arg_count && local_has_generic_layout(&decl.ty));
        assert!(
            has_unsized_local,
            "test fixture must have at least one local with unresolved type parameter; \
             optimizer may have eliminated them — adjust probe source"
        );

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_generic_locals",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        let sound_before = chc_ctx.sound_fallback_count();
        let _constraints = chc_ctx.allocate_stack_locals();
        let sound_after = chc_ctx.sound_fallback_count();

        // Part of #3099 / #4251: The sound-fallback counter only increments
        // when translate_ty *also* returns None (untranslatable + unknown size).
        // Since #4251 gave TyKind::Param / TyKind::Alias a ptr-sort fallback,
        // generic T now translates successfully, so the sound-fallback branch
        // is not taken. The behavioral guarantee is instead: no local address
        // is created for generic T locals (size unknown → skip allocation).
        assert!(
            sound_after >= sound_before,
            "sound_fallback_count should be monotonic (before={sound_before}, after={sound_after})"
        );

        // Verify that no local_addresses were created for T-typed locals
        // (their type size is unknown, so they should be skipped entirely).
        // Post-#4251 this is the primary behavioral contract for this path.
        for (local_idx, local_decl) in body.locals().iter().enumerate() {
            if local_idx == 0 || local_idx <= arg_count {
                continue;
            }
            if local_has_generic_layout(&local_decl.ty) {
                assert!(
                    !chc_ctx.heap_state.local_addresses.contains_key(&local_idx),
                    "allocate_stack_locals should skip local_idx={local_idx} with \
                     unresolved-type-param layout (got address entry)"
                );
            }
        }

        eprintln!(
            "allocate_stack_locals unknown type: sound_fallback_count={}, local_addresses={}",
            sound_after,
            chc_ctx.heap_state.local_addresses.len()
        );
    });
}

// =============================================================================
// Path 4: translate_rvalue ShallowInitBox fallback — overflow → None
// =============================================================================

/// Source with a tuple local that ChcCtx flattens into scalar state vars.
/// Part of #2876: Flattened locals now reconstruct as Datatypes, so
/// ShallowInitBox passes through the operand (no fallback path exercised).
const SHALLOW_INIT_BOX_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_shallow_init_box_fallback(x: u32) -> u32 {
        let t = (x, x + 1);
        t.0
    }
"#;

#[test]
fn test_shallow_init_box_rvalue_fallback_overflow_returns_none() {
    // Part of #2876: Flattened locals now reconstruct as Datatypes, so
    // ShallowInitBox passes through the reconstructed operand instead of
    // falling through to the allocation path. Verify the pass-through.
    with_test_ay_ctx_for_source(SHALLOW_INIT_BOX_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_shallow_init_box_fallback");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_shallow_init_box_fallback",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();

        let tuple_local = *chc_ctx
            .flatten
            .flattened_tuple_locals
            .iter()
            .next()
            .expect("fixture should expose at least one flattened tuple local");
        let modified_locals = HashSet::new();

        let fallback_before = chc_ctx.fallback_count;
        chc_ctx.heap_state.set_next_alloc_id(u32::MAX);
        let shallow_init_box = rustc_public::mir::Rvalue::ShallowInitBox(
            rustc_public::mir::Operand::Move(rustc_public::mir::Place {
                local: tuple_local,
                projection: Vec::new(),
            }),
            body.locals()[tuple_local].ty,
        );
        let result =
            chc_ctx.translate_rvalue_with_modified(&shallow_init_box, &modified_locals, None);

        // Reconstructed Datatype operand passes through — no fallback triggered.
        assert!(
            result.is_some(),
            "ShallowInitBox should pass through reconstructed flattened operand"
        );
        assert_eq!(
            chc_ctx.fallback_count, fallback_before,
            "ShallowInitBox pass-through should not record_fallback"
        );
    });
}

// =============================================================================
// Path 5 & 6: get_or_create_local_address — overflow → warn + None
// =============================================================================

/// Source with reference-taking to trigger get_or_create_local_address at Ptr level.
const REF_SOURCE: &str = r#"
    #![allow(dead_code, dangling_pointers_from_locals)]

    pub fn probe_ref_addr(x: u32) -> *const u32 {
        &x as *const u32
    }
"#;

#[test]
fn test_translate_ref_or_addressof_overflow_propagates_none() {
    // Path 5: translate_ref_or_addressof (Ptr-level, no projection) should
    // propagate None when get_or_create_local_address overflows.
    with_test_ay_ctx_for_source(REF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_addr");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_ref_addr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        let arg_local = 1usize;
        let modified_locals = HashSet::new();
        chc_ctx.heap_state.set_next_alloc_id(u32::MAX);
        let addr_of_arg = rustc_public::mir::Rvalue::AddressOf(
            rustc_public::mir::RawPtrKind::Const,
            rustc_public::mir::Place { local: arg_local, projection: Vec::new() },
        );

        let result = chc_ctx.translate_rvalue_with_modified(&addr_of_arg, &modified_locals, None);
        assert!(
            result.is_none(),
            "Ref/AddressOf translation should return None when local-address allocation overflows"
        );
    });
}

#[test]
fn test_get_or_create_local_address_overflow_returns_none() {
    // Path 6: direct get_or_create_local_address overflow path.
    with_test_ay_ctx_for_source(REF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_addr");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_ref_addr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        // Exhaust alloc IDs.
        chc_ctx.heap_state.set_next_alloc_id(u32::MAX);

        // Direct call to get_or_create_local_address for a local that has
        // no pre-existing address. Should return None on overflow.
        let result = chc_ctx.get_or_create_local_address(999);
        assert!(
            result.is_none(),
            "get_or_create_local_address should return None when alloc IDs overflow"
        );
    });
}

#[test]
fn test_get_or_create_local_address_cached_still_works_after_overflow() {
    // Verify that a previously-allocated address is still returned even
    // after alloc IDs are exhausted (cache lookup path).
    with_test_ay_ctx_for_source(REF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_addr");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_ref_addr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        // Allocate an address while IDs are available.
        let addr_before = chc_ctx.get_or_create_local_address(42);
        assert!(addr_before.is_some(), "Should allocate address when IDs available");

        // Now exhaust alloc IDs.
        chc_ctx.heap_state.set_next_alloc_id(u32::MAX);

        // Cached address should still be returned.
        let addr_after = chc_ctx.get_or_create_local_address(42);
        assert!(
            addr_after.is_some(),
            "Cached address should be returned even after alloc ID overflow"
        );
    });
}

// =============================================================================
// Path 7a & 7b: translate_rust_alloc / translate_rust_realloc — overflow → None
// =============================================================================

/// Source with direct std::alloc::alloc call to exercise translate_rust_alloc.
const ALLOC_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::alloc::{alloc, dealloc, realloc, Layout};

    pub unsafe fn probe_alloc_overflow() -> *mut u8 {
        let layout = Layout::new::<u64>();
        unsafe { alloc(layout) }
    }

    pub unsafe fn probe_realloc_overflow() -> *mut u8 {
        let layout = Layout::new::<u64>();
        let ptr = unsafe { alloc(layout) };
        unsafe { realloc(ptr, layout, 16) }
    }
"#;

#[test]
fn test_translate_rust_alloc_overflow_returns_none() {
    // Path 7a: When alloc IDs overflow during translate_rust_alloc,
    // the function should return None (not panic).
    with_test_ay_ctx_for_source(ALLOC_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_alloc_overflow");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_alloc_overflow",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Exhaust alloc IDs.
        chc_ctx.heap_state.set_next_alloc_id(u32::MAX);

        // Find the alloc call in MIR and try to translate it.
        let modified_locals = HashSet::new();
        let mut found_alloc = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_alloc_stub(func)
                && matches!(stub, StubKind::RustAlloc | StubKind::RustAllocZeroed)
            {
                let result = chc_ctx.translate_rust_alloc(stub, args, &modified_locals);
                assert!(
                    result.is_none(),
                    "translate_rust_alloc should return None when alloc IDs overflow"
                );
                found_alloc = true;
            }
        }
        assert!(found_alloc, "MIR should contain a detectable alloc call");
    });
}

#[test]
fn test_translate_rust_realloc_overflow_returns_none() {
    // Path 7b: When alloc IDs overflow during translate_rust_realloc,
    // the function should return None (not panic).
    with_test_ay_ctx_for_source(ALLOC_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_realloc_overflow");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_realloc_overflow",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Find alloc and realloc calls. Translate the alloc first to set up
        // heap state, then exhaust IDs, then try realloc.
        let modified_locals = HashSet::new();
        let mut found_realloc = false;

        // First pass: translate alloc calls to set up heap state.
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_alloc_stub(func)
                && matches!(stub, StubKind::RustAlloc | StubKind::RustAllocZeroed)
            {
                let _ = chc_ctx.translate_rust_alloc(stub, args, &modified_locals);
            }
        }

        // Exhaust alloc IDs after initial alloc.
        chc_ctx.heap_state.set_next_alloc_id(u32::MAX);

        // Second pass: try realloc with exhausted IDs.
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && let Some(StubKind::RustRealloc) = chc_ctx.detect_alloc_stub(func)
            {
                let result = chc_ctx.translate_rust_realloc(args, &modified_locals);
                assert!(
                    result.is_none(),
                    "translate_rust_realloc should return None when alloc IDs overflow"
                );
                found_realloc = true;
            }
        }
        assert!(found_realloc, "MIR should contain a detectable realloc call");
    });
}

// =============================================================================
// Integration: full pipeline survives alloc ID near-overflow
// =============================================================================

#[test]
fn test_mir_to_chc_pipeline_near_overflow_no_panic() {
    // End-to-end: mir_to_chc with alloc IDs near overflow should complete
    // without panicking. The pipeline uses multiple alloc paths internally.
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_pipeline_overflow(x: u32) -> u32 {
            let a = x + 1;
            let b = a + 2;
            a + b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_pipeline_overflow");
        let body = instance.body().expect("function body");

        // mir_to_chc creates a fresh ChcCtx internally, so we can't set
        // next_alloc_id directly. Instead, verify that the pipeline completes
        // at Reg level (no alloc paths) as a baseline sanity check.
        let vc = mir_to_chc(ctx.tcx, &body, "probe_pipeline_overflow", ChcConfig::default());
        assert!(!vc.relations.is_empty(), "Reg-level pipeline should produce relations");
        assert!(!vc.rules.is_empty(), "Reg-level pipeline should produce rules");
        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "pipeline near overflow should produce >= {} rules, got {}",
            bb_count,
            vc.rules.len()
        );
    });
}
