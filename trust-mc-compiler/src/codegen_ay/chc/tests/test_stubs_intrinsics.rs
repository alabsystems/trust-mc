// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven tests for CHC stubs_util_intrinsics.rs — raw_eq detection,
//! copy_nonoverlapping detection, kani::mem stub detection, mem::size_of/align_of
//! intrinsics, pointer memory stubs, pointer utility stubs, and ref operand resolution.
//!
//! Part of #2231 (zero test coverage for stubs_util_intrinsics.rs, 316 LOC).

#![allow(clippy::unwrap_used)]

use super::common::*;
use num_bigint::BigInt;

fn assert_ptr_is_null_expr(expr: &ay_bindings::Expr) {
    let is_zero_ptr = |candidate: &ay_bindings::Expr| {
        matches!(
            candidate.value(),
            ExprValue::BitVecConst { value, width }
                if *width == crate::codegen_ay::types::POINTER_WIDTH
                    && value == &BigInt::from(0u8)
        )
    };

    match expr.value() {
        ExprValue::Eq(lhs, rhs) => {
            assert!(
                is_zero_ptr(lhs) || is_zero_ptr(rhs),
                "ptr::is_null should compare against a null pointer, got {:?}",
                expr.value()
            );
            let ptr_side = if is_zero_ptr(lhs) { rhs } else { lhs };
            assert_eq!(
                ptr_side.sort().bitvec_width(),
                Some(crate::codegen_ay::types::POINTER_WIDTH),
                "pointer side should be pointer-width"
            );
        }
        other => panic!("expected ptr::is_null equality, got {other:?}"),
    }
}

fn find_crate_item_by_suffix(tcx: TyCtxt<'_>, suffix: &str) -> rustc_public::CrateItem {
    let matches: Vec<_> = rustc_public::all_local_items()
        .into_iter()
        .filter(|item| {
            let def_id = rustc_public::rustc_internal::internal(tcx, item.def_id());
            let path = tcx.def_path_str(def_id);
            path == suffix || path.ends_with(&format!("::{suffix}"))
        })
        .collect();
    let names: Vec<_> = matches
        .iter()
        .map(|item| {
            let def_id = rustc_public::rustc_internal::internal(tcx, item.def_id());
            tcx.def_path_str(def_id)
        })
        .collect();
    assert!(!matches.is_empty(), "missing item with suffix '{suffix}' (known items: {names:?})");
    assert_eq!(
        matches.len(),
        1,
        "ambiguous suffix '{suffix}' ({} matches: {names:?})",
        matches.len()
    );
    matches[0]
}

// =============================================================================
// raw_eq detection (detect_raw_eq_call)
// =============================================================================

#[test]
fn test_detect_raw_eq_call_array_eq() {
    // Array equality in Rust lowers to raw_eq in MIR
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![allow(internal_features)]
        #![feature(core_intrinsics)]

        pub fn probe_raw_eq(a: &[u8; 4], b: &[u8; 4]) -> bool {
            unsafe { std::intrinsics::raw_eq(a, b) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_eq");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_raw_eq", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_raw_eq_call(func)
            {
                found = true;
            }
        }
        assert!(found, "raw_eq call should be detected");
    });
}

#[test]
fn test_detect_raw_eq_call_negative() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_no_raw_eq(a: u32, b: u32) -> bool {
            a == b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_no_raw_eq");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_no_raw_eq", ChcConfig::default());

        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                assert!(
                    !chc_ctx.detect_raw_eq_call(func),
                    "Scalar equality should not be detected as raw_eq"
                );
            }
        }
    });
}

// =============================================================================
// copy_nonoverlapping detection (detect_copy_nonoverlapping_call)
// =============================================================================

#[test]
fn test_detect_copy_nonoverlapping_call() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_copy_nonoverlapping(src: *const u32, dst: *mut u32, count: usize) {
            unsafe { std::ptr::copy_nonoverlapping(src, dst, count); }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_nonoverlapping");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_copy_nonoverlapping", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_copy_nonoverlapping_call(func)
            {
                found = true;
            }
        }
        assert_mir_pattern_found(found, "copy_nonoverlapping call in MIR");
    });
}

// =============================================================================
// mem::size_of / mem::align_of intrinsic detection (detect_mem_intrinsic_stub)
// =============================================================================

#[test]
fn test_detect_mem_intrinsic_stub_size_of() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_size_of() -> usize {
            std::mem::size_of::<u64>()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_size_of");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_size_of", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_mem_intrinsic)
            {
                assert_eq!(stub, StubKind::MemSizeOf);
                found = true;
            }
        }
        assert_mir_pattern_found(found, "mem::size_of call in MIR");
    });
}

#[test]
fn test_detect_mem_intrinsic_stub_align_of() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_align_of() -> usize {
            std::mem::align_of::<u64>()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_align_of");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_align_of", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_mem_intrinsic)
            {
                assert!(
                    stub.is_mem_intrinsic(),
                    "detected stub should be a mem intrinsic, got {stub:?}"
                );
                found = true;
            }
        }
        assert_mir_pattern_found(found, "mem::align_of call in MIR");
    });
}

/// Part of #2783: generic `size_of::<T>` must fail closed in CHC translation
/// when `T` is unresolved (non-monomorphized item body), and record fallback.
#[test]
fn test_translate_mem_intrinsic_generic_size_of_increments_sound_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_size_of_generic<T>(_v: T) -> usize {
            core::mem::size_of::<T>()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let item = find_crate_item_by_suffix(ctx.tcx, "probe_size_of_generic");
        let body = item.body().expect("generic function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_size_of_generic", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_mem_intrinsic)
                    == Some(StubKind::MemSizeOf)
            {
                found = true;
                let before = chc_ctx.sound_fallback_count();
                let translated = chc_ctx.translate_mem_intrinsic_call(StubKind::MemSizeOf, func);
                let after = chc_ctx.sound_fallback_count();
                assert!(
                    translated.is_none(),
                    "non-monomorphized size_of::<T> must fail closed (None)"
                );
                assert!(
                    after > before,
                    "generic size_of::<T> fail-closed path must increment sound_fallback_count() \
                     (before={before}, after={after})"
                );
            }
        }

        assert_mir_pattern_found(found, "generic mem::size_of call in MIR");
    });
}

/// Part of #2783: generic `align_of::<T>` must fail closed in CHC translation
/// when `T` is unresolved (non-monomorphized item body), and record fallback.
#[test]
fn test_translate_mem_intrinsic_generic_align_of_increments_sound_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_align_of_generic<T>(_v: T) -> usize {
            core::mem::align_of::<T>()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let item = find_crate_item_by_suffix(ctx.tcx, "probe_align_of_generic");
        let body = item.body().expect("generic function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_align_of_generic", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_mem_intrinsic)
                    == Some(StubKind::MemAlignOf)
            {
                found = true;
                let before = chc_ctx.sound_fallback_count();
                let translated = chc_ctx.translate_mem_intrinsic_call(StubKind::MemAlignOf, func);
                let after = chc_ctx.sound_fallback_count();
                assert!(
                    translated.is_none(),
                    "non-monomorphized align_of::<T> must fail closed (None)"
                );
                assert!(
                    after > before,
                    "generic align_of::<T> fail-closed path must increment sound_fallback_count() \
                     (before={before}, after={after})"
                );
            }
        }

        assert_mir_pattern_found(found, "generic mem::align_of call in MIR");
    });
}

// =============================================================================
// Pointer memory stub detection (detect_ptr_memory_stub)
// =============================================================================

#[test]
fn test_detect_ptr_memory_stub_write() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_write(p: *mut u32, val: u32) {
            unsafe { p.write(val); }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_write");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_write", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
            {
                assert_eq!(stub, StubKind::PtrWrite);
                found = true;
            }
        }
        assert!(found, "PtrWrite stub should be detected");
    });
}

#[test]
fn test_detect_ptr_memory_stub_read() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_read(p: *const u32) -> u32 {
            unsafe { p.read() }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_read");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_read", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
            {
                assert_eq!(stub, StubKind::PtrRead);
                found = true;
            }
        }
        assert!(found, "PtrRead stub should be detected");
    });
}

#[test]
fn test_detect_ptr_memory_stub_add() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_add(p: *const u32, offset: usize) -> *const u32 {
            unsafe { p.add(offset) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_add");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_add", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
            {
                assert_eq!(stub, StubKind::PtrAdd);
                found = true;
            }
        }
        assert_mir_pattern_found(found, "ptr.add call in MIR");
    });
}

// =============================================================================
// Pointer utility stub detection (detect_pointer_utility_stub)
// =============================================================================

#[test]
fn test_detect_pointer_utility_stub_is_null() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_is_null(p: *const u32) -> bool {
            p.is_null()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_is_null");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_is_null", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_pointer_utility)
            {
                assert!(
                    stub == StubKind::PtrIsNull || stub == StubKind::PtrIsNullRuntime,
                    "Expected PtrIsNull or PtrIsNullRuntime, got {:?}",
                    stub
                );
                found = true;
            }
        }
        assert_mir_pattern_found(found, "ptr::is_null call in MIR");
    });
}

#[test]
fn test_detect_pointer_utility_stub_without_provenance() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_without_provenance(addr: usize) -> *const u32 {
            std::ptr::without_provenance(addr)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_without_provenance");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_without_provenance", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_pointer_utility)
            {
                assert!(
                    stub == StubKind::WithoutProvenance || stub == StubKind::WithoutProvenanceMut,
                    "Expected WithoutProvenance variant, got {:?}",
                    stub
                );
                found = true;
            }
        }
        assert_mir_pattern_found(found, "ptr::without_provenance call in MIR");
    });
}

// =============================================================================
// Fallback counter tests for translate_ptr_add_call
// Part of #2783: ensure record_fallback() sites have dedicated tests.
// =============================================================================

/// translate_ptr_add_call increments sound_fallback_count() when the first argument's
/// type is not a pointer/reference, so the pointee size cannot be determined.
///
/// Production site: stubs_util_intrinsics.rs line 131 — `self.record_fallback()`
/// in the `None` arm of `elem_size_opt`.
#[test]
fn test_translate_ptr_add_unknown_pointee_increments_sound_fallback_counter() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_add_fallback(p: *const u32, offset: usize) -> *const u32 {
            unsafe { p.add(offset) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_add_fallback");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_ptr_add_fallback", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find the ptr.add call site to get valid argument operands
        let mut call_args = None;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
                    == Some(StubKind::PtrAdd)
            {
                call_args = Some(args.clone());
                break;
            }
        }
        let args = call_args.expect("expected PtrAdd call in MIR");
        assert!(args.len() >= 2, "PtrAdd should have at least 2 args");

        // Swap args so args[0] is the usize (count) instead of the pointer.
        // This means args[0].ty() resolves to usize (not *const u32), which
        // causes elem_size_opt to be None → record_fallback().
        let swapped_args = [args[1].clone(), args[0].clone()];
        let modified = HashSet::<usize>::new();

        let before = chc_ctx.sound_fallback_count();
        let result = chc_ctx.translate_ptr_add_call(&swapped_args, &modified);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            result.is_none(),
            "translate_ptr_add_call with non-pointer first arg should return None"
        );
        assert!(
            after > before,
            "translate_ptr_add_call should increment sound_fallback_count() when pointee size \
             is unknown (before={before}, after={after})"
        );
    });
}

/// Negative: translate_ptr_add_call does NOT increment sound_fallback_count() when
/// given valid pointer arguments with a known pointee type.
#[test]
fn test_translate_ptr_add_valid_pointer_does_not_increment_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_add_ok(p: *const u32, offset: usize) -> *const u32 {
            unsafe { p.add(offset) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_add_ok");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_add_ok", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_args = None;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
                    == Some(StubKind::PtrAdd)
            {
                call_args = Some(args.clone());
                break;
            }
        }
        let args = call_args.expect("expected PtrAdd call in MIR");
        let modified = HashSet::<usize>::new();

        let before = chc_ctx.sound_fallback_count();
        let result = chc_ctx.translate_ptr_add_call(&args, &modified);
        let after = chc_ctx.sound_fallback_count();

        assert!(
            result.is_some(),
            "translate_ptr_add_call with valid *const u32 args should return Some"
        );
        assert_eq!(
            after, before,
            "translate_ptr_add_call with valid pointer args should NOT increment sound_fallback_count()"
        );
    });
}

// =============================================================================
// translate_pointer_utility_call unit tests (pure expression generation)
// =============================================================================

#[test]
fn test_translate_pointer_utility_call_is_null_compares_pointer_to_zero() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_is_null_translate(p: *const u32) -> bool {
            p.is_null()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_is_null_translate");
        let body = instance.body().expect("function body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_is_null_translate", ChcConfig::default());

        let modified = HashSet::new();
        let mut found_target = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_pointer_utility)
                && (stub == StubKind::PtrIsNull || stub == StubKind::PtrIsNullRuntime)
            {
                found_target = true;
                let result = chc_ctx.translate_pointer_utility_call(stub, args, &modified);
                assert!(result.is_some(), "PtrIsNull should produce a result");
                let expr = result.unwrap();
                assert!(expr.sort().is_bool(), "PtrIsNull result should be Bool");
                assert_ptr_is_null_expr(&expr);
            }
        }
        assert_mir_pattern_found(found_target, "ptr::is_null translation path in MIR");
    });
}

#[test]
fn test_translate_pointer_utility_call_nonnull_cast_returns_pointer_expr() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        use core::ptr::NonNull;

        pub fn probe_nonnull_cast_translate(p: NonNull<u8>) -> NonNull<u16> {
            p.cast::<u16>()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nonnull_cast_translate");
        let body = instance.body().expect("function body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_nonnull_cast_translate", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let modified = HashSet::new();
        let mut found_target = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_pointer_utility)
                && stub == StubKind::NonNullCast
            {
                found_target = true;
                let result = chc_ctx.translate_pointer_utility_call(stub, args, &modified);
                assert!(result.is_some(), "NonNullCast should translate as pointer identity");
                let expr = result.unwrap();
                assert_eq!(
                    expr.sort().bitvec_width(),
                    Some(crate::codegen_ay::types::POINTER_WIDTH),
                    "NonNullCast result should be pointer-width bitvec"
                );
            }
        }
        assert_mir_pattern_found(found_target, "NonNull::cast pointer utility translation path");
    });
}
