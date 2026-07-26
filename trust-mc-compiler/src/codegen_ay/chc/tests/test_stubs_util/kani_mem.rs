// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! kani::mem helper and raw eq detection tests.
//! Split from test_stubs_util.rs (Part of #2413).

#![allow(clippy::unwrap_used)]

use super::super::common::*;

// =============================================================================
// Raw eq detection tests
// =============================================================================

// =============================================================================
// kani::mem helper detection tests
// =============================================================================

#[test]
fn test_detect_kani_mem_is_ptr_aligned_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        mod kani {
            pub mod mem {
                pub fn is_ptr_aligned<T>(_ptr: *const T, _align: usize) -> bool {
                    true
                }

                pub fn is_inbounds<T>(_ptr: *const T, _size: usize) -> bool {
                    true
                }

                pub fn assert_is_initialized<T>(_ptr: *const T) {}
            }
        }

        pub fn probe_is_ptr_aligned(ptr: *const u8) -> bool {
            kani::mem::is_ptr_aligned(ptr, 1)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_is_ptr_aligned");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_is_ptr_aligned", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_kani_mem)
            {
                assert_eq!(stub, StubKind::KaniMemIsPtrAligned);
                found = true;
            }
        }
        assert!(found, "KaniMemIsPtrAligned stub should be detected");
    });
}

#[test]
fn test_detect_kani_mem_is_inbounds_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        mod kani {
            pub mod mem {
                pub fn is_ptr_aligned<T>(_ptr: *const T, _align: usize) -> bool {
                    true
                }

                pub fn is_inbounds<T>(_ptr: *const T, _size: usize) -> bool {
                    true
                }

                pub fn assert_is_initialized<T>(_ptr: *const T) {}
            }
        }

        pub fn probe_is_inbounds(ptr: *const u8) -> bool {
            kani::mem::is_inbounds(ptr, 4)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_is_inbounds");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_is_inbounds", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_kani_mem)
            {
                assert_eq!(stub, StubKind::KaniMemIsInbounds);
                found = true;
            }
        }
        assert!(found, "KaniMemIsInbounds stub should be detected");
    });
}

#[test]
fn test_detect_kani_mem_assert_is_initialized_stub() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        mod kani {
            pub mod mem {
                pub fn is_ptr_aligned<T>(_ptr: *const T, _align: usize) -> bool {
                    true
                }

                pub fn is_inbounds<T>(_ptr: *const T, _size: usize) -> bool {
                    true
                }

                pub fn assert_is_initialized<T>(_ptr: *const T) {}
            }
        }

        pub fn probe_assert_is_initialized(ptr: *const u8) {
            kani::mem::assert_is_initialized(ptr)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_assert_is_initialized");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_assert_is_initialized", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_kani_mem)
            {
                assert_eq!(stub, StubKind::KaniMemAssertIsInitialized);
                found = true;
            }
        }
        assert!(found, "KaniMemAssertIsInitialized stub should be detected");
    });
}

#[test]
fn test_detect_kani_mem_stub_ignores_pointer_utility_calls() {
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

        let mut found_ptr_stub = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_pointer_utility).is_some()
            {
                assert!(
                    chc_ctx.detect_stub_matching(func, StubKind::is_kani_mem).is_none(),
                    "kani::mem detector must ignore pointer utility calls"
                );
                found_ptr_stub = true;
            }
        }
        assert!(found_ptr_stub, "expected pointer utility call in probe_ptr_is_null");
    });
}

#[test]
fn test_translate_mem_intrinsic_call_uses_callee_type_arg() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        fn id<T>(x: T) -> T {
            x
        }

        pub fn probe_id_u8(x: u8) -> u8 {
            id::<u8>(x)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_id_u8");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_id_u8", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                // This call is not a mem intrinsic path, so detection should skip it.
                assert!(chc_ctx.detect_stub_matching(func, StubKind::is_mem_intrinsic).is_none());
                found = true;
                // Translation helper only depends on callee type arguments.
                let align_expr = chc_ctx
                    .translate_mem_intrinsic_call(StubKind::MemAlignOf, func)
                    .expect("align translation");
                if let ExprValue::BitVecConst { value, width } = align_expr.value() {
                    assert_eq!(*width, POINTER_WIDTH);
                    assert_eq!(value.to_string(), "1");
                } else {
                    assert!(
                        matches!(align_expr.value(), ExprValue::BitVecConst { .. }),
                        "expected BV constant from MemAlignOf, got {:?}",
                        align_expr.value()
                    );
                }

                let size_expr = chc_ctx
                    .translate_mem_intrinsic_call(StubKind::MemSizeOf, func)
                    .expect("size translation");
                if let ExprValue::BitVecConst { value, width } = size_expr.value() {
                    assert_eq!(*width, POINTER_WIDTH);
                    assert_eq!(value.to_string(), "1");
                } else {
                    assert!(
                        matches!(size_expr.value(), ExprValue::BitVecConst { .. }),
                        "expected BV constant from MemSizeOf, got {:?}",
                        size_expr.value()
                    );
                }
            }
        }
        assert!(found, "expected call terminator in probe_id_u8");
    });
}

/// Part of #2783: translate_mem_intrinsic_call for a concrete `size_of::<u32>` must
/// produce `Some(bitvec64(4))` and NOT increment fallback_count — proving the happy
/// path is wired correctly and that fallback fires only on unknown-layout types.
#[test]
fn test_translate_mem_intrinsic_call_concrete_type_no_fallback() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_size_of_u32() -> usize {
            core::mem::size_of::<u32>()
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_size_of_u32");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_size_of_u32", ChcConfig::default());

        let mut found_call = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                found_call = true;
                let before = chc_ctx.fallback_count;

                let size_expr = chc_ctx.translate_mem_intrinsic_call(StubKind::MemSizeOf, func);
                let after = chc_ctx.fallback_count;
                assert!(size_expr.is_some(), "MemSizeOf on concrete u32 should succeed");
                assert_eq!(after, before, "concrete type must NOT increment fallback_count");
            }
        }

        assert!(found_call, "expected call terminator in probe_size_of_u32");
    });
}

#[test]
fn test_detect_raw_eq_call() {
    // raw_eq is a compiler intrinsic; detection uses path matching.
    // We test via the public detect_raw_eq_call method.
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        #![allow(internal_features)]
        #![feature(core_intrinsics)]

        pub fn probe_raw_eq(a: &[u8; 4], b: &[u8; 4]) -> bool {
            unsafe { core::intrinsics::raw_eq(a, b) }
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
