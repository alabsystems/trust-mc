// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR-driven alloc/kani::mem dispatch tests: Box alloc, kani::mem predicates.
//!
//! Split from dispatch.rs per #3678.

use super::super::*;
use super::build_codegen_for_fn_info;

// Alloc stubs dispatch: MIR-driven test
// -----------------------------------------------------------------------------

/// Probe source: allocation via Box — triggers RustAlloc/RustDealloc stubs.
const ALLOC_PROBE: &str = r#"
pub fn box_alloc_probe() -> Box<i32> {
    Box::new(42)
}
"#;

/// Test Box::new dispatch through alloc stubs.
/// Box::new involves alloc + Box wrapping — verify alloc path routing.
#[test]
fn test_mir_box_alloc_dispatch() {
    with_test_ay_ctx_for_source(ALLOC_PROBE, |mut ctx| {
        let info = build_codegen_for_fn_info(&mut ctx, "box_alloc_probe");
        assert!(info.call_count >= 1, "Box::new should have alloc Call, got {}", info.call_count);
        assert!(
            info.call_paths
                .iter()
                .any(|p| p.contains("alloc") || p.contains("exchange_malloc") || p.contains("Box")),
            "expected alloc/exchange_malloc/Box in call paths, got {:?}",
            info.call_paths
        );
    });
}

// -----------------------------------------------------------------------------
// kani::mem predicate stubs: MIR-driven test
// -----------------------------------------------------------------------------

/// Probe source for kani::mem helper calls that may bypass inlining.
const KANI_MEM_DISPATCH_PROBE: &str = r#"
pub mod kani {
    pub mod mem {
        #[inline(never)]
        pub fn is_ptr_aligned<T>(_ptr: *const T, _align: usize) -> bool {
            false
        }

        #[inline(never)]
        pub fn is_inbounds<T>(_ptr: *const T, _size: usize) -> bool {
            false
        }

        #[inline(never)]
        pub fn assert_is_initialized<T>(_ptr: *const T) {}
    }
}

pub fn is_ptr_aligned_probe(ptr: *const u8) -> bool {
    kani::mem::is_ptr_aligned(ptr, 1)
}

pub fn is_inbounds_probe(ptr: *const u8) -> bool {
    kani::mem::is_inbounds(ptr, 4)
}

pub fn assert_is_initialized_probe(ptr: *const u8) -> bool {
    kani::mem::assert_is_initialized(ptr);
    true
}
"#;

/// Codegen statements/terminators until a call matching `callee_substr` is handled.
/// Returns:
/// - all resolved call paths seen,
/// - the matched call path (if found),
/// - destination assignment after matching call,
/// - successor count from codegen_terminator_with_successors.
pub(super) fn codegen_matching_call_destination(
    ctx: &mut AYCtx<'_, 'static>,
    fn_suffix: &str,
    callee_substr: &str,
) -> (Vec<String>, Option<String>, Option<Expr>, Option<usize>) {
    let instance = find_instance_by_suffix(ctx, fn_suffix);
    let body = instance.body().expect("body");
    ctx.set_current_fn(instance);
    let tuple_usage = TupleUsageAnalysis::run(&body);
    let mut codegen = StatementCodegen::new(ctx, &body, tuple_usage);

    let mut call_paths = Vec::new();
    for bb in &body.blocks {
        for stmt in &bb.statements {
            codegen.codegen_statement(stmt);
        }

        if let rustc_public::mir::TerminatorKind::Call { func, destination, .. } =
            &bb.terminator.kind
            && let Some(path) = codegen.resolve_callee_path(func)
        {
            call_paths.push(path.clone());
            if path.contains(callee_substr) {
                let dest_base = codegen.ssa_base_name(destination);
                let successors = codegen.codegen_terminator_with_successors(&bb.terminator);
                let assigned = codegen.env_lookup(&dest_base).cloned();
                return (call_paths, Some(path), assigned, Some(successors.len()));
            }
        }
        let _ = codegen.codegen_terminator_with_successors(&bb.terminator);
    }

    (call_paths, None, None, None)
}

#[test]
fn test_mir_kani_mem_is_ptr_aligned_stub_returns_true() {
    with_test_ay_ctx_for_source(KANI_MEM_DISPATCH_PROBE, |mut ctx| {
        let (call_paths, matched_path, assigned, successor_count) =
            codegen_matching_call_destination(
                &mut ctx,
                "is_ptr_aligned_probe",
                "kani::mem::is_ptr_aligned",
            );
        assert!(
            call_paths.iter().any(|p| p.contains("kani::mem::is_ptr_aligned")),
            "expected resolved kani::mem::is_ptr_aligned call, got {call_paths:?}"
        );
        let matched_path = matched_path.expect("expected matching kani::mem::is_ptr_aligned call");
        assert_eq!(
            crate::codegen_ay::stubs::StubRegistry::new().lookup(&matched_path),
            Some(crate::codegen_ay::stubs::StubKind::KaniMemIsPtrAligned)
        );
        assert!(
            successor_count.unwrap_or(0) > 0,
            "stubbed call should continue (non-divergent), paths: {call_paths:?}"
        );

        let ret = assigned.expect("is_ptr_aligned call destination should be assigned");
        assert!(ret.sort().is_bool(), "expected bool destination, got {:?}", ret.sort());
    });
}

#[test]
fn test_mir_kani_mem_is_inbounds_stub_returns_true() {
    with_test_ay_ctx_for_source(KANI_MEM_DISPATCH_PROBE, |mut ctx| {
        let (call_paths, matched_path, assigned, successor_count) =
            codegen_matching_call_destination(
                &mut ctx,
                "is_inbounds_probe",
                "kani::mem::is_inbounds",
            );
        assert!(
            call_paths.iter().any(|p| p.contains("kani::mem::is_inbounds")),
            "expected resolved kani::mem::is_inbounds call, got {call_paths:?}"
        );
        let matched_path = matched_path.expect("expected matching kani::mem::is_inbounds call");
        assert_eq!(
            crate::codegen_ay::stubs::StubRegistry::new().lookup(&matched_path),
            Some(crate::codegen_ay::stubs::StubKind::KaniMemIsInbounds)
        );
        assert!(
            successor_count.unwrap_or(0) > 0,
            "stubbed call should continue (non-divergent), paths: {call_paths:?}"
        );

        let ret = assigned.expect("is_inbounds call destination should be assigned");
        assert!(ret.sort().is_bool(), "expected bool destination, got {:?}", ret.sort());
    });
}

#[test]
fn test_mir_kani_mem_assert_is_initialized_stub_nondivergent() {
    with_test_ay_ctx_for_source(KANI_MEM_DISPATCH_PROBE, |mut ctx| {
        let (call_paths, matched_path, assigned, successor_count) =
            codegen_matching_call_destination(
                &mut ctx,
                "assert_is_initialized_probe",
                "kani::mem::assert_is_initialized",
            );
        assert!(
            call_paths.iter().any(|p| p.contains("kani::mem::assert_is_initialized")),
            "expected resolved kani::mem::assert_is_initialized call, got {call_paths:?}"
        );
        let matched_path =
            matched_path.expect("expected matching kani::mem::assert_is_initialized call");
        assert_eq!(
            crate::codegen_ay::stubs::StubRegistry::new().lookup(&matched_path),
            Some(crate::codegen_ay::stubs::StubKind::KaniMemAssertIsInitialized)
        );
        assert!(
            successor_count.unwrap_or(0) > 0,
            "assert_is_initialized stub should continue (non-divergent), paths: {call_paths:?}"
        );

        // assert_is_initialized is modeled as assume-true (returns bool, always true).
        let ret = assigned.expect("assert_is_initialized call destination should be assigned");
        assert!(ret.sort().is_bool(), "expected bool destination, got {:?}", ret.sort());
    });
}

// =============================================================================
// extract_element_type_layout: MIR-driven test (Part of #2016)
// =============================================================================
// extract_element_type_layout extracts size/align from generic function calls
// like Layout::array::<T>(n). Previously had zero test coverage.

const LAYOUT_PROBE_SOURCE: &str = r#"
use std::alloc::Layout;
pub fn layout_array_probe() -> Layout {
    Layout::array::<u32>(10).unwrap()
}
pub fn layout_new_probe() -> Layout {
    Layout::new::<u64>()
}
"#;

/// Test extract_element_type_layout via Layout::array::<u32>.
#[test]
fn test_extract_element_type_layout_u32() {
    with_test_ay_ctx_for_source(LAYOUT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "layout_array_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Find a Call terminator with Layout::array
        let mut found = false;
        for bb in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &bb.terminator.kind
                && let Some(path) = codegen.resolve_callee_path(func)
                && path.contains("Layout")
                && path.contains("array")
            {
                let (size, align) = codegen.extract_element_type_layout(func);
                // u32: size=4, align=4
                assert_eq!(size, 4, "u32 size should be 4, got {size}");
                assert_eq!(align, 4, "u32 align should be 4, got {align}");
                found = true;
                break;
            }
        }
        assert!(
            found,
            "MIR should contain a Layout::array call — if rustc inlined it, \
            the probe source needs adjustment"
        );
    });
}

/// Test extract_element_type_layout via Layout::new::<u64>.
#[test]
fn test_extract_element_type_layout_u64() {
    with_test_ay_ctx_for_source(LAYOUT_PROBE_SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(&ctx, "layout_new_probe");
        let body = instance.body().expect("body");
        ctx.set_current_fn(instance);
        let tuple_usage = TupleUsageAnalysis::run(&body);
        let codegen = StatementCodegen::new(&mut ctx, &body, tuple_usage);

        // Find a Call terminator with Layout::new
        let mut found = false;
        for bb in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &bb.terminator.kind
                && let Some(path) = codegen.resolve_callee_path(func)
                && path.contains("Layout")
                && path.contains("new")
            {
                let (size, align) = codegen.extract_element_type_layout(func);
                // u64: size=8, align=8
                assert_eq!(size, 8, "u64 size should be 8, got {size}");
                assert_eq!(align, 8, "u64 align should be 8, got {align}");
                found = true;
                break;
            }
        }
        assert!(
            found,
            "MIR should contain a Layout::new call — if rustc inlined it, \
            the probe source needs adjustment"
        );
    });
}

// =============================================================================
