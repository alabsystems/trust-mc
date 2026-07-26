// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for CHC atomic intrinsic dispatch (`codegen_call_atomic.rs`,
//! `codegen_call_atomic_rmw.rs`).
//!
//! Part of #3604 — zero test coverage for soundness-critical atomic codegen.
//!
//! Coverage areas:
//! - `coerce_atomic_bool_sorts`: Bool↔BV sort coercion for atomic operations
//! - Atomic load/store/new via MIR-backed probes (end-to-end VC generation)
//! - Atomic compare_exchange via MIR-backed probes

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::codegen_call_cmp_string::math_const_prescan::compute_single_assign_locals;
use ay_bindings::{Expr, Sort};

// =============================================================================
// coerce_atomic_bool_sorts: pure unit tests
// =============================================================================

use super::super::codegen_call_atomic_rmw::coerce_atomic_bool_sorts;

/// Same-sort operands pass through unchanged.
#[test]
fn test_coerce_atomic_bool_sorts_same_sort_passthrough() {
    let a = Expr::bitvec_const(42u64, 32);
    let b = Expr::bitvec_const(7u64, 32);
    let (out_a, out_b) = coerce_atomic_bool_sorts(a, b);
    assert_eq!(*out_a.sort(), Sort::bitvec(32));
    assert_eq!(*out_b.sort(), Sort::bitvec(32));
}

/// BV + Bool: Bool operand gets coerced to BV via ite(b, 1, 0).
#[test]
fn test_coerce_atomic_bool_sorts_bv_plus_bool() {
    let a = Expr::bitvec_const(1u64, 8);
    let b = Expr::bool_const(true);
    let (out_a, out_b) = coerce_atomic_bool_sorts(a, b);
    assert_eq!(*out_a.sort(), Sort::bitvec(8), "BV operand unchanged");
    assert_eq!(*out_b.sort(), Sort::bitvec(8), "Bool operand coerced to BV8");
}

/// Bool + BV: Bool operand gets coerced to BV via ite(a, 1, 0).
#[test]
fn test_coerce_atomic_bool_sorts_bool_plus_bv() {
    let a = Expr::bool_const(false);
    let b = Expr::bitvec_const(0u64, 8);
    let (out_a, out_b) = coerce_atomic_bool_sorts(a, b);
    assert_eq!(*out_a.sort(), Sort::bitvec(8), "Bool operand coerced to BV8");
    assert_eq!(*out_b.sort(), Sort::bitvec(8), "BV operand unchanged");
}

/// Two Bool operands: same-sort passthrough (no coercion needed).
#[test]
fn test_coerce_atomic_bool_sorts_both_bool() {
    let a = Expr::bool_const(true);
    let b = Expr::bool_const(false);
    let (out_a, out_b) = coerce_atomic_bool_sorts(a, b);
    assert!(out_a.sort().is_bool(), "Bool stays Bool");
    assert!(out_b.sort().is_bool(), "Bool stays Bool");
}

/// Non-BV non-Bool sorts pass through without coercion.
/// This exercises the implicit invariant flagged in #3604: mixed-sort operands
/// that are neither BV nor Bool are silently accepted.
#[test]
fn test_coerce_atomic_bool_sorts_non_bv_non_bool_passthrough() {
    let a = Expr::int_const(42);
    let b = Expr::int_const(7);
    let (out_a, out_b) = coerce_atomic_bool_sorts(a, b);
    assert_eq!(*out_a.sort(), Sort::int(), "Int passes through");
    assert_eq!(*out_b.sort(), Sort::int(), "Int passes through");
}

/// BV16 + Bool: width is preserved at 16 bits.
#[test]
fn test_coerce_atomic_bool_sorts_bv16_width_preserved() {
    let a = Expr::bitvec_const(0u64, 16);
    let b = Expr::bool_const(true);
    let (out_a, out_b) = coerce_atomic_bool_sorts(a, b);
    assert_eq!(out_a.sort().bitvec_width(), Some(16));
    assert_eq!(out_b.sort().bitvec_width(), Some(16), "Bool coerced to BV16");
}

// =============================================================================
// MIR-backed probes: atomic load/store/new
// =============================================================================

/// Probe: AtomicBool::new(true) followed by load.
/// Exercises the full atomic dispatch pipeline: new → load.
const ATOMIC_BOOL_LOAD_PROBE: &str = r#"
    #![allow(dead_code)]
    use std::sync::atomic::{AtomicBool, Ordering};

    pub fn probe_atomic_bool_load() -> bool {
        let a = AtomicBool::new(true);
        a.load(Ordering::SeqCst)
    }
"#;

/// A function using AtomicBool::new + load should produce a valid VC with
/// relations and rules. The atomic dispatch pipeline must handle both
/// `new` (constructor) and `load` intrinsics.
#[test]
fn test_atomic_bool_load_produces_valid_vc() {
    with_test_ay_ctx_for_source(ATOMIC_BOOL_LOAD_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_atomic_bool_load");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_atomic_bool_load", ChcConfig::default());

        assert!(!vc.relations.is_empty(), "atomic load function should produce relations");
        assert!(!vc.rules.is_empty(), "atomic load function should produce rules");

        // The function returns bool, so relations should contain a bool sort
        let has_bool =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(ay_bindings::Sort::is_bool));
        assert!(has_bool, "relations should include Bool sort for bool return");
    });
}

/// Probe: AtomicBool::new(true) followed by store(false).
const ATOMIC_BOOL_STORE_PROBE: &str = r#"
    #![allow(dead_code)]
    use std::sync::atomic::{AtomicBool, Ordering};

    pub fn probe_atomic_bool_store() {
        let a = AtomicBool::new(true);
        a.store(false, Ordering::SeqCst);
    }
"#;

/// AtomicBool::store dispatches through the atomic store handler.
/// The VC should be valid (non-degenerate) even though the function has no return value.
#[test]
fn test_atomic_bool_store_produces_valid_vc() {
    with_test_ay_ctx_for_source(ATOMIC_BOOL_STORE_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_atomic_bool_store");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_atomic_bool_store", ChcConfig::default());

        assert!(!vc.relations.is_empty(), "atomic store function should produce relations");
        assert!(!vc.rules.is_empty(), "atomic store function should produce rules");
        // At least 2 rules: entry + transition (store is not a trivial no-op)
        assert!(
            vc.rules.len() >= 2,
            "atomic store should produce entry + transition rules, got {}",
            vc.rules.len()
        );
    });
}

// =============================================================================
// MIR-backed probes: compare_exchange
// =============================================================================

/// Probe: AtomicBool compare_exchange (stable API returning Result<T,T>).
const ATOMIC_CMP_EXCHANGE_PROBE: &str = r#"
    #![allow(dead_code)]
    use std::sync::atomic::{AtomicBool, Ordering};

    pub fn probe_compare_exchange() -> bool {
        let a = AtomicBool::new(false);
        match a.compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst) {
            Ok(_) => true,
            Err(_) => false,
        }
    }
"#;

/// compare_exchange exercises one of the most complex atomic paths:
/// Result<T,T> flattened encoding with conditional store.
#[test]
fn test_atomic_compare_exchange_produces_valid_vc() {
    with_test_ay_ctx_for_source(ATOMIC_CMP_EXCHANGE_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_compare_exchange");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_compare_exchange", ChcConfig::default());

        assert!(!vc.relations.is_empty(), "compare_exchange function should produce relations");
        assert!(!vc.rules.is_empty(), "compare_exchange function should produce rules");

        // compare_exchange has branching (match Ok/Err), so we expect more rules
        // than a simple linear function
        assert!(
            vc.rules.len() >= 3,
            "compare_exchange with match should produce >= 3 rules, got {}",
            vc.rules.len()
        );
    });
}

// =============================================================================
// MIR-backed probes: fetch_add (RMW operation)
// =============================================================================

/// Probe: AtomicUsize fetch_add (read-modify-write).
const ATOMIC_FETCH_ADD_PROBE: &str = r#"
    #![allow(dead_code)]
    use std::sync::atomic::{AtomicUsize, Ordering};

    pub fn probe_fetch_add() -> usize {
        let a = AtomicUsize::new(10);
        a.fetch_add(5, Ordering::SeqCst)
    }
"#;

/// fetch_add exercises the RMW pipeline: read old value, compute new (bvadd),
/// store new, return old.
#[test]
fn test_atomic_fetch_add_produces_valid_vc() {
    with_test_ay_ctx_for_source(ATOMIC_FETCH_ADD_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_fetch_add");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_fetch_add", ChcConfig::default());

        assert!(!vc.relations.is_empty(), "fetch_add function should produce relations");
        assert!(!vc.rules.is_empty(), "fetch_add function should produce rules");
    });
}

// =============================================================================
// MIR-backed probes: from_ptr (transparent alias boundary)
// =============================================================================

/// Probe: AtomicUsize::from_ptr + store + load.
/// Exercises the from_ptr alias boundary: raw pointer → &AtomicUsize → store/load.
/// Part of #3598.
const ATOMIC_FROM_PTR_PROBE: &str = r#"
    #![allow(dead_code)]
    use std::sync::atomic::{AtomicUsize, Ordering};

    pub fn probe_atomic_from_ptr() -> usize {
        let mut val: usize = 0;
        let ptr: *mut usize = &mut val as *mut usize;
        let atomic = unsafe { AtomicUsize::from_ptr(ptr) };
        atomic.store(42, Ordering::SeqCst);
        atomic.load(Ordering::SeqCst)
    }
"#;

/// Probe: stable AtomicPtr fetch_or should stay on the heap/memory path without
/// falling into unknown-layout fail-closed checks.
const ATOMIC_PTR_FETCH_OR_PROBE: &str = r#"
    #![allow(dead_code)]
    use std::sync::atomic::{AtomicPtr, Ordering};

    pub fn probe_atomic_ptr_fetch_or() -> *mut i32 {
        let mut value = 3i32;
        let pointer = &mut value as *mut i32;
        let atom = AtomicPtr::<i32>::new(pointer);
        atom.fetch_or(1, Ordering::Relaxed)
    }
"#;

/// from_ptr exercises the alias boundary: the destination &AtomicUsize must
/// gain ref_targets metadata so that subsequent store/load can resolve the
/// pointee. The VC should be valid and non-degenerate.
#[test]
fn test_atomic_from_ptr_produces_valid_vc() {
    with_test_ay_ctx_for_source(ATOMIC_FROM_PTR_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_atomic_from_ptr");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_atomic_from_ptr", ChcConfig::default());

        assert!(!vc.relations.is_empty(), "from_ptr function should produce relations");
        assert!(!vc.rules.is_empty(), "from_ptr function should produce rules");
        // from_ptr + store + load has at least 3 blocks: entry, store, load/return
        assert!(
            vc.rules.len() >= 3,
            "from_ptr + store + load should produce >= 3 rules, got {}",
            vc.rules.len()
        );
    });
}

#[test]
fn test_atomic_ptr_fetch_or_has_no_unknown_layout_heap_checks() {
    with_test_ay_ctx_for_source(ATOMIC_PTR_FETCH_OR_PROBE, |ctx| {
        let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let before = crate::codegen_ay::chc::get_chc_heap_check_unknown_layout_count();

        let instance = find_instance_by_suffix(ctx.tcx, "probe_atomic_ptr_fetch_or");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_atomic_ptr_fetch_or",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let after = crate::codegen_ay::chc::get_chc_heap_check_unknown_layout_count();
        assert_eq!(
            after - before,
            0,
            "AtomicPtr::fetch_or should not emit heap_check_unknown_layout"
        );
        assert!(
            !vc.relations.is_empty() && !vc.rules.is_empty(),
            "AtomicPtr::fetch_or should still produce a non-degenerate VC"
        );
    });
}

/// Probe: heap-backed AtomicUsize::from_ptr + store + load + swap + free.
/// Mirrors the `tests/trust_mc/Uninit/atomic.rs::local_atomic` shape.
const ATOMIC_HEAP_FROM_PTR_PROBE: &str = r#"
    #![allow(dead_code)]
    use std::sync::atomic::{AtomicUsize, Ordering};

    pub fn probe_atomic_heap_from_ptr() {
        let ptr: *mut usize = Box::into_raw(Box::new(0usize));
        let atomic = unsafe { AtomicUsize::from_ptr(ptr) };
        atomic.store(1, Ordering::SeqCst);
        let _ = atomic.load(Ordering::SeqCst);
        let _ = atomic.swap(2, Ordering::SeqCst);
        unsafe { drop(Box::from_raw(ptr)); }
    }
"#;

/// Heap-backed from_ptr must use the memory model rather than requiring a
/// stack-local ref_target. The `local_atomic` regression shape should not
/// increment CHC fallback or translation-drop metrics.
#[test]
fn test_atomic_heap_from_ptr_local_atomic_shape_has_no_chc_fallbacks() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();

    with_test_ay_ctx_for_source(ATOMIC_HEAP_FROM_PTR_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_atomic_heap_from_ptr");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_atomic_heap_from_ptr", ChcConfig::default());

        assert!(!vc.relations.is_empty(), "heap-backed from_ptr function should produce relations");
        assert!(!vc.rules.is_empty(), "heap-backed from_ptr function should produce rules");

        let fallback_count =
            get_chc_fallback_counts().get("probe_atomic_heap_from_ptr").copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "heap-backed from_ptr should not increment CHC fallback count, got {fallback_count}"
        );

        let translation_drops = take_translation_drop_by_fn();
        let translation_drop_count =
            translation_drops.get("probe_atomic_heap_from_ptr").copied().unwrap_or(0);
        // Part of #3710: the heap-backed atomic path is now fully modeled.
        // This probe includes Box::into_raw, AtomicUsize::from_ptr, store/load/
        // swap, and Box::from_raw cleanup, so translation drops here would
        // regress either the atomic Mem-level bridge or the cleanup-tail parity.
        assert_eq!(
            translation_drop_count, 0,
            "heap-backed from_ptr should keep translation-drop count at zero, map={translation_drops:?}"
        );
    });

    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
}

// =============================================================================
// MIR-backed probes: isolation of cleanup-tail translation drops (Part of #3706)
// =============================================================================

/// Probe: atomic path WITHOUT the Box::from_raw cleanup tail.
/// Leaks the Box deliberately to isolate atomic translation drops from
/// cleanup-tail translation drops.
const ATOMIC_NO_CLEANUP_PROBE: &str = r#"
    #![allow(dead_code)]
    use std::sync::atomic::{AtomicUsize, Ordering};

    pub fn probe_atomic_no_cleanup() {
        let ptr: *mut usize = Box::into_raw(Box::new(0usize));
        let atomic = unsafe { AtomicUsize::from_ptr(ptr) };
        atomic.store(1, Ordering::SeqCst);
        let _ = atomic.load(Ordering::SeqCst);
        let _ = atomic.swap(2, Ordering::SeqCst);
        // Deliberately no Box::from_raw cleanup — isolates atomic path drops.
    }
"#;

/// Probe: heap-backed AtomicUsize::from_ptr with symbolic Ordering helpers.
/// Mirrors the `local_atomic` harness's `kani::any()`-backed ordering calls
/// without the deallocation tail so the test isolates fn_inline behavior.
const ATOMIC_SYMBOLIC_ORDERING_PROBE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]
    use std::sync::atomic::{AtomicUsize, Ordering};

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            panic!("model-only marker function")
        }
    }

    fn any_ordering() -> Ordering {
        match kani::any() {
            0 => Ordering::Relaxed,
            1 => Ordering::Release,
            2 => Ordering::Acquire,
            3 => Ordering::AcqRel,
            _ => Ordering::SeqCst,
        }
    }

    fn store_ordering() -> Ordering {
        match kani::any() {
            0 => Ordering::Relaxed,
            1 => Ordering::Release,
            _ => Ordering::SeqCst,
        }
    }

    fn load_ordering() -> Ordering {
        match kani::any() {
            0 => Ordering::Relaxed,
            1 => Ordering::Acquire,
            _ => Ordering::SeqCst,
        }
    }

    pub fn probe_atomic_symbolic_ordering() {
        let ptr: *mut usize = Box::into_raw(Box::new(0usize));
        let atomic = unsafe { AtomicUsize::from_ptr(ptr) };
        atomic.store(1, store_ordering());
        let _ = atomic.load(load_ordering());
        let _ = atomic.swap(2, any_ordering());
    }
"#;

/// Probe: Box::from_raw cleanup ONLY, no atomic operations.
/// Isolates the cleanup-tail translation drops from the atomic path.
const BOX_FROM_RAW_DROP_ONLY_PROBE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_box_from_raw_drop_only() {
        let ptr: *mut usize = Box::into_raw(Box::new(0usize));
        unsafe { drop(Box::from_raw(ptr)); }
    }
"#;

/// Part of #3706 D2: Isolation probe — atomic path without cleanup tail.
/// Measures translation drops from atomic operations alone.
#[test]
fn test_atomic_no_cleanup_translation_drops() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();

    with_test_ay_ctx_for_source(ATOMIC_NO_CLEANUP_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_atomic_no_cleanup");
        let body = instance.body().expect("function body");
        let _vc = mir_to_chc(ctx.tcx, &body, "probe_atomic_no_cleanup", ChcConfig::default());

        let fallback_count =
            get_chc_fallback_counts().get("probe_atomic_no_cleanup").copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "atomic-only path (no cleanup) should have zero CHC fallbacks, got {fallback_count}"
        );

        let translation_drops = take_translation_drop_by_fn();
        let drop_count = translation_drops.get("probe_atomic_no_cleanup").copied().unwrap_or(0);
        // Part of #3710: the atomic setup path is fully modeled now.
        // This no-cleanup probe leaks the Box deliberately, so any remaining
        // translation drops would come from Box::into_raw / from_ptr / the
        // atomic ops themselves, not from deallocation.
        assert_eq!(
            drop_count, 0,
            "atomic-only path (no cleanup) should have zero translation drops, got {drop_count}"
        );
    });

    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
}

/// Regression guard for #3710: fn_inline must handle nested `kani::any()` calls
/// inside the small Ordering helper functions used by `local_atomic`.
#[test]
fn test_atomic_symbolic_ordering_helpers_inline_without_inferable_fallback() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();

    with_test_ay_ctx_for_source(ATOMIC_SYMBOLIC_ORDERING_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_atomic_symbolic_ordering");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_atomic_symbolic_ordering", ChcConfig::default());

        assert!(!vc.relations.is_empty(), "symbolic-ordering probe should produce relations");
        assert!(!vc.rules.is_empty(), "symbolic-ordering probe should produce rules");

        let fallback_count =
            get_chc_fallback_counts().get("probe_atomic_symbolic_ordering").copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "symbolic-ordering probe should not increment CHC fallback count, got {fallback_count}"
        );

        let _ = crate::codegen_ay::take_inferable_predicate_count();

        let translation_drops = take_translation_drop_by_fn();
        let drop_count =
            translation_drops.get("probe_atomic_symbolic_ordering").copied().unwrap_or(0);
        assert_eq!(
            drop_count, 0,
            "symbolic-ordering probe should have zero translation drops, map={translation_drops:?}"
        );
    });

    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
}

/// Part of #3706 D2: Isolation probe — Box::from_raw cleanup tail only.
/// Measures translation drops from the deallocation path alone.
#[test]
fn test_box_from_raw_drop_only_translation_drops() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();

    with_test_ay_ctx_for_source(BOX_FROM_RAW_DROP_ONLY_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_from_raw_drop_only");
        let body = instance.body().expect("function body");
        let _vc = mir_to_chc(ctx.tcx, &body, "probe_box_from_raw_drop_only", ChcConfig::default());

        let fallback_count =
            get_chc_fallback_counts().get("probe_box_from_raw_drop_only").copied().unwrap_or(0);
        assert_eq!(
            fallback_count, 0,
            "box-from-raw cleanup should have zero CHC fallbacks, got {fallback_count}"
        );

        let translation_drops = take_translation_drop_by_fn();
        let drop_count =
            translation_drops.get("probe_box_from_raw_drop_only").copied().unwrap_or(0);
        // Empirically measured: 0 translation drops after D1 parity fix.
        // The cleanup-only probe (Box::into_raw + drop(Box::from_raw(ptr)))
        // confirms the call-terminator drop path now produces zero drops,
        // proving the D1 fix eliminated the cleanup-tail deficit.
        assert_eq!(
            drop_count, 0,
            "box-from-raw cleanup should have zero translation drops after D1 parity fix, got {drop_count}"
        );
    });

    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
}

// =============================================================================
// MIR-backed probes: atomic fence (no-op verification)
// =============================================================================

/// Probe: atomic fence (should be a no-op in sequential verification).
const ATOMIC_FENCE_PROBE: &str = r#"
    #![allow(dead_code)]
    use std::sync::atomic::{fence, Ordering};

    pub fn probe_fence() -> u32 {
        fence(Ordering::SeqCst);
        42
    }
"#;

/// Fences are no-ops in sequential verification. The VC should still be valid
/// and the function should produce a normal VC as if the fence wasn't there.
#[test]
fn test_atomic_fence_produces_valid_vc() {
    with_test_ay_ctx_for_source(ATOMIC_FENCE_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_fence");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_fence", ChcConfig::default());

        assert!(!vc.relations.is_empty(), "fence function should produce relations");
        assert!(!vc.rules.is_empty(), "fence function should produce rules");

        // Should have bv32 for the u32 return
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "fence function should have bv32 for u32 return");
    });
}

// =============================================================================
// Atomic write-dropping fallback counter regression (#3721)
// =============================================================================

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_atomic::CallDispatchAtomic;

const ATOMIC_STORE_PROBE: &str = r#"
    #![allow(dead_code)]
    use core::sync::atomic::{AtomicUsize, Ordering};

    pub fn probe_atomic_store(a: &AtomicUsize) {
        a.store(42, Ordering::SeqCst);
    }
"#;

const UNSTABLE_ATOMIC_STORE_SINGLE_ASSIGN_PROBE: &str = r#"
    #![allow(dead_code, internal_features)]
    #![feature(core_intrinsics)]
    use std::intrinsics::{AtomicOrdering, atomic_store};

    pub unsafe fn probe_unstable_atomic_store_single_assign() -> u8 {
        let mut value = 0u8;
        let ptr: *mut u8 = &mut value;
        unsafe { atomic_store::<_, { AtomicOrdering::SeqCst }>(ptr, 1u8); }
        value
    }
"#;

fn find_atomic_call_site(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    expected_fragments: &[&str],
) -> (usize, Operand, Place, Option<rustc_public::mir::BasicBlockIdx>, String) {
    let mut seen_paths = Vec::new();
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        if let rustc_public::mir::TerminatorKind::Call { func, destination, target, .. } =
            &block.terminator.kind
            && let Some(path) = chc_ctx.resolve_callee_path(func)
        {
            seen_paths.push(path.clone());
            if expected_fragments.iter().any(|fragment| path.contains(fragment)) {
                return (bb_idx, func.clone(), destination.clone(), *target, path);
            }
        }
    }

    panic!(
        "expected atomic call matching {expected_fragments:?}; observed call paths: {seen_paths:?}"
    );
}

#[test]
fn test_atomic_store_referent_local_excluded_from_single_assign_prescan() {
    use rustc_public::mir::{Operand, StatementKind, TerminatorKind};

    with_test_ay_ctx_for_source(UNSTABLE_ATOMIC_STORE_SINGLE_ASSIGN_PROBE, |ctx| {
        let instance =
            find_instance_by_suffix(ctx.tcx, "probe_unstable_atomic_store_single_assign");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_unstable_atomic_store_single_assign",
            ChcConfig::default(),
        );
        chc_ctx.declare_block_relations();

        let ptr_local = body
            .blocks
            .iter()
            .find_map(|block| match &block.terminator.kind {
                TerminatorKind::Call { func, args, .. }
                    if chc_ctx
                        .resolve_callee_path(func)
                        .or_else(|| chc_ctx.resolve_fn_def_name(func))
                        .as_deref()
                        .is_some_and(|path| path.contains("atomic_store")) =>
                {
                    match args.first().expect("atomic_store ptr arg") {
                        Operand::Copy(place) | Operand::Move(place)
                            if place.projection.is_empty() =>
                        {
                            Some(place.local)
                        }
                        other => panic!(
                            "expected bare-local ptr operand for atomic_store, got {other:?}"
                        ),
                    }
                }
                _ => None,
            })
            .expect("atomic_store call terminator");

        let ref_target = chc_ctx
            .ref_resolution
            .ref_targets
            .get(&ptr_local)
            .expect("atomic_store pointer should resolve through ref_targets");
        assert!(
            ref_target.projections.is_empty(),
            "atomic_store test expects plain-local ref_target, got {:?}",
            ref_target.projections
        );
        let referent_local = ref_target.local;

        let direct_assign_count = body
            .blocks
            .iter()
            .flat_map(|block| block.statements.iter())
            .filter(|stmt| match &stmt.kind {
                StatementKind::Assign(lhs, _) => {
                    lhs.projection.is_empty() && lhs.local == referent_local
                }
                _ => false,
            })
            .count();
        assert_eq!(
            direct_assign_count, 1,
            "probe should have exactly one direct MIR assign to the referent local before the indirect atomic write"
        );

        compute_single_assign_locals(&mut chc_ctx);

        assert!(
            !chc_ctx.encode.single_assign_locals.contains(&referent_local),
            "atomic_store referent local _{} must be excluded from single_assign_locals to avoid stale const_folded_call_results",
            referent_local
        );
    });
}

fn block_relation_app(chc_ctx: &ChcCtx<'_, '_>, bb_idx: usize) -> RelationApp {
    let from_rel = chc_ctx
        .block_relations
        .get(&bb_idx)
        .expect("source relation for atomic call block")
        .clone();
    let output_args: Vec<_> = chc_ctx
        .state_var_mgr
        .state_vars
        .iter()
        .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
        .collect();
    RelationApp::new(&from_rel, output_args)
}

fn assert_atomic_empty_args_fallback_is_demoted(
    source: &str,
    fn_suffix: &str,
    expected_fragments: &[&str],
    fallback_label: &str,
) {
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_suffix);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_suffix, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, func, destination, target, callee_path) =
            find_atomic_call_site(&chc_ctx, &body, expected_fragments);
        assert!(target.is_some(), "{fallback_label}: expected non-diverging atomic call");

        let from_app = block_relation_app(&chc_ctx, bb_idx);
        let modified_locals = HashSet::new();
        let before_rules = chc_ctx.vc.rules.len();
        let before_fallback = chc_ctx.fallback_count;
        let before_sound = chc_ctx.sound_fallback_count();

        let dcx = DispatchCallContext {
            bb_idx,
            func: &func,
            args: &[],
            destination: &destination,
            target: &target,
            from_app: &from_app,
            stmt_constraints: &[],
            modified_locals: &modified_locals,
            callee_path: None,
        };
        assert!(
            chc_ctx.try_dispatch_call_atomic(&dcx),
            "{fallback_label}: dispatcher should claim {callee_path}"
        );

        assert_eq!(
            chc_ctx.vc.rules.len(),
            before_rules + 1,
            "{fallback_label}: forced empty-args fallback should emit exactly one goto rule"
        );
        assert_eq!(
            chc_ctx.fallback_count,
            before_fallback + 1,
            "{fallback_label}: forced empty-args fallback must increment fallback_count (DEMOTED)"
        );
        assert_eq!(
            chc_ctx.sound_fallback_count(),
            before_sound,
            "{fallback_label}: forced empty-args fallback must NOT increment sound_fallback_count"
        );
    });
}

/// Part of #3721 D2: atomic_store insufficient-args fallback must increment
/// `fallback_count` (DEMOTED), not `sound_fallback_count` (SOUND_APPROXIMATION).
///
/// The store fallback drops the memory write, which is an under-approximation
/// that can lead to false PROOF. Reclassified from `record_sound_fallback()` to
/// `record_fallback()` in the same packet.
#[test]
fn test_atomic_store_fallback_increments_demoted_counter() {
    assert_atomic_empty_args_fallback_is_demoted(
        ATOMIC_STORE_PROBE,
        "probe_atomic_store",
        &["atomic_store", "::store"],
        "atomic_store write-dropping fallback",
    );
}

/// Part of #3721 D2: stable compare_exchange insufficient-args fallback must
/// increment `fallback_count` (DEMOTED), not `sound_fallback_count()`.
#[test]
fn test_atomic_compare_exchange_fallback_increments_demoted_counter() {
    assert_atomic_empty_args_fallback_is_demoted(
        ATOMIC_CMP_EXCHANGE_PROBE,
        "probe_compare_exchange",
        &["compare_exchange", "atomic_cxchg"],
        "atomic compare_exchange write-dropping fallback",
    );
}

/// Part of #3721 D2: shared atomic_rmw insufficient-args fallback must
/// increment `fallback_count` (DEMOTED), not `sound_fallback_count()`.
#[test]
fn test_atomic_fetch_add_fallback_increments_demoted_counter() {
    assert_atomic_empty_args_fallback_is_demoted(
        ATOMIC_FETCH_ADD_PROBE,
        "probe_fetch_add",
        &["fetch_add", "atomic_xadd", "atomic_uadd"],
        "atomic fetch_add write-dropping fallback",
    );
}

// =============================================================================
// Part of #3741: const-generic unstable atomic dispatch
// =============================================================================

use super::super::codegen_call_atomic::{detect_atomic_intrinsic, strip_generic_args};

// --- D4: Regression tests for const-generic path parsing ---

/// The exact path shape observed from diagnostic runs of unstable const-generic
/// atomic intrinsics. `strip_generic_args` must strip the trailing generics so
/// the function name can be extracted.
#[test]
fn test_strip_generic_args_unstable_atomic_path() {
    let path = "core::intrinsics::atomic_xadd::<u8, u8, std::intrinsics::AtomicOrdering::SeqCst>";
    assert_eq!(strip_generic_args(path), "core::intrinsics::atomic_xadd");
}

#[test]
fn test_strip_generic_args_no_generics() {
    let path = "core::intrinsics::atomic_xadd_seqcst";
    assert_eq!(strip_generic_args(path), path);
}

#[test]
fn test_strip_generic_args_stable_path() {
    let path = "std::sync::atomic::AtomicBool::load";
    assert_eq!(strip_generic_args(path), path);
}

/// `detect_atomic_intrinsic` must parse the const-generic path correctly.
#[test]
fn test_detect_atomic_intrinsic_const_generic_xadd() {
    let path = "core::intrinsics::atomic_xadd::<u8, u8, std::intrinsics::AtomicOrdering::SeqCst>";
    let kind = detect_atomic_intrinsic(path);
    assert!(
        matches!(kind, Some(super::super::codegen_call_atomic::AtomicKind::FetchAdd)),
        "expected FetchAdd for const-generic atomic_xadd, got {kind:?}"
    );
}

#[test]
fn test_detect_atomic_intrinsic_const_generic_store() {
    let path = "core::intrinsics::atomic_store::<u8, u8, std::intrinsics::AtomicOrdering::Release>";
    let kind = detect_atomic_intrinsic(path);
    assert!(
        matches!(kind, Some(super::super::codegen_call_atomic::AtomicKind::Store)),
        "expected Store for const-generic atomic_store, got {kind:?}"
    );
}

#[test]
fn test_detect_atomic_intrinsic_const_generic_cxchg() {
    let path = "core::intrinsics::atomic_cxchg::<u8, u8, std::intrinsics::AtomicOrdering::SeqCst, std::intrinsics::AtomicOrdering::SeqCst>";
    let kind = detect_atomic_intrinsic(path);
    assert!(
        matches!(kind, Some(super::super::codegen_call_atomic::AtomicKind::Cxchg)),
        "expected Cxchg for const-generic atomic_cxchg, got {kind:?}"
    );
}

/// Non-atomic path with `::<` should not be matched.
#[test]
fn test_detect_atomic_intrinsic_non_atomic_generic() {
    let path = "std::vec::Vec::<i32>::push";
    assert!(detect_atomic_intrinsic(path).is_none());
}

/// `detect_atomic_intrinsic` must parse const-generic `atomic_cxchgweak` paths
/// with two ordering type parameters.
#[test]
fn test_detect_atomic_intrinsic_const_generic_cxchgweak() {
    let path = "core::intrinsics::atomic_cxchgweak::<u8, u8, std::intrinsics::AtomicOrdering::SeqCst, std::intrinsics::AtomicOrdering::SeqCst>";
    let kind = detect_atomic_intrinsic(path);
    assert!(
        matches!(kind, Some(super::super::codegen_call_atomic::AtomicKind::Cxchg)),
        "expected Cxchg for const-generic atomic_cxchgweak, got {kind:?}"
    );
}

// --- D1: MIR-backed unstable atomic probes ---

/// Probe: unstable const-generic atomic_xadd.
/// Uses `#![feature(core_intrinsics)]` to test the exact call shape that
/// `tests/trust_mc/Intrinsics/Atomic/Unstable/AtomicAdd/main.rs` uses.
const UNSTABLE_ATOMIC_XADD_PROBE: &str = r#"
    #![feature(core_intrinsics)]
    #![allow(dead_code)]
    use std::intrinsics::{AtomicOrdering, atomic_xadd};

    pub fn probe_unstable_xadd() -> u8 {
        let mut a = 0u8;
        let ptr: *mut u8 = &mut a;
        unsafe { atomic_xadd::<_, _, { AtomicOrdering::SeqCst }>(ptr, 1u8) }
    }
"#;

/// CHC dispatch must claim the unstable const-generic atomic_xadd call.
/// Before #3741 fix, `detect_atomic_intrinsic` couldn't parse the generic path
/// and the call fell through as unhandled.
#[test]
fn test_unstable_atomic_xadd_dispatch_claimed() {
    with_test_ay_ctx_for_source(UNSTABLE_ATOMIC_XADD_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unstable_xadd");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_unstable_xadd", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Scan all call terminators and check that at least one atomic call is found.
        let mut atomic_claimed = false;
        let mut all_paths = Vec::new();
        let mut none_count = 0;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                let path =
                    chc_ctx.resolve_callee_path(func).or_else(|| chc_ctx.resolve_fn_def_name(func));
                match path {
                    Some(p) => {
                        if p.contains("atomic") {
                            atomic_claimed = true;
                        }
                        all_paths.push(format!("bb{bb_idx}: {p}"));
                    }
                    None => {
                        none_count += 1;
                        all_paths.push(format!("bb{bb_idx}: <None>"));
                    }
                }
            }
        }

        assert!(
            atomic_claimed,
            "resolve_callee_path (or fallback) must recover an atomic path \
             for unstable const-generic intrinsics. \
             Observed paths: {all_paths:?}, None count: {none_count}"
        );
    });
}

/// Unstable const-generic atomic_xadd should produce a valid VC (non-degenerate).
#[test]
fn test_unstable_atomic_xadd_produces_valid_vc() {
    with_test_ay_ctx_for_source(UNSTABLE_ATOMIC_XADD_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unstable_xadd");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_unstable_xadd", ChcConfig::default());

        assert!(!vc.relations.is_empty(), "unstable xadd should produce relations");
        assert!(!vc.rules.is_empty(), "unstable xadd should produce rules");
    });
}
