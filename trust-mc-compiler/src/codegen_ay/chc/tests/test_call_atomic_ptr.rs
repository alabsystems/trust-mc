// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for AtomicPtr-specific atomic dispatch paths.
//!
//! Part of #3776 — AtomicPtr::<T> stable method dispatch was broken because
//! `strip_generic_args` truncated at the type-level generic parameter,
//! losing the method name.
//!
//! Split from `test_call_atomic.rs` for file-size compliance.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

// =============================================================================
// D2: Regression tests for AtomicPtr::<T> generic path detection (#3776)
// =============================================================================

use super::super::codegen_call_atomic::detect_atomic_intrinsic;

/// AtomicPtr::<i32>::compare_exchange must be detected as CompareExchange.
#[test]
fn test_detect_atomic_intrinsic_atomicptr_compare_exchange() {
    let path = "std::sync::atomic::AtomicPtr::<i32>::compare_exchange";
    let kind = detect_atomic_intrinsic(path);
    assert!(
        matches!(kind, Some(super::super::codegen_call_atomic::AtomicKind::CompareExchange)),
        "expected CompareExchange for AtomicPtr::<i32>::compare_exchange, got {kind:?}"
    );
}

/// AtomicPtr::<i32>::compare_exchange_weak must also be detected.
#[test]
fn test_detect_atomic_intrinsic_atomicptr_compare_exchange_weak() {
    let path = "std::sync::atomic::AtomicPtr::<i32>::compare_exchange_weak";
    let kind = detect_atomic_intrinsic(path);
    assert!(
        matches!(kind, Some(super::super::codegen_call_atomic::AtomicKind::CompareExchange)),
        "expected CompareExchange for AtomicPtr::<i32>::compare_exchange_weak, got {kind:?}"
    );
}

/// AtomicPtr::<i32>::new must be detected as New.
#[test]
fn test_detect_atomic_intrinsic_atomicptr_new() {
    let path = "std::sync::atomic::AtomicPtr::<i32>::new";
    let kind = detect_atomic_intrinsic(path);
    assert!(
        matches!(kind, Some(super::super::codegen_call_atomic::AtomicKind::New)),
        "expected New for AtomicPtr::<i32>::new, got {kind:?}"
    );
}

/// AtomicPtr::<i32>::load must be detected as Load.
#[test]
fn test_detect_atomic_intrinsic_atomicptr_load() {
    let path = "std::sync::atomic::AtomicPtr::<i32>::load";
    let kind = detect_atomic_intrinsic(path);
    assert!(
        matches!(kind, Some(super::super::codegen_call_atomic::AtomicKind::Load)),
        "expected Load for AtomicPtr::<i32>::load, got {kind:?}"
    );
}

/// AtomicPtr::<i32>::store must be detected as Store.
#[test]
fn test_detect_atomic_intrinsic_atomicptr_store() {
    let path = "std::sync::atomic::AtomicPtr::<i32>::store";
    let kind = detect_atomic_intrinsic(path);
    assert!(
        matches!(kind, Some(super::super::codegen_call_atomic::AtomicKind::Store)),
        "expected Store for AtomicPtr::<i32>::store, got {kind:?}"
    );
}

/// AtomicPtr::<i32>::swap must be detected as Exchange.
#[test]
fn test_detect_atomic_intrinsic_atomicptr_swap() {
    let path = "std::sync::atomic::AtomicPtr::<i32>::swap";
    let kind = detect_atomic_intrinsic(path);
    assert!(
        matches!(kind, Some(super::super::codegen_call_atomic::AtomicKind::Exchange)),
        "expected Exchange for AtomicPtr::<i32>::swap, got {kind:?}"
    );
}

/// Non-generic AtomicBool paths still work after the reorder.
#[test]
fn test_detect_atomic_intrinsic_atomicbool_compare_exchange_still_works() {
    let path = "std::sync::atomic::AtomicBool::compare_exchange";
    let kind = detect_atomic_intrinsic(path);
    assert!(
        matches!(kind, Some(super::super::codegen_call_atomic::AtomicKind::CompareExchange)),
        "expected CompareExchange for AtomicBool::compare_exchange, got {kind:?}"
    );
}

// =============================================================================
// D1: MIR-backed probe for AtomicPtr compare_exchange (#3776)
// =============================================================================

/// Probe: AtomicPtr::<i32> compare_exchange — mirrors the smoke harness shape.
const ATOMIC_PTR_CMP_EXCHANGE_PROBE: &str = r#"
    #![allow(dead_code)]
    use std::sync::atomic::{AtomicPtr, Ordering};

    pub fn probe_atomicptr_compare_exchange() -> bool {
        let mut val: i32 = 42;
        let ptr: *mut i32 = &mut val;
        let atom = AtomicPtr::new(ptr);
        let result = atom.compare_exchange(
            ptr,
            core::ptr::null_mut(),
            Ordering::SeqCst,
            Ordering::SeqCst,
        );
        result.is_ok()
    }
"#;

/// AtomicPtr::<i32>::compare_exchange must produce a valid VC with zero
/// inferable predicates. Before the fix, the stable AtomicPtr method fell
/// through all dispatchers into the inferable-predicate fallback.
#[test]
fn test_atomicptr_compare_exchange_no_inferable_predicates() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_inferable_predicate_count();

    with_test_ay_ctx_for_source(ATOMIC_PTR_CMP_EXCHANGE_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_atomicptr_compare_exchange");
        let body = instance.body().expect("function body");
        let vc =
            mir_to_chc(ctx.tcx, &body, "probe_atomicptr_compare_exchange", ChcConfig::default());

        assert!(!vc.relations.is_empty(), "AtomicPtr compare_exchange should produce relations");
        assert!(!vc.rules.is_empty(), "AtomicPtr compare_exchange should produce rules");

        let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
        assert_eq!(
            inferable_count, 0,
            "AtomicPtr::<i32>::compare_exchange must NOT produce inferable predicates \
             (got {inferable_count}). If >0, the dispatch path is not reaching the \
             atomic handler — check detect_atomic_intrinsic for generic path parsing."
        );
    });

    let _ = crate::codegen_ay::take_inferable_predicate_count();
}
