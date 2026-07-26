// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for CHC memory model (memory_model.rs, memory_impl.rs, heap_state.rs).
//!
//! Part of #2188 — coverage for wide memory manager, pointer metadata,
//! and memory store/load constraint generation paths.
//!
//! ChcHeapState is tested indirectly through MIR-driven integration tests
//! since its methods are private to the chc module.

#![allow(clippy::unwrap_used)]

use super::super::memory_model::{MemPtr, WideMemManager};
use super::common::*;
use crate::codegen_ay::emit_chc;

// =============================================================================
// MemPtr tests (memory_model.rs)
// =============================================================================

#[test]
fn test_memptr_wide_has_size() {
    let ptr = MemPtr::wide(Expr::bitvec_const(64u64, 64));
    assert!(ptr.get_size().is_some(), "wide pointer should have size");
}

#[test]
fn test_memptr_wide_size_value() {
    let size = Expr::bitvec_const(128u64, 64);
    let ptr = MemPtr::wide(size.clone());
    let got_size = ptr.get_size().unwrap();
    assert_eq!(got_size.to_string(), size.to_string(), "wide pointer size should match");
}

#[test]
fn test_memptr_no_size() {
    let ptr = MemPtr { size: None };
    assert!(ptr.get_size().is_none(), "no-size pointer should return None");
}

#[test]
fn test_memptr_clone() {
    let ptr = MemPtr::wide(Expr::bitvec_const(32u64, 64));
    let cloned = ptr.clone();
    assert_eq!(
        cloned.get_size().unwrap().to_string(),
        ptr.get_size().unwrap().to_string(),
        "cloned MemPtr should have same size"
    );
}

// =============================================================================
// WideMemManager tests (memory_model.rs)
// =============================================================================

#[test]
fn test_wide_mem_new_64bit() {
    let mgr = WideMemManager::new(64);
    let ptr = MemPtr::wide(Expr::bitvec_const(8u64, 64));
    let result = mgr.is_dereferenceable(&ptr, 4);
    assert!(result.sort().is_bool(), "is_dereferenceable should return Bool sort");
}

#[test]
fn test_wide_mem_new_32bit() {
    let mgr = WideMemManager::new(32);
    let ptr = MemPtr::wide(Expr::bitvec_const(16u64, 32));
    let result = mgr.is_dereferenceable(&ptr, 8);
    assert!(result.sort().is_bool());
}

#[test]
fn test_wide_mem_dereferenceable_uses_bvuge() {
    let mgr = WideMemManager::new(64);
    let ptr = MemPtr::wide(Expr::bitvec_const(8u64, 64));
    let result = mgr.is_dereferenceable(&ptr, 8);
    let smt = result.to_string();
    assert!(smt.contains("bvuge"), "should use unsigned GE comparison, got: {smt}");
}

#[test]
fn test_wide_mem_dereferenceable_zero_access() {
    let mgr = WideMemManager::new(64);
    let ptr = MemPtr::wide(Expr::bitvec_const(0u64, 64));
    let result = mgr.is_dereferenceable(&ptr, 0);
    assert!(result.sort().is_bool());
}

#[test]
fn test_wide_mem_no_size_never_dereferenceable() {
    let mgr = WideMemManager::new(64);
    let ptr = MemPtr { size: None };
    let result = mgr.is_dereferenceable(&ptr, 1024);
    let smt = result.to_string();
    assert!(smt.contains("false"), "no-size pointer must fail closed, got: {smt}");
}

#[test]
fn test_wide_mem_missing_size_regression_cannot_pass_dereferenceability() {
    let mgr = WideMemManager::new(64);
    let ptr = MemPtr { size: None };

    for access_size in [1usize, 8, 1024] {
        let smt = mgr.is_dereferenceable(&ptr, access_size).to_string();
        assert!(
            smt.contains("false"),
            "missing size metadata must not silently satisfy dereferenceability for access {access_size}, got: {smt}"
        );
    }
}

#[test]
fn test_wide_mem_symbolic_size() {
    // Size is a symbolic variable, not a constant
    let mgr = WideMemManager::new(64);
    let mut vc = ChcVc::new();
    let sym_size = vc.declare_var("sz", Sort::bitvec(64));
    let ptr = MemPtr::wide(sym_size);
    let result = mgr.is_dereferenceable(&ptr, 16);
    let smt = result.to_string();
    assert!(smt.contains("sz"), "symbolic size should appear in bounds check, got: {smt}");
    assert!(smt.contains("bvuge"), "should use unsigned GE, got: {smt}");
}

#[test]
fn test_wide_mem_large_access_size() {
    let mgr = WideMemManager::new(64);
    let ptr = MemPtr::wide(Expr::bitvec_const(4u64, 64));
    // Access larger than allocation
    let result = mgr.is_dereferenceable(&ptr, 1_000_000);
    assert!(result.sort().is_bool());
}

// =============================================================================
// Memory-level translate integration tests (memory_impl.rs, heap_state.rs)
// =============================================================================

/// Tests that Mem-level tracking produces non-trivial VC for reference writes.
#[test]
fn test_mem_level_deref_store() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn write_through_ref(r: &mut u32, val: u32) {
            *r = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "write_through_ref");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "write_through_ref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(!smt.is_empty(), "Mem-level VC should produce non-empty SMT output");
        // Mem-level should declare relations for basic blocks
        assert!(
            smt.contains("declare-rel") || smt.contains("declare-fun"),
            "VC should declare block relations"
        );
        // Semantic: Mem-level deref store should use store() for heap memory writes.
        assert!(
            smt.contains("store"),
            "Mem-level deref store should use store() for memory writes, got: {}",
            &smt[..smt.len().min(500)]
        );
    });
}

/// Tests that Reg-level tracking of simple arithmetic produces a valid VC.
#[test]
fn test_reg_level_simple_arithmetic() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn simple_value(x: u32) -> u32 {
            x + 1
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "simple_value");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "simple_value", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(!smt.is_empty(), "Reg-level VC should produce non-empty SMT output");
        // Reg-level should also declare block relations
        assert!(
            smt.contains("declare-rel") || smt.contains("declare-fun"),
            "Reg-level VC should declare block relations"
        );
        // Should produce rules for all basic blocks
        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "Should have at least {bb_count} rules (one per BB), got {}",
            vc.rules.len()
        );
    });
}

/// Tests alloc stub detection for direct std::alloc::alloc calls.
#[test]
fn test_alloc_detection_direct_alloc() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::alloc::{alloc, Layout};

        pub fn probe_alloc_direct() -> *mut u8 {
            unsafe {
                let layout = Layout::new::<u32>();
                alloc(layout)
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_alloc_direct");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_alloc_direct",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Exercise alloc stub classification over all call terminators.
        let mut call_count = 0;
        let mut alloc_count = 0;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind {
                call_count += 1;
                if chc_ctx.detect_alloc_stub(func).is_some() {
                    alloc_count += 1;
                }
            }
        }
        assert!(call_count >= 1, "expected at least one call terminator in probe_alloc_direct");
        assert!(
            alloc_count >= 1,
            "expected at least one alloc-related stub call in probe_alloc_direct; got {alloc_count}"
        );
    });
}

/// Tests that Mem-level translate works end-to-end for a function with
/// both read and write through a mutable reference.
#[test]
fn test_mem_level_read_and_write() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn increment(r: &mut u32) {
            *r = *r + 1;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "increment");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "increment",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();
        assert!(
            !vc.rules.is_empty(),
            "Mem-level translate of increment should produce at least one rule"
        );
        // Semantic: increment (*r = *r + 1) at Mem-level should use store() for
        // the memory write and bvadd for the arithmetic.
        assert!(smt.contains("store"), "Mem-level increment should use store() for memory write");
    });
}

/// Tests Mem-level with array indexing (exercises handle_array_element_store).
#[test]
fn test_mem_level_array_write() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn write_array(arr: &mut [u32; 4], idx: usize, val: u32) {
            arr[idx] = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "write_array");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "write_array",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();
        assert!(!smt.is_empty(), "Mem-level array write should produce non-empty VC");
        // Should declare relations for basic blocks
        assert!(
            smt.contains("declare-rel") || smt.contains("declare-fun"),
            "Mem-level array write VC should declare block relations"
        );
        // Should produce rules for all basic blocks
        let bb_count = body.blocks.len();
        assert!(
            vc.rules.len() >= bb_count,
            "Should have at least {bb_count} rules (one per BB), got {}",
            vc.rules.len()
        );
        // Semantic: Mem-level array write should use store() for memory updates.
        assert!(smt.contains("store"), "Mem-level array write should use store()");
    });
}

// =============================================================================
// Mem-level struct field access tests (memory_impl.rs: translate_ref_to_address, Field projection)
// =============================================================================

/// Tests Mem-level translate with struct field write through mutable reference.
/// Exercises translate_ref_to_address → Field projection path.
#[test]
fn test_mem_level_struct_field_write() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Point { pub x: u32, pub y: u32 }

        pub fn set_x(p: &mut Point, val: u32) {
            p.x = val;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "set_x");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "set_x",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(!smt.is_empty(), "Mem-level struct field write should produce non-empty VC");
        assert!(
            vc.rules.len() >= body.blocks.len(),
            "Should have at least one rule per BB, got {} rules for {} BBs",
            vc.rules.len(),
            body.blocks.len()
        );
        // Semantic: Mem-level struct field write should use store() for heap memory.
        assert!(smt.contains("store"), "Mem-level struct field write should use store()");
    });
}

/// Tests Mem-level translate for reading a struct field through a reference.
#[test]
fn test_mem_level_struct_field_read() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Pair { pub a: u32, pub b: u32 }

        pub fn read_b(p: &Pair) -> u32 {
            p.b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "read_b");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "read_b",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();
        assert!(
            !vc.rules.is_empty(),
            "Mem-level struct field read should produce at least one rule"
        );
        // Semantic: Mem-level struct field read should use select() for memory load
        // or produce Array-typed state variables for the heap.
        assert!(
            smt.contains("select") || smt.contains("Array"),
            "Mem-level struct field read should use select() or Array sort"
        );
    });
}

/// Tests Reg-level translate for tuple element access (Field projection on tuples).
#[test]
fn test_reg_level_tuple_access() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn swap_tuple(t: (u32, u32)) -> (u32, u32) {
            (t.1, t.0)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "swap_tuple");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "swap_tuple", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(!smt.is_empty(), "Tuple access VC should not be empty");
        assert!(vc.rules.len() >= body.blocks.len(), "Should have at least one rule per BB");
        // Semantic: tuple of (u32, u32) should produce BitVec 32 state variables.
        assert!(smt.contains("BitVec 32"), "Tuple of u32 elements should have BitVec 32 sorts");
    });
}

// =============================================================================
// Control flow tests (codegen_rules.rs: SwitchInt, branch handling)
// =============================================================================

/// Tests that conditional branches (if/else) produce rules for both paths.
#[test]
fn test_conditional_branch_both_paths() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn abs_val(x: i32) -> i32 {
            if x < 0 { -x } else { x }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "abs_val");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "abs_val", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(!smt.is_empty(), "Conditional VC should not be empty");
        // if/else should produce at least 4 BBs (entry, true, false, return) → 4+ rules
        assert!(
            vc.rules.len() >= 4,
            "Conditional should produce at least 4 rules (got {})",
            vc.rules.len()
        );
        // Must declare the error relation
        assert!(
            vc.relations.iter().any(|r| r.name == "error"),
            "translate() must declare the error relation"
        );
    });
}

/// Tests match on enum-like values (SwitchInt with multiple targets).
#[test]
fn test_match_multiple_arms() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn classify(x: u32) -> u32 {
            match x {
                0 => 100,
                1 => 200,
                _ => 300,
            }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "classify");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "classify", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(!smt.is_empty(), "Match VC should not be empty");
        // Match with 3 arms should produce multiple rules
        assert!(
            vc.rules.len() >= 4,
            "Match with 3 arms should produce at least 4 rules (got {})",
            vc.rules.len()
        );
    });
}

// =============================================================================
// Reg-level edge case tests
// =============================================================================

/// Tests that a function with no parameters translates correctly.
#[test]
fn test_reg_level_no_params() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn constant() -> u32 {
            42
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "constant");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "constant", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        assert!(!vc.rules.is_empty(), "Constant function should still produce rules");
        // Should have an entry relation (named {fn_name}__bb{n})
        assert!(
            vc.relations.iter().any(|r| r.name.contains("__bb")),
            "Should declare at least one basic block relation"
        );
    });
}

/// Tests that boolean operations translate correctly at Reg level.
#[test]
fn test_reg_level_boolean_ops() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn and_or(a: bool, b: bool, c: bool) -> bool {
            (a && b) || c
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "and_or");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "and_or", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(!smt.is_empty(), "Boolean ops VC should not be empty");
        // Boolean short-circuit should produce multiple BBs
        assert!(vc.rules.len() >= body.blocks.len(), "Should have at least one rule per BB");
    });
}

/// Tests Mem-level translate with multiple mutable reference writes.
#[test]
fn test_mem_level_multi_write() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn swap(a: &mut u32, b: &mut u32) {
            let tmp = *a;
            *a = *b;
            *b = tmp;
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "swap");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "swap",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(!smt.is_empty(), "Multi-write VC should not be empty");
        assert!(vc.rules.len() >= body.blocks.len(), "Should have at least one rule per BB");
        // Semantic: swap's two writes through `&mut u32` references must produce
        // explicit per-write state transitions at Mem level. The encoder may
        // express this either through `store(mem, addr, val)` on a symbolic
        // heap array OR through per-pointee sidecar state vars
        // (`_foo_N_pointee`, `_foo_mem_u32_at_0x...`) when the pointer can be
        // resolved to a concrete-address sidecar. Either encoding is acceptable
        // as long as both writes are individually observable.
        let has_store = smt.contains("store");
        let has_pointee_track = smt.contains("_pointee") || smt.contains("_mem_u32_at_");
        assert!(
            has_store || has_pointee_track,
            "Mem-level multi-write swap should track both writes via store() \
             or per-pointee state vars; got SMT without either pattern"
        );
    });
}

/// Tests Reg-level with loop (exercises codegen_rules loop handling).
#[test]
fn test_reg_level_loop() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn sum_to(n: u32) -> u32 {
            let mut total = 0u32;
            let mut i = 0u32;
            while i < n {
                total = total.wrapping_add(i);
                i = i.wrapping_add(1);
            }
            total
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "sum_to");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "sum_to", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(!smt.is_empty(), "Loop VC should not be empty");
        // Loops create back edges which require rules connecting back to loop header
        assert!(
            vc.rules.len() >= body.blocks.len(),
            "Loop should produce at least one rule per BB (got {} rules for {} BBs)",
            vc.rules.len(),
            body.blocks.len()
        );
        // Semantic: wrapping_add in loop should produce bvadd in the SMT output.
        assert!(smt.contains("bvadd"), "Loop with wrapping_add should produce bvadd in SMT");
    });
}

// =============================================================================
// Mem-level store path tests (codegen_stmt_store.rs)
// =============================================================================

/// Tests Mem-level translate with nested struct access (Field + Field projection chain).
#[test]
fn test_mem_level_nested_struct_access() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct Inner { pub val: u32 }
        pub struct Outer { pub inner: Inner, pub tag: u32 }

        pub fn get_inner_val(o: &Outer) -> u32 {
            o.inner.val
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "get_inner_val");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "get_inner_val",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();
        assert!(!vc.rules.is_empty(), "Nested struct access at Mem level should produce rules");
        assert!(vc.rules.len() >= body.blocks.len(), "Should have at least one rule per BB");
        // Semantic: Mem-level nested struct read should produce Array-typed
        // state variables for the heap memory model.
        assert!(
            smt.contains("Array"),
            "Mem-level nested struct access should use Array sort for heap"
        );
    });
}

/// Tests Mem-level translate with slice length access (ConstantIndex projection).
#[test]
fn test_mem_level_slice_length_pattern() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn first_elem(s: &[u32]) -> u32 {
            s[0]
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "first_elem");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "first_elem",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        // Slice indexing involves bounds checks → panic paths → error rules
        assert!(!vc.rules.is_empty(), "Slice indexing at Mem level should produce rules");
        assert!(
            vc.relations.iter().any(|r| r.name == "error"),
            "Slice indexing should declare the error relation for bounds check panics"
        );

        // Semantic: Mem-level slice access should engage the memory model
        // (Array sort for heap memory) and bounds checking should produce
        // comparison constraints (bvult for unsigned index < length).
        let has_mem_var = vc.vars().iter().any(|v| v.sort.is_array());
        assert!(has_mem_var, "Mem-level slice access should declare Array-sorted memory variable");
        assert!(
            has_any_constraints(&vc),
            "Slice indexing should produce non-empty body constraints for bounds checks"
        );
    });
}

/// Tests that Reg-level translate handles cast operations correctly.
#[test]
fn test_reg_level_cast_widen() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn widen(x: u8) -> u32 {
            x as u32
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "widen");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "widen", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(!smt.is_empty(), "Cast widen VC should not be empty");
        assert!(vc.rules.len() >= body.blocks.len(), "Should have at least one rule per BB");
        // Semantic: cast from u8 to u32 should declare both BitVec 8 and BitVec 32 sorts.
        assert!(
            smt.contains("BitVec 8") && smt.contains("BitVec 32"),
            "Widening cast should have both 8-bit and 32-bit sorts"
        );
    });
}

/// Tests Reg-level translate with signed arithmetic (i32 operations).
#[test]
fn test_reg_level_signed_arithmetic() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn signed_diff(a: i32, b: i32) -> i32 {
            a.wrapping_sub(b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "signed_diff");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "signed_diff", ChcConfig::default());

        let (vc, _needs_mem_promote) = chc_ctx.translate();
        let smt = emit_chc(&vc).to_string();

        assert!(!smt.is_empty(), "Signed arithmetic VC should not be empty");
        assert!(vc.rules.len() >= body.blocks.len(), "Should have at least one rule per BB");
        // Semantic: wrapping_sub should produce bvsub in the SMT output.
        assert!(
            smt.contains("bvsub"),
            "wrapping_sub should produce bvsub in SMT, got: {}",
            &smt[..smt.len().min(500)]
        );
    });
}
