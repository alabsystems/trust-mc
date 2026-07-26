// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Focused helper coverage for chc/memory_impl.rs.
//!
//! Part of #2231 (true remaining gaps in memory_impl helper coverage).

#![allow(clippy::unwrap_used)]

use std::sync::Arc;

use super::common::*;

#[test]
fn test_get_or_create_local_address_is_stable_and_distinct() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_addr_locals(a: u32, b: u32) -> u32 {
            a.wrapping_add(b)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_addr_locals");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_addr_locals",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // MIR locals: 0=return, 1=arg a, 2=arg b.
        let addr_a_first = chc_ctx.get_or_create_local_address(1).unwrap();
        let addr_a_second = chc_ctx.get_or_create_local_address(1).unwrap();
        let addr_b = chc_ctx.get_or_create_local_address(2).unwrap();

        assert_eq!(addr_a_first, addr_a_second, "same local should map to same symbolic address");
        assert_ne!(
            addr_a_first, addr_b,
            "distinct locals should map to distinct symbolic addresses"
        );
        assert_eq!(addr_a_first.sort().bitvec_width(), Some(64));
        assert_eq!(addr_b.sort().bitvec_width(), Some(64));

        let obj_a = ChcCtx::try_extract_obj_id(&addr_a_first).expect("obj id for local a");
        let obj_b = ChcCtx::try_extract_obj_id(&addr_b).expect("obj id for local b");
        assert_ne!(obj_a, obj_b, "different locals should use different object ids");
    });
}

#[test]
fn test_load_ptr_from_memory_returns_pointer_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_arg(p: *const u32) -> usize {
            p as usize
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_ptr_arg");
        let ptr_ty = fn_sig.inputs()[0];

        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_arg");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_ptr_arg",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let addr = Expr::bitvec_const(0x1_0000_0000u128, 64);
        let loaded_ptr = chc_ctx
            .load_ptr_from_memory(addr, ptr_ty)
            .expect("pointer load should produce expression");

        assert_eq!(
            loaded_ptr.sort().bitvec_width(),
            Some(64),
            "pointer load should produce pointer-width bitvector"
        );
        assert!(
            loaded_ptr.to_string().contains("select"),
            "pointer load should be encoded as array select"
        );
    });
}

#[test]
fn test_build_memory_store_then_load_uses_store_chain() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_scalar_arg(x: u32) -> u32 {
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_scalar_arg");
        let scalar_ty = fn_sig.inputs()[0];

        let instance = find_instance_by_suffix(ctx.tcx, "probe_scalar_arg");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_scalar_arg",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let addr = Expr::bitvec_const(0x2_0000_0008u128, 64);
        let value = Expr::bitvec_const(123u128, 32);

        let store_result = chc_ctx.build_memory_store(addr.clone(), value, scalar_ty);
        assert!(
            store_result.is_none(),
            "stores are accumulated and emitted at block end, not returned immediately"
        );

        let loaded =
            chc_ctx.load_from_memory(addr, scalar_ty).expect("load should succeed after store");
        assert_eq!(
            loaded.sort().bitvec_width(),
            Some(32),
            "u32 load should produce bv32 expression"
        );

        // Part of #3608: constant-address store-to-load forwarding returns
        // the stored value directly instead of going through select(store(...)).
        // The value should be the original constant (possibly coerced).
        let load_smt = loaded.to_string();
        let uses_forwarding = !load_smt.contains("select");
        let uses_store_chain = load_smt.contains("store") && load_smt.contains("select");
        assert!(
            uses_forwarding || uses_store_chain,
            "load-after-store should use forwarding or store chain: {load_smt}"
        );
    });
}

#[test]
fn test_zst_array_memory_store_and_load_use_canonical_value() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_zst_array_arg(x: [(); 10]) -> [(); 10] {
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_zst_array_arg");
        let array_ty = fn_sig.inputs()[0];
        let pointee_sort = ChcCtx::translate_ty(array_ty).expect("ZST array sort");
        assert!(pointee_sort.is_bool(), "canonical [(); 10] sort should be Bool");

        let instance = find_instance_by_suffix(ctx.tcx, "probe_zst_array_arg");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_zst_array_arg",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let addr = Expr::bitvec_const(0x3_0000_0010u128, 64);
        let value = Expr::const_array(ay_bindings::Sort::bitvec(64), Expr::bool_const(true));
        assert!(value.sort().is_array(), "fixture should reproduce array-shaped ZST payload");

        let before_gap = chc_ctx.diagnostics.aggregate_encoding_gap.get();
        let store_result = chc_ctx.build_memory_store(addr.clone(), value, array_ty);
        assert!(
            store_result.is_none(),
            "stores are accumulated and emitted at block end, not returned immediately"
        );
        assert_eq!(
            chc_ctx.diagnostics.aggregate_encoding_gap.get(),
            before_gap,
            "ZST array memory store should not coerce through an unconstrained scalar"
        );

        let type_key = chc_ctx.type_key_for_body_ty(array_ty);
        let store_chain = chc_ctx
            .heap_state
            .get_store_chain(&type_key)
            .expect("ZST array store should update the type-indexed store chain");
        let stored_elem_sort =
            &store_chain.sort().array_sort().expect("store chain array").element_sort;
        assert!(
            stored_elem_sort.is_bool(),
            "typed heap stores ZST arrays through a canonical Bool cell"
        );

        let loaded =
            chc_ctx.load_from_memory(addr, array_ty).expect("ZST array load should succeed");
        assert_eq!(
            loaded.sort(),
            &pointee_sort,
            "ZST array load should produce the canonical value sort, not the array payload"
        );
    });
}

/// Fresh-allocation writes (BoxNew) suppress store-side heap access checks.
///
/// Regression for self-audit of #3589: `codegen_call_alloc` now drains
/// `pending_checks`, so `build_memory_store` must be able to skip the
/// destination write checks for fresh allocations while still allowing
/// unrelated source-load checks to flow through the call handler.
#[test]
fn test_build_memory_store_suppresses_fresh_alloc_write_checks() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_scalar_arg(x: u32) -> u32 {
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_scalar_arg");
        let scalar_ty = fn_sig.inputs()[0];

        let instance = find_instance_by_suffix(ctx.tcx, "probe_scalar_arg");
        let body = instance.body().expect("function body");
        let addr = Expr::bitvec_const(0x2_0000_0010u128, 64);
        let value = Expr::bitvec_const(55u128, 32);

        let mut baseline_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_scalar_arg_baseline_store_checks",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        baseline_ctx.build_memory_store(addr.clone(), value.clone(), scalar_ty);
        assert!(
            !baseline_ctx.heap_state.pending_checks.is_empty(),
            "ordinary stores should enqueue heap access checks"
        );

        let mut suppressed_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_scalar_arg_suppressed_store_checks",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        suppressed_ctx.suppress_heap_store_checks = true;
        suppressed_ctx.build_memory_store(addr, value, scalar_ty);
        assert!(
            suppressed_ctx.heap_state.pending_checks.is_empty(),
            "suppressed fresh-allocation stores must not enqueue heap access checks"
        );
    });
}

#[test]
fn test_load_from_memory_forwarding_is_same_block_only() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_scalar_forward(x: u32) -> u32 {
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_scalar_forward");
        let scalar_ty = fn_sig.inputs()[0];

        let instance = find_instance_by_suffix(ctx.tcx, "probe_scalar_forward");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_scalar_forward",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let addr = Expr::bitvec_const(11u128, 32).concat(Expr::bitvec_const(8u128, 32));
        let stored_value = Expr::bitvec_const(123u128, 32);
        let stored_value_smt = stored_value.to_string();

        let store_result = chc_ctx.build_memory_store(addr.clone(), stored_value, scalar_ty);
        assert!(store_result.is_none(), "stores remain block-accumulated");

        let same_block = chc_ctx
            .load_from_memory(addr.clone(), scalar_ty)
            .expect("same-block load should succeed");
        let same_block_smt = same_block.to_string();
        assert!(
            same_block_smt.contains(&stored_value_smt),
            "same-block load should use forwarding: {same_block_smt}"
        );

        chc_ctx.heap_state.reset_modified_arrays();
        chc_ctx.current_encode_bb += 1;

        let next_block = chc_ctx
            .load_from_memory(addr, scalar_ty)
            .expect("cross-block load should still succeed");
        let next_block_smt = next_block.to_string();
        assert!(
            next_block_smt.contains("select"),
            "cross-block load should fall back to array select, got: {next_block_smt}"
        );
        assert!(
            !next_block_smt.contains(&stored_value_smt),
            "cross-block load must not reuse stale forwarded value: {next_block_smt}"
        );
    });
}

#[test]
fn test_load_ptr_from_memory_forwarding_is_same_block_only() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_forward(p: *const u32) -> usize {
            p as usize
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_ptr_forward");
        let ptr_ty = fn_sig.inputs()[0];

        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_forward");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_ptr_forward",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let addr = Expr::bitvec_const(13u128, 32).concat(Expr::bitvec_const(16u128, 32));
        let stored_ptr = Expr::bitvec_const(0x1234_5678u128, 64);
        let stored_ptr_smt = stored_ptr.to_string();

        let store_result = chc_ctx.build_memory_store(addr.clone(), stored_ptr, ptr_ty);
        assert!(store_result.is_none(), "pointer stores remain block-accumulated");

        let same_block = chc_ctx
            .load_ptr_from_memory(addr.clone(), ptr_ty)
            .expect("same-block pointer load should succeed");
        let same_block_smt = same_block.to_string();
        assert!(
            same_block_smt.contains(&stored_ptr_smt),
            "same-block pointer load should use forwarding: {same_block_smt}"
        );

        chc_ctx.heap_state.reset_modified_arrays();
        chc_ctx.current_encode_bb += 1;

        let next_block = chc_ctx
            .load_ptr_from_memory(addr, ptr_ty)
            .expect("cross-block pointer load should still succeed");
        let next_block_smt = next_block.to_string();
        assert!(
            next_block_smt.contains("select"),
            "cross-block pointer load should fall back to array select, got: {next_block_smt}"
        );
        assert!(
            !next_block_smt.contains(&stored_ptr_smt),
            "cross-block pointer load must not reuse stale forwarded value: {next_block_smt}"
        );
    });
}

/// Part of #3664: A symbolic-address store within the same block must
/// invalidate all forwarding entries, preventing stale reads.
///
/// Scenario: constant store → symbolic store (same block) → constant load.
/// Without the fix, the load returns the stale forwarded value from the
/// first store instead of falling back to the array select.
#[test]
fn test_symbolic_store_invalidates_forwarding_same_block() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_symbolic_invalidation(x: u32, _ptr: *mut u32) -> u32 {
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_symbolic_invalidation");
        let scalar_ty = fn_sig.inputs()[0];

        let instance = find_instance_by_suffix(ctx.tcx, "probe_symbolic_invalidation");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_symbolic_invalidation",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Step 1: Constant-address store — creates a forwarding entry
        let const_addr = Expr::bitvec_const(11u128, 32).concat(Expr::bitvec_const(8u128, 32));
        let stored_value = Expr::bitvec_const(999u128, 32);
        let stored_value_smt = stored_value.to_string();
        chc_ctx.build_memory_store(const_addr.clone(), stored_value, scalar_ty);

        // Verify forwarding works before symbolic store
        let before_symbolic =
            chc_ctx.load_from_memory(const_addr.clone(), scalar_ty).expect("load should succeed");
        assert!(
            before_symbolic.to_string().contains(&stored_value_smt),
            "before symbolic store, forwarding should work"
        );

        // Step 2: Symbolic-address store — should invalidate all forwarding
        let symbolic_addr = Expr::var("_symbolic_ptr", ay_bindings::Sort::bitvec(64));
        let new_value = Expr::bitvec_const(777u128, 32);
        chc_ctx.build_memory_store(symbolic_addr, new_value, scalar_ty);

        // Step 3: Load from same constant address — must NOT use stale forwarding.
        // With forwarding, the result would be the direct constant (e.g., "#x000003e7").
        // Without forwarding, the result is a select over the store chain, which is
        // correct — the solver evaluates whether the symbolic address aliases.
        let after_symbolic = chc_ctx
            .load_from_memory(const_addr, scalar_ty)
            .expect("load should succeed after symbolic store");
        let after_smt = after_symbolic.to_string();
        assert!(
            after_smt.contains("select"),
            "after symbolic store, load must fall back to array select (#3664): {after_smt}"
        );
        // The forwarded value was a bare constant; after invalidation it should be
        // wrapped in a select expression, not returned directly.
        assert!(
            after_smt != stored_value_smt,
            "after symbolic store, result must not be the bare forwarded constant: {after_smt}"
        );
    });
}

#[test]
fn test_build_memory_store_ptr_mirrors_nonnull_alias_chain() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::ptr::NonNull;

        pub fn probe_ptr_alias(p: *const u32, q: NonNull<u32>) -> usize {
            (p as usize) ^ (q.as_ptr() as usize)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_ptr_alias");
        let ptr_ty = fn_sig.inputs()[0];
        let nonnull_ty = fn_sig.inputs()[1];

        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_alias");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_ptr_alias",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let addr = Expr::bitvec_const(0x6_0000_0008u128, 64);
        let value = Expr::bitvec_const(0x1234u128, 64);
        let store_result = chc_ctx.build_memory_store(addr.clone(), value, ptr_ty);
        assert!(store_result.is_none(), "store should be accumulated into store chain");

        let nonnull_key = ChcCtx::type_key_for_ty(nonnull_ty).into_owned();
        let store_keys: Vec<_> =
            chc_ctx.heap_state.store_chains.keys().map(|k| k.as_ref().to_string()).collect();
        assert!(
            chc_ctx.heap_state.get_store_chain(&nonnull_key).is_some(),
            "ptr store should mirror into NonNull alias store chain; nonnull_key={nonnull_key} store_keys={store_keys:?}"
        );

        let loaded = chc_ctx
            .load_from_memory(addr, nonnull_ty)
            .expect("load through NonNull alias should succeed");
        let load_smt = loaded.to_string();
        // Part of #3608: constant-address forwarding may bypass store chain
        let uses_forwarding = !load_smt.contains("select");
        let uses_store_chain = load_smt.contains("store");
        assert!(
            uses_forwarding || uses_store_chain,
            "alias load should use forwarding or store chain: {load_smt}"
        );
        assert_eq!(loaded.sort().bitvec_width(), Some(64));
    });
}

#[test]
fn test_build_memory_store_nonnull_mirrors_ptr_alias_chain() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        use std::ptr::NonNull;

        pub fn probe_nonnull_alias(p: *const u32, q: NonNull<u32>) -> usize {
            (p as usize).wrapping_add(q.as_ptr() as usize)
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_nonnull_alias");
        let ptr_ty = fn_sig.inputs()[0];
        let nonnull_ty = fn_sig.inputs()[1];

        let instance = find_instance_by_suffix(ctx.tcx, "probe_nonnull_alias");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_nonnull_alias",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let addr = Expr::bitvec_const(0x7_0000_0008u128, 64);
        let value = Expr::bitvec_const(0x55u128, 64);
        let store_result = chc_ctx.build_memory_store(addr.clone(), value, nonnull_ty);
        assert!(store_result.is_none(), "store should be accumulated into store chain");

        let ptr_key = ChcCtx::type_key_for_ty(ptr_ty).into_owned();
        let store_keys: Vec<_> =
            chc_ctx.heap_state.store_chains.keys().map(|k| k.as_ref().to_string()).collect();
        assert!(
            chc_ctx.heap_state.get_store_chain(&ptr_key).is_some(),
            "NonNull store should mirror into ptr alias store chain; ptr_key={ptr_key} store_keys={store_keys:?}"
        );

        let loaded =
            chc_ctx.load_from_memory(addr, ptr_ty).expect("load through ptr alias should succeed");
        let load_smt = loaded.to_string();
        // Part of #3608: constant-address forwarding may bypass store chain
        let uses_forwarding = !load_smt.contains("select");
        let uses_store_chain = load_smt.contains("store");
        assert!(
            uses_forwarding || uses_store_chain,
            "ptr load should use forwarding or store chain: {load_smt}"
        );
        assert_eq!(loaded.sort().bitvec_width(), Some(64));
    });
}

#[test]
fn test_build_memory_store_uses_declared_type_array_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_declared_sort(x: u32) -> u32 {
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_declared_sort");
        let scalar_ty = fn_sig.inputs()[0];

        let instance = find_instance_by_suffix(ctx.tcx, "probe_declared_sort");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_declared_sort",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let type_key = ChcCtx::type_key_for_ty(scalar_ty);
        let arr_name = format!("_{}_mem_{}", "probe_declared_sort", type_key);

        // Simulate pre-declared type-array metadata with a widened element sort.
        // build_memory_store should follow the declared sort rather than rebuilding
        // the array expression from translate_ty and drifting at drain time.
        chc_ctx
            .heap_state
            .type_arrays
            .insert(type_key.into_owned().into(), (Arc::from(arr_name.as_str()), Sort::bitvec(64)));
        // Part of #2793: keep reverse index in sync so drain_store_chains sort guard works.
        chc_ctx
            .heap_state
            .array_name_to_elem_sort
            .insert(Arc::from(arr_name.as_str()), Sort::bitvec(64));

        let addr = Expr::bitvec_const(0x3_0000_0008u128, 64);
        let value = Expr::bitvec_const(7u128, 32);
        let store_result = chc_ctx.build_memory_store(addr.clone(), value, scalar_ty);
        assert!(store_result.is_none(), "store should be accumulated into store chain");

        let constraints = chc_ctx.heap_state.drain_store_chains(&chc_ctx.diagnostics);
        assert_eq!(
            constraints.len(),
            1,
            "declared-sort store should survive drain_store_chains without mismatch drop"
        );

        let loaded = chc_ctx
            .load_from_memory(addr, scalar_ty)
            .expect("load should use declared type-array sort");
        assert_eq!(
            loaded.sort().bitvec_width(),
            Some(64),
            "load should use the declared array element sort"
        );
    });
}

#[test]
fn test_load_from_memory_datatype_pointee_falls_back_to_type_key_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[repr(C)]
        pub struct Pair {
            pub a: u8,
            pub b: u32,
        }

        pub fn probe_pair_arg(p: Pair) -> u32 {
            p.b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_pair_arg");
        let pair_ty = fn_sig.inputs()[0];

        let instance = find_instance_by_suffix(ctx.tcx, "probe_pair_arg");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_pair_arg",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let addr = Expr::bitvec_const(0x4_0000_0010u128, 64);
        let loaded = chc_ctx
            .load_from_memory(addr, pair_ty)
            .expect("load should succeed with datatype pointee fallback");

        let type_key = ChcCtx::type_key_for_ty(pair_ty);
        let (_, declared_sort) = chc_ctx
            .heap_state
            .type_arrays
            .get(&*type_key)
            .expect("type-indexed array should be created for datatype pointee");

        assert!(
            !declared_sort.is_datatype(),
            "datatype pointee should fallback to non-datatype bitvec sort in type array"
        );
        // Part of #2323: Datatype sorts are now flattened to bitvec based on
        // actual type size instead of falling to opaque byte-array. Pair is
        // repr(C) with (u8 + 3pad + u32) = 8 bytes = 64 bits.
        assert_eq!(
            declared_sort,
            &Sort::bitvec(64),
            "ADT type should flatten to size-based bitvec sort in type array"
        );
        // Part of #1739: coerce_loaded_value_for_pointee unflattens bitvec
        // back to Datatype on load, so the loaded sort is Datatype, not bitvec.
        assert!(
            loaded.sort().is_datatype(),
            "loaded value should be unflattened to Datatype sort via coerce_loaded_value_for_pointee"
        );
    });
}

#[test]
fn test_build_memory_store_datatype_pointee_falls_back_to_type_key_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[repr(C)]
        pub struct Pair {
            pub a: u8,
            pub b: u32,
        }

        pub fn probe_pair_arg(p: Pair) -> u32 {
            p.b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_pair_arg");
        let pair_ty = fn_sig.inputs()[0];

        let instance = find_instance_by_suffix(ctx.tcx, "probe_pair_arg");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_pair_arg",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let addr = Expr::bitvec_const(0x5_0000_0010u128, 64);
        let value = Expr::bitvec_const(7u128, 32);
        let store_result = chc_ctx.build_memory_store(addr, value, pair_ty);
        assert!(store_result.is_none(), "store should be accumulated into store chain");

        let constraints = chc_ctx.heap_state.drain_store_chains(&chc_ctx.diagnostics);
        assert_eq!(
            constraints.len(),
            1,
            "datatype pointee store should survive drain via type-key fallback sort"
        );

        let type_key = ChcCtx::type_key_for_ty(pair_ty);
        let (_, declared_sort) = chc_ctx
            .heap_state
            .type_arrays
            .get(&*type_key)
            .expect("type-indexed array should be created for datatype pointee");

        assert!(
            !declared_sort.is_datatype(),
            "datatype pointee memory array should not retain datatype element sort"
        );
        // Part of #2323: Datatype sorts are now flattened to bitvec based on
        // actual type size instead of falling to opaque byte-array.
        assert_eq!(
            declared_sort,
            &Sort::bitvec(64),
            "ADT type should flatten to size-based bitvec sort"
        );
    });
}

/// Exercise the `region_sort == elem_sort` path in `load_from_memory`.
///
/// This path was previously uncovered: no test set up a region array with a
/// typed sort matching the requested elem_sort and then loaded via an address
/// whose obj_id is statically extractable. The `.expect("region array must
/// exist for allocated obj_id")` at the re-fetch site would silently succeed
/// without any test ever reaching it.
#[test]
fn test_load_from_memory_zeroed_bv8_region_returns_typed_zero_without_upgrade() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_zeroed_region_load(x: u32) -> u32 {
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_zeroed_region_load");
        let scalar_ty = fn_sig.inputs()[0]; // u32

        let instance = find_instance_by_suffix(ctx.tcx, "probe_zeroed_region_load");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_zeroed_region_load",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let obj_id: u32 = 13;
        let (region_in, _region_out) =
            chc_ctx.assign_region_array_to_relation(obj_id, Sort::bitvec(8));
        chc_ctx.heap_state.mark_heap_obj_zeroed(obj_id);

        let addr = Expr::bitvec_const(obj_id as u128, 32).concat(Expr::bitvec_const(0u128, 32));
        let loaded =
            chc_ctx.load_from_memory(addr, scalar_ty).expect("zeroed region load should succeed");

        assert_eq!(loaded, Expr::bitvec_const(0u128, 32), "zeroed typed load should be bv32 zero");
        let (_region_name, _region_out_name, region_sort) =
            chc_ctx.heap_state.get_region_array(obj_id).expect("region should still exist");
        assert_eq!(
            region_sort,
            Sort::bitvec(8),
            "zeroed typed load should not upgrade the raw region"
        );
        assert!(
            !chc_ctx.heap_state.write_used_type_arrays.contains_key(&region_in),
            "zero shortcut must not synthesize a write to the raw region",
        );
    });
}

#[test]
fn test_load_from_memory_zeroed_bv8_region_written_still_upgrades() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_zeroed_region_written(x: u32) -> u32 {
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_zeroed_region_written");
        let scalar_ty = fn_sig.inputs()[0]; // u32

        let instance = find_instance_by_suffix(ctx.tcx, "probe_zeroed_region_written");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_zeroed_region_written",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let obj_id: u32 = 17;
        let (region_in, _region_out) =
            chc_ctx.assign_region_array_to_relation(obj_id, Sort::bitvec(8));
        chc_ctx.heap_state.mark_heap_obj_zeroed(obj_id);
        chc_ctx.heap_state.mark_type_array_written(&region_in, chc_ctx.current_encode_bb);

        let addr = Expr::bitvec_const(obj_id as u128, 32).concat(Expr::bitvec_const(0u128, 32));
        let loaded = chc_ctx
            .load_from_memory(addr, scalar_ty)
            .expect("written zeroed region load should succeed");

        assert!(
            loaded.to_string().contains("select"),
            "written zeroed region should take the normal array-select path"
        );
        let (_region_name, _region_out_name, region_sort) =
            chc_ctx.heap_state.get_region_array(obj_id).expect("region should still exist");
        assert_eq!(
            region_sort,
            Sort::bitvec(32),
            "written zeroed region should upgrade to typed sort"
        );
    });
}

#[test]
fn test_load_from_memory_zeroed_bv8_region_ignores_unrelated_type_array_write() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_zeroed_region_unrelated_write(x: u32) -> u32 {
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_zeroed_region_unrelated_write");
        let scalar_ty = fn_sig.inputs()[0]; // u32

        let instance = find_instance_by_suffix(ctx.tcx, "probe_zeroed_region_unrelated_write");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_zeroed_region_unrelated_write",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let written_obj_id: u32 = 23;
        let zeroed_obj_id: u32 = 24;
        let (_written_region_in, _written_region_out) =
            chc_ctx.assign_region_array_to_relation(written_obj_id, Sort::bitvec(8));
        let (_zeroed_region_in, _zeroed_region_out) =
            chc_ctx.assign_region_array_to_relation(zeroed_obj_id, Sort::bitvec(8));
        chc_ctx.heap_state.mark_heap_obj_zeroed(zeroed_obj_id);

        let write_addr =
            Expr::bitvec_const(written_obj_id as u128, 32).concat(Expr::bitvec_const(0u128, 32));
        let value = Expr::bitvec_const(42u128, 32);
        assert!(
            chc_ctx.build_memory_store(write_addr, value, scalar_ty).is_none(),
            "typed store should accumulate into heap state"
        );

        let load_addr =
            Expr::bitvec_const(zeroed_obj_id as u128, 32).concat(Expr::bitvec_const(0u128, 32));
        let loaded = chc_ctx
            .load_from_memory(load_addr, scalar_ty)
            .expect("zeroed region load should succeed");

        assert_eq!(
            loaded,
            Expr::bitvec_const(0u128, 32),
            "unrelated typed-array writes must not suppress the zeroed-region shortcut"
        );
        let (_region_name, _region_out_name, region_sort) =
            chc_ctx.heap_state.get_region_array(zeroed_obj_id).expect("region should still exist");
        assert_eq!(
            region_sort,
            Sort::bitvec(8),
            "zeroed region should stay raw when only unrelated objects were written"
        );
    });
}

#[test]
fn test_load_from_memory_unrelated_type_array_write_still_upgrades_region() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_region_load_unrelated_write(x: u32) -> u32 {
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_region_load_unrelated_write");
        let scalar_ty = fn_sig.inputs()[0]; // u32

        let instance = find_instance_by_suffix(ctx.tcx, "probe_region_load_unrelated_write");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_region_load_unrelated_write",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let written_obj_id: u32 = 31;
        let loaded_obj_id: u32 = 32;
        let (_written_region_in, _written_region_out) =
            chc_ctx.assign_region_array_to_relation(written_obj_id, Sort::bitvec(8));
        let (_loaded_region_in, _loaded_region_out) =
            chc_ctx.assign_region_array_to_relation(loaded_obj_id, Sort::bitvec(8));

        let write_addr =
            Expr::bitvec_const(written_obj_id as u128, 32).concat(Expr::bitvec_const(0u128, 32));
        let value = Expr::bitvec_const(42u128, 32);
        assert!(
            chc_ctx.build_memory_store(write_addr, value, scalar_ty).is_none(),
            "typed store should accumulate into heap state"
        );

        let load_addr =
            Expr::bitvec_const(loaded_obj_id as u128, 32).concat(Expr::bitvec_const(0u128, 32));
        let loaded = chc_ctx
            .load_from_memory(load_addr, scalar_ty)
            .expect("load from unrelated region should succeed");

        let (region_in, _region_out, region_sort) =
            chc_ctx.heap_state.get_region_array(loaded_obj_id).expect("region should still exist");
        assert_eq!(
            region_sort,
            Sort::bitvec(32),
            "writes to another object must not suppress this object's bv8->typed region upgrade"
        );
        let load_smt = loaded.to_string();
        assert!(load_smt.contains("select"), "upgraded region load should use select: {load_smt}");
        assert!(
            load_smt.contains(&*region_in),
            "upgraded region load should use the loaded object's region array '{region_in}': {load_smt}"
        );
    });
}

#[test]
fn test_load_from_memory_region_array_matching_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_region_load(x: u32) -> u32 {
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_region_load");
        let scalar_ty = fn_sig.inputs()[0]; // u32

        let instance = find_instance_by_suffix(ctx.tcx, "probe_region_load");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_region_load",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // Determine what elem_sort load_from_memory will compute for u32.
        let elem_sort = chc_ctx.elem_sort_for_memory_array(scalar_ty);
        assert_eq!(elem_sort, Sort::bitvec(32), "u32 should map to bv32 elem sort");

        // Assign a region array for obj_id=7 with elem_sort bv32 (matching).
        let obj_id: u32 = 7;
        let (region_in, _region_out) = chc_ctx.assign_region_array_to_relation(obj_id, elem_sort);

        // Build a split-pointer address: concat(obj_id_bv32, offset_bv32).
        // try_extract_obj_id will parse the upper 32 bits as obj_id.
        let addr = Expr::bitvec_const(obj_id as u128, 32).concat(Expr::bitvec_const(0x10u128, 32));
        assert_eq!(addr.sort().bitvec_width(), Some(64));

        // Verify try_extract_obj_id can parse our address.
        let extracted = ChcCtx::try_extract_obj_id(&addr);
        assert_eq!(extracted, Some(obj_id), "obj_id should be extractable from concat address");

        // Load from memory using the region array path.
        let loaded = chc_ctx
            .load_from_memory(addr, scalar_ty)
            .expect("load via region array should succeed");

        // The result should be a `select` on the region array, not a type array.
        let smt = loaded.to_string();
        assert!(smt.contains("select"), "region array load should use select: {smt}");
        assert!(
            smt.contains(&*region_in),
            "load should reference the region input array '{region_in}': {smt}"
        );
        assert_eq!(loaded.sort().bitvec_width(), Some(32), "u32 region load should produce bv32");
    });
}

/// Exercise the `region_sort == elem_sort` path in `build_memory_store`.
///
/// Same gap as load: the `.expect("region array must exist for allocated
/// obj_id")` at the store re-fetch site had zero direct coverage.
#[test]
fn test_build_memory_store_region_array_matching_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_region_store(x: u32) -> u32 {
            x
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_region_store");
        let scalar_ty = fn_sig.inputs()[0]; // u32

        let instance = find_instance_by_suffix(ctx.tcx, "probe_region_store");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_region_store",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let elem_sort = chc_ctx.elem_sort_for_memory_array(scalar_ty);

        // Assign a region array for obj_id=9 with matching sort.
        let obj_id: u32 = 9;
        let (_region_in, _region_out) = chc_ctx.assign_region_array_to_relation(obj_id, elem_sort);

        // Build split-pointer address with extractable obj_id.
        let addr = Expr::bitvec_const(obj_id as u128, 32).concat(Expr::bitvec_const(0x20u128, 32));

        let value = Expr::bitvec_const(42u128, 32);
        let store_result = chc_ctx.build_memory_store(addr.clone(), value, scalar_ty);
        assert!(store_result.is_none(), "region stores are accumulated, not returned");

        // The region key should have an accumulated store chain.
        let region_key = names::region_key(obj_id);
        let chain = chc_ctx.heap_state.get_store_chain(&region_key);
        assert!(
            chain.is_some(),
            "store on region array should accumulate a store chain for key '{region_key}'"
        );

        // Verify the accumulated store contains a `store` expression.
        let chain_smt = chain.unwrap().to_string();
        assert!(chain_smt.contains("store"), "store chain should contain store op: {chain_smt}");

        // The region should be marked modified.
        assert!(
            chc_ctx.heap_state.is_array_modified(&region_key),
            "region array should be marked modified after store"
        );

        // Load-after-store should return the stored value, either via
        // store-to-load forwarding (literal) or via store/select chain.
        let loaded = chc_ctx
            .load_from_memory(addr, scalar_ty)
            .expect("load-after-store via region should succeed");

        let load_smt = loaded.to_string();
        let forwarded = load_smt.contains("#x0000002a");
        let chain_path = load_smt.contains("store") && load_smt.contains("select");
        assert!(
            forwarded || chain_path,
            "load-after-store should return stored value (forwarded) or reference store/select chain: {load_smt}"
        );
    });
}

#[test]
fn test_layout_helpers_for_repr_c_struct() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        #[repr(C)]
        pub struct Pair {
            pub a: u8,
            pub b: u32,
        }

        pub fn probe_pair_layout(p: Pair) -> u32 {
            p.b
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let fn_sig = fn_sig_by_suffix(ctx.tcx, "probe_pair_layout");
        let pair_ty = fn_sig.inputs()[0];

        let instance = find_instance_by_suffix(ctx.tcx, "probe_pair_layout");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_pair_layout", ChcConfig::default());

        assert_eq!(chc_ctx.get_field_offset(pair_ty, 0), Some(0));
        assert_eq!(chc_ctx.get_field_offset(pair_ty, 1), Some(4));
        assert_eq!(chc_ctx.get_type_size(pair_ty), Some(8));
        assert_eq!(chc_ctx.get_type_align(pair_ty), Some(4));
    });
}
