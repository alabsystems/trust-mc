// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for stub-internal type-array predeclaration.
//!
//! Part of #3713: `predeclare_stub_internal_type_arrays()` must predict
//! `std_mem_MaybeUninit_*` keys even when the only local using that type lives
//! on an error-only path that `collect_local_type_arrays()` skips.

use super::common::*;

const ASYNC_SPAWN_REAL_FILE: &str =
    include_str!("../../../../../tests/trust_mc/AsyncAwait/spawn.rs");
const LOCAL_KANI_ASYNC_RUNTIME: &str = include_str!("test_call_block_on_with_spawn_runtime.txt");
const STORAGE_MARKERS_REAL_FILE: &str =
    include_str!("../../../../../tests/trust_mc/StorageMarkers/main.rs");

fn build_async_spawn_decl_source(source: &str) -> String {
    let mut result = String::from(LOCAL_KANI_ASYNC_RUNTIME);
    result.push('\n');
    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("#[kani::proof")
            || trimmed.starts_with("#[kani::unwind")
            || trimmed.starts_with("// kani-expect:")
            || trimmed.starts_with("// compile-flags:")
            || trimmed.starts_with("// kani-flags:")
            || trimmed.starts_with("//!")
        {
            continue;
        }
        result.push_str(line);
        result.push('\n');
    }
    result
}

#[test]
fn test_predeclare_spawn_runtime_support_type_arrays() {
    let source = build_async_spawn_decl_source(ASYNC_SPAWN_REAL_FILE);
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_edition(&source, "2018", |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "round_robin_schedule_manual");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "round_robin_schedule_manual",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        let keys: Vec<_> = chc_ctx.heap_state.type_arrays.keys().map(|k| k.as_ref()).collect();
        assert!(
            keys.iter().any(|key| key.contains("Scheduler")),
            "spawn predeclare should register scheduler state carriers. keys: {keys:?}"
        );
        assert!(
            keys.iter().any(|key| key.contains("JoinHandle")),
            "spawn predeclare should register JoinHandle state. keys: {keys:?}"
        );
        assert!(
            keys.iter().any(|key| key.contains("YieldNow")),
            "spawn predeclare should register YieldNow state. keys: {keys:?}"
        );
        assert!(
            keys.iter().any(|key| key.contains("RoundRobin")),
            "spawn predeclare should register scheduling-plan state. keys: {keys:?}"
        );
        for contains_key in [
            "ref_std_task_Waker",
            "ref_std_task_LocalWaker",
            "std_panic_AssertUnwindSafe_core_task_wake_ExtData",
            "ptr",
            "std_boxed_Box_u8_std_alloc_Global",
        ] {
            assert!(
                keys.iter().any(|key| *key == contains_key),
                "spawn predeclare should register scheduler/waker support key {contains_key}. keys: {keys:?}"
            );
        }
        assert!(
            keys.iter().any(|key| key.contains("AtomicI64")),
            "spawn predeclare should register AtomicI64 state. keys: {keys:?}"
        );

        let opaque_fallback = ChcCtx::unknown_type_key_fallback_sort();
        for contains_key in [
            "Scheduler",
            "JoinHandle",
            "YieldNow",
            "RoundRobin",
            "SchedulingAssumption",
            "AtomicI64",
            "std_task_Waker",
            "std_task_LocalWaker",
            "core_task_wake_ExtData",
            "std_boxed_Box_u8_std_alloc_Global",
        ] {
            let (type_key, (_, elem_sort)) = chc_ctx
                .heap_state
                .type_arrays
                .iter()
                .find(|(type_key, _)| type_key.contains(contains_key))
                .unwrap_or_else(|| panic!("missing spawn support key containing {contains_key}"));
            assert_ne!(
                *elem_sort, opaque_fallback,
                "spawn predeclare should use MIR-derived sort for {type_key}, not opaque fallback"
            );
        }
    });
}

// Part of #3714: Vec<i32> into_iter must predeclare `i32` element type key so
// `mem_i32` is not late-created when codegen encounters a typed store.
const VEC_I32_INTO_ITER_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn vec_i32_into_iter_next() -> Option<i32> {
        let v = vec![1i32];
        let mut iter = v.into_iter();
        iter.next()
    }
"#;

#[test]
fn test_predeclare_vec_i32_into_iter_element_type() {
    with_test_ay_ctx_for_source(VEC_I32_INTO_ITER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "vec_i32_into_iter_next");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "vec_i32_into_iter_next",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        assert!(
            chc_ctx.heap_state.type_arrays.contains_key("i32"),
            "stub-internal predeclare should register i32 from Vec<i32>/IntoIter<i32>. keys: {:?}",
            chc_ctx.heap_state.type_arrays.keys().collect::<Vec<_>>()
        );
    });
}

#[test]
fn test_storage_marker_locals_predeclare_cleanup_type_arrays() {
    with_test_ay_ctx_for_source(STORAGE_MARKERS_REAL_FILE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "check_storagemarker_btreemap");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "check_storagemarker_btreemap",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        let keys: Vec<_> = chc_ctx.heap_state.type_arrays.keys().collect();
        for expected in [
            "ptr_InternalNode",
            "ptr_LeafNode",
            "LazyLeafRange_marker_Dying",
            "std_option_Option_LazyLeafHandle_marker_Dying",
            "NodeRef_marker_Dying_marker_Leaf",
        ] {
            assert!(
                chc_ctx.heap_state.type_arrays.contains_key(expected),
                "storage marker predeclare should register {expected}. keys: {keys:?}"
            );
        }
    });
}

const MAYBE_UNINIT_ERROR_PATH_SOURCE: &str = r#"
    #![allow(dead_code)]

    use core::mem::MaybeUninit;

    pub struct NonCopyWrapper {
        pub value: u32,
    }

    pub fn maybe_uninit_u32_in_panic(flag: bool) -> u32 {
        if flag {
            let slot: MaybeUninit<u32> = MaybeUninit::uninit();
            let _addr = slot.as_ptr() as usize;
            panic!("boom");
        }
        0
    }

    pub fn maybe_uninit_wrapper_in_panic(flag: bool) -> u32 {
        if flag {
            let slot: MaybeUninit<NonCopyWrapper> = MaybeUninit::uninit();
            let _addr = slot.as_ptr() as usize;
            panic!("boom");
        }
        0
    }
"#;

#[test]
fn test_declare_block_relations_predeclares_error_only_maybe_uninit_u32() {
    with_test_ay_ctx_for_source(MAYBE_UNINIT_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "maybe_uninit_u32_in_panic");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "maybe_uninit_u32_in_panic",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        // MaybeUninit<u32> is transparent-unwrapped to u32 by type_key_for_body_ty
        // (via unwrap_heap_transparent_ty). The inner type "u32" should be predeclared.
        let (arr_name, elem_sort) = chc_ctx
            .heap_state
            .type_arrays
            .get("u32")
            .expect("stub-internal predeclare should register u32 (unwrapped from MaybeUninit<u32>) on panic path");
        assert!(
            arr_name.contains("_mem_u32"),
            "array name should mention the u32 key, got {arr_name}"
        );
        assert_eq!(
            elem_sort.bitvec_width(),
            Some(32),
            "MaybeUninit<u32> unwraps to u32 element sort"
        );
    });
}

#[test]
fn test_declare_block_relations_maybe_uninit_wrapper_universal_types_predeclared() {
    // MaybeUninit<NonCopyWrapper> is transparent-unwrapped to NonCopyWrapper by
    // type_key_for_body_ty (via unwrap_heap_transparent_ty). The MaybeUninit
    // scanning code in predeclare_stub_internal_type_arrays currently cannot
    // detect this (dead filter on "std_mem_MaybeUninit_" prefix — see #3713).
    // Verify that universal types are still predeclared for this function body.
    with_test_ay_ctx_for_source(MAYBE_UNINIT_ERROR_PATH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "maybe_uninit_wrapper_in_panic");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "maybe_uninit_wrapper_in_panic",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        // Universal types (Option<usize>, Layout) should always be predeclared
        assert!(
            chc_ctx.heap_state.type_arrays.contains_key("std_option_Option_usize"),
            "universal type Option<usize> should be predeclared. keys: {:?}",
            chc_ctx.heap_state.type_arrays.keys().collect::<Vec<_>>()
        );
        assert!(
            chc_ctx.heap_state.type_arrays.contains_key("u32"),
            "u32 (from bool->u32 return and NonCopyWrapper field) should be predeclared. keys: {:?}",
            chc_ctx.heap_state.type_arrays.keys().collect::<Vec<_>>()
        );
    });
}

// Part of #4033: Rc<dyn Trait> must discover concrete element types from callee
// body locals when the concrete type is only visible inside called functions.
const RC_DYN_CALLEE_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::rc::Rc;

    struct Widget {
        pub active: bool,
    }

    trait Renderable {
        fn render(&self) -> u32;
    }

    impl Renderable for Widget {
        fn render(&self) -> u32 {
            if self.active { 1 } else { 0 }
        }
    }

    impl Widget {
        fn new_renderable(active: bool) -> Rc<dyn Renderable> {
            Rc::new(Widget { active })
        }
    }

    pub fn use_rc_dyn(active: bool) -> u32 {
        let r = Widget::new_renderable(active);
        r.render()
    }
"#;

#[test]
fn test_predeclare_rc_dyn_discovers_concrete_type_from_callee() {
    with_test_ay_ctx_for_source(RC_DYN_CALLEE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "use_rc_dyn");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "use_rc_dyn",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        let keys: Vec<_> = chc_ctx.heap_state.type_arrays.keys().collect();

        // The harness body only sees Rc<dyn Renderable>, but the callee
        // Widget::new_renderable has Rc<Widget> and Widget in its locals.
        // Callee scanning should discover Widget as an Rc element type.
        assert!(
            chc_ctx.heap_state.type_arrays.contains_key("std_rc_RcInner_Widget"),
            "RcInner<Widget> should be predeclared via callee body scan. keys: {keys:?}"
        );

        // Universal Rc infrastructure should also be present
        assert!(
            chc_ctx.heap_state.type_arrays.contains_key("std_rc_WeakInner"),
            "WeakInner should be predeclared. keys: {keys:?}"
        );

        // Part of #4033: stdlib-internal Rc element types (bool, u8) should be
        // predeclared — these come from deep Rc::drop/dealloc call chains.
        assert!(
            chc_ctx.heap_state.type_arrays.contains_key("std_rc_RcInner_bool"),
            "RcInner<bool> should be predeclared (stdlib internal). keys: {keys:?}"
        );
        assert!(
            chc_ctx.heap_state.type_arrays.contains_key("std_rc_RcInner_u8"),
            "RcInner<u8> should be predeclared (stdlib internal). keys: {keys:?}"
        );
        assert!(
            chc_ctx.heap_state.type_arrays.contains_key("std_rc_Rc_bool_std_alloc_Global"),
            "Rc<bool, Global> should be predeclared (stdlib internal). keys: {keys:?}"
        );
        assert!(
            chc_ctx.heap_state.type_arrays.contains_key("std_rc_Weak_u8_ref_std_alloc_Global"),
            "Weak<u8, &Global> should be predeclared (stdlib internal). keys: {keys:?}"
        );
    });
}

// Part of #4033: Rc<i32> must predeclare RcInner<i32>, PhantomData<RcInner<i32>>,
// and universal Rc infrastructure (WeakInner, ref_usize, ref_std_alloc_Global).
const RC_I32_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::rc::Rc;

    pub fn rc_i32_clone(x: i32) -> i32 {
        let a = Rc::new(x);
        let b = a.clone();
        *a + *b
    }
"#;

#[test]
fn test_predeclare_rc_i32_infrastructure_types() {
    with_test_ay_ctx_for_source(RC_I32_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "rc_i32_clone");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "rc_i32_clone",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        let keys: Vec<_> = chc_ctx.heap_state.type_arrays.keys().collect();

        // Element type itself should be predeclared (via carrier detection)
        assert!(
            chc_ctx.heap_state.type_arrays.contains_key("i32"),
            "Rc<i32> element type i32 should be predeclared. keys: {keys:?}"
        );

        // Rc infrastructure: RcInner<i32>
        assert!(
            chc_ctx.heap_state.type_arrays.contains_key("std_rc_RcInner_i32"),
            "Rc<i32> infrastructure RcInner<i32> should be predeclared. keys: {keys:?}"
        );

        // Rc infrastructure: PhantomData<RcInner<i32>>
        assert!(
            chc_ctx
                .heap_state
                .type_arrays
                .contains_key("std_marker_PhantomData_std_rc_RcInner_i32"),
            "PhantomData<RcInner<i32>> should be predeclared. keys: {keys:?}"
        );

        // Universal Rc infrastructure
        assert!(
            chc_ctx.heap_state.type_arrays.contains_key("std_rc_WeakInner"),
            "WeakInner should be predeclared. keys: {keys:?}"
        );
        assert!(
            chc_ctx.heap_state.type_arrays.contains_key("ref_usize"),
            "ref_usize should be predeclared. keys: {keys:?}"
        );
        assert!(
            chc_ctx.heap_state.type_arrays.contains_key("ref_std_alloc_Global"),
            "ref_std_alloc_Global should be predeclared. keys: {keys:?}"
        );
    });
}
