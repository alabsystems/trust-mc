// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Prescan controls only: shared owner handles can reach interior mutation.
//! The plain-data Safe/Bug twins below test exemption symmetry, not solver
//! semantics. Existing registered unchanged-getter Safe/Bug CLI rows remain
//! the full semantic controls for preservation after applying this draft.

use super::common::*;
use super::test_trust_box_new::{mem_config, with_native_box_ctx};
use crate::callee_body::CalleeBody;
use crate::kani_middle::std_abstraction::StdAbstraction;
use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};

const SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::{Cell, RefCell, UnsafeCell};

    // The printed name is not an interior-mutability classification.
    struct Mutex(u8);
    struct OrdinaryName(UnsafeCell<u8>);

    #[inline(never)]
    fn opaque_cell_mutation(values: &Vec<Cell<u8>>) { values[0].set(9); }
    #[inline(never)]
    fn opaque_refcell_mutation(values: &Vec<RefCell<u8>>) { values[0].replace(9); }
    #[inline(never)]
    fn opaque_mutex_mutation(values: &Vec<std::sync::Mutex<u8>>) {
        *values[0].lock().unwrap() = 9;
    }
    #[inline(never)]
    fn opaque_ordinary_mutation(values: &Vec<OrdinaryName>) {
        unsafe { *values[0].0.get() = 9; }
    }
    #[inline(never)]
    fn opaque_raw_owner_mutation(values: *const Vec<u8>) {
        unsafe { (&mut *values.cast_mut())[0] = 9; }
    }
    #[inline(never)]
    fn opaque_read_plain(values: &Vec<u8>) -> usize { values.len() }
    #[inline(never)]
    fn opaque_read_lookalike(values: &Vec<Mutex>) -> usize { values.len() }

    mod mimic {
        use std::cell::Cell;
        pub struct Vec<T>(pub std::marker::PhantomData<T>);
        // A query-looking name is still an effectful user function.
        #[inline(never)]
        pub fn len(values: &std::vec::Vec<Cell<u8>>) { values[0].set(9); }
    }

    pub fn classify_shared_buffer_types(
        _: Vec<Cell<u8>>,
        _: Vec<&Cell<u8>>,
        _: Vec<u8>,
        _: Vec<Mutex>,
        _: Vec<OrdinaryName>,
        _: Vec<Vec<Cell<u8>>>,
        _: Vec<std::sync::Mutex<u8>>,
        _: Vec<RefCell<u8>>,
        _: mimic::Vec<Cell<u8>>,
        _: Vec<mimic::Vec<Cell<u8>>>,
    ) {}

    pub fn shared_cell_before_getter_refusal() {
        let values = vec![Cell::new(3)];
        let handle = &values;
        opaque_cell_mutation(handle);
        let pointer = Vec::as_ptr(handle);
        unsafe { assert!((*pointer).get() == 9); }
    }

    pub fn shared_cell_after_getter_refusal() {
        let values = vec![Cell::new(3)];
        let handle = &values;
        let pointer = Vec::as_ptr(handle);
        opaque_cell_mutation(handle);
        unsafe { assert!((*pointer).get() == 9); }
    }

    pub fn shared_cell_parameter_before_getter_refusal(values: &Vec<Cell<u8>>) {
        if values.is_empty() { return; }
        opaque_cell_mutation(values);
        let pointer = Vec::as_ptr(values);
        unsafe { assert!((*pointer).get() == 9); }
    }

    pub fn shared_cell_parameter_after_getter_refusal(values: &Vec<Cell<u8>>) {
        if values.is_empty() { return; }
        let pointer = Vec::as_ptr(values);
        opaque_cell_mutation(values);
        unsafe { assert!((*pointer).get() == 9); }
    }

    pub fn raw_const_owner_parameter_refusal(values: *const Vec<u8>) {
        let handle = unsafe { &*values };
        if handle.is_empty() { return; }
        let pointer = Vec::as_ptr(handle);
        opaque_raw_owner_mutation(values);
        unsafe { assert!(*pointer == 9); }
    }

    pub fn shared_parameter_aggregate_refusal(values: &Vec<Cell<u8>>) {
        if values.is_empty() { return; }
        let pointer = Vec::as_ptr(values);
        let carrier = (values,);
        opaque_cell_mutation(carrier.0);
        unsafe { assert!((*pointer).get() == 9); }
    }

    pub fn shared_refcell_parameter_refusal(values: &Vec<RefCell<u8>>) {
        if values.is_empty() { return; }
        let pointer = Vec::as_ptr(values);
        opaque_refcell_mutation(values);
        unsafe { assert!(*(*pointer).borrow() == 9); }
    }

    pub fn shared_mutex_parameter_refusal(values: &Vec<std::sync::Mutex<u8>>) {
        if values.is_empty() { return; }
        let pointer = Vec::as_ptr(values);
        opaque_mutex_mutation(values);
        unsafe { assert!(*(*pointer).lock().unwrap() == 9); }
    }

    pub fn shared_ordinary_name_parameter_refusal(values: &Vec<OrdinaryName>) {
        if values.is_empty() { return; }
        let pointer = Vec::as_ptr(values);
        opaque_ordinary_mutation(values);
        unsafe { assert!(*(*pointer).0.get() == 9); }
    }

    pub fn shared_fake_query_name_refusal(values: &Vec<Cell<u8>>) {
        if values.is_empty() { return; }
        let pointer = Vec::as_ptr(values);
        mimic::len(values);
        unsafe { assert!((*pointer).get() == 9); }
    }

    pub fn interior_queries_preserve_exemption(values: &Vec<Cell<u8>>) {
        if values.is_empty() { return; }
        let pointer = Vec::as_ptr(values);
        let _ = values.len();
        let _ = values.capacity();
        let _ = values.is_empty();
        // Read only the address; Cell::get itself is outside this query-only
        // exemption control. No solver claim is made for this prescan case.
        let _value = unsafe { core::ptr::read(pointer) };
    }

    pub fn shared_plain_safe() {
        let values = vec![3u8];
        let handle = &values;
        let pointer = Vec::as_ptr(handle);
        assert!(opaque_read_plain(handle) == 1);
        unsafe { assert!(*pointer == 3); }
    }

    pub fn shared_plain_bug() {
        let values = vec![3u8];
        let handle = &values;
        let pointer = Vec::as_ptr(handle);
        assert!(opaque_read_plain(handle) == 1);
        unsafe { assert!(*pointer == 4); }
    }

    pub fn shared_lookalike_safe() {
        let values = vec![Mutex(3)];
        let handle = &values;
        let pointer = Vec::as_ptr(handle);
        assert!(opaque_read_lookalike(handle) == 1);
        unsafe { assert!((*pointer).0 == 3); }
    }

    pub fn shared_lookalike_bug() {
        let values = vec![Mutex(3)];
        let handle = &values;
        let pointer = Vec::as_ptr(handle);
        assert!(opaque_read_lookalike(handle) == 1);
        unsafe { assert!((*pointer).0 == 4); }
    }
"#;

#[test]
fn native_vec_buffer_guard_tracks_shared_interior_handles() {
    with_native_box_ctx(SOURCE, |ctx| {
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        for depth in [0, 32] {
            for name in [
                "shared_cell_before_getter_refusal",
                "shared_cell_after_getter_refusal",
                "shared_cell_parameter_before_getter_refusal",
                "shared_cell_parameter_after_getter_refusal",
                "raw_const_owner_parameter_refusal",
                "shared_parameter_aggregate_refusal",
                "shared_refcell_parameter_refusal",
                "shared_mutex_parameter_refusal",
                "shared_ordinary_name_parameter_refusal",
                "shared_fake_query_name_refusal",
                "interior_queries_preserve_exemption",
                "shared_plain_safe",
                "shared_plain_bug",
                "shared_lookalike_safe",
                "shared_lookalike_bug",
            ] {
                let instance = find_instance_by_suffix(ctx.tcx, name);
                let (_, body) = FunctionInlinePass::new(InlineConfig {
                    max_depth: depth,
                    chc_native_box_drop: true,
                    ..InlineConfig::default()
                })
                .transform_with_body_provider(
                    ctx.tcx,
                    instance.callee_body().unwrap(),
                    instance,
                    |callee| {
                        // Keep an effectful local call and its shared argument
                        // visible at both depths. These are prescan controls;
                        // no local-call or Cell solver semantics are credited.
                        if abstraction.abstracts_public_instance(ctx.tcx, callee)
                            || callee.name().contains("opaque_")
                            || callee.name().contains("mimic::len")
                        {
                            None
                        } else {
                            callee.callee_body()
                        }
                    },
                );
                let context = ChcCtx::new(ctx.tcx, &body, name, mem_config());
                context.book_vec_buffer_access_after_mutation();
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                    .remove(name)
                    .unwrap_or_default();
                let refused =
                    reasons.get("vec_buffer_access_after_mutation").copied().unwrap_or(0) > 0;
                assert_eq!(refused, name.ends_with("refusal"), "{name} depth={depth}: {reasons:?}");
            }
        }
    });
}

#[test]
fn native_vec_shared_storage_keeps_declared_element_authority() {
    with_native_box_ctx(SOURCE, |ctx| {
        let name = "classify_shared_buffer_types";
        let instance = find_instance_by_suffix(ctx.tcx, name);
        let body = instance.callee_body().unwrap();
        let context = ChcCtx::new(ctx.tcx, &body, name, mem_config());
        let expected = [
            ("Vec<Cell<u8>>", true),
            ("Vec<&Cell<u8>>", true),
            ("Vec<u8>", false),
            ("Vec<local Mutex(u8)>", false),
            ("Vec<OrdinaryName(UnsafeCell<u8>)>", true),
            ("Vec<Vec<Cell<u8>>>", true),
            ("Vec<std::sync::Mutex<u8>>", true),
            ("Vec<RefCell<u8>>", true),
            ("mimic::Vec<Cell<u8>>", false),
            ("Vec<mimic::Vec<Cell<u8>>>", false),
        ];
        assert_eq!(body.arg_locals().len(), expected.len());
        let mut type_memo = std::collections::HashMap::new();
        for (index, (label, can_change)) in expected.into_iter().enumerate() {
            assert_eq!(
                context
                    .vec_shared_type_can_change_buffer(body.locals()[index + 1].ty, &mut type_memo),
                can_change,
                "declared storage classification: {label}",
            );
        }
    });
}
