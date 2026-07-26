// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Stable-atomic inline policy tests.
//!
//! Part of #3777.

use super::FunctionInlinePass;

#[test]
fn test_has_special_codegen_handler_stable_atomic_ptr_methods() {
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "std::sync::atomic::AtomicPtr::<i32>::new"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "std::sync::atomic::AtomicPtr::<i32>::compare_exchange"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "core::sync::atomic::AtomicPtr::<i32>::compare_exchange_weak"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "core::sync::atomic::AtomicPtr::<i32>::fetch_byte_add"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "core::sync::atomic::AtomicPtr::<i32>::fetch_byte_sub"
    ));
}

#[test]
fn test_has_special_codegen_handler_stable_atomic_fetch_update_exception() {
    assert!(!FunctionInlinePass::has_special_codegen_handler(
        "core::sync::atomic::AtomicUsize::fetch_update"
    ));
    assert!(!FunctionInlinePass::has_special_codegen_handler(
        "core::sync::atomic::AtomicUsize::fetch_update::<{closure@src/lib.rs:10:5}>"
    ));
}

#[test]
fn test_has_special_codegen_handler_stable_atomic_excludes_backend_selectable_ops() {
    assert!(!FunctionInlinePass::has_special_codegen_handler(
        "core::sync::atomic::AtomicPtr::<i32>::from_ptr"
    ));
    assert!(!FunctionInlinePass::has_special_codegen_handler(
        "core::sync::atomic::AtomicUsize::into_inner"
    ));
}
