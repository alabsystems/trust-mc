// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Unit tests for pure string-matching predicates in `codegen_call_dispatch_dyn`.
//!
//! Part of #4138: these are the 5 untested string matchers that guard
//! Rc/Arc/Box dispatch routing. They have zero MIR dependency and are
//! critical path — a false negative silently drops the specialized handler
//! and falls through to the generic (often unsound) path.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::ChcCtx;

// ─── is_pointer_wrapper_deref_path ───

#[test]
fn test_is_pointer_wrapper_deref_path_box() {
    assert!(ChcCtx::is_pointer_wrapper_deref_path(
        "<alloc::boxed::Box<dyn Trait> as core::ops::deref::Deref>::deref"
    ));
}

#[test]
fn test_is_pointer_wrapper_deref_path_rc() {
    assert!(ChcCtx::is_pointer_wrapper_deref_path(
        "<alloc::rc::Rc<dyn Trait> as core::ops::deref::Deref>::deref"
    ));
}

#[test]
fn test_is_pointer_wrapper_deref_path_arc() {
    assert!(ChcCtx::is_pointer_wrapper_deref_path(
        "<alloc::sync::Arc<dyn Trait> as core::ops::deref::Deref>::deref"
    ));
}

#[test]
fn test_is_pointer_wrapper_deref_path_rejects_non_wrapper() {
    assert!(!ChcCtx::is_pointer_wrapper_deref_path(
        "<alloc::vec::Vec<u8> as core::ops::deref::Deref>::deref"
    ));
}

#[test]
fn test_is_pointer_wrapper_deref_path_rejects_no_deref_trait() {
    // Has ::deref suffix but no Deref> trait bound in path.
    assert!(!ChcCtx::is_pointer_wrapper_deref_path("alloc::boxed::Box<u8>::deref"));
}

#[test]
fn test_is_pointer_wrapper_deref_path_rejects_non_deref_suffix() {
    assert!(!ChcCtx::is_pointer_wrapper_deref_path(
        "<alloc::boxed::Box<dyn Trait> as core::ops::deref::Deref>::deref_mut"
    ));
}

// ─── is_pointer_wrapper_as_ptr_path ───

#[test]
fn test_is_pointer_wrapper_as_ptr_path_rc() {
    assert!(ChcCtx::is_pointer_wrapper_as_ptr_path("alloc::rc::Rc<T>::as_ptr"));
}

#[test]
fn test_is_pointer_wrapper_as_ptr_path_arc() {
    assert!(ChcCtx::is_pointer_wrapper_as_ptr_path("alloc::sync::Arc<T>::as_ptr"));
}

#[test]
fn test_is_pointer_wrapper_as_ptr_path_arc_as_mut_ptr() {
    assert!(ChcCtx::is_pointer_wrapper_as_ptr_path("alloc::sync::Arc<T>::as_mut_ptr"));
}

#[test]
fn test_is_pointer_wrapper_as_ptr_path_rejects_box() {
    // Box does not have as_ptr dispatch in this codegen path.
    assert!(!ChcCtx::is_pointer_wrapper_as_ptr_path("alloc::boxed::Box<T>::as_ptr"));
}

#[test]
fn test_is_pointer_wrapper_as_ptr_path_rejects_vec() {
    assert!(!ChcCtx::is_pointer_wrapper_as_ptr_path("alloc::vec::Vec<T>::as_ptr"));
}

// ─── is_rc_arc_clone_path ───

#[test]
fn test_is_rc_arc_clone_path_rc() {
    assert!(ChcCtx::is_rc_arc_clone_path(
        "<alloc::rc::Rc<dyn Trait> as core::clone::Clone>::clone"
    ));
}

#[test]
fn test_is_rc_arc_clone_path_arc() {
    assert!(ChcCtx::is_rc_arc_clone_path(
        "<alloc::sync::Arc<dyn Trait> as core::clone::Clone>::clone"
    ));
}

#[test]
fn test_is_rc_arc_clone_path_rejects_box() {
    assert!(!ChcCtx::is_rc_arc_clone_path("<alloc::boxed::Box<T> as core::clone::Clone>::clone"));
}

#[test]
fn test_is_rc_arc_clone_path_rejects_vec() {
    assert!(!ChcCtx::is_rc_arc_clone_path("<alloc::vec::Vec<T> as core::clone::Clone>::clone"));
}

// ─── is_rc_arc_new_path ───

#[test]
fn test_is_rc_arc_new_path_rc() {
    assert!(ChcCtx::is_rc_arc_new_path("alloc::rc::Rc<T>::new"));
}

#[test]
fn test_is_rc_arc_new_path_arc() {
    assert!(ChcCtx::is_rc_arc_new_path("alloc::sync::Arc<T>::new"));
}

#[test]
fn test_is_rc_arc_new_path_rejects_box() {
    assert!(!ChcCtx::is_rc_arc_new_path("alloc::boxed::Box<T>::new"));
}

#[test]
fn test_is_rc_arc_new_path_rejects_suffix_mismatch() {
    assert!(!ChcCtx::is_rc_arc_new_path("alloc::rc::Rc<T>::new_uninit"));
}

// ─── is_shared_pointer_wrapper_constructor_path ───

#[test]
fn test_is_shared_pointer_wrapper_constructor_path_rc_from_inner() {
    assert!(ChcCtx::is_shared_pointer_wrapper_constructor_path("alloc::rc::Rc<T>::from_inner"));
}

#[test]
fn test_is_shared_pointer_wrapper_constructor_path_rc_from_inner_in() {
    assert!(ChcCtx::is_shared_pointer_wrapper_constructor_path("alloc::rc::Rc<T>::from_inner_in"));
}

#[test]
fn test_is_shared_pointer_wrapper_constructor_path_arc_from_inner() {
    assert!(ChcCtx::is_shared_pointer_wrapper_constructor_path("alloc::sync::Arc<T>::from_inner"));
}

#[test]
fn test_is_shared_pointer_wrapper_constructor_path_rejects_box() {
    assert!(!ChcCtx::is_shared_pointer_wrapper_constructor_path(
        "alloc::boxed::Box<T>::from_inner"
    ));
}

#[test]
fn test_is_shared_pointer_wrapper_constructor_path_rejects_from_raw() {
    assert!(!ChcCtx::is_shared_pointer_wrapper_constructor_path("alloc::rc::Rc<T>::from_raw"));
}
