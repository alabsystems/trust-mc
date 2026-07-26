// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Classification helpers for nested calls inside the inline walker.
//!
//! Part of #3768: When fn-inlined functions contain Rc::new, Box::new, or
//! similar allocation chains, the inline walker encounters nested calls that
//! it can't recursively inline. These classifiers detect call patterns that
//! can be handled with specialized semantics (concrete allocation, identity
//! passthrough, no-op) instead of falling back to nondeterministic overapprox.

/// Detect allocation calls that should produce concrete addresses in the inline walker.
///
/// When the inline walker encounters these inside a function being inlined
/// (e.g., Rc::new inside Table::new_furniture), the allocation body is
/// intrinsic-like and fails to inline recursively. Without interception,
/// the walker produces a nondeterministic address that disconnects all
/// downstream stores from loads.
pub(super) fn is_inline_alloc_call(path: &str) -> bool {
    path.ends_with("exchange_malloc")
        || path.ends_with("__rust_alloc")
        || path.ends_with("__rust_alloc_zeroed")
        || (path.contains("Box") && path.ends_with("::new"))
}

/// Detect pointer identity calls that are passthrough at the BV level.
///
/// Inside the inline walker, these calls often fail to resolve through the
/// stub registry (path normalization differences). Direct path matching
/// ensures the identity semantics are preserved so allocation addresses
/// propagate through NonNull/Unique/ptr::cast chains inside Rc::new, Box::new, etc.
pub(super) fn is_inline_pointer_identity_call(path: &str) -> bool {
    let method = path.rsplit("::").next().unwrap_or("");
    match method {
        "new_unchecked" => {
            path.contains("NonNull") || path.contains("Unique") || path.contains("pin::Pin")
        }
        "as_ptr" | "as_mut_ptr" => path.contains("NonNull"),
        "cast" => path.contains("NonNull") || path.contains("*const") || path.contains("*mut"),
        "as_non_null_ptr" => path.contains("NonNull"),
        "into_raw" | "into_raw_with_allocator" => {
            path.contains("Box") || path.contains("Rc") || path.contains("Arc")
        }
        // Rc/Arc::from_raw — reconstruct wrapper from raw pointer (identity at BV level).
        "from_raw" => path.contains("Rc") || path.contains("Arc"),
        // Rc/Arc constructors from NonNull — identity at BV level.
        "from_inner_in" | "from_inner" => path.contains("Rc") || path.contains("Arc"),
        _ => false,
    }
}

/// Detect calls that are no-ops at the SMT level (zero-sized result).
///
/// `mem::forget` transfers ownership without executing destructors — at the
/// SMT level this is a no-op. Without interception, the inline walker
/// produces a nondeterministic result, wasting a variable.
pub(super) fn is_inline_noop_call(path: &str) -> bool {
    if path.ends_with("::forget") && path.contains("mem") {
        return true;
    }
    // Part of #4067: Mutex/RwLock drop is a no-op in single-threaded CHC verification.
    // The Mutex type is transparent (Mutex<T> → T), so its Drop impl just destroys
    // the platform mutex (pthread) which has no semantic effect. Without this, the
    // inline walker expands into pthread foreign calls creating unconstrained memory.
    if (path.contains("sync::Mutex") || path.contains("sync::RwLock"))
        && (path.contains("drop_in_place") || path.ends_with("::drop"))
    {
        return true;
    }
    // Platform sync internals that appear in Mutex/RwLock drop paths.
    if path.contains("sys::sync::mutex")
        || path.contains("sys::pal::unix::sync")
        || path.contains("sync::poison")
    {
        return true;
    }
    false
}

/// Detect standard library UB-precondition check calls that are no-ops for CHC encoding.
///
/// The Rust standard library inserts `precondition_check` calls inside
/// `from_raw_parts`, `from_raw_parts_mut`, etc., guarded by `cfg(ub_checks)`.
/// These check pointer alignment, non-null, and size overflow at runtime but
/// return `()` and have no semantic effect on program state. Their bodies are
/// complex (alignment math, panic paths) and exhaust the inline walker budget,
/// producing 100+ symbolic fallback variables that contaminate the formula.
///
/// Skipping them is sound: the properties they check (alignment, non-null) are
/// either already modeled by the CHC encoding or are assumed-correct for
/// internal Vec/slice operations. Part of #4050.
pub(super) fn is_inline_ub_precondition_noop(path: &str) -> bool {
    path.ends_with("::precondition_check")
        && (path.contains("from_raw_parts")
            || path.contains("slice")
            || path.contains("hint::assert_unchecked"))
}

/// Detect Vec/RawVec internal allocation calls that are transparent at the CHC level.
///
/// Inside the inline walker, Vec operations like `Vec::new()` and
/// `RawVecInner::grow_amortized()` appear as nested calls. The Vec DT encoding
/// is handled by the top-level stub infrastructure, but the inline walker
/// re-encounters these calls when walking functions that use Vec internally.
///
/// These calls are allocation infrastructure with complex bodies (capacity
/// math, alignment, error handling) that exhaust the inline walker budget.
/// Treating them as no-ops is sound: allocation is assumed to always succeed,
/// and Vec capacity/buffer state is modeled by the Vec DT at the outer level.
/// Part of #4050.
pub(super) fn is_inline_vec_internal_noop(path: &str) -> bool {
    // RawVec growth/reserve calls — allocation infrastructure that always succeeds.
    if path.contains("RawVec") {
        let method = path.rsplit("::").next().unwrap_or("");
        if matches!(method, "grow_amortized" | "grow_one" | "reserve_for_push" | "reserve") {
            return true;
        }
    }
    // Vec::new — creates a zero-capacity Vec with no allocation.
    // Its body constructs RawVec::NEW → NonNull::dangling → alignment math,
    // which exhausts the inline walker budget. A noop is sound: the Vec DT
    // fields (len, cap, ptr) are set by the outer stub infrastructure.
    if path.contains("Vec") && path.ends_with("::new") && !path.contains("Box") {
        return true;
    }
    false
}

/// Check whether a type is a pointer wrapper (Box, Rc, Arc, etc.).
pub(super) fn type_is_pointer_wrapper(ty: rustc_public::ty::Ty) -> bool {
    use rustc_public::ty::{RigidTy, TyKind};
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
            type_is_pointer_wrapper(inner)
        }
        TyKind::RigidTy(RigidTy::Adt(..)) => {
            super::super::dyn_coercion::peel_pointer_like_wrapper_ty(ty) != ty
        }
        _ => false,
    }
}

/// Detect pointer wrapper deref calls (Box::deref, Rc::deref, etc.).
pub(super) fn is_nested_pointer_wrapper_deref_call(
    callee_path: &str,
    args: &[rustc_public::mir::Operand],
    outer_body: &rustc_public::mir::Body,
) -> bool {
    if !callee_path.ends_with("::deref") || !callee_path.contains("Deref>") {
        return false;
    }
    if super::super::ChcCtx::is_pointer_wrapper_deref_path(callee_path) {
        return true;
    }
    args.first()
        .and_then(|arg| arg.ty(outer_body.locals()).ok())
        .is_some_and(type_is_pointer_wrapper)
}
