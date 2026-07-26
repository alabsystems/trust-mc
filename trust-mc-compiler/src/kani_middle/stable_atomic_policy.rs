// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared stable-atomic path classifier.
//!
//! Provides a single policy for classifying stable atomic API paths
//! (`std::sync::atomic::Atomic*`) into handler-backed operations vs.
//! methods that require MIR body inlining.
//!
//! Consumed by:
//! - `reachability.rs` — abstraction boundary (handler-backed = skip body collection)
//! - `transform/inline/mod.rs` — inline preservation (handler-backed = don't inline)
//!
//! Part of #3777

/// A recognized stable atomic operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StableAtomicOp {
    Load,
    Store,
    Swap,
    FetchAdd,
    FetchSub,
    FetchAnd,
    FetchOr,
    FetchXor,
    FetchNand,
    FetchMax,
    FetchMin,
    CompareExchange,
    CompareExchangeWeak,
    New,
    FromPtr,
    GetMut,
    Fence,
}

/// How the stable atomic path should be treated by the abstraction boundary
/// and inline pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StableAtomicDisposition {
    /// The operation has a CHC handler — preserve the call, skip body collection.
    PreserveForHandler(StableAtomicOp),
    /// The operation must be MIR-inlined (e.g., `fetch_update` contains a CAS loop
    /// with a closure that must go through normal dispatch).
    InlineBody,
}

/// Classify a `def_path_str()` path as a stable atomic operation, if applicable.
///
/// Returns `Some(PreserveForHandler(..))` for recognized stable-atomic operations,
/// `Some(InlineBody)` for operations requiring MIR inlining (e.g., `fetch_update`),
/// or `None` for non-atomic or unsupported atomic paths.
///
/// Accepts monomorphized paths like `std::sync::atomic::AtomicPtr::<i32>::swap`.
pub(crate) fn classify_stable_atomic_path(path: &str) -> Option<StableAtomicDisposition> {
    // Quick reject: path must contain the atomic module marker.
    if !is_stable_atomic_path(path) {
        return None;
    }

    // fetch_update must be inlined — it contains a CAS loop with a closure.
    // Use contains() because monomorphized paths may have trailing closure markers:
    // `::fetch_update::<{closure@...}>`
    if path.contains("::fetch_update") {
        return Some(StableAtomicDisposition::InlineBody);
    }

    // Match known stable-atomic operations by method suffix.
    // After the type name (e.g., `AtomicPtr::<i32>`) comes `::method_name`.
    let op = if path.contains("::load") {
        StableAtomicOp::Load
    } else if path.contains("::store") {
        StableAtomicOp::Store
    } else if path.contains("::swap") {
        StableAtomicOp::Swap
    } else if path.contains("::fetch_byte_add") || path.contains("::fetch_add") {
        StableAtomicOp::FetchAdd
    } else if path.contains("::fetch_byte_sub") || path.contains("::fetch_sub") {
        StableAtomicOp::FetchSub
    } else if path.contains("::fetch_and") {
        StableAtomicOp::FetchAnd
    } else if path.contains("::fetch_or") {
        StableAtomicOp::FetchOr
    } else if path.contains("::fetch_xor") {
        StableAtomicOp::FetchXor
    } else if path.contains("::fetch_nand") {
        StableAtomicOp::FetchNand
    } else if path.contains("::fetch_max") {
        StableAtomicOp::FetchMax
    } else if path.contains("::fetch_min") {
        StableAtomicOp::FetchMin
    } else if path.contains("::compare_exchange_weak") {
        StableAtomicOp::CompareExchangeWeak
    } else if path.contains("::compare_exchange") {
        StableAtomicOp::CompareExchange
    } else if path.contains("::new") {
        StableAtomicOp::New
    } else if path.contains("::from_ptr") {
        StableAtomicOp::FromPtr
    } else if path.contains("::get_mut") {
        StableAtomicOp::GetMut
    } else if path.ends_with("::fence") {
        StableAtomicOp::Fence
    } else {
        return None;
    };

    Some(StableAtomicDisposition::PreserveForHandler(op))
}

/// Returns `true` if the path belongs to the stable atomic API module.
///
/// Matches paths starting with or containing `core::sync::atomic::Atomic` or
/// `std::sync::atomic::Atomic`. Also matches angle-bracket forms like
/// `<std::sync::atomic::AtomicBool as core::fmt::Debug>::fmt`.
/// Also matches the free function `sync::atomic::fence` (Part of #4067).
pub(crate) fn is_stable_atomic_path(path: &str) -> bool {
    path.contains("sync::atomic::Atomic") || path.contains("sync::atomic::fence")
}

/// Returns `true` if this stable atomic path is handler-backed for the shared
/// phase-1 policy used by reachability and inline preservation.
///
/// `from_ptr` is intentionally excluded here: it is recognized by the classifier,
/// but phase 1 keeps backend-specific handling out of the shared abstraction
/// boundary and inline policy.
pub(crate) fn is_handler_backed_stable_atomic(path: &str) -> bool {
    matches!(
        classify_stable_atomic_path(path),
        Some(StableAtomicDisposition::PreserveForHandler(
            StableAtomicOp::Load
                | StableAtomicOp::Store
                | StableAtomicOp::Swap
                | StableAtomicOp::FetchAdd
                | StableAtomicOp::FetchSub
                | StableAtomicOp::FetchAnd
                | StableAtomicOp::FetchOr
                | StableAtomicOp::FetchXor
                | StableAtomicOp::FetchNand
                | StableAtomicOp::FetchMax
                | StableAtomicOp::FetchMin
                | StableAtomicOp::CompareExchange
                | StableAtomicOp::CompareExchangeWeak
                | StableAtomicOp::New
                | StableAtomicOp::GetMut
                | StableAtomicOp::Fence
        ))
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    // --- D4: Policy unit tests (Part of #3777) ---

    #[test]
    fn test_stable_atomic_classify_load() {
        let d = classify_stable_atomic_path("core::sync::atomic::AtomicBool::load");
        assert!(matches!(
            d,
            Some(StableAtomicDisposition::PreserveForHandler(StableAtomicOp::Load))
        ));
    }

    #[test]
    fn test_stable_atomic_classify_store() {
        let d = classify_stable_atomic_path("std::sync::atomic::AtomicU32::store");
        assert!(matches!(
            d,
            Some(StableAtomicDisposition::PreserveForHandler(StableAtomicOp::Store))
        ));
    }

    #[test]
    fn test_stable_atomic_classify_swap_monomorphized() {
        let d = classify_stable_atomic_path("std::sync::atomic::AtomicPtr::<i32>::swap");
        assert!(matches!(
            d,
            Some(StableAtomicDisposition::PreserveForHandler(StableAtomicOp::Swap))
        ));
    }

    #[test]
    fn test_stable_atomic_classify_fetch_add() {
        let d = classify_stable_atomic_path("core::sync::atomic::AtomicIsize::fetch_add");
        assert!(matches!(
            d,
            Some(StableAtomicDisposition::PreserveForHandler(StableAtomicOp::FetchAdd))
        ));
    }

    #[test]
    fn test_stable_atomic_classify_fetch_byte_add() {
        let d = classify_stable_atomic_path("core::sync::atomic::AtomicPtr::<i32>::fetch_byte_add");
        assert!(matches!(
            d,
            Some(StableAtomicDisposition::PreserveForHandler(StableAtomicOp::FetchAdd))
        ));
    }

    #[test]
    fn test_stable_atomic_classify_fetch_byte_sub() {
        let d = classify_stable_atomic_path("core::sync::atomic::AtomicPtr::<i32>::fetch_byte_sub");
        assert!(matches!(
            d,
            Some(StableAtomicDisposition::PreserveForHandler(StableAtomicOp::FetchSub))
        ));
    }

    #[test]
    fn test_stable_atomic_classify_compare_exchange() {
        let d =
            classify_stable_atomic_path("std::sync::atomic::AtomicPtr::<i32>::compare_exchange");
        assert!(matches!(
            d,
            Some(StableAtomicDisposition::PreserveForHandler(StableAtomicOp::CompareExchange))
        ));
    }

    #[test]
    fn test_stable_atomic_classify_compare_exchange_weak() {
        let d =
            classify_stable_atomic_path("core::sync::atomic::AtomicUsize::compare_exchange_weak");
        assert!(matches!(
            d,
            Some(StableAtomicDisposition::PreserveForHandler(StableAtomicOp::CompareExchangeWeak))
        ));
    }

    #[test]
    fn test_stable_atomic_classify_new() {
        let d = classify_stable_atomic_path("std::sync::atomic::AtomicPtr::<i32>::new");
        assert!(matches!(
            d,
            Some(StableAtomicDisposition::PreserveForHandler(StableAtomicOp::New))
        ));
    }

    #[test]
    fn test_stable_atomic_classify_from_ptr() {
        let d = classify_stable_atomic_path("core::sync::atomic::AtomicPtr::<u8>::from_ptr");
        assert!(matches!(
            d,
            Some(StableAtomicDisposition::PreserveForHandler(StableAtomicOp::FromPtr))
        ));
    }

    #[test]
    fn test_stable_atomic_fetch_update_inlined() {
        let d = classify_stable_atomic_path("core::sync::atomic::AtomicUsize::fetch_update");
        assert!(matches!(d, Some(StableAtomicDisposition::InlineBody)));
    }

    #[test]
    fn test_stable_atomic_fetch_update_monomorphized_closure() {
        // Monomorphized form with closure type parameter
        let d = classify_stable_atomic_path(
            "core::sync::atomic::AtomicUsize::fetch_update::<{closure@src/main.rs:10:5}>",
        );
        assert!(matches!(d, Some(StableAtomicDisposition::InlineBody)));
    }

    #[test]
    fn test_stable_atomic_non_atomic_returns_none() {
        assert!(classify_stable_atomic_path("std::sync::Mutex::lock").is_none());
        assert!(classify_stable_atomic_path("std::sync::Arc::new").is_none());
        assert!(classify_stable_atomic_path("my_module::AtomicCounter::load").is_none());
        assert!(classify_stable_atomic_path("alloc::vec::Vec::push").is_none());
    }

    #[test]
    fn test_stable_atomic_unknown_atomic_methods_return_none() {
        assert!(
            classify_stable_atomic_path("core::sync::atomic::AtomicUsize::into_inner").is_none()
        );
        assert!(
            classify_stable_atomic_path("<std::sync::atomic::AtomicBool as core::fmt::Debug>::fmt")
                .is_none()
        );
    }

    #[test]
    fn test_stable_atomic_classify_get_mut() {
        let d = classify_stable_atomic_path("std::sync::atomic::AtomicPtr::<T>::get_mut");
        assert!(matches!(
            d,
            Some(StableAtomicDisposition::PreserveForHandler(StableAtomicOp::GetMut))
        ));
    }

    #[test]
    fn test_stable_atomic_classify_fence() {
        let d = classify_stable_atomic_path("std::sync::atomic::fence");
        assert!(matches!(
            d,
            Some(StableAtomicDisposition::PreserveForHandler(StableAtomicOp::Fence))
        ));
    }

    #[test]
    fn test_is_handler_backed_stable_atomic() {
        assert!(is_handler_backed_stable_atomic("std::sync::atomic::AtomicBool::load"));
        assert!(is_handler_backed_stable_atomic(
            "std::sync::atomic::AtomicPtr::<i32>::compare_exchange"
        ));
        assert!(is_handler_backed_stable_atomic("std::sync::atomic::AtomicPtr::<i32>::new"));
        assert!(is_handler_backed_stable_atomic(
            "core::sync::atomic::AtomicPtr::<i32>::fetch_byte_add"
        ));
        // fetch_update is NOT handler-backed — it needs inlining
        assert!(!is_handler_backed_stable_atomic("core::sync::atomic::AtomicUsize::fetch_update"));
        assert!(!is_handler_backed_stable_atomic("core::sync::atomic::AtomicUsize::from_ptr"));
        assert!(!is_handler_backed_stable_atomic(
            "<std::sync::atomic::AtomicBool as core::fmt::Debug>::fmt"
        ));
        // Non-atomic is not handler-backed
        assert!(!is_handler_backed_stable_atomic("std::sync::Mutex::lock"));
        // Part of #4067: get_mut and fence are handler-backed
        assert!(is_handler_backed_stable_atomic("std::sync::atomic::AtomicPtr::<T>::get_mut"));
        assert!(is_handler_backed_stable_atomic("std::sync::atomic::fence"));
    }
}
