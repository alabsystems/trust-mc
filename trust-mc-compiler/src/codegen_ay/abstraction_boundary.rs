// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! AY-specific implementation of the [`AbstractionBoundary`] trait.
//!
//! Bridges `kani_middle::reachability` (backend-agnostic) to `codegen_ay::stubs`
//! (backend-specific) via dependency inversion.

use crate::codegen_ay::diagnostics::record_unstubbed_abstraction;
use crate::codegen_ay::stubs::StubRegistry;
use crate::kani_middle::reachability::AbstractionBoundary;
use crate::kani_middle::stable_atomic_policy;

pub(in crate::codegen_ay) struct AYAbstractionBoundary {
    stub_registry: StubRegistry,
}

impl AYAbstractionBoundary {
    pub(in crate::codegen_ay) fn new() -> Self {
        Self { stub_registry: StubRegistry::new() }
    }
}

pub(crate) fn is_handler_backed_ay_abstraction(path: &str) -> bool {
    stable_atomic_policy::is_handler_backed_stable_atomic(path)
        || is_handler_backed_slice_contains(path)
        || is_handler_backed_sync_wrapper(path)
}

/// Mutex/RwLock methods handled by generic_preroutes (Part of #4067).
fn is_handler_backed_sync_wrapper(path: &str) -> bool {
    let is_sync = path.contains("sync::Mutex") || path.contains("sync::RwLock");
    if !is_sync {
        return false;
    }
    path.ends_with("::new")
        || path.ends_with("::into_inner")
        || path.ends_with("::get_mut")
        || path.ends_with("::lock")
        || path.ends_with("::read")
        || path.ends_with("::write")
}

fn is_handler_backed_slice_contains(path: &str) -> bool {
    if !path.ends_with("::contains") {
        return false;
    }

    (path.contains("slice::") || path.contains("<["))
        && !path.contains("HashMap")
        && !path.contains("BTreeMap")
        && !path.contains("BTreeSet")
        && !path.contains("HashSet")
        && !path.contains("Vec")
        && !path.contains("String")
}

impl AbstractionBoundary for AYAbstractionBoundary {
    fn has_explicit_stub(&self, path: &str) -> bool {
        self.stub_registry.has_stub(path)
    }

    fn has_handler_backed_abstraction(&self, path: &str) -> bool {
        is_handler_backed_ay_abstraction(path)
    }

    fn record_unstubbed_abstraction(&self, path: &str) {
        record_unstubbed_abstraction(path);
    }
}

#[cfg(test)]
mod tests {
    use super::is_handler_backed_ay_abstraction;

    #[test]
    fn test_handler_backed_ay_abstraction_accepts_stable_atomic_load() {
        assert!(is_handler_backed_ay_abstraction("std::sync::atomic::AtomicBool::load"));
    }

    #[test]
    fn test_handler_backed_ay_abstraction_accepts_slice_contains() {
        assert!(is_handler_backed_ay_abstraction("core::slice::<impl [char]>::contains"));
    }

    #[test]
    fn test_handler_backed_ay_abstraction_rejects_vec_and_string_contains() {
        assert!(!is_handler_backed_ay_abstraction("alloc::vec::Vec::<u8>::contains"));
        assert!(!is_handler_backed_ay_abstraction("core::str::<impl str>::contains"));
    }
}
