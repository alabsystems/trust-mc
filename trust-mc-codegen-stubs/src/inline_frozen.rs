// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unified inline-freeze registry for MIR inlining control.
//!
//! Consolidates the exclusion logic from `has_special_codegen_handler()` in
//! `kani_middle/transform/inline/mod.rs` and the `StubRegistry::lookup()` path
//! resolution into a single source of truth. Functions returning
//! `Some(InlineFrozenKind)` must NOT be inlined by the MIR InlinePass because
//! the CHC/BMC codegen has dedicated handlers for them.
//!
//! Part of #4248, #4244 — Phase 1 of the MIR inlining robustness design.
//! See `designs/2026-04-16-mir-inlining-robustness.md`.

use crate::{StubKind, StubRegistry};

/// Why a function path is frozen from MIR inlining.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InlineFrozenKind {
    /// Has a semantic stub model in `StubRegistry` (HashMap, Vec, BigInt, etc.).
    Stub(StubKind),
    /// Checked/wrapping/saturating/overflowing/unchecked arithmetic intrinsics.
    /// These have direct SMT encoding (bvadd, bvsub, etc.) that would be lost
    /// if the MIR body (which contains branching overflow checks) were inlined.
    ArithmeticIntrinsic,
    /// Power / euclidean div-rem operations.
    /// The CHC handler encodes these as ite-guarded BV operations directly.
    ArithmeticMethod,
    /// `block_on` and coroutine entry points.
    /// The CHC specializer rewrites the unbounded poll loop into a single-poll.
    BlockBoundary,
    /// Rc::new / Arc::new — CHC models allocation + store directly.
    WrapperConstructor,
    /// SIMD operations (from_array, to_array, splat, etc.).
    /// CHC encodes these via transparent SIMD type unwrapping.
    SimdOperation,
    /// typed_swap / mem::swap — CHC models as direct cross-assignment.
    SwapIntrinsic,
    /// ArraySolver methods — CHC shadow dispatcher replaces loop-heavy bodies
    /// with single SMT array operations.
    ArraySolverMethod,
    /// Dispatch-chain handler without a StubKind (slice::contains disjunction,
    /// etc.). These have CHC handlers that are dispatched via the call spine
    /// but are not registered in the StubRegistry path-to-StubKind mapping.
    DispatchChainHandler,
}

impl StubRegistry {
    /// Returns `Some(InlineFrozenKind)` if the given function path must NOT be
    /// inlined by the MIR InlinePass. Returns `None` if the function is safe
    /// to inline.
    ///
    /// This is the single source of truth for path-based inline exclusion.
    /// The `has_special_codegen_handler()` function in the inline pass should
    /// delegate to this method.
    ///
    /// NOTE: This covers only *path-based* exclusion. Instance-resolved checks
    /// (Rc/Arc clone, compound PartialEq, iterator adapter next, stubbed trait
    /// impls) require type information and remain in the inline pass as
    /// supplementary guards.
    pub fn is_inline_frozen(&self, path: &str) -> Option<InlineFrozenKind> {
        if let Some(stub_kind) = self.lookup(path) {
            return Some(InlineFrozenKind::Stub(stub_kind));
        }
        if Self::is_frozen_collection_module(path) {
            return Some(InlineFrozenKind::DispatchChainHandler);
        }
        if let Some(kind) = Self::is_frozen_intrinsic_or_special(path) {
            return Some(kind);
        }
        if Self::is_frozen_slice_contains(path) {
            return Some(InlineFrozenKind::DispatchChainHandler);
        }
        None
    }

    /// Non-stub, non-collection frozen paths: arithmetic intrinsics, power/euclid
    /// methods, block_on, Rc/Arc::new, SIMD, swap, ArraySolver.
    fn is_frozen_intrinsic_or_special(path: &str) -> Option<InlineFrozenKind> {
        if path.contains("checked_")
            || path.contains("wrapping_")
            || path.contains("saturating_")
            || path.contains("overflowing_")
            || path.contains("unchecked_")
        {
            return Some(InlineFrozenKind::ArithmeticIntrinsic);
        }
        if path.ends_with("::pow") {
            return Some(InlineFrozenKind::ArithmeticMethod);
        }
        if path.ends_with("::div_euclid") || path.ends_with("::rem_euclid") {
            return Some(InlineFrozenKind::ArithmeticMethod);
        }
        if path.ends_with("::block_on") || path == "block_on" {
            return Some(InlineFrozenKind::BlockBoundary);
        }
        if (path.contains("rc::Rc") || path.contains("sync::Arc")) && path.ends_with("::new") {
            return Some(InlineFrozenKind::WrapperConstructor);
        }
        if (path.contains("Simd") || path.contains("simd"))
            && (path.ends_with("::from_array")
                || path.ends_with("::to_array")
                || path.ends_with("::as_array")
                || path.ends_with("::as_mut_array")
                || path.ends_with("::splat")
                || path.ends_with("::resize"))
        {
            return Some(InlineFrozenKind::SimdOperation);
        }
        if path.contains("typed_swap_nonoverlapping")
            || (path.contains("std::mem::swap") && !path.contains("swap_nonoverlapping"))
        {
            return Some(InlineFrozenKind::SwapIntrinsic);
        }
        if path.contains("ArraySolver::") {
            return Some(InlineFrozenKind::ArraySolverMethod);
        }
        None
    }

    /// Check if a path belongs to a collection/stdlib module that should be
    /// broadly frozen from inlining. These are conservative guards matching the
    /// old `has_special_codegen_handler()` patterns.
    ///
    /// Step 1 (`self.lookup()`) catches paths with known StubKind entries. This
    /// method catches remaining paths in the same module that lack specific
    /// stubs but would expose harmful internals (raw pointers, bucket probing,
    /// BTree node traversal, etc.) if inlined.
    fn is_frozen_collection_module(path: &str) -> bool {
        // HashMap/HashSet/hashbrown internals (#798, #788, #3057)
        if path.contains("hashbrown::")
            || path.contains("HashMap")
            || path.contains("HashSet")
            || path.contains("hash_map::")
            || path.contains("hash_set::")
        {
            return true;
        }

        // BTreeSet/BTreeMap/btree internals (Part of #1659)
        if path.contains("BTreeSet") || path.contains("BTreeMap") || path.contains("btree") {
            return true;
        }

        // Vec operations — exclude RawVec which may need inlining (#1037).
        let contains_vec = path.contains("std::vec::Vec") || path.contains("alloc::vec::Vec");
        if contains_vec && !path.contains("RawVec") {
            return true;
        }

        // Vec IntoIter operations (#2876 RC2)
        if path.contains("IntoIter") && (path.contains("alloc::vec") || path.contains("std::vec")) {
            return true;
        }

        // String operations (#1691)
        if path.contains("alloc::string::String") || path.contains("std::string::String") {
            return true;
        }

        // Cow<str> operations (#1691)
        if path.contains("std::borrow::Cow") || path.contains("alloc::borrow::Cow") {
            return true;
        }

        // ToString::to_string (#1691) — broad substring check catches edge
        // cases with non-standard paths beyond what StubRegistry matches.
        if path.contains("ToString") && path.contains("to_string") {
            return true;
        }

        false
    }

    /// Check if a path is a slice::contains that should be frozen for the CHC
    /// dispatch chain handler. Excludes collection-type contains methods which
    /// have their own StubKind entries.
    fn is_frozen_slice_contains(path: &str) -> bool {
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
}
