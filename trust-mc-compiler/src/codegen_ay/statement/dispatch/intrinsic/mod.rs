// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Standard library intrinsic dispatch, grouped by family.
//!
//! Dispatches intrinsic calls by matching function name patterns against
//! known families (arithmetic, memory, atomics, SIMD, etc.). Each family
//! method handles a category of related intrinsics with ordering-sensitive
//! substring checks to disambiguate overlapping names.
//!
//! Refactored per #2027 from a single ~610-line if-chain into per-family
//! dispatch methods. Decomposed per #2179 into submodules.
//!
//! Not table-driven: many intrinsics use substring matching (e.g.,
//! `contains("atomic")`) rather than exact keys, so a `HashMap` lookup
//! would not be a direct replacement.

mod arithmetic;
mod atomics;
mod bit_ops;
mod math;
mod memory;
mod noop;
mod option;
mod partial_ord;
mod raw_eq_cmp;
mod result;
mod simd;
mod step;
mod ub_checks;

#[cfg(test)]
mod tests;

use rustc_public::mir::{BasicBlockIdx, Operand, Place};

pub(super) use super::CallDispatchOutcome;
use crate::codegen_ay::statement::StatementCodegen;

/// Check if fn_name matches a SIMD intrinsic name.
/// Matches both full paths (e.g., "::simd_add::") and bare names (e.g., "simd_add").
/// Uses ::name:: or ends_with(::name) patterns to avoid matching longer names
/// (e.g., simd_add shouldn't match simd_add_reduce).
///
/// Part of #2044: Avoids per-call String allocations by using direct byte checks.
pub(in crate::codegen_ay::statement) fn matches_simd_intrinsic(
    fn_name: &str,
    intrinsic: &str,
) -> bool {
    if fn_name == intrinsic {
        return true;
    }
    // Check all occurrences of intrinsic in fn_name, not just the first.
    // Each must be preceded by "::" and followed by "::" or end of string.
    let bytes = fn_name.as_bytes();
    let mut search_start = 0;
    while let Some(rel_pos) = fn_name[search_start..].find(intrinsic) {
        let pos = search_start + rel_pos;
        let preceded_by_colons = pos >= 2 && bytes[pos - 2] == b':' && bytes[pos - 1] == b':';
        if preceded_by_colons {
            let after = pos + intrinsic.len();
            let followed_ok = after == fn_name.len()
                || (after + 1 < fn_name.len() && bytes[after] == b':' && bytes[after + 1] == b':');
            if followed_ok {
                return true;
            }
        }
        search_start = pos + 1;
    }
    false
}

/// Extract the final method/function segment from a Rust def-path-like string.
/// Handles both direct paths (`::method`) and generic impl paths (`>::method`).
pub(in crate::codegen_ay::statement) fn extract_method_name(path: &str) -> Option<&str> {
    if let Some(idx) = path.rfind(">::") {
        return Some(&path[idx + 3..]);
    }
    if let Some(idx) = path.rfind("::") {
        return Some(&path[idx + 2..]);
    }
    if path.is_empty() {
        return None;
    }
    Some(path)
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Try to codegen a standard library intrinsic call.
    ///
    /// Dispatches to appropriate handler based on function name patterns.
    ///
    /// Dispatch order matters for overlapping patterns (e.g., "copy" vs
    /// "copy_nonoverlapping", "atomic_max" vs "atomic_umax"). Each family
    /// method handles ordering internally.
    pub(in crate::codegen_ay::statement) fn try_codegen_std_intrinsic(
        &mut self,
        fn_name: &str,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> CallDispatchOutcome {
        // Dispatch by intrinsic family. Try each family in turn; the first
        // match wins. Within each family, patterns are ordered to avoid
        // ambiguous prefix matches.
        // All families currently return Option<BasicBlockIdx> (None = miss);
        // bridge to CallDispatchOutcome at the boundary.
        let outcome = CallDispatchOutcome::from_optional_target(self.dispatch_arithmetic(
            fn_name,
            args,
            destination,
            target,
        ));
        if !matches!(outcome, CallDispatchOutcome::Miss) {
            return outcome;
        }
        let outcome = CallDispatchOutcome::from_optional_target(self.dispatch_option(
            fn_name,
            args,
            destination,
            target,
        ));
        if !matches!(outcome, CallDispatchOutcome::Miss) {
            return outcome;
        }
        let outcome = CallDispatchOutcome::from_optional_target(self.dispatch_result(
            fn_name,
            args,
            destination,
            target,
        ));
        if !matches!(outcome, CallDispatchOutcome::Miss) {
            return outcome;
        }
        let outcome = CallDispatchOutcome::from_optional_target(self.dispatch_noop(
            fn_name,
            args,
            destination,
            target,
        ));
        if !matches!(outcome, CallDispatchOutcome::Miss) {
            return outcome;
        }
        let outcome = self.dispatch_memory(fn_name, args, destination, target);
        if !matches!(outcome, CallDispatchOutcome::Miss) {
            return outcome;
        }
        let outcome = CallDispatchOutcome::from_optional_target(self.dispatch_bit_ops(
            fn_name,
            args,
            destination,
            target,
        ));
        if !matches!(outcome, CallDispatchOutcome::Miss) {
            return outcome;
        }
        let outcome = CallDispatchOutcome::from_optional_target(self.dispatch_raw_eq_and_cmp(
            fn_name,
            args,
            destination,
            target,
        ));
        if !matches!(outcome, CallDispatchOutcome::Miss) {
            return outcome;
        }
        let outcome = CallDispatchOutcome::from_optional_target(self.dispatch_atomics(
            fn_name,
            args,
            destination,
            target,
        ));
        if !matches!(outcome, CallDispatchOutcome::Miss) {
            return outcome;
        }
        let outcome = CallDispatchOutcome::from_optional_target(self.dispatch_math(
            fn_name,
            args,
            destination,
            target,
        ));
        if !matches!(outcome, CallDispatchOutcome::Miss) {
            return outcome;
        }
        let outcome = CallDispatchOutcome::from_optional_target(self.dispatch_simd(
            fn_name,
            args,
            destination,
            target,
        ));
        if !matches!(outcome, CallDispatchOutcome::Miss) {
            return outcome;
        }
        let outcome = CallDispatchOutcome::from_optional_target(self.dispatch_ub_checks(
            fn_name,
            args,
            destination,
            target,
        ));
        if !matches!(outcome, CallDispatchOutcome::Miss) {
            return outcome;
        }
        let outcome = CallDispatchOutcome::from_optional_target(self.dispatch_partial_ord(
            fn_name,
            args,
            destination,
            target,
        ));
        if !matches!(outcome, CallDispatchOutcome::Miss) {
            return outcome;
        }
        let outcome = CallDispatchOutcome::from_optional_target(self.dispatch_step(
            fn_name,
            args,
            destination,
            target,
        ));
        if !matches!(outcome, CallDispatchOutcome::Miss) {
            return outcome;
        }
        CallDispatchOutcome::Miss
    }
}
