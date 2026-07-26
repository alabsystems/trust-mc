// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Path and operation classifier helpers for `codegen_call_cmp_string`.
//!
//! Extracted from `mod.rs` per #3254 packet 1.

use ay_bindings::Expr;
use rustc_public::mir::BinOp;

use super::super::ChcCtx;
use super::div_euclid;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn max_bitvec_width(lhs: &Expr, rhs: &Expr) -> Option<u32> {
        Some(lhs.sort().bitvec_width()?.max(rhs.sort().bitvec_width()?))
    }

    /// Detect wrapping/unchecked arithmetic method calls and map them to BinOp.
    ///
    /// `unchecked_*` integer methods appear in range-lowered MIR and are encoded
    /// with the same bitvector operator family as wrapping arithmetic.
    /// Returns `(BinOp, is_unchecked)` — `is_unchecked` is true for `unchecked_*`
    /// methods which have UB on overflow (Part of #3299).
    pub(in crate::codegen_ay::chc) fn wrapping_arithmetic_method(
        path: &str,
    ) -> Option<(BinOp, bool)> {
        match path.rsplit("::").next() {
            Some("wrapping_add") => Some((BinOp::Add, false)),
            Some("wrapping_sub") => Some((BinOp::Sub, false)),
            Some("wrapping_mul") => Some((BinOp::Mul, false)),
            Some("unchecked_add") => Some((BinOp::Add, true)),
            Some("unchecked_sub") => Some((BinOp::Sub, true)),
            Some("unchecked_mul") => Some((BinOp::Mul, true)),
            Some("unchecked_div") => Some((BinOp::Div, true)),
            Some("unchecked_rem") => Some((BinOp::Rem, true)),
            Some("unchecked_shl") => Some((BinOp::Shl, true)),
            Some("unchecked_shr") => Some((BinOp::Shr, true)),
            _ => None, // non-enum: &str (method name)
        }
    }

    /// Detect checked arithmetic method calls returning `Option<T>`.
    ///
    /// `checked_*` methods return `Some(result)` on no overflow, `None` on overflow.
    /// Part of #3094: these fall through all dispatchers without this handler.
    pub(in crate::codegen_ay::chc) fn checked_arithmetic_method(path: &str) -> Option<BinOp> {
        match path.rsplit("::").next() {
            Some("checked_add") => Some(BinOp::Add),
            Some("checked_sub") => Some(BinOp::Sub),
            Some("checked_mul") => Some(BinOp::Mul),
            Some("checked_div") => Some(BinOp::Div),
            Some("checked_rem") => Some(BinOp::Rem),
            Some("checked_shl") => Some(BinOp::Shl),
            Some("checked_shr") => Some(BinOp::Shr),
            _ => None, // non-enum: &str (method name)
        }
    }

    /// Detect overflowing arithmetic calls returning `(T, bool)`.
    ///
    /// This covers both integer methods (`overflowing_add`) and raw compiler
    /// intrinsics (`add_with_overflow`).
    pub(in crate::codegen_ay::chc) fn overflowing_arithmetic_method(path: &str) -> Option<BinOp> {
        match path.rsplit("::").next() {
            Some("overflowing_add" | "add_with_overflow") => Some(BinOp::Add),
            Some("overflowing_sub" | "sub_with_overflow") => Some(BinOp::Sub),
            Some("overflowing_mul" | "mul_with_overflow") => Some(BinOp::Mul),
            _ => None, // non-enum: &str (method name)
        }
    }

    /// Detect saturating arithmetic method calls returning `T`.
    ///
    /// `saturating_*` methods clamp the result to `T::MIN`/`T::MAX` on overflow.
    /// Part of #3094: encoded as `ite(overflow, MAX/MIN, wrapping_result)`.
    pub(in crate::codegen_ay::chc) fn saturating_arithmetic_method(path: &str) -> Option<BinOp> {
        match path.rsplit("::").next() {
            Some("saturating_add") => Some(BinOp::Add),
            Some("saturating_sub") => Some(BinOp::Sub),
            _ => None, // non-enum: &str (method name)
        }
    }

    /// Detect `exact_div` intrinsic calls (#3177).
    pub(in crate::codegen_ay::chc) fn is_exact_div(path: &str) -> bool {
        matches!(path.rsplit("::").next(), Some("exact_div"))
    }

    /// Detect `pow`/`wrapping_pow` integer method calls (Part of #3186).
    ///
    /// These are loop-based in MIR (exponentiation by squaring) and exceed the
    /// inline block limit, falling through to unconstrained. Handle specially
    /// for constant base 2 (→ bvshl) or fully constant args (→ evaluate).
    pub(in crate::codegen_ay::chc) fn is_pow_method(path: &str) -> bool {
        matches!(path.rsplit("::").next(), Some("pow" | "wrapping_pow"))
    }

    /// Detect `div_euclid`/`rem_euclid` integer method calls (Part of #3186).
    ///
    /// Euclidean division/remainder have branching MIR bodies that fn_inline
    /// expands into complex CHC rule sets the solver cannot handle.
    pub(in crate::codegen_ay::chc) fn euclid_method(path: &str) -> Option<div_euclid::EuclidOp> {
        match path.rsplit("::").next() {
            Some("div_euclid") => Some(div_euclid::EuclidOp::Div),
            Some("rem_euclid") => Some(div_euclid::EuclidOp::Rem),
            _ => None,
        }
    }

    /// Detect `wrapping_abs` / `abs` integer method calls (Part of #3293).
    ///
    /// `wrapping_abs` has a branching MIR body (`if self < 0 { wrapping_neg }
    /// else { self }`) that fn_inline expands into rules the solver can't
    /// handle. Encode directly as `ite(bvslt(x, 0), bvneg(x), x)`.
    pub(in crate::codegen_ay::chc) fn is_wrapping_abs(path: &str) -> bool {
        matches!(path.rsplit("::").next(), Some("wrapping_abs"))
    }

    /// Detect `wrapping_neg` integer method calls (Part of #3293).
    ///
    /// `wrapping_neg` appears as a function call inside `wrapping_abs`'s MIR
    /// body. When fn_inline processes `wrapping_abs`, it encounters
    /// `wrapping_neg` which has no stub. Encode as `bvneg(x)`.
    pub(in crate::codegen_ay::chc) fn is_wrapping_neg(path: &str) -> bool {
        matches!(path.rsplit("::").next(), Some("wrapping_neg"))
    }

    /// Detect `overflowing_add_signed` calls (Part of #3300).
    ///
    /// `usize::overflowing_add_signed(self, rhs: isize) -> (usize, bool)` appears
    /// in MIR for `ptr.offset()`: the compiler inlines `ptr.offset()` into calls to
    /// `overflowing_add_signed` rather than lowering to `BinOp::Offset`. Must be
    /// handled before fn_inline to emit correct overflow semantics.
    pub(in crate::codegen_ay::chc) fn is_overflowing_add_signed(path: &str) -> bool {
        matches!(path.rsplit("::").next(), Some("overflowing_add_signed"))
    }

    /// Detect formatting/debug/panic infrastructure function paths.
    ///
    /// Returns true for calls to formatting and panic infrastructure that are
    /// safety-irrelevant. These calls appear on assertion-failure and panic paths
    /// and produce unconstrained return values that cascade into spurious CTREX.
    ///
    /// Error-blocking these paths (emitting error() with no successor) matches
    /// Kani's `codegen_unimplemented` pattern (assert(false); assume(false)).
    ///
    /// Part of #3323, Strategy 1 + overapprox design expansion.
    pub(in crate::codegen_ay::chc) fn is_formatting_path(path: &str) -> bool {
        // Display/Debug trait implementations
        if path.contains("::fmt") && (path.contains("Display") || path.contains("Debug")) {
            return true;
        }
        // Formatter methods (write_str, write_fmt, write_char, pad, etc.)
        if path.contains("core::fmt::Formatter") || path.contains("std::fmt::Formatter") {
            return true;
        }
        // Number/string formatting helpers
        if path.contains("core::fmt::num::") || path.contains("core::fmt::float::") {
            return true;
        }
        // fmt::Write trait implementations
        if path.contains("fmt::Write::") {
            return true;
        }
        // Format argument construction (macro expansion infrastructure)
        if path.contains("core::fmt::Arguments::")
            || path.contains("std::fmt::Arguments::")
            || path.contains("core::fmt::rt::")
            || path.contains("std::fmt::rt::")
        {
            return true;
        }
        // The core format function itself
        if path.contains("core::fmt::write") || path.contains("alloc::fmt::format") {
            return true;
        }
        // Debug builder infrastructure (DebugStruct, DebugTuple, DebugList, etc.)
        if path.contains("core::fmt::builders::") {
            return true;
        }
        // Panic formatting infrastructure — calls on assertion-failure paths.
        // These construct panic messages and are not safety-relevant.
        if path.contains("core::panicking::") || path.contains("std::panicking::") {
            return true;
        }
        // Result/Option unwrap failure helpers are no-return panic shims. They
        // live outside `core::panicking`, but should be treated the same by the
        // inline walker so dead unwrap-failure arms do not become encoding gaps.
        if path.contains("core::result::unwrap_failed")
            || path.contains("std::result::unwrap_failed")
            || path.contains("core::option::unwrap_failed")
            || path.contains("std::option::unwrap_failed")
        {
            return true;
        }
        // std::rt runtime infrastructure (panic hooks, etc.)
        if path.contains("std::rt::") {
            return true;
        }
        // I/O write_fmt (println!, eprintln!, write! macros) — side effects only.
        if path.contains("io::Write::write_fmt") || path.contains("io::_print") {
            return true;
        }
        // Process termination — unreachable past this point.
        if path.contains("std::process::abort") || path.contains("std::process::exit") {
            return true;
        }
        // core::panic module — PanicInfo, Location, etc. (distinct from core::panicking).
        // PanicInfo::message(), Location::file()/line()/column() are diagnostic-only.
        // std::panic — set_hook, take_hook, PanicHookInfo are diagnostic infrastructure.
        // EXCLUDES catch_unwind / resume_unwind — these are semantically significant
        // control-flow functions, not formatting infrastructure. Part of #3570.
        if path.contains("core::panic::") || path.contains("std::panic::") {
            // catch_unwind and resume_unwind are NOT formatting/diagnostic paths.
            if path.contains("catch_unwind") || path.contains("resume_unwind") {
                return false;
            }
            return true;
        }
        // Allocation error paths — capacity_overflow, handle_alloc_error.
        // These diverge (panic/abort) and their intermediate formatting values
        // should not produce unconstrained cascades. Part of #2183.
        if path.contains("alloc::raw_vec::capacity_overflow")
            || path.contains("alloc::alloc::handle_alloc_error")
        {
            return true;
        }
        // core::error::Error / std::error::Error trait methods — error
        // description/source chains. Used on error reporting paths, never
        // assertion-relevant. Part of #2183. `def_path_str` may return
        // either `core::error::` or `std::error::` depending on re-export
        // resolution. Part of #4231.
        if path.contains("core::error::") || path.contains("std::error::") {
            return true;
        }
        // Backtrace capture — diagnostic-only infrastructure. Part of #2183.
        if path.contains("std::backtrace::") {
            return true;
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::ChcCtx;

    #[test]
    fn formatting_path_includes_unwrap_failed_panic_shims() {
        assert!(ChcCtx::is_formatting_path("core::result::unwrap_failed"));
        assert!(ChcCtx::is_formatting_path("std::result::unwrap_failed"));
        assert!(ChcCtx::is_formatting_path("core::option::unwrap_failed"));
        assert!(!ChcCtx::is_formatting_path("core::result::Result::<u8, u8>::unwrap"));
    }
}
