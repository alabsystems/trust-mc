// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared utilities for `chc` and `statement` codegen modules.
//!
//! Items here were previously defined in one module but consumed by the other,
//! creating a circular dependency. Extracted to a standalone crate so that
//! future codegen subcrates can depend on these without a circular dependency
//! on `trust_mc-compiler`.
//!
//! Part of #2997: split codegen_ay into subcrates.
//! Originally Part of #2881: circular dependency chc <-> statement via shared utilities.

#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_public;

use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

use rustc_public::CrateDef;
use rustc_public::mir::BinOp;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, trace, warn};

/// Process-global signedness fallback counter (Part of #2997: break shared→chc cycle).
///
/// Previously lived in `GLOBAL_COUNTERS.signedness_fallback` inside the chc module.
/// Moved here so that `shared.rs` has no dependency on `chc`, enabling crate extraction.
static SIGNEDNESS_FALLBACK_COUNT: AtomicU64 = AtomicU64::new(0);

// ---------------------------------------------------------------------------
// IntoOption trait (moved from statement/mod.rs)
// ---------------------------------------------------------------------------

/// Conversion trait used by codegen paths to unify `Option<T>` and `Result<T, E>`
/// return types into `Option<T>`, with telemetry for dropped errors.
pub trait IntoOption<T> {
    fn into_option(self) -> Option<T>;
}

impl<T> IntoOption<T> for Option<T> {
    fn into_option(self) -> Option<T> {
        self
    }
}

impl<T, E: std::fmt::Debug> IntoOption<T> for Result<T, E> {
    fn into_option(self) -> Option<T> {
        match self {
            Ok(value) => Some(value),
            Err(err) => {
                INTO_OPTION_RESULT_DROPPED_COUNT.fetch_add(1, Ordering::Relaxed);
                debug!(
                    error = ?err,
                    "IntoOption dropped Result::Err and skipped codegen path"
                );
                None
            }
        }
    }
}

/// Telemetry counter for Result→Option drops in statement codegen (#2597).
static INTO_OPTION_RESULT_DROPPED_COUNT: AtomicUsize = AtomicUsize::new(0);

/// Reset the `IntoOption` drop counter, returning the previous value.
pub fn take_into_option_dropped_count() -> usize {
    INTO_OPTION_RESULT_DROPPED_COUNT.swap(0, Ordering::Relaxed)
}

/// Non-destructive read of the `IntoOption` drop counter (Part of #3080).
pub fn get_into_option_dropped_count() -> usize {
    INTO_OPTION_RESULT_DROPPED_COUNT.load(Ordering::Relaxed)
}

/// Replace the `IntoOption` drop counter for downstream test seeding.
///
/// Not behind `#[cfg(test)]` because consumer crate tests need access.
#[doc(hidden)]
pub fn replace_into_option_dropped_count_for_test(count: usize) -> usize {
    INTO_OPTION_RESULT_DROPPED_COUNT.swap(count, Ordering::Relaxed)
}

// ---------------------------------------------------------------------------
// Signedness fallback helpers (moved from chc/codegen_expr_signedness.rs)
// ---------------------------------------------------------------------------

// SIGNEDNESS_FALLBACK_COUNT consolidated into GLOBAL_COUNTERS (Part of #2906).

/// Reset the signedness fallback counter, returning the previous value.
pub fn take_signedness_fallback_count() -> usize {
    SIGNEDNESS_FALLBACK_COUNT.swap(0, Ordering::Relaxed) as usize
}

/// Non-destructive read of the signedness fallback counter.
pub fn get_signedness_fallback_count() -> usize {
    SIGNEDNESS_FALLBACK_COUNT.load(Ordering::Relaxed) as usize
}

/// Replace the signedness fallback counter for downstream test seeding.
///
/// Not behind `#[cfg(test)]` because consumer crate tests need access.
#[doc(hidden)]
pub fn replace_signedness_fallback_count_for_test(count: usize) -> usize {
    SIGNEDNESS_FALLBACK_COUNT.swap(count as u64, Ordering::Relaxed) as usize
}

/// Operation class for signedness fallback defaults.
///
/// Exposed publicly so that generic entry points (e.g. `arg_signedness_or_fallback`)
/// can accept caller-specified operation context (Part of #3129).
#[derive(Clone, Copy, Debug)]
pub enum SignednessFallbackKind {
    /// Ordered comparisons (`<`, `<=`, `>`, `>=`, `cmp`) and equivalent coercions.
    Comparison,
    /// Add/Sub/Mul and overflow-related checks where neither signedness default
    /// is universally conservative.
    Arithmetic,
    /// Division and remainder (`/`, `%`) where signed default can model
    /// unsigned values incorrectly.
    DivRem,
    /// Casts and width-coercions where sign-extension vs zero-extension differs.
    CastOrCoerce,
    /// Right-shift (`>>`) where signed vs unsigned produces different bit patterns.
    /// Unlike Add/Sub/Mul (same result regardless of signedness), `bvashr` sign-extends
    /// while `bvlshr` zero-extends. Default unsigned: zero-extending an actually-signed
    /// value is detectable (too-small positive), while sign-extending an actually-unsigned
    /// value silently corrupts the high bit.
    Shift,
    /// Sign-agnostic bitwise operations (`&`, `|`, `^`) where the BV result is
    /// identical regardless of signedness interpretation. `bvand`, `bvor`, `bvxor`
    /// operate on bit patterns with no signed/unsigned distinction. Fallback to
    /// this kind does NOT increment the signedness counter, since the encoding
    /// is sound regardless of the signedness choice (Part of #3355).
    Bitwise,
    /// Sign-agnostic equality/inequality (`==`, `!=`). SMT-LIB `=` is
    /// sort-polymorphic and produces identical results regardless of signedness
    /// interpretation on same-width bitvectors. When operands have different
    /// widths, the coercion path uses `signed`, but the fallback choice does
    /// not affect correctness for the overwhelmingly common same-width case.
    /// Fallback to this kind does NOT increment the signedness counter.
    /// Part of #3446.
    Equality,
}

impl SignednessFallbackKind {
    fn default_signed(self) -> bool {
        match self {
            Self::Comparison | Self::Arithmetic => true,
            Self::DivRem | Self::CastOrCoerce | Self::Shift => false,
            // Bitwise and equality ops are sign-agnostic; the choice doesn't
            // affect the result. Default false (unsigned) — arbitrary.
            Self::Bitwise | Self::Equality => false,
        }
    }

    /// Returns true if this operation kind is sign-agnostic (the BV result is
    /// identical regardless of signed/unsigned interpretation).
    fn is_sign_agnostic(self) -> bool {
        matches!(self, Self::Bitwise | Self::Equality)
    }
}

pub fn signedness_fallback_with_kind(context: &str, kind: SignednessFallbackKind) -> bool {
    let signed = kind.default_signed();
    if kind.is_sign_agnostic() {
        // Sign-agnostic operations (bitwise AND/OR/XOR): the BV result is identical
        // regardless of signedness. Skip counter increment to avoid spurious PROOF
        // demotion (Part of #3355).
        trace!(
            context,
            ?kind,
            signed,
            "signedness unknown but operation is sign-agnostic — no encoding gap"
        );
        return signed;
    }
    let count = SIGNEDNESS_FALLBACK_COUNT.fetch_add(1, Ordering::Relaxed) + 1;
    warn!(context, count, ?kind, signed, "signedness unknown — using operation-specific fallback");
    signed
}

/// Compatibility fallback for call sites that require comparison semantics.
///
/// Note: "default signed is conservative" is only correct for ordered
/// comparisons; non-comparison operations should use a specific helper below.
pub fn signedness_fallback(context: &str) -> bool {
    signedness_fallback_with_kind(context, SignednessFallbackKind::Comparison)
}

/// Fallback for Add/Sub/Mul-style arithmetic and overflow checks.
pub fn signedness_fallback_for_arithmetic(context: &str) -> bool {
    signedness_fallback_with_kind(context, SignednessFallbackKind::Arithmetic)
}

/// Fallback for cast/width-coercion operations (prefer zero-extension semantics).
pub fn signedness_fallback_for_cast_or_coerce(context: &str) -> bool {
    signedness_fallback_with_kind(context, SignednessFallbackKind::CastOrCoerce)
}

/// Fallback selected by MIR binary operation semantics.
pub fn signedness_fallback_for_binop(op: BinOp, context: &str) -> bool {
    let kind = match op {
        BinOp::Div | BinOp::Rem => SignednessFallbackKind::DivRem,
        BinOp::Lt | BinOp::Le | BinOp::Ge | BinOp::Gt | BinOp::Cmp => {
            SignednessFallbackKind::Comparison
        }
        BinOp::Shr | BinOp::ShrUnchecked => SignednessFallbackKind::Shift,
        // Sign-agnostic: bvand/bvor/bvxor produce identical results regardless
        // of signedness interpretation (Part of #3355).
        BinOp::BitXor | BinOp::BitAnd | BinOp::BitOr => SignednessFallbackKind::Bitwise,
        // Sign-agnostic: SMT-LIB `=` is sort-polymorphic and produces identical
        // results regardless of signedness on same-width bitvectors. Part of #3446.
        BinOp::Eq | BinOp::Ne => SignednessFallbackKind::Equality,
        BinOp::Add
        | BinOp::AddUnchecked
        | BinOp::Sub
        | BinOp::SubUnchecked
        | BinOp::Mul
        | BinOp::MulUnchecked
        | BinOp::Shl
        | BinOp::ShlUnchecked
        | BinOp::Offset => SignednessFallbackKind::Arithmetic, // external enum: BinOp
    };
    signedness_fallback_with_kind(context, kind)
}

// ---------------------------------------------------------------------------
// Type signedness detection (shared core for chc + statement modules)
// ---------------------------------------------------------------------------
// Moved from chc/codegen_expr_signedness.rs — Part of #2944.

/// Returns true for ADT types that wrap pointers: Box, Unique, NonNull (#2082).
pub fn is_pointer_wrapper_adt(adt_name: &str) -> bool {
    let short = adt_name.rsplit("::").next().unwrap_or(adt_name);
    matches!(short, "Box" | "Unique" | "NonNull")
}

/// Shared signedness logic for non-pointer, non-recursive types.
///
/// Handles: Int, Uint, Bool, Char, and Atomic ADTs.
/// Does NOT handle Ref/RawPtr recursion, pointer-wrapper ADTs, or Tuple —
/// callers handle those before falling through to this function.
///
/// Part of #2944: extract shared core from BMC and CHC ty_signedness.
pub fn ty_signedness_shallow(ty: rustc_public::ty::Ty) -> Option<bool> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Int(_)) => Some(true),
        TyKind::RigidTy(RigidTy::Uint(_)) => Some(false),
        TyKind::RigidTy(RigidTy::Bool) => Some(false),
        TyKind::RigidTy(RigidTy::Char) => Some(false),
        // Part of #3094: Float types modeled as bitvectors use unsigned
        // semantics. For Eq/Ne signedness is irrelevant; for ordered
        // comparisons on positive IEEE 754 values unsigned BV order matches
        // magnitude order. This prevents false signedness_fallback demotion.
        TyKind::RigidTy(RigidTy::Float(_)) => Some(false),
        TyKind::RigidTy(RigidTy::Adt(def, _args)) => {
            let name = def.name();
            let is_atomic = |short: &str| {
                name == short
                    || name.strip_suffix(short).is_some_and(|prefix: &str| prefix.ends_with("::"))
            };
            if is_atomic("AtomicIsize")
                || is_atomic("AtomicI8")
                || is_atomic("AtomicI16")
                || is_atomic("AtomicI32")
                || is_atomic("AtomicI64")
            {
                Some(true)
            } else if is_atomic("AtomicUsize")
                || is_atomic("AtomicU8")
                || is_atomic("AtomicU16")
                || is_atomic("AtomicU32")
                || is_atomic("AtomicU64")
                || is_atomic("AtomicBool")
            {
                Some(false)
            } else {
                trace!(ty = ?ty, adt_name = ?name, "ty_signedness: unrecognized ADT");
                None
            }
        }
        // Part of #3446: Function pointers, closures, and coroutines are
        // encoded as BV addresses (unsigned). Returning Some(false) prevents
        // spurious signedness_fallback increments that demote valid PROOFs.
        TyKind::RigidTy(RigidTy::FnDef(..))
        | TyKind::RigidTy(RigidTy::FnPtr(..))
        | TyKind::RigidTy(RigidTy::Closure(..))
        | TyKind::RigidTy(RigidTy::Coroutine(..))
        | TyKind::RigidTy(RigidTy::CoroutineWitness(..))
        | TyKind::RigidTy(RigidTy::Dynamic(..))
        | TyKind::RigidTy(RigidTy::Str)
        | TyKind::RigidTy(RigidTy::Slice(..))
        | TyKind::RigidTy(RigidTy::Foreign(..))
        | TyKind::RigidTy(RigidTy::Never) => Some(false),
        other => {
            trace!(ty = ?ty, kind = ?other, "ty_signedness: unhandled type kind");
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Mutex;

    use super::{
        get_into_option_dropped_count, get_signedness_fallback_count,
        replace_into_option_dropped_count_for_test, replace_signedness_fallback_count_for_test,
        take_into_option_dropped_count, take_signedness_fallback_count,
    };

    static COUNTER_TEST_MUTEX: Mutex<()> = Mutex::new(());

    #[test]
    fn test_signedness_counter_helpers_replace_get_take_roundtrip() {
        let _guard = COUNTER_TEST_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
        let prev = replace_signedness_fallback_count_for_test(5);

        assert_eq!(get_signedness_fallback_count(), 5);
        assert_eq!(take_signedness_fallback_count(), 5);
        assert_eq!(get_signedness_fallback_count(), 0);

        replace_signedness_fallback_count_for_test(prev);
    }

    #[test]
    fn test_into_option_counter_helpers_replace_get_take_roundtrip() {
        let _guard = COUNTER_TEST_MUTEX.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
        let prev = replace_into_option_dropped_count_for_test(3);

        assert_eq!(get_into_option_dropped_count(), 3);
        assert_eq!(take_into_option_dropped_count(), 3);
        assert_eq!(get_into_option_dropped_count(), 0);

        replace_into_option_dropped_count_for_test(prev);
    }
}
