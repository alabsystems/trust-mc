// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Static type-validity oracle for the `assert_inhabited` / `assert_zero_valid`
//! / `assert_mem_uninitialized_valid` compiler intrinsics.
//!
//! These intrinsics are inserted by the standard library (e.g. `mem::zeroed`,
//! `mem::uninitialized`) and are undefined behaviour exactly when the target
//! type does not permit the corresponding raw initialization. This module wraps
//! rustc's own `check_validity_requirement` query so both the CHC and BMC
//! encoders can decide, statically, whether one of these assertions is a
//! *definitive* UB (emit an error) versus satisfiable / undecidable (no-op).

use rustc_const_eval::util::check_validity_requirement;
use rustc_middle::ty::layout::ValidityRequirement;
use rustc_middle::ty::{PseudoCanonicalInput, TyCtxt, TypingEnv};
use rustc_public::rustc_internal;
use rustc_public::ty::Ty;

/// Map an `assert_*` intrinsic method name to the rustc validity requirement it
/// encodes. Mirrors `rustc_middle::ty::layout::ValidityRequirement::from_intrinsic`
/// so trust-mc fires exactly when rustc's own compile-time check would.
///
/// Returns `None` for any other name.
#[must_use]
pub(crate) fn validity_requirement_for_intrinsic(method: &str) -> Option<ValidityRequirement> {
    match method {
        "assert_inhabited" => Some(ValidityRequirement::Inhabited),
        "assert_zero_valid" => Some(ValidityRequirement::Zero),
        // rustc lowers `assert_mem_uninitialized_valid` to the 0x01-fill-mitigated
        // check, not the strict `Uninit` one — matching that keeps trust-mc from
        // flagging types rustc itself accepts (e.g. `mem::uninitialized::<bool>()`).
        "assert_mem_uninitialized_valid" => Some(ValidityRequirement::UninitMitigated0x01Fill),
        _ => None,
    }
}

/// Returns `true` iff rustc can *definitively* prove type `ty` violates the
/// validity `requirement` — i.e. the corresponding `assert_*` intrinsic is
/// undefined behaviour for `ty`.
///
/// Returns `false` whenever the requirement is satisfied, the type is
/// parametric / un-monomorphized, its layout cannot be computed, or the query
/// panics. Callers therefore fire an error only on a hard "not permitted"
/// answer and treat every other outcome as a no-op — never a false positive.
/// In particular `mem::zeroed::<u32>()` (whose lowering contains
/// `assert_zero_valid::<u32>()`) is *not* flagged, because `u32` permits the
/// all-zero bit pattern.
#[must_use]
pub(crate) fn assert_requirement_definitely_violated(
    tcx: TyCtxt<'_>,
    ty: Ty,
    requirement: ValidityRequirement,
) -> bool {
    let internal_ty = rustc_internal::internal(tcx, ty);
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let input = PseudoCanonicalInput {
            typing_env: TypingEnv::fully_monomorphized(),
            value: internal_ty,
        };
        check_validity_requirement(tcx, requirement, input)
    }));
    // Ok(Ok(false)) => requirement provably NOT satisfiable => definite UB.
    // Ok(Ok(true))  => satisfiable                          => no-op.
    // Ok(Err(_))    => layout error                         => no-op.
    // Err(_)        => query panicked                       => no-op.
    matches!(outcome, Ok(Ok(false)))
}
