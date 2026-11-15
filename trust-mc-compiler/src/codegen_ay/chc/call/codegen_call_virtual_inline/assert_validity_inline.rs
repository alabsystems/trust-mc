// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Walker-side routing for the `assert_*` type-validity intrinsics.
//!
//! `assert_inhabited` / `assert_zero_valid` / `assert_mem_uninitialized_valid`
//! were already RECOGNIZED by `detect_misc_intrinsic` and already DECIDED by
//! `kani_middle::type_validity::assert_requirement_definitely_violated` — the
//! STATEMENT path uses both (`misc_intrinsics::codegen_assert_validity`). The
//! inline walker consulted neither, so inside an inlined body the call fell
//! through to the symbolic fallback and became a fresh unconstrained
//! `__nested_call_overapprox` variable.
//!
//! This is reuse of an existing decision on the path that skipped it, the same
//! shape as the layout-intrinsic folding in `terminator_exec.rs` ("Not new
//! modelling, just reusing the existing model on the path that skipped it").
//!
//! Measured 2026-09-18 (`docs/chc-nested-call-overapprox-2026-09-18/`), single
//! harness `expected/any_vec/exact_length.rs`, whole call module at debug:
//! **68 of that unit's 168 `nested_call_overapprox` havocs were
//! `std::intrinsics::assert_inhabited`**, and ZERO interception lines were
//! logged for it. Corpus-wide (2026-09-14 per-unit logs) 13 units carry it, 5
//! of them with a counterexample that rests on the approximation.
//!
//! `assert_*` takes NO arguments, which is why the call site sits ahead of
//! translated-argument collection in `nested_call.rs`: no argument failure can
//! defeat it, and that is also why this family is provably not the `M1`
//! argument-bail case.

use ay_bindings::Expr;
use rustc_middle::ty::layout::ValidityRequirement;
use rustc_public::mir::Operand;
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};
use tracing::debug;
use trust_mc_core::violation::PropertyKind;

use super::super::ChcCtx;
use super::super::codegen_call_cmp_string::misc_intrinsics::{
    MiscIntrinsicKind, detect_misc_intrinsic,
};
use super::super::inline_body::{DeferredInlineCheck, InlineReturn};
use crate::codegen_ay::chc::heap_state::HeapWriteMark;
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::kani_middle::type_validity::assert_requirement_definitely_violated;

/// The validity requirement an `assert_*` intrinsic path asserts, if any.
///
/// PURE (path in, requirement out) and deliberately routed through
/// `detect_misc_intrinsic` rather than matching path text again, so the walker
/// and the statement path cannot drift apart on which callees are claimed.
pub(super) fn assert_validity_requirement(callee_path: &str) -> Option<ValidityRequirement> {
    match detect_misc_intrinsic(callee_path)? {
        MiscIntrinsicKind::AssertInhabited => Some(ValidityRequirement::Inhabited),
        MiscIntrinsicKind::AssertZeroValid => Some(ValidityRequirement::Zero),
        MiscIntrinsicKind::AssertMemUninitializedValid => {
            Some(ValidityRequirement::UninitMitigated0x01Fill)
        }
        _ => None,
    }
}

/// The inline result for an `assert_*` call whose requirement was decided.
///
/// PURE, so the SHAPE is testable without a compiled body: which value the
/// destination takes, and which obligation (if any) is carried out.
///
/// * not violated — a pure no-op. The intrinsic returns `()`; the
///   pointer-width zero constant is the same unit stand-in the neighbouring
///   no-op interceptions use.
/// * violated — the no-op value PLUS the obligation, never the value alone.
///   Dropping it would be fail-open: `codegen_assert_validity` emits exactly
///   this condition at the statement level, and a `DeferredInlineCheck` is how
///   the walker carries an obligation to `emit_deferred_inline_check_errors`.
///   `check` is a MUST-HOLD condition, so a definitely violated requirement is
///   `false` — always violated, hence always an error rule.
pub(super) fn assert_validity_inline_return(
    callee_path: &str,
    violated: bool,
    write_mark: HeapWriteMark,
) -> InlineReturn {
    let mut result = InlineReturn::value_only(Expr::bitvec_const(0u64, POINTER_WIDTH));
    if violated {
        push_validity_obligation(&mut result, callee_path, write_mark);
    }
    result
}

/// Carry a DEFINITELY violated validity requirement out of the walker beside
/// whatever value `result` already holds: a MUST-HOLD condition of `false`,
/// the same condition `codegen_assert_validity` emits at the statement level.
///
/// `write_mark` is the heap write generation at the point the obligation is
/// recorded, as for every other deferred check. The condition is the constant
/// `false`, so it reads no heap state; the mark only keeps the drop-walk
/// accounting (`walk_drop_body`) uniform.
pub(super) fn push_validity_obligation(
    result: &mut InlineReturn,
    callee_path: &str,
    write_mark: HeapWriteMark,
) {
    result.deferred_checks.push(DeferredInlineCheck {
        check: Expr::bool_const(false),
        kind: PropertyKind::UndefinedBehavior,
        message: Some(format!("{callee_path}: type validity requirement definitely violated")),
        write_mark,
        merge_key: None,
    });
}

/// Is `requirement` DEFINITELY violated for `ty`? An undecidable, parametric
/// or layout-error answer is `false` (a no-op), exactly as the statement path
/// treats it.
pub(super) fn validity_definitely_violated(
    ctx: &ChcCtx<'_, '_>,
    ty: Ty,
    requirement: ValidityRequirement,
) -> bool {
    !matches!(ty.kind(), TyKind::Param(_))
        && assert_requirement_definitely_violated(ctx.tcx, ty, requirement)
}

/// The single generic type argument `T` of an `assert_*::<T>()` call.
///
/// Mirrors `misc_intrinsics::assert_validity_type_arg`, including its skip of
/// unresolved `Param` types — only a concrete, monomorphized type can answer
/// the validity query — but reads the operand against the INLINED body's
/// locals, which is the one difference the walker requires.
fn assert_validity_type_arg(func: &Operand, outer_body: &rustc_public::mir::Body) -> Option<Ty> {
    let func_ty = func.ty(outer_body.locals()).ok()?;
    let substs = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(_, substs)) => substs,
        _ => return None,
    };
    let ty = substs
        .0
        .iter()
        .find_map(|arg| if let GenericArgKind::Type(ty) = arg { Some(*ty) } else { None })?;
    if matches!(ty.kind(), TyKind::Param(_)) {
        return None;
    }
    Some(ty)
}

/// Intercept an `assert_*` type-validity intrinsic inside an inlined body.
///
/// Returns `None` for every other callee, so this can only ever REPLACE a
/// havoc with the statement path's own answer. An undecidable, parametric or
/// layout-error answer is a no-op, exactly as `codegen_assert_validity` treats
/// it.
pub(super) fn try_inline_assert_validity_intrinsic(
    ctx: &ChcCtx<'_, '_>,
    callee_path: &str,
    func: &Operand,
    outer_body: &rustc_public::mir::Body,
) -> Option<InlineReturn> {
    let requirement = assert_validity_requirement(callee_path)?;
    let violated = assert_validity_type_arg(func, outer_body)
        .is_some_and(|ty| validity_definitely_violated(ctx, ty, requirement));
    debug!(
        %callee_path,
        violated,
        "nested call: assert_* validity intrinsic decided by the statement path's query \
         instead of havocking the destination"
    );
    Some(assert_validity_inline_return(callee_path, violated, ctx.heap_state.write_mark()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_bindings::ExprValue;

    #[test]
    fn requirement_mapping_matches_the_statement_path() {
        assert_eq!(
            assert_validity_requirement("std::intrinsics::assert_inhabited"),
            Some(ValidityRequirement::Inhabited)
        );
        assert_eq!(
            assert_validity_requirement("core::intrinsics::assert_zero_valid"),
            Some(ValidityRequirement::Zero)
        );
        assert_eq!(
            assert_validity_requirement("std::intrinsics::assert_mem_uninitialized_valid"),
            Some(ValidityRequirement::UninitMitigated0x01Fill)
        );
    }

    /// The other three callees MEASURED beside `assert_inhabited` in the same
    /// probe. This arm must not claim any of them: `cast` is an identity whose
    /// ARGUMENT failed to translate (M1), `metadata` has its own dispatch
    /// route, and `write_bytes` is a memory effect, not a validity assertion.
    #[test]
    fn the_other_probe_callees_are_not_claimed() {
        for path in [
            "std::ptr::const_ptr::<impl *const T>::cast",
            "std::ptr::metadata",
            "std::intrinsics::write_bytes",
            "<std::ops::try_trait::Wrapped<T, A, F> as std::ops::FnMut<(A,)>>::call_mut",
        ] {
            assert!(
                assert_validity_requirement(path).is_none(),
                "{path} must not be claimed as an assert_* validity intrinsic"
            );
        }
    }

    #[test]
    fn an_undecided_requirement_is_a_no_op_with_no_obligation() {
        let result = assert_validity_inline_return(
            "std::intrinsics::assert_inhabited",
            false,
            HeapWriteMark::default(),
        );
        assert!(
            result.deferred_checks.is_empty(),
            "a no-op must carry no obligation out of the walker"
        );
        match result.value.value() {
            ExprValue::BitVecConst { value, width } => {
                assert_eq!(*width, POINTER_WIDTH, "unit destination takes the pointer-width zero");
                assert_eq!(value, &num_bigint::BigInt::from(0u64));
            }
            other => panic!("expected the unit zero constant, got {other:?}"),
        }
    }

    /// The fail-closed half: a definitely violated requirement must STATE the
    /// obligation, not return the quiet no-op value alone.
    #[test]
    fn a_violated_requirement_states_the_obligation() {
        let result = assert_validity_inline_return(
            "std::intrinsics::assert_inhabited",
            true,
            HeapWriteMark::default(),
        );
        assert_eq!(result.deferred_checks.len(), 1, "exactly one obligation is carried out");
        let check = &result.deferred_checks[0];
        assert!(
            matches!(check.check.value(), ExprValue::BoolConst(false)),
            "a MUST-HOLD condition of `false` is what makes this always an error rule"
        );
        assert!(
            matches!(check.kind, PropertyKind::UndefinedBehavior),
            "a violated validity requirement is UB, not a user assertion"
        );
        assert!(
            check.message.as_deref().is_some_and(|m| m.contains("assert_inhabited")),
            "the obligation names the callee it came from"
        );
        // The no-op value is unchanged by the obligation: control flow still
        // continues through the unit destination.
        assert!(matches!(result.value.value(), ExprValue::BitVecConst { .. }));
    }
}
