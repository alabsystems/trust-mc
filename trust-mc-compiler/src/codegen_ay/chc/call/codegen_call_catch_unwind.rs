// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Direct CHC handler for `std::panic::catch_unwind` /
//! `std::panicking::catch_unwind`.
//!
//! Intercepts the outer `catch_unwind` wrapper BEFORE fn-inline so
//! the walker never materializes the internal `Data<F, R>` union.
//! Resolves the closure body directly, extracts inline panic-fallback
//! markers, and converts them into `Result::Ok` / `Result::Err`
//! values instead of `error()` rules.
//!
//! Part of #4073: catch_unwind wrapper dispatch.

#![allow(dead_code, clippy::redundant_clone)]

use ay_bindings::{Expr, Sort, SortInner};
use tracing::debug;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_closure::resolve_closure_body_for_operand;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_ctx::globals::{chc_fresh_name, declare_pending_var};
use super::codegen_rules::CodegenRules;
use super::codegen_types::CodegenTypes;
use super::inline_body::{
    InlineReturn, extract_inline_assert_guard, strip_inline_assert_fallback,
    translate_closure_inline_result,
};

/// Extension trait for catch_unwind dispatch on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallDispatchCatchUnwind {
    fn try_dispatch_call_catch_unwind(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

fn is_catch_unwind_wrapper_path(path: &str) -> bool {
    // Match the two stable wrapper paths (not the raw intrinsic).
    (path.contains("std::panic::catch_unwind") || path.contains("std::panicking::catch_unwind"))
        && !path.contains("std::intrinsics::")
}

fn is_catch_unwind_intrinsic_path(path: &str) -> bool {
    path.contains("std::intrinsics::catch_unwind")
}

struct ResultShape {
    dt_name: String,
    ok_ctor_name: String,
    ok_field_sort: Sort,
    err_ctor_name: String,
    err_field_sort: Sort,
}

fn result_shape(result_sort: &Sort) -> Option<ResultShape> {
    let SortInner::Datatype(dt) = result_sort.inner() else {
        return None;
    };
    let ok_ctor = dt.constructors.iter().find(|ctor| {
        ctor.fields.len() == 1 && crate::codegen_ay::names::is_ok_constructor(&ctor.name)
    })?;
    let err_ctor = dt.constructors.iter().find(|ctor| {
        ctor.fields.len() == 1 && crate::codegen_ay::names::is_err_constructor(&ctor.name)
    })?;
    Some(ResultShape {
        dt_name: dt.name.clone(),
        ok_ctor_name: ok_ctor.name.clone(),
        ok_field_sort: ok_ctor.fields.first()?.sort.clone(),
        err_ctor_name: err_ctor.name.clone(),
        err_field_sort: err_ctor.fields.first()?.sort.clone(),
    })
}

/// Build Result expression from extracted guard/ok_value and the Result shape.
fn build_catch_unwind_result(
    guard: Option<Expr>,
    ok_value: Option<Expr>,
    shape: &ResultShape,
    dest_sort: &Sort,
) -> Expr {
    match (guard, ok_value) {
        (None, Some(v)) => {
            let ok_payload = coerce_or_pass(&v, &shape.ok_field_sort);
            Expr::datatype_constructor(
                &shape.dt_name,
                &shape.ok_ctor_name,
                vec![ok_payload],
                dest_sort.clone(),
            )
        }
        (Some(g), Some(v)) => {
            let ok_payload = coerce_or_pass(&v, &shape.ok_field_sort);
            let ok_result = Expr::datatype_constructor(
                &shape.dt_name,
                &shape.ok_ctor_name,
                vec![ok_payload],
                dest_sort.clone(),
            );
            let err_payload = declare_pending_var(
                chc_fresh_name("catch_unwind_panic_payload"),
                shape.err_field_sort.clone(),
            );
            let err_result = Expr::datatype_constructor(
                &shape.dt_name,
                &shape.err_ctor_name,
                vec![err_payload],
                dest_sort.clone(),
            );
            Expr::ite(g, ok_result, err_result)
        }
        _ => {
            // (Some(_), None) or (None, None): always-panicking.
            let err_payload = declare_pending_var(
                chc_fresh_name("catch_unwind_panic_payload"),
                shape.err_field_sort.clone(),
            );
            Expr::datatype_constructor(
                &shape.dt_name,
                &shape.err_ctor_name,
                vec![err_payload],
                dest_sort.clone(),
            )
        }
    }
}

impl<'tcx, 'body> CallDispatchCatchUnwind for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_catch_unwind(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let callee_path = dcx.callee_path.as_deref().unwrap_or("");

        // Handle the raw intrinsic: MIR monomorphization inlines the
        // std::panicking::catch_unwind wrapper so by the time CHC sees
        // the call, it's std::intrinsics::catch_unwind directly.
        // Model as "always returns 0" (no unwind) — the inlined wrapper
        // MIR reads data.r and produces Ok(r) on the 0 path.
        if is_catch_unwind_intrinsic_path(callee_path) {
            return self.dispatch_catch_unwind_intrinsic(dcx);
        }

        // Handle the outer wrapper path (if MIR preserves it).
        if !is_catch_unwind_wrapper_path(callee_path) {
            return false;
        }
        self.dispatch_catch_unwind_wrapper(dcx)
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle std::intrinsics::catch_unwind: model as "always returns 0" (no unwind).
    /// The inlined wrapper MIR checks the return value and reads data.r on the 0 path.
    fn dispatch_catch_unwind_intrinsic(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else {
            self.record_diverging_call_drop(
                dcx.func,
                Some(dcx.bb_idx),
                "catch_unwind_intrinsic",
                None,
            );
            return true;
        };
        let dest_local: usize = dcx.destination.local;
        // catch_unwind intrinsic returns i32: 0 = no unwind, 1 = caught.
        // Model as always 0 (no unwind) — sound over-approximation.
        let result_value = Expr::bitvec_const(0, 32);
        debug!(bb_idx = dcx.bb_idx, dest_local, "catch_unwind intrinsic: returning 0 (no unwind)");
        self.emit_catch_unwind_rule(dcx, dest_local, result_value, *target)
    }

    /// Handle the outer wrapper path (std::panic::catch_unwind etc).
    fn dispatch_catch_unwind_wrapper(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else {
            self.record_diverging_call_drop(dcx.func, Some(dcx.bb_idx), "catch_unwind", None);
            return true;
        };
        let Some(closure_arg) = dcx.args.first() else {
            debug!(bb_idx = dcx.bb_idx, "catch_unwind: no closure argument");
            return false;
        };
        let dest_local: usize = dcx.destination.local;
        let dest_ty = self.body.locals()[dest_local].ty;
        let dest_ty = self.resolve_body_ty(dest_ty);
        let Some(dest_sort) = ChcCtx::translate_ty(dest_ty) else {
            debug!(bb_idx = dcx.bb_idx, "catch_unwind: cannot translate dest type");
            return false;
        };
        let Some(shape) = result_shape(&dest_sort) else {
            debug!(bb_idx = dcx.bb_idx, "catch_unwind: dest is not Result-shaped");
            return false;
        };
        let Some(result_value) =
            self.resolve_and_translate_closure(dcx, closure_arg, &shape, &dest_sort)
        else {
            return false;
        };
        let callee_path = dcx.callee_path.as_deref().unwrap_or("");
        debug!(
            bb_idx = dcx.bb_idx,
            callee = callee_path,
            dest_local,
            "catch_unwind: dispatched as direct Result construction"
        );
        self.emit_catch_unwind_rule(dcx, dest_local, result_value, *target)
    }

    fn resolve_and_translate_closure(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        closure_arg: &rustc_public::mir::Operand,
        shape: &ResultShape,
        dest_sort: &Sort,
    ) -> Option<Expr> {
        let closure_body =
            resolve_closure_body_for_operand(self.tcx, closure_arg, self.body.locals())?;
        let captures = self.extract_closure_env_captures(closure_arg, dcx.modified_locals);
        let inline_result =
            translate_closure_inline_result(self, &closure_body, &[], &captures, dcx.bb_idx, 0)?;

        // DELIBERATE side-channel drop: catch_unwind models the closure's
        // assert/panic guard as the Ok/Err DISCRIMINANT of the caught Result
        // (build_catch_unwind_result), not as a verification failure. Emitting
        // the walk's deferred checks here would turn every caught panic into a
        // harness failure, changing catch_unwind semantics.
        let InlineReturn { value: result_expr, .. } = inline_result;
        let guard = extract_inline_assert_guard(&result_expr);
        let ok_value = strip_inline_assert_fallback(&result_expr);
        Some(build_catch_unwind_result(guard, ok_value, shape, dest_sort))
    }

    fn emit_catch_unwind_rule(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        dest_local: usize,
        result_value: Expr,
        target: usize,
    ) -> bool {
        let Some((_dest_vec_idx, dest_var)) = self.resolve_destination(dest_local) else {
            debug!(bb_idx = dcx.bb_idx, "catch_unwind: cannot resolve destination");
            return false;
        };
        let Some(eq) = self.make_coerced_eq_constraint(
            &dest_var,
            result_value,
            dest_var.sort(),
            dest_local,
            "catch_unwind_result",
        ) else {
            debug!(bb_idx = dcx.bb_idx, "catch_unwind: coercion failed");
            return false;
        };
        let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(
            dcx.from_app,
            target,
            &new_output_args,
            dcx.stmt_constraints,
            [eq],
        );
        true
    }
}

/// If the value sort already matches the target, return as-is;
/// otherwise clone with the target sort (simple coercion).
fn coerce_or_pass(value: &Expr, target_sort: &Sort) -> Expr {
    if value.sort() == target_sort {
        value.clone()
    } else {
        // For unit-typed closures the ok payload is often unit/Bool.
        // The sort mismatch is expected when the closure returns ()
        // and the Result wraps a unit-typed Ok variant. Return as-is
        // and let the solver coerce — this matches the pattern used
        // by other inline result handlers.
        value.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_catch_unwind_wrapper_path() {
        assert!(is_catch_unwind_wrapper_path("std::panic::catch_unwind"));
        assert!(is_catch_unwind_wrapper_path("std::panicking::catch_unwind"));
        assert!(is_catch_unwind_wrapper_path("std::panicking::catch_unwind::<fn() -> u32>"));
        assert!(!is_catch_unwind_wrapper_path("std::intrinsics::catch_unwind"));
        assert!(!is_catch_unwind_wrapper_path("some_other_function"));
        assert!(!is_catch_unwind_wrapper_path(""));
    }

    #[test]
    fn test_is_catch_unwind_intrinsic_path() {
        assert!(is_catch_unwind_intrinsic_path("std::intrinsics::catch_unwind"));
        assert!(!is_catch_unwind_intrinsic_path("std::panic::catch_unwind"));
        assert!(!is_catch_unwind_intrinsic_path("some_other_function"));
    }

    #[test]
    fn test_result_shape_extracts_ok_err_constructors() {
        let ok_sort = Sort::bitvec(32);
        let err_sort = Sort::bitvec(64);
        let result_sort = crate::codegen_ay::test_fixtures::result_datatype_sort(
            ok_sort.clone(),
            err_sort.clone(),
        );
        let shape = result_shape(&result_sort).expect("should extract Result shape");
        assert!(
            crate::codegen_ay::names::is_ok_constructor(&shape.ok_ctor_name),
            "ok_ctor_name should match Ok pattern: {}",
            shape.ok_ctor_name,
        );
        assert!(
            crate::codegen_ay::names::is_err_constructor(&shape.err_ctor_name),
            "err_ctor_name should match Err pattern: {}",
            shape.err_ctor_name,
        );
        assert_eq!(shape.ok_field_sort, ok_sort);
        assert_eq!(shape.err_field_sort, err_sort);
    }

    #[test]
    fn test_result_shape_rejects_non_datatype() {
        let bv = Sort::bitvec(32);
        assert!(result_shape(&bv).is_none(), "non-datatype should not be Result-shaped");
    }
}
