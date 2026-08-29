// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC stub utility functions (Option/Result helpers, shared utilities).
//!
//! Converted from include!() to proper module per #2595.
//! Split from stubs_impl.rs per #1880 for reviewability.
//! Decomposed per #2220: collection, intrinsic, and dispatch detectors
//! moved to stubs_util_collections.rs, stubs_util_intrinsics.rs,
//! stubs_util_dispatch.rs.

use std::collections::HashSet;

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::Operand;
use tracing::{debug, trace};

use super::stubs::StubKind;
use super::stubs_option_helpers::OptionHelpers;
use super::{ChcCtx, chc_fresh_name, declare_pending_var};
use crate::codegen_ay::chc::codegen_ctx::diagnostics::CellCounter;
use crate::codegen_ay::types::CtorFieldExt;

/// Recovers Option payload from a reconstructed flattened ITE:
/// `ite(cond, Some(payload), None)` or `ite(cond, None, Some(payload))`
/// -> `payload`.
#[must_use]
pub(in crate::codegen_ay::chc) fn extract_payload_from_option_reconstruction_ite(
    expr: &Expr,
) -> Option<Expr> {
    let ExprValue::Ite { then_expr, else_expr, .. } = expr.value() else {
        return None;
    };

    fn option_ctor_payload(expr: &Expr) -> Option<Option<Expr>> {
        let ExprValue::DatatypeConstructor { args, .. } = expr.value() else {
            return None;
        };
        match args[..] {
            [] => Some(None),
            [ref payload] => Some(Some(payload.clone())),
            _ => None,
        }
    }

    match (option_ctor_payload(then_expr), option_ctor_payload(else_expr)) {
        (Some(Some(payload)), Some(None)) | (Some(None), Some(Some(payload))) => Some(payload),
        _ => None,
    }
}

/// Convert a flattened enum discriminant into a boolean predicate.
///
/// Returns `None` when the discriminant sort is neither Bool nor BitVec.
#[must_use]
fn discr_to_bool_predicate(discr: Expr) -> Option<Expr> {
    if discr.sort().is_bool() {
        Some(discr)
    } else {
        // Non-zero discriminant means the "true" variant.
        discr.sort().bitvec_width().map(|width| discr.ne(Expr::bitvec_const(0u64, width)))
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Resolves a function call to a `StubKind`, returning it only if it
    /// matches one of the `accept`ed variants.
    ///
    /// All `detect_*_stub` functions share this pattern: resolve callee path →
    /// registry lookup → filter to accepted set → trace on mismatch.
    ///
    /// Part of #2304 (FE1): Extracted from 4 near-identical detect functions.
    pub(in crate::codegen_ay::chc) fn detect_stub_filtered(
        &self,
        func: &Operand,
        accept: &[StubKind],
        context: &str,
    ) -> Option<StubKind> {
        let callee_path = self.resolve_callee_path(func)?;
        let stub = self.stub_registry.lookup(&callee_path)?;
        if accept.contains(&stub) {
            Some(stub)
        } else {
            trace!(?stub, "detect_{context}_stub: non-{context} stub from registry");
            None
        }
    }

    /// Translate Option::is_some/is_none calls to discriminant checks.
    ///
    /// is_some(&self) -> bool: checks if the Option variant is Some
    /// is_none(&self) -> bool: checks if the Option variant is None
    ///
    /// Part of #2244: After flattening (#2214), Option locals are decomposed into
    /// scalar state vars (fld0=Bool discriminant, fld1=payload). The datatype path
    /// no longer applies; instead, read fld0 directly as the is_some predicate.
    pub(in crate::codegen_ay::chc) fn translate_option_predicate_call(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // Part of #2244: Try the flattened-enum path first. When the Option local
        // has been flattened, its discriminant (fld0) is the is_some Bool directly.
        if let Some(discr_expr) = self.resolve_flattened_enum_discr(args, modified_locals) {
            let is_some = discr_to_bool_predicate(discr_expr)?;
            return if stub == StubKind::OptionIsSome {
                Some(is_some)
            } else if stub == StubKind::OptionIsNone {
                Some(is_some.not())
            } else {
                None
            };
        }

        // The self argument is a reference to the Option value.
        // Part of #3036: Use the full 6-tier referent resolution instead of just
        // ref_targets + translate_operand. This handles cases where ref_targets
        // doesn't track the reference (e.g., function parameter references resolved
        // via ref_arg_pointee_idx, const refs via const_ref_values).
        let option_expr = args
            .first()
            .and_then(|arg| self.resolve_ref_or_const_referent_impl(arg, modified_locals))?;

        // Check that we have a datatype sort (Option)
        if !option_expr.sort().is_datatype() {
            debug!("option predicate on non-datatype sort {:?}", option_expr.sort());
            return None;
        }
        self.declare_datatype_sort_if_needed(option_expr.sort());

        if stub == StubKind::OptionIsSome {
            Some(self.option_is_some(option_expr))
        } else if stub == StubKind::OptionIsNone {
            Some(self.option_is_some(option_expr).not())
        } else {
            None
        }
    }

    /// Translate Result::is_ok/is_err calls to discriminant checks.
    ///
    /// is_ok(&self) -> bool: checks if the Result variant is Ok
    /// is_err(&self) -> bool: checks if the Result variant is Err
    /// Part of #2125: CHC bool-method stub parity gap.
    ///
    /// Part of #2244: After flattening (#2214), Result locals are decomposed into
    /// scalar state vars (fld0=Bool discriminant, fld1=payload). The discriminant
    /// convention is true_variant=0 (Ok), false_variant=1 (Err), so fld0=true means
    /// Ok and fld0=false means Err.
    pub(in crate::codegen_ay::chc) fn translate_result_predicate_call(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // Part of #2244: Try the flattened-enum path first.
        if let Some(discr_expr) = self.resolve_flattened_enum_discr(args, modified_locals) {
            let is_ok = discr_to_bool_predicate(discr_expr)?;
            return if stub == StubKind::ResultIsOk {
                Some(is_ok)
            } else if stub == StubKind::ResultIsErr {
                Some(is_ok.not())
            } else {
                None
            };
        }

        // The self argument is a reference to the Result value.
        // Part of #3036: Use the full 6-tier referent resolution instead of just
        // ref_targets + translate_operand. Same fix as Option predicate path.
        let result_expr = args
            .first()
            .and_then(|arg| self.resolve_ref_or_const_referent_impl(arg, modified_locals))?;

        // Check that we have a datatype sort (Result)
        if !result_expr.sort().is_datatype() {
            debug!("result predicate on non-datatype sort {:?}", result_expr.sort());
            return None;
        }
        self.declare_datatype_sort_if_needed(result_expr.sort());

        if stub == StubKind::ResultIsOk {
            Some(self.result_variant_tester(result_expr, "Ok", "result_is_ok"))
        } else if stub == StubKind::ResultIsErr {
            Some(self.result_variant_tester(result_expr, "Err", "result_is_err"))
        } else {
            None
        }
    }

    /// Translate Option::unwrap_or / Result::unwrap_or calls.
    ///
    /// unwrap_or(self, default) -> T:
    ///   Option: ITE(is_some, value, default)
    ///   Result: ITE(is_ok, ok_value, default)
    pub(in crate::codegen_ay::chc) fn translate_unwrap_or_call(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if args.len() < 2 {
            return None;
        }

        // args[0] = Option/Result (self — by value), args[1] = default
        let default_expr = self.translate_operand_with_modified(&args[1], modified_locals)?;

        // Part of #2244: Try the flattened-enum path for unwrap_or.
        if let Some(discr) = self.resolve_flattened_enum_discr_by_value(&args[0], modified_locals)
            && let Some(payload) = self.resolve_flattened_enum_payload(&args[0], modified_locals)
        {
            let is_some_or_ok = discr_to_bool_predicate(discr)?;
            return Some(Expr::ite(is_some_or_ok, payload, default_expr));
        }

        let self_expr = self.translate_operand_with_modified(&args[0], modified_locals)?;

        if !self_expr.sort().is_datatype() {
            debug!("unwrap_or on non-datatype sort {:?}", self_expr.sort());
            return None;
        }
        self.declare_datatype_sort_if_needed(self_expr.sort());

        if stub == StubKind::OptionUnwrapOr {
            let is_some = self.option_is_some(self_expr.clone());
            let inner = self.option_unwrap_value_on_some_path(self_expr)?;
            Some(Expr::ite(is_some, inner, default_expr))
        } else if stub == StubKind::ResultUnwrapOr {
            let is_ok = self.result_variant_tester(self_expr.clone(), "Ok", "result_is_ok");
            // Extract the Ok value — clone Sort (O(1) Arc) so dt_name borrows
            // from sort_ref rather than self_expr, avoiding .to_string() allocation.
            let sort_ref = self_expr.sort().clone();
            let dt_name = sort_ref.datatype_name()?;
            let field_name = if sort_ref.datatype_has_field("value") {
                "value"
            } else if sort_ref.datatype_has_field("ok") {
                "ok"
            } else {
                return None;
            };
            let inner = self_expr.field_select(dt_name, field_name, default_expr.sort().clone());
            Some(Expr::ite(is_ok, inner, default_expr))
        } else {
            None
        }
    }

    /// Emit the None/Err-panic obligation for an unwrap/expect stub call.
    ///
    /// The obligation is `good_variant` (the condition that must hold);
    /// `emit_error_rule_for_condition_with_kind` negates it and skips the rule
    /// when it const-folds to `true` (so `Some(7).unwrap()` stays green).
    pub(in crate::codegen_ay::chc) fn emit_unwrap_expect_panic_obligation(
        &mut self,
        cx: &crate::codegen_ay::chc::call::chc_call_context::ChcCallContext<'_>,
        bb_idx: usize,
    ) {
        let Some(good_variant) =
            self.unwrap_expect_good_variant_predicate(cx.stub, cx.args, cx.modified_locals)
        else {
            debug!(?cx.stub, bb_idx, "unwrap/expect: no variant predicate; panic obligation not emitted");
            return;
        };
        let message = match cx.stub {
            StubKind::OptionUnwrap | StubKind::OptionExpect => {
                "called `Option::unwrap()` on a `None` value"
            }
            StubKind::ResultUnwrapErr => "called `Result::unwrap_err()` on an `Ok` value",
            _ => "called `Result::unwrap()` on an `Err` value",
        };
        self.emit_error_rule_for_condition_with_kind(
            cx.from_app,
            good_variant,
            cx.stmt_constraints,
            bb_idx,
            trust_mc_core::violation::PropertyKind::Panic,
            Some(message.to_string()),
        );
    }

    /// SOUNDNESS (None/Err-panic obligation for the CHC lane).
    ///
    /// Build the "good variant" predicate for an unwrap/expect stub: the
    /// condition that MUST HOLD for the call not to panic. `unwrap`/`expect`
    /// survive `fn_inline` as `Call` terminators
    /// (`has_special_codegen_handler`), so the library body's
    /// `unwrap_failed` / `panic_stub` edge never reaches codegen and the panic
    /// property has to be emitted HERE — exactly as the BMC twin
    /// `codegen_option_unwrap_impl` does.
    ///
    /// `OptionUnwrapUnchecked` is deliberately excluded: reaching it on `None`
    /// is UB, not a panic (it is in the same `UNWRAP_EXPECT` stub group).
    pub(in crate::codegen_ay::chc) fn unwrap_expect_good_variant_predicate(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if args.is_empty() {
            return None;
        }
        let inverted = match stub {
            StubKind::OptionUnwrap
            | StubKind::OptionExpect
            | StubKind::ResultUnwrap
            | StubKind::ResultExpect => false,
            // unwrap_err panics on the Ok variant.
            StubKind::ResultUnwrapErr => true,
            _ => return None,
        };
        let flip = |e: Expr| if inverted { e.not() } else { e };

        // Flattened (fld0 = discriminant) path — the representation uw.rs /
        // sym.rs take.
        if let Some(discr) = self.resolve_flattened_enum_discr_by_value(&args[0], modified_locals) {
            return discr_to_bool_predicate(discr).map(flip);
        }

        let self_expr = self.translate_operand_with_modified(&args[0], modified_locals)?;

        if !self_expr.sort().is_datatype() {
            // Niche-optimized Option<ptr/ref>: None is the null pointer.
            if matches!(stub, StubKind::OptionUnwrap | StubKind::OptionExpect)
                && let Some(width) = self_expr.sort().bitvec_width()
            {
                return Some(self_expr.ne(Expr::bitvec_const(0u64, width)));
            }
            return None;
        }
        self.declare_datatype_sort_if_needed(self_expr.sort());

        match stub {
            StubKind::OptionUnwrap | StubKind::OptionExpect => Some(self.option_is_some(self_expr)),
            StubKind::ResultUnwrap | StubKind::ResultExpect | StubKind::ResultUnwrapErr => {
                Some(flip(self.result_variant_tester(self_expr, "Ok", "result_is_ok")))
            }
            _ => None,
        }
    }

    /// Translate Option::unwrap / Option::expect / Result::unwrap / Result::expect /
    /// Result::unwrap_err to value extraction.
    ///
    /// These extract the inner value from Option/Result.
    /// Part of #1836: Recover harnesses calling unwrap/expect.
    /// Part of #3587: Add Result::unwrap_err parity.
    ///
    /// Part of #2244: After flattening, Option/Result locals are scalar state vars.
    /// The payload is fld1, so unwrap returns fld1 directly.
    /// For same-sort Result<T, T> (e.g., compare_exchange), unwrap_err also
    /// returns fld1 since T == E share the payload slot.
    pub(in crate::codegen_ay::chc) fn translate_unwrap_expect_call(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if args.is_empty() {
            return None;
        }

        // Part of #2244: Try the flattened-enum path. unwrap/expect take self by
        // value but MIR may pass a Move of the local. The payload is at fld1.
        // For same-sort Result<T, T>, unwrap_err also uses the shared payload slot.
        if let Some(payload) = self.resolve_flattened_enum_payload(&args[0], modified_locals) {
            return Some(payload);
        }

        // args[0] = Option/Result (self — by value)
        let self_expr = self.translate_operand_with_modified(&args[0], modified_locals)?;

        if !self_expr.sort().is_datatype() {
            // Part of #3979: Niche-optimized Option<ptr/ref> is represented as
            // BV(64) (pointer width), not a datatype. The null pointer is the
            // None variant, and any non-null value IS the Some payload. For
            // unwrap/expect, the value is semantically identity — the panic on
            // None is encoded elsewhere as a bounds guard. Return the BV directly.
            if matches!(
                stub,
                StubKind::OptionUnwrap | StubKind::OptionExpect | StubKind::OptionUnwrapUnchecked
            ) && self_expr.sort().is_bitvec()
            {
                debug!(
                    "unwrap/expect: niche-optimized Option with BV sort {:?}; identity pass-through",
                    self_expr.sort()
                );
                return Some(self_expr);
            }
            debug!("unwrap/expect on non-datatype sort {:?}", self_expr.sort());
            return None;
        }
        self.declare_datatype_sort_if_needed(self_expr.sort());

        if matches!(
            stub,
            StubKind::OptionUnwrap | StubKind::OptionExpect | StubKind::OptionUnwrapUnchecked
        ) {
            if let Some(payload) = extract_payload_from_option_reconstruction_ite(&self_expr) {
                return Some(payload);
            }
            // Extract inner value from Option (expect/unwrap_unchecked = unwrap semantics)
            self.option_unwrap_value_on_some_path(self_expr)
        } else if matches!(stub, StubKind::ResultUnwrap | StubKind::ResultExpect) {
            // Extract Ok value from Result — clone Sort (O(1) Arc) so dt_name
            // borrows from sort_ref rather than self_expr.
            let sort_ref = self_expr.sort().clone();
            let dt_name = sort_ref.datatype_name()?;
            let field_name = if sort_ref.datatype_has_field("value") {
                "value"
            } else if sort_ref.datatype_has_field("ok") {
                "ok"
            } else {
                return None;
            };
            // Extract field sort from datatype constructor definitions
            let dt = sort_ref.datatype_sort()?;
            let inner_sort = dt.constructors.iter().find_map(|c| c.field_sort(field_name))?;
            Some(self_expr.field_select(dt_name, field_name, inner_sort))
        } else if stub == StubKind::ResultUnwrapErr {
            // Part of #3587: Extract Err value from Result.
            // For datatype-backed heterogeneous Result<T, E>, select the "err" field.
            let sort_ref = self_expr.sort().clone();
            let dt_name = sort_ref.datatype_name()?;
            let field_name = if sort_ref.datatype_has_field("err") {
                "err"
            } else if sort_ref.datatype_has_field("value") {
                // Same-sort Result uses shared "value" field for both variants
                "value"
            } else {
                return None;
            };
            let dt = sort_ref.datatype_sort()?;
            let inner_sort = dt.constructors.iter().find_map(|c| c.field_sort(field_name))?;
            Some(self_expr.field_select(dt_name, field_name, inner_sort))
        } else {
            None
        }
    }

    /// Translate Option::unwrap_or_else / Result::unwrap_or_else calls.
    ///
    /// Over-approximation: closure result is modeled as unconstrained symbolic value.
    ///   Option: ITE(is_some, value, symbolic_T)
    ///   Result: ITE(is_ok, ok_value, symbolic_T)
    ///
    /// AUDIT (task #65, stub_approximation — all three increment sites below):
    /// NOT a certified SoundHavoc, keep counting. The RESULT value is a pure
    /// fresh-var widening (universally quantified — sound for proofs), but the
    /// closure BODY is dropped entirely: its panics/assertions and diverging
    /// behavior vanish from the model, so `x.unwrap_or_else(|| panic!())` with
    /// `x = None` verifies as a clean pass while the real program panics. That
    /// is a fail-open on the closure's own obligations, not a pure widening.
    /// Plumbed via generate_metadata (codegen_units.rs) as SOUND_APPROXIMATION
    /// so the driver's Step-C fail-closes any Success carrying it.
    pub(in crate::codegen_ay::chc) fn translate_unwrap_or_else_call(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if args.is_empty() {
            return None;
        }

        // args[0] = Option/Result (self — by value), args[1] = closure (ignored)

        // Part of #2244: Try flattened path. For unwrap_or_else, the closure result
        // is over-approximated as symbolic, so we only need discr + payload.
        if let Some(discr) = self.resolve_flattened_enum_discr_by_value(&args[0], modified_locals)
            && let Some(payload) = self.resolve_flattened_enum_payload(&args[0], modified_locals)
        {
            let is_some_or_ok = discr_to_bool_predicate(discr)?;
            self.diagnostics.stub_approximation.inc();
            let closure_name = chc_fresh_name("unwrap_or_else_chc");
            let closure_sort = payload.sort().clone();
            let closure_result = declare_pending_var(closure_name, closure_sort);
            return Some(Expr::ite(is_some_or_ok, payload, closure_result));
        }

        let self_expr = self.translate_operand_with_modified(&args[0], modified_locals)?;

        if !self_expr.sort().is_datatype() {
            debug!("unwrap_or_else on non-datatype sort {:?}", self_expr.sort());
            return None;
        }
        self.declare_datatype_sort_if_needed(self_expr.sort());

        if stub == StubKind::OptionUnwrapOrElse {
            let is_some = self.option_is_some(self_expr.clone());
            let inner = self.option_unwrap_value(self_expr)?;
            // Symbolic closure result with same sort as inner value
            self.diagnostics.stub_approximation.inc();
            let closure_name = chc_fresh_name("opt_unwrap_or_else_chc");
            let closure_sort = inner.sort().clone();
            let closure_result = declare_pending_var(closure_name, closure_sort);
            Some(Expr::ite(is_some, inner, closure_result))
        } else if stub == StubKind::ResultUnwrapOrElse {
            let is_ok = self.result_variant_tester(self_expr.clone(), "Ok", "result_is_ok");
            // Clone Sort (O(1) Arc) so dt_name borrows from sort_ref.
            let sort_ref = self_expr.sort().clone();
            let dt_name = sort_ref.datatype_name()?;
            let field_name = if sort_ref.datatype_has_field("value") {
                "value"
            } else if sort_ref.datatype_has_field("ok") {
                "ok"
            } else {
                return None;
            };
            // Extract field sort from datatype constructor definitions
            let dt = sort_ref.datatype_sort()?;
            let inner_sort = dt.constructors.iter().find_map(|c| c.field_sort(field_name))?;
            let ok_value = self_expr.field_select(dt_name, field_name, inner_sort.clone());
            // Symbolic closure result
            self.diagnostics.stub_approximation.inc();
            let closure_name = chc_fresh_name("res_unwrap_or_else_chc");
            let closure_result = declare_pending_var(closure_name, inner_sort);
            Some(Expr::ite(is_ok, ok_value, closure_result))
        } else {
            None
        }
    }

    /// Translate Option/Result combinator calls.
    ///
    /// These return symbolic values because closures cannot be modeled in CHC.
    /// Part of #1836: Recover harnesses calling combinators on Option/Result values.
    pub(in crate::codegen_ay::chc) fn translate_combinator_call(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        _modified_locals: &HashSet<usize>,
        dest_sort: &Sort,
    ) -> Option<Expr> {
        if args.is_empty() {
            return None;
        }

        let prefix = match stub {
            StubKind::OptionAndThen => "opt_and_then",
            StubKind::OptionOkOrElse => "opt_ok_or_else",
            StubKind::OptionOkOr => "opt_ok_or",
            StubKind::OptionMap => "opt_map",
            StubKind::ResultMap => "res_map",
            StubKind::ResultAndThen => "res_and_then",
            StubKind::ResultMapErr => "res_map_err",
            StubKind::ResultOk => "res_ok",
            StubKind::ResultErr => "res_err",
            _ => return None, // partial dispatch: StubKind
        };

        // Over-approximate: return symbolic value of the destination sort.
        // This is sound — it admits more behaviors than the real program.
        //
        // AUDIT (task #65, stub_approximation): keep counting, NOT SoundHavoc.
        // The closure-taking combinators (map/and_then/ok_or_else/map_err)
        // drop the closure body's panics and effects — same fail-open as
        // unwrap_or_else above. The pure value combinators in this table
        // (ok/err/ok_or) ARE pure fresh-var widenings and could in principle
        // be reclassified as certified SoundHavoc, but splitting the
        // classification per StubKind ungates proofs and therefore needs its
        // own missed-bug gate; until then all arms stay counted and Step-C
        // decides (fail-closed).
        self.diagnostics.stub_approximation.inc();
        let sym_name = chc_fresh_name(prefix);
        Some(declare_pending_var(sym_name, dest_sort.clone()))
    }

    // Flattened enum fld0/fld1 helpers moved to stubs_util_flattened_enum.rs
    // per #2408 decomposition.
    //
    // Option/Result/Ordering helper methods and datatype constructors moved to
    // stubs_option_helpers.rs per #2164 decomposition. Methods moved:
    // option_unwrap_value, make_option_sort, make_none_expr, make_none_expr_for_option,
    // coerce_value_to_sort, make_some_expr_for_option, option_is_some,
    // result_variant_tester, option_value_sort, option_payload_variant_name,
    // option_empty_variant_name, wrap_ordering_int_in_option, convert_ordering_int_to_bv
}
