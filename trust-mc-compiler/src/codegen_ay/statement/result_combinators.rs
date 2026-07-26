// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Result combinator codegen: unwrap_or_else, map, and_then, map_err, ok, err.
//!
//! Extracted from `result.rs` — Part of #4206.

use super::StatementCodegen;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::warn;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen `Result::unwrap_or_else(self, f) -> T`.
    ///
    /// Over-approximation: `ITE(is_ok, ok_value, symbolic_T)`.
    /// The closure result is modeled as unconstrained since we cannot execute
    /// closures in the verification model. This is sound (more behaviors than
    /// real program) and allows verification to proceed.
    ///
    /// Part of #1836: Recover harnesses calling unwrap_or_else on Result values.
    ///
    /// REQUIRES: `args[0]` is a `Result<T, E>` value, `args[1]` is a closure
    /// ENSURES: Stores `ITE(is_ok, ok_value, symbolic_T)` to destination
    pub(super) fn codegen_result_unwrap_or_else(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("codegen_result_unwrap_or_else: expected at least 1 arg, got 0");
            return None;
        }

        let result_base = self
            .get_result_base_direct(&args[0])
            .or_else(|| self.get_result_base_from_ref(&args[0]))?;

        let dest_sort = self.infer_sort_from_place(destination)?;

        // Build is_ok condition and extract Ok value
        let discrim_name = crate::codegen_ay::names::discrim_name(result_base.as_ref());
        let (is_ok, ok_value) = if let Some(discrim_expr) = self.env_lookup(&discrim_name) {
            let zero = self.make_zero_for_discrim(discrim_expr)?;
            let is_ok = discrim_expr.clone().eq(zero);
            let value_name = crate::codegen_ay::names::payload_name(result_base.as_ref());
            let inner = self.env_lookup(&value_name)?.clone();
            (is_ok, inner)
        } else if let Some(result_expr) = self.env_lookup(result_base.as_ref()) {
            // Both methods now consume self — clone needed.
            let sort = result_expr.sort();
            let dt_name = sort.datatype_name()?;
            // Part of #2631: Use scoped constructor name.
            let ok_ctor = Self::find_result_constructor(sort, "Ok", dt_name)?;
            let field_name = if sort.datatype_has_field("value") {
                "value"
            } else if sort.datatype_has_field("ok") {
                "ok"
            } else {
                warn!("Result::unwrap_or_else: datatype '{}' missing value/ok field", dt_name);
                // Part of #3211: Track constraint drop in demotion pipeline.
                self.ctx.unsupported_with_fallback(
                    "result_unwrap_or_else_missing_field",
                    "datatype missing value/ok field",
                );
                return None;
            };
            let is_ok = result_expr.clone().is_constructor(dt_name, ok_ctor);
            let inner = result_expr.clone().field_select(dt_name, field_name, dest_sort.clone());
            (is_ok, inner)
        } else {
            warn!("Result::unwrap_or_else: could not find Result value for {}", result_base);
            // Part of #3211: Track constraint drop in demotion pipeline.
            self.ctx.unsupported_with_fallback(
                "result_unwrap_or_else_missing_value",
                "could not find Result value",
            );
            return None;
        };

        // Over-approximate closure result with symbolic value
        let closure_name = self.ctx.fresh_name("res_unwrap_or_else");
        let closure_result = self.ctx.declare_var(&closure_name, dest_sort);

        // ITE(is_ok, ok_value, symbolic_closure_result)
        let result = ay_bindings::Expr::ite(is_ok, ok_value, closure_result);

        self.bind_ssa_result(destination, result);
        target
    }

    /// Codegen `Result::map(self, f) -> Result<U, E>`.
    ///
    /// Over-approximation: produces symbolic `Result<U, E>`.
    /// The closure result is modeled as unconstrained since we cannot execute
    /// closures in the verification model. Sound over-approximation.
    ///
    /// Part of #1836: Recover harnesses calling map on Result values.
    ///
    /// REQUIRES: `args[0]` is a `Result<T, E>` value, `args[1]` is a closure
    /// ENSURES: Stores symbolic `Result<U, E>` to destination
    pub(super) fn codegen_result_map(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("codegen_result_map: expected at least 1 arg, got 0");
            return None;
        }

        // Result::map returns Result<U, E> which is the destination type
        // Since we can't model the closure, produce a symbolic result
        self.codegen_symbolic_result(destination);
        target
    }

    /// Codegen `Result::and_then(self, f) -> Result<U, E>`.
    ///
    /// Over-approximation: produces symbolic `Result<U, E>`.
    /// The closure `f: FnOnce(T) -> Result<U, E>` is modeled as unconstrained
    /// since we cannot execute closures in the verification model.
    ///
    /// Part of #1836: Recover harnesses calling and_then on Result values.
    ///
    /// REQUIRES: `args[0]` is a `Result<T, E>` value, `args[1]` is a closure
    /// ENSURES: Stores symbolic `Result<U, E>` to destination
    pub(super) fn codegen_result_and_then(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("codegen_result_and_then: expected at least 1 arg, got 0");
            return None;
        }

        // and_then returns Result<U, E> which is the destination type
        // Since we can't model the closure, produce a symbolic result
        self.codegen_symbolic_result(destination);
        target
    }

    /// Codegen `Result::map_err(self, f) -> Result<T, F>`.
    ///
    /// Over-approximation: produces symbolic `Result<T, F>`.
    /// The closure `f: FnOnce(E) -> F` is modeled as unconstrained
    /// since we cannot execute closures in the verification model.
    ///
    /// Part of #1836: Recover harnesses calling map_err on Result values.
    ///
    /// REQUIRES: `args[0]` is a `Result<T, E>` value, `args[1]` is a closure
    /// ENSURES: Stores symbolic `Result<T, F>` to destination
    pub(super) fn codegen_result_map_err(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("codegen_result_map_err: expected at least 1 arg, got 0");
            return None;
        }

        // map_err returns Result<T, F> which is the destination type
        // Since we can't model the closure, produce a symbolic result
        self.codegen_symbolic_result(destination);
        target
    }

    /// Codegen `Result::ok(self) -> Option<T>`.
    ///
    /// Converts `Result<T, E>` to `Option<T>`: `Ok(t) -> Some(t)`, `Err(_) -> None`.
    /// Faithful path (#multi-hop-flattened-option, Link B): derive the Option
    /// from the REAL Result value (flattened keys or constrained datatype expr).
    /// Falls back to the sound symbolic over-approximation — now TRACKED via
    /// `unsupported_with_fallback` — only when the Result self is unresolvable
    /// (previously this was a SILENT unconstrained symbolic, so a spurious CEX
    /// through it triaged as "Genuine" with Clean quality).
    ///
    /// Part of #1836: Recover harnesses calling ok() on Result values.
    ///
    /// REQUIRES: `args[0]` is a `Result<T, E>` value
    /// ENSURES: Stores `Ok(t) -> Some(t) / Err(_) -> None` derived from the real
    /// Result when resolvable, else a tracked symbolic `Option<T>`
    pub(super) fn codegen_result_ok(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("codegen_result_ok: expected at least 1 arg, got 0");
            return None;
        }

        if self.try_codegen_result_to_option(&args[0], destination, true) {
            return target;
        }

        // Unresolvable Result self: sound symbolic over-approximation, tracked.
        self.ctx.unsupported_with_fallback(
            "result_ok_symbolic_fallback",
            "Result::ok: unresolvable Result self; symbolic Option<T>",
        );
        self.codegen_symbolic_result(destination);
        target
    }

    /// Codegen `Result::err(self) -> Option<E>`.
    ///
    /// Converts `Result<T, E>` to `Option<E>`: `Err(e) -> Some(e)`, `Ok(_) -> None`.
    /// Faithful path (#multi-hop-flattened-option, Link B): mirror of
    /// [`Self::codegen_result_ok`] with the taken variant flipped; the fallback
    /// symbolic over-approximation is tracked (previously silent).
    ///
    /// Part of #1836: Recover harnesses calling err() on Result values.
    ///
    /// REQUIRES: `args[0]` is a `Result<T, E>` value
    /// ENSURES: Stores `Err(e) -> Some(e) / Ok(_) -> None` derived from the real
    /// Result when resolvable, else a tracked symbolic `Option<E>`
    pub(super) fn codegen_result_err(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("codegen_result_err: expected at least 1 arg, got 0");
            return None;
        }

        if self.try_codegen_result_to_option(&args[0], destination, false) {
            return target;
        }

        // Unresolvable Result self: sound symbolic over-approximation, tracked.
        self.ctx.unsupported_with_fallback(
            "result_err_symbolic_fallback",
            "Result::err: unresolvable Result self; symbolic Option<E>",
        );
        self.codegen_symbolic_result(destination);
        target
    }

    /// Faithful `Result<T, E> -> Option<_>` lowering for `ok()` / `err()`
    /// (#multi-hop-flattened-option, Link B).
    ///
    /// Publishes the destination Option in the FLATTENED convention (the one
    /// `codegen_option_copied` / the mini-inline re-keys consume):
    ///   - `{dest}.0`                  = BV32 discriminant, Some = 1 / None = 0
    ///   - `{dest}.1`, `{dest}_variant_1_field_0`, `{dest}` = payload VALUE
    ///
    /// Every published expr is DERIVED from the real Result value — either its
    /// flattened `.0`/`.1` keys (Ok = variant 0) or its constrained datatype
    /// expr via `is_constructor`/`field_select`. Never a fresh symbolic: the
    /// reverted transparent-Downcast shortcut showed a synthesized value here is
    /// a false-verify surface. Returns `false` (caller emits the TRACKED
    /// symbolic fallback) when the Result self, its taken-variant payload, or a
    /// bitvec payload representation is not resolvable.
    fn try_codegen_result_to_option(
        &mut self,
        self_arg: &Operand,
        destination: &Place,
        want_ok: bool,
    ) -> bool {
        let Some(result_base) = self
            .get_result_base_direct(self_arg)
            .or_else(|| self.get_result_base_from_ref(self_arg))
        else {
            return false;
        };

        let discrim_key = crate::codegen_ay::names::discrim_name(result_base.as_ref());
        let (is_taken, payload) = if let Some(discrim_expr) = self.env_lookup(&discrim_key).cloned()
        {
            // Flattened Result: `.0` holds the discriminant with Ok = 0 (the
            // `codegen_result_unwrap_or_else` convention); the Ok payload lives
            // under `.1`, the Err payload under `_variant_1_field_0`.
            let Some(zero) = self.make_zero_for_discrim(&discrim_expr) else {
                return false;
            };
            let is_ok = discrim_expr.eq(zero);
            let is_taken = if want_ok {
                is_ok
            } else {
                ay_bindings::Expr::ite(
                    is_ok,
                    ay_bindings::Expr::bool_const(false),
                    ay_bindings::Expr::bool_const(true),
                )
            };
            let payload_key = if want_ok {
                crate::codegen_ay::names::payload_name(result_base.as_ref())
            } else {
                crate::codegen_ay::names::base_variant_field_name(result_base.as_ref(), 1, 0)
            };
            let Some(payload) = self.env_lookup(&payload_key).cloned() else {
                return false;
            };
            (is_taken, payload)
        } else if let Some(result_expr) = self.env_lookup(result_base.as_ref()).cloned() {
            // Native SMT-datatype Result: constructor test + payload select on
            // the constrained expr (both faithful by construction).
            let sort = result_expr.sort().clone();
            let Some(dt_name) = sort.datatype_name() else {
                return false;
            };
            let want: fn(&str) -> bool = if want_ok {
                crate::codegen_ay::names::is_ok_constructor
            } else {
                crate::codegen_ay::names::is_err_constructor
            };
            let Some((ctor_idx, ctor)) = sort
                .datatype_sort()
                .into_iter()
                .flat_map(|dt| dt.constructors.iter().enumerate())
                .find(|(_, c)| want(&c.name))
            else {
                return false;
            };
            if ctor.fields.len() != 1 {
                return false;
            }
            let is_taken = result_expr.clone().is_constructor(dt_name, &*ctor.name);
            let Some(payload) =
                crate::codegen_ay::types::datatype_field_select(result_expr, ctor_idx, 0)
            else {
                return false;
            };
            (is_taken, payload)
        } else {
            return false;
        };

        // Bool payload -> BV1 so the flattened Option stays bitvec (mirrors
        // `codegen_option_copied`); non-bitvec payloads bail to the tracked
        // fallback rather than inventing a representation.
        let payload = if payload.sort().is_bool() {
            ay_bindings::Expr::ite(
                payload,
                ay_bindings::Expr::bitvec_const(1u64, 1),
                ay_bindings::Expr::bitvec_const(0u64, 1),
            )
        } else {
            payload
        };
        let Some(payload_width) = payload.sort().bitvec_width() else {
            return false;
        };

        // `{dest}.0` = ite(is_taken, 1, 0) in the BV32 flattened convention.
        let discrim_bv32 = ay_bindings::Expr::ite(
            is_taken,
            ay_bindings::Expr::bitvec_const(1u64, 32),
            ay_bindings::Expr::bitvec_const(0u64, 32),
        );

        let dest_base = self.ssa_base_name(destination);

        let dest_discrim_key = crate::codegen_ay::names::discrim_name(&dest_base);
        let dn = self.ssa_name_from_base(&dest_discrim_key, true);
        let dv = self.ctx.declare_var(&dn, ay_bindings::Sort::bitvec(32));
        self.assert_ssa_def(dv.clone(), discrim_bv32, &dest_discrim_key);
        self.env_update(dest_discrim_key, dv);

        // Payload under all three keys the downstream consumers probe
        // (`codegen_option_copied` prefers `.1`, then `_variant_1_field_0`,
        // then the base; the mini-inline re-keys carry whichever exist).
        for key in [
            crate::codegen_ay::names::payload_name(&dest_base),
            crate::codegen_ay::names::base_variant_field_name(&dest_base, 1, 0),
            dest_base,
        ] {
            let name = self.ssa_name_from_base(&key, true);
            let var = self.ctx.declare_var(&name, ay_bindings::Sort::bitvec(payload_width));
            self.assert_ssa_def(var.clone(), payload.clone(), &key);
            self.env_update(key, var);
        }
        true
    }
}
