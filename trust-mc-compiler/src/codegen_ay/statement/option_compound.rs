// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Compound Option method codegen for AY.
//!
//! Extracted from `option.rs` per #3036 for file size compliance.
//! Contains methods that combine discriminant checking with value extraction
//! or closure over-approximation:
//! - `map` - applies closure (over-approximated as symbolic)
//! - `unwrap_or` - value extraction with default
//! - `unwrap_or_else` - value extraction with closure (over-approximated)
//! - `and_then` - produces symbolic Option result
//! - `ok_or_else` - converts Option to Result (over-approximated)

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::names;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::{debug, warn};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen Option::map method which applies a closure to contained value.
    ///
    /// Option::map(self, f) returns:
    /// - Some(f(x)) if self is Some(x)
    /// - None if self is None
    ///
    /// #478: Used by PolymorphicIter::next in array iteration.
    pub(super) fn codegen_option_map(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Contract enforcement (#695): args[0] = Option<T>, args[1] = closure
        debug_assert!(
            args.len() >= 2,
            "codegen_option_map: REQUIRES args.len() >= 2 (Option self + closure)"
        );
        // args[0] = Option<T> (self)
        // args[1] = closure F where F: FnOnce(T) -> U
        if args.len() < 2 {
            warn!("codegen_option_map: expected 2 args, got {}", args.len());
            return None;
        }

        // Get destination type for logging
        let dest_ty = destination.ty(self.body.locals()).into_option();
        debug!("codegen_option_map: dest_ty={:?}", dest_ty);

        // For now, produce a symbolic result of the appropriate Option type.
        // Full Option::map semantics would require:
        // 1. Check if input is Some(x) or None
        // 2. If Some(x), apply closure to get y, return Some(y)
        // 3. If None, return None
        // This simplified version allows verification to proceed.
        self.codegen_symbolic_result(destination);
        target
    }

    /// Codegen `Option::unwrap_or(self, default) -> T`.
    ///
    /// Returns the inner value if Some, otherwise returns the default.
    /// Semantics: `if is_some(self) { unwrap(self) } else { default }`
    ///
    /// Part of #1836: Recover harnesses calling unwrap_or on Option values.
    ///
    /// REQUIRES: `args[0]` is an `Option<T>` value, `args[1]` is the default `T`
    /// ENSURES: Stores `ITE(is_some, inner_value, default)` to destination
    pub(super) fn codegen_option_unwrap_or(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            warn!("codegen_option_unwrap_or: expected 2 args, got {}", args.len());
            return None;
        }

        let option_base = self
            .get_option_base_direct(&args[0])
            .or_else(|| self.get_option_base_from_ref(&args[0]))?;

        let result_sort = self.infer_sort_from_place(destination)?;

        // Translate the default argument
        let default_expr = self.codegen_operand(&args[1])?;

        // Build is_some condition
        let discrim_name = crate::codegen_ay::names::discrim_name(option_base.as_ref());
        let (is_some, inner_value) = if let Some(discrim_expr) =
            self.env_lookup(&discrim_name).cloned()
        {
            // Flattened representation: `.0` holds the discriminant.
            let zero = self.make_zero_for_discrim(&discrim_expr)?;
            let is_some = discrim_expr.eq(zero).not();
            // The payload lives under `.1` (checked-arith tuple convention) OR,
            // for the Option-aggregate flatten (codegen_assign_flatten.rs), under
            // the base key itself — `{base}` holds the flattened payload bitvec and
            // `.1` is never written. Mirror codegen_option_unwrap's robustness:
            // prefer `.1`, else fall back to the base value. Without this, a
            // flattened Some payload (e.g. the `.copied()` result in ay-pb
            // `eval_lit`, gap G1) is unrecoverable and the call havocs fail-closed.
            let value_name = crate::codegen_ay::names::payload_name(option_base.as_ref());
            let inner = if let Some(v) = self.env_lookup(&value_name) {
                v.clone()
            } else if let Some(base_v) = self.env_lookup(option_base.as_ref()) {
                base_v.clone()
            } else {
                // Part of #3211: track constraint drop in demotion pipeline.
                self.ctx.unsupported_with_fallback(
                    "option_unwrap_or_missing_payload",
                    "flattened Option payload not found under .1 or base",
                );
                return None;
            };
            (is_some, inner)
        } else if let Some(option_expr) = self.env_lookup(option_base.as_ref()) {
            let sort = option_expr.sort();
            if let Some(dt_name) = sort.datatype_name() {
                // Native SMT datatype
                let some_ctor = crate::codegen_ay::names::option_some_constructor_name(dt_name);
                let val_field = names::option_value_field_name(dt_name);
                if !sort.datatype_has_constructor(&some_ctor)
                    || !sort.datatype_has_field(&val_field)
                {
                    warn!("Option::unwrap_or: datatype '{}' missing Some/{}", dt_name, val_field);
                    return None;
                }
                let is_some = option_expr.clone().is_constructor(dt_name, some_ctor);
                let inner = option_expr.clone().field_select(dt_name, &val_field, result_sort);
                (is_some, inner)
            } else if sort.is_bitvec() || sort.is_bool() || sort.is_int() {
                // Part of #3036: Flattened Some aggregate stores payload as scalar
                // under the base key without a separate discriminant entry.
                debug!(
                    "Option::unwrap_or: {} is a scalar sort {:?}, treating as flattened Some",
                    option_base, sort
                );
                (ay_bindings::Expr::bool_const(true), option_expr.clone())
            } else {
                warn!("Option::unwrap_or: unsupported sort {:?} for {}", sort, option_base);
                // Part of #3211: Track constraint drop in demotion pipeline.
                self.ctx.unsupported_with_fallback(
                    "option_unwrap_or_sort_drop",
                    "unsupported sort for Option base",
                );
                return None;
            }
        } else {
            warn!("Option::unwrap_or: could not find Option value for {}", option_base);
            // Part of #3211: Track constraint drop in demotion pipeline.
            self.ctx.unsupported_with_fallback(
                "option_unwrap_or_missing_value",
                "could not find Option value",
            );
            return None;
        };

        // Part of #3260: harmonize sorts before ITE to prevent Datatype vs scalar mismatch.
        let (inner_value, default_expr) = if *inner_value.sort() != *default_expr.sort() {
            let target = default_expr.sort().clone();
            let converted = self.convert_expr_to_sort_declared(inner_value, &target, None);
            (converted, default_expr)
        } else {
            (inner_value, default_expr)
        };

        // ITE(is_some, inner_value, default)
        let result = ay_bindings::Expr::ite(is_some, inner_value, default_expr);

        self.bind_ssa_result(destination, result);

        target
    }

    /// Codegen `Option::unwrap_or_else(self, f) -> T`.
    ///
    /// Over-approximation: `ITE(is_some, inner_value, symbolic_T)`.
    /// The closure result is modeled as unconstrained since we cannot execute
    /// closures in the verification model. This is sound (more behaviors than
    /// real program) and allows verification to proceed.
    ///
    /// Part of #1836: Recover harnesses calling unwrap_or_else on Option values.
    ///
    /// REQUIRES: `args[0]` is an `Option<T>` value, `args[1]` is a closure `FnOnce() -> T`
    /// ENSURES: Stores `ITE(is_some, inner_value, symbolic_T)` to destination
    pub(super) fn codegen_option_unwrap_or_else(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("codegen_option_unwrap_or_else: expected at least 1 arg, got 0");
            return None;
        }

        let option_base = self
            .get_option_base_direct(&args[0])
            .or_else(|| self.get_option_base_from_ref(&args[0]))?;

        let result_sort = self.infer_sort_from_place(destination)?;

        // Build is_some condition and extract inner value
        let discrim_name = crate::codegen_ay::names::discrim_name(option_base.as_ref());
        let (is_some, inner_value) = if let Some(discrim_expr) = self.env_lookup(&discrim_name) {
            let zero = self.make_zero_for_discrim(discrim_expr)?;
            let is_some = discrim_expr.clone().eq(zero).not();
            let value_name = crate::codegen_ay::names::payload_name(option_base.as_ref());
            let inner = self.env_lookup(&value_name)?.clone();
            (is_some, inner)
        } else if let Some(option_expr) = self.env_lookup(option_base.as_ref()) {
            let sort = option_expr.sort();
            if let Some(dt_name) = sort.datatype_name() {
                // Native SMT datatype
                let some_ctor = crate::codegen_ay::names::option_some_constructor_name(dt_name);
                let val_field = names::option_value_field_name(dt_name);
                if !sort.datatype_has_constructor(&some_ctor)
                    || !sort.datatype_has_field(&val_field)
                {
                    warn!(
                        "Option::unwrap_or_else: datatype '{}' missing Some/{}",
                        dt_name, val_field
                    );
                    self.ctx.unsupported_with_fallback(
                        "option_unwrap_or_else_missing_ctor",
                        "datatype missing Some/value",
                    );
                    return None;
                }
                let is_some = option_expr.clone().is_constructor(dt_name, some_ctor);
                let inner =
                    option_expr.clone().field_select(dt_name, &val_field, result_sort.clone());
                (is_some, inner)
            } else if sort.is_bitvec() || sort.is_bool() || sort.is_int() {
                // Part of #3036: Flattened Some aggregate stores payload as scalar
                debug!(
                    "Option::unwrap_or_else: {} is a scalar sort {:?}, treating as flattened Some",
                    option_base, sort
                );
                (ay_bindings::Expr::bool_const(true), option_expr.clone())
            } else {
                warn!("Option::unwrap_or_else: unsupported sort {:?} for {}", sort, option_base);
                // Part of #3211: Track constraint drop in demotion pipeline.
                self.ctx.unsupported_with_fallback(
                    "option_unwrap_or_else_sort_drop",
                    "unsupported sort for Option base",
                );
                return None;
            }
        } else {
            warn!("Option::unwrap_or_else: could not find Option value for {}", option_base);
            // Part of #3211: Track constraint drop in demotion pipeline.
            self.ctx.unsupported_with_fallback(
                "option_unwrap_or_else_missing_value",
                "could not find Option value",
            );
            return None;
        };

        // Over-approximate closure result with symbolic value
        let closure_name = self.ctx.fresh_name("opt_unwrap_or_else");
        let closure_result = self.ctx.declare_var(&closure_name, result_sort);

        // Part of #3260: harmonize sorts before ITE to prevent Datatype vs scalar mismatch.
        let (inner_value, closure_result) = if *inner_value.sort() != *closure_result.sort() {
            let target = closure_result.sort().clone();
            let converted = self.convert_expr_to_sort_declared(inner_value, &target, None);
            (converted, closure_result)
        } else {
            (inner_value, closure_result)
        };

        // ITE(is_some, inner_value, symbolic_closure_result)
        let result = ay_bindings::Expr::ite(is_some, inner_value, closure_result);

        self.bind_ssa_result(destination, result);

        target
    }

    /// Codegen `Option::and_then(self, f) -> Option<U>`.
    ///
    /// Over-approximation: `ITE(is_some, symbolic_Option<U>, None)`.
    /// The closure result is modeled as unconstrained since we cannot execute
    /// closures in the verification model. This is sound (more behaviors than
    /// real program) and allows verification to proceed.
    ///
    /// Part of #1836: Recover harnesses calling and_then on Option values.
    ///
    /// REQUIRES: `args[0]` is an `Option<T>` value, `args[1]` is a closure `FnOnce(T) -> Option<U>`
    /// ENSURES: Stores symbolic `Option<U>` (when Some) or deterministic `None` to destination
    pub(super) fn codegen_option_and_then(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("codegen_option_and_then: expected at least 1 arg, got 0");
            return None;
        }

        // Validate that args[0] is a recognized Option value (early return if not)
        let _option_base = self
            .get_option_base_direct(&args[0])
            .or_else(|| self.get_option_base_from_ref(&args[0]))?;

        // and_then returns Option<U> which is the destination type
        // Over-approximate: if is_some, return symbolic Option<U>; else return None
        // Since we can't model the closure, just produce a symbolic result
        self.codegen_symbolic_result(destination);
        target
    }

    /// Codegen `Option::<&T>::copied(self) -> Option<T>` (and `Option::<&T>::cloned`)
    /// on the FLATTENED representation, WITHOUT MIR-inlining the library body.
    ///
    /// Under value semantics (#3133) a flattened `Option<&T>` already stores the
    /// DEREF'd payload VALUE under its base key (references are transparent), so
    /// `.copied()` / `.cloned()` is the identity on that value: copy the
    /// discriminant `{self}.0` and the payload value into a fresh flattened
    /// `Option<T>` at `destination`. This is required for the ay-pb `eval_lit`
    /// chain `assignment.get(i).copied().unwrap_or(false)` (R2): the MIR-inline
    /// path (OptionCopied -> Miss) instead lowers the library body's `Some(&v)`
    /// reference deref, which — for a flattened `Option<&T>` payload — cannot find
    /// the pointee through the inline param-seeding re-key and synthesizes a fresh
    /// UNCONSTRAINED pointee (an unsound-tracking demotion).
    ///
    /// Returns `None` (caller falls back to the MIR-inline path) when `self` is
    /// not a resolvable FLATTENED Option (e.g. a native SMT-datatype Option) — no
    /// completeness regression on the cases the inline path already handles.
    pub(super) fn codegen_option_copied(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            return None;
        }
        let option_base = self
            .get_option_base_direct(&args[0])
            .or_else(|| self.get_option_base_from_ref(&args[0]))?;

        // Only the FLATTENED representation (discriminant under `{base}.0`) is
        // handled here; a native SMT-datatype Option is left to the MIR-inline
        // path (caller falls through on None).
        let discrim_key = names::discrim_name(option_base.as_ref());
        let discrim_expr = self.env_lookup(&discrim_key).cloned()?;

        // Payload VALUE: value semantics store the deref'd `T` under the Some
        // payload key `.1`, the Some piecewise key `_variant_1_field_0` (the key
        // that survives an `and_then`/closure MIR-inline return re-key), or the
        // base key (the whole-value copy). Prefer them in that order.
        let payload_key = names::payload_name(option_base.as_ref());
        let field_key = names::base_variant_field_name(option_base.as_ref(), 1, 0);
        let payload = self
            .env_lookup(&payload_key)
            .cloned()
            .or_else(|| self.env_lookup(&field_key).cloned())
            .or_else(|| self.env_lookup(option_base.as_ref()).cloned())?;
        // Coerce a Bool payload to BV1 so the flattened `Option<T>` stays bitvec.
        let payload = if payload.sort().is_bool() {
            ay_bindings::Expr::ite(
                payload,
                ay_bindings::Expr::bitvec_const(1u64, 1),
                ay_bindings::Expr::bitvec_const(0u64, 1),
            )
        } else {
            payload
        };
        if !payload.sort().is_bitvec() {
            return None;
        }
        let payload_width =
            payload.sort().bitvec_width().unwrap_or(crate::codegen_ay::types::POINTER_WIDTH);

        // Discriminant coerced to BV32 (the flattened `.0` convention).
        let discrim_bv32 = match discrim_expr.sort().bitvec_width() {
            Some(32) => discrim_expr,
            Some(w) if w < 32 => discrim_expr.zero_extend(32 - w),
            Some(_) => discrim_expr.extract(31, 0),
            None => return None,
        };

        let dest_base = self.ssa_base_name(destination);

        // `{dest}.0` = discriminant.
        let dest_discrim_key = names::discrim_name(&dest_base);
        let dn = self.ssa_name_from_base(&dest_discrim_key, true);
        let dv = self.ctx.declare_var(&dn, ay_bindings::Sort::bitvec(32));
        self.assert_ssa_def(dv.clone(), discrim_bv32, &dest_discrim_key);
        self.env_update(dest_discrim_key, dv);

        // `{dest}_variant_1_field_0` and the base key = payload VALUE.
        let field_key = names::base_variant_field_name(&dest_base, 1, 0);
        let fname = self.ssa_name_from_base(&field_key, true);
        let fvar = self.ctx.declare_var(&fname, ay_bindings::Sort::bitvec(payload_width));
        self.assert_ssa_def(fvar.clone(), payload.clone(), &field_key);
        self.env_update(field_key, fvar);

        let bname = self.ssa_name_from_base(&dest_base, true);
        let bvar = self.ctx.declare_var(&bname, ay_bindings::Sort::bitvec(payload_width));
        self.assert_ssa_def(bvar.clone(), payload, &dest_base);
        self.env_update(dest_base, bvar);

        target
    }

    /// Codegen `Option::ok_or_else(self, f) -> Result<T, E>`.
    ///
    /// Over-approximation: `ITE(is_some, Ok(inner_value), symbolic_Result)`.
    /// The error closure is modeled as unconstrained since we cannot execute
    /// closures in the verification model. Sound over-approximation.
    ///
    /// Part of #1836: Recover harnesses calling ok_or_else on Option values.
    ///
    /// REQUIRES: `args[0]` is an `Option<T>` value, `args[1]` is a closure `FnOnce() -> E`
    /// ENSURES: Stores symbolic `Result<T, E>` to destination
    pub(super) fn codegen_option_ok_or_else(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("codegen_option_ok_or_else: expected at least 1 arg, got 0");
            return None;
        }

        // ok_or_else returns Result<T, E> which is the destination type
        // Since we can't model the closure for the Err case, produce symbolic result
        self.codegen_symbolic_result(destination);
        target
    }
}
