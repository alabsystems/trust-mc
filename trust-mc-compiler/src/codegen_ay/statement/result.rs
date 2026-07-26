// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Result type handling for AY codegen.
//!
//! This module implements codegen for Rust's `Result<T, E>` predicates and
//! value extraction methods: `is_ok`, `is_err`, `unwrap`, `unwrap_or`,
//! `unwrap_err`.
//!
//! Combinator methods (unwrap_or_else, map, and_then, map_err, ok, err)
//! are in `result_combinators.rs`.
//!
//! Supports both flattened representation (discriminant in `.0`) and native
//! SMT datatype representation.

use super::StatementCodegen;
use crate::codegen_ay::names;
use ay_bindings::Sort;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::{debug, warn};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen Result::is_ok(&self).
    ///
    /// REQUIRES: `args[0]` is a reference to a Result type.
    /// ENSURES: Stores bool destination true iff value is Ok.
    pub(super) fn codegen_result_is_ok(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_result_predicate(args, destination, target, "Ok", true)
    }

    /// Codegen Result::is_err(&self).
    ///
    /// REQUIRES: `args[0]` is a reference to a Result type.
    /// ENSURES: Stores bool destination true iff value is Err.
    pub(super) fn codegen_result_is_err(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        self.codegen_result_predicate(args, destination, target, "Err", false)
    }

    fn codegen_result_predicate(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        ctor: &str,
        ok_discriminant_zero: bool,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            return None;
        }

        let result_base = self.get_result_base_from_ref(&args[0])?;
        let discrim_name = crate::codegen_ay::names::discrim_name(result_base.as_ref());

        // Part of #2267: static lowercase — ctor is always "Ok" or "Err".
        let ctor_lower = Self::ctor_lowercase(ctor);

        let predicate_expr = if let Some(discrim_expr) = self.env_lookup(&discrim_name) {
            let zero = self.make_zero_for_discrim(discrim_expr)?;
            if ok_discriminant_zero {
                discrim_expr.clone().eq(zero)
            } else {
                discrim_expr.clone().eq(zero).not()
            }
        } else if let Some(result_expr) = self.env_lookup(result_base.as_ref()) {
            let sort = result_expr.sort();
            let Some(dt_name) = sort.datatype_name() else {
                warn!("Result::{}: {} is not a datatype, sort={:?}", ctor_lower, result_base, sort);
                return None;
            };
            // Part of #2631: Use scoped constructor name to match datatype declaration.
            let scoped_ctor = Self::find_result_constructor(sort, ctor, dt_name)?;
            debug!(
                "AY codegen: Result::{} using native datatype '{}' constructor '{}' for {}",
                ctor_lower, dt_name, scoped_ctor, result_base
            );
            result_expr.clone().is_constructor(dt_name, scoped_ctor)
        } else {
            warn!(
                "Result::{}: could not find discriminant ({}.0) or Result value ({})",
                ctor_lower, result_base, result_base
            );
            return None;
        };

        self.bind_ssa_result(destination, predicate_expr);
        target
    }

    /// Codegen `Result::unwrap_or(self, default) -> T`.
    ///
    /// Returns the Ok value if Ok, otherwise returns the default.
    /// Semantics: `if is_ok(self) { ok_value } else { default }`
    ///
    /// Part of #1836: Recover harnesses calling unwrap_or on Result values.
    ///
    /// REQUIRES: `args[0]` is a `Result<T, E>` value, `args[1]` is the default `T`
    /// ENSURES: Stores `ITE(is_ok, ok_value, default)` to destination
    pub(super) fn codegen_result_unwrap_or(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            warn!("codegen_result_unwrap_or: expected 2 args, got {}", args.len());
            return None;
        }

        let result_base = self
            .get_result_base_direct(&args[0])
            .or_else(|| self.get_result_base_from_ref(&args[0]))?;

        let result_sort = self.infer_sort_from_place(destination)?;

        // Translate the default argument
        let default_expr = self.codegen_operand(&args[1])?;

        // Build is_ok condition and extract Ok value
        let discrim_name = crate::codegen_ay::names::discrim_name(result_base.as_ref());
        let (is_ok, ok_value) = if let Some(discrim_expr) = self.env_lookup(&discrim_name) {
            // Flattened representation: .0 = discriminant, .1 = value
            let zero = self.make_zero_for_discrim(discrim_expr)?;
            let is_ok = discrim_expr.clone().eq(zero);
            let value_name = crate::codegen_ay::names::payload_name(result_base.as_ref());
            let inner = self.env_lookup(&value_name)?.clone();
            (is_ok, inner)
        } else if let Some(result_expr) = self.env_lookup(result_base.as_ref()) {
            // Native SMT datatype — clone needed for consuming methods.
            let sort = result_expr.sort();
            let dt_name = sort.datatype_name()?;
            // Part of #2631: scoped constructor name. Select the Ok payload by the Ok
            // constructor's ACTUAL first-field selector rather than a hardcoded
            // "value"/"ok": the general enum-sort path (sort_inference_adt.rs) names the
            // Ok payload via `variant_field_name`, so the hardcoded names miss and
            // unwrap_or drops to INCONCLUSIVE. fields[0] is the Ok payload in every
            // representation (the canonical Result path's "value" is also fields[0]), so
            // this is strictly more robust and stays correct there.
            let dt = sort.datatype_sort()?;
            let ok_ctor_struct =
                dt.constructors.iter().find(|c| names::is_ok_constructor(&c.name))?;
            let ok_ctor = ok_ctor_struct.name.as_str();
            let Some(ok_field) = ok_ctor_struct.fields.first() else {
                warn!(
                    "Result::unwrap_or: Ok constructor '{}' of '{}' has no payload field",
                    ok_ctor, dt_name
                );
                // Part of #3211: Track constraint drop in demotion pipeline.
                self.ctx.unsupported_with_fallback(
                    "result_unwrap_or_missing_field",
                    "Ok constructor has no payload field",
                );
                return None;
            };
            let field_name = ok_field.name.clone();
            let is_ok = result_expr.clone().is_constructor(dt_name, ok_ctor);
            let ok_value = result_expr.clone().field_select(dt_name, &field_name, result_sort);
            (is_ok, ok_value)
        } else {
            warn!("Result::unwrap_or: could not find Result value for {}", result_base);
            // Part of #3211: Track constraint drop in demotion pipeline.
            self.ctx.unsupported_with_fallback(
                "result_unwrap_or_missing_value",
                "could not find Result value",
            );
            return None;
        };

        // ITE(is_ok, ok_value, default)
        let result = ay_bindings::Expr::ite(is_ok, ok_value, default_expr);

        self.bind_ssa_result(destination, result);
        target
    }

    /// Codegen `Result::unwrap(self) -> T`.
    ///
    /// Extracts the Ok value from `Result<T, E>`. Supports both:
    /// - Flattened representation: value in field `.1` (discriminant 0 = Ok)
    /// - Native SMT datatype: use field_select with "value"/"ok" selector
    ///
    /// Note: unwrap on Err is UB/panic in Rust - we just extract the Ok value
    /// since verification typically uses assume(is_ok()) first.
    ///
    /// Part of #1836: Recover harnesses calling unwrap on Result values.
    ///
    /// REQUIRES: `args[0]` is a `Result<T, E>` value (by value)
    /// ENSURES: Stores inner `T` value to destination
    pub(super) fn codegen_result_unwrap(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            return None;
        }

        let result_base = self
            .get_result_base_direct(&args[0])
            .or_else(|| self.get_result_base_from_ref(&args[0]))?;

        let result_sort = self.infer_sort_from_place(destination)?;

        // Try flattened representation first: value in field .1
        let value_name = crate::codegen_ay::names::payload_name(result_base.as_ref());
        let value_expr = if let Some(value_expr) = self.env_lookup(&value_name) {
            debug!("AY codegen: Result::unwrap using flattened representation for {}", result_base);
            value_expr.clone()
        } else if let Some(result_expr) = self.env_lookup(result_base.as_ref()) {
            // Resolve field name; field_select now consumes self, clone needed.
            let sort = result_expr.sort();
            let dt_name = sort.datatype_name()?;
            let field_name = if sort.datatype_has_field("value") {
                "value"
            } else if sort.datatype_has_field("ok") {
                "ok"
            } else {
                warn!(
                    "Result::unwrap: datatype '{}' missing value/ok field for {}",
                    dt_name, result_base
                );
                return None;
            };
            debug!(
                "AY codegen: Result::unwrap using native datatype '{}' field '{}'",
                dt_name, field_name
            );
            result_expr.clone().field_select(dt_name, field_name, result_sort)
        } else {
            warn!(
                "Result::unwrap: could not find value ({}.1) or Result value ({})",
                result_base, result_base
            );
            return None;
        };

        self.bind_ssa_result(destination, value_expr);

        target
    }

    /// Codegen `Result::unwrap_err(self) -> E`.
    ///
    /// Extracts the Err payload from a Result value.
    /// For same-sort flattened `Result<T, T>` (e.g., from `compare_exchange`),
    /// the shared payload slot is reused since T == E.
    /// For datatype-backed heterogeneous `Result<T, E>`, selects the "err" field.
    ///
    /// Part of #3587: Restore stub parity for Result::unwrap_err.
    ///
    /// REQUIRES: `args[0]` is a `Result<T, E>` value (by value)
    /// ENSURES: Stores inner `E` value to destination
    pub(super) fn codegen_result_unwrap_err(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            return None;
        }

        let result_base = self
            .get_result_base_direct(&args[0])
            .or_else(|| self.get_result_base_from_ref(&args[0]))?;

        let result_sort = self.infer_sort_from_place(destination)?;

        // Try flattened representation first: for same-sort Result<T, T>,
        // the payload at field .1 is shared between Ok and Err variants.
        let value_name = crate::codegen_ay::names::payload_name(result_base.as_ref());
        let value_expr = if let Some(value_expr) = self.env_lookup(&value_name) {
            debug!(
                "AY codegen: Result::unwrap_err using flattened representation for {}",
                result_base
            );
            value_expr.clone()
        } else if let Some(result_expr) = self.env_lookup(result_base.as_ref()) {
            // For datatype-backed Result, select the Err payload field.
            let sort = result_expr.sort();
            let dt_name = sort.datatype_name()?;
            let field_name = if sort.datatype_has_field("err") {
                "err"
            } else if sort.datatype_has_field("value") {
                // Same-sort Result uses shared "value" field for both variants
                "value"
            } else {
                warn!(
                    "Result::unwrap_err: datatype '{}' missing err/value field for {}",
                    dt_name, result_base
                );
                return None;
            };
            debug!(
                "AY codegen: Result::unwrap_err using native datatype '{}' field '{}'",
                dt_name, field_name
            );
            result_expr.clone().field_select(dt_name, field_name, result_sort)
        } else {
            warn!(
                "Result::unwrap_err: could not find value ({}.1) or Result value ({})",
                result_base, result_base
            );
            return None;
        };

        self.bind_ssa_result(destination, value_expr);

        target
    }

    /// Find the actual constructor name for a Result variant in a datatype sort.
    ///
    /// Searches for both bare (`Ok`/`Err`) and scoped (`Ok_Result_bv32`/`Err_Result_bv32`)
    /// constructor names. Returns the matching constructor name, or None with a warning
    /// if no matching constructor is found.
    ///
    /// Part of #2631: Prevents constructor-name collisions when multiple Result
    /// instantiations coexist in one SMT program.
    pub(super) fn find_result_constructor<'s>(
        sort: &'s Sort,
        bare_name: &str,
        dt_name: &str,
    ) -> Option<&'s str> {
        let is_match: fn(&str) -> bool = match bare_name {
            "Ok" => names::is_ok_constructor,
            "Err" => names::is_err_constructor,
            _ => return None, // non-enum: &str
        };
        if let Some(dt) = sort.datatype_sort() {
            for ctor in &dt.constructors {
                if is_match(&ctor.name) {
                    return Some(&ctor.name);
                }
            }
        }
        warn!(
            "Result::{}: datatype '{}' missing {} constructor",
            Self::ctor_lowercase(bare_name),
            dt_name,
            bare_name
        );
        None
    }

    /// Part of #2267: static lowercase for Result constructor names (avoids `to_lowercase()` alloc).
    pub(super) fn ctor_lowercase(ctor: &str) -> &str {
        match ctor {
            "Ok" => "ok",
            "Err" => "err",
            other => other,
        }
    }
}

// Combinator methods moved to result_combinators.rs per #4206.
