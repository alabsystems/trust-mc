// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Core Option type handling for AY codegen.
//!
//! This module implements codegen for Rust's `Option<T>` primitive methods:
//! - `is_none`, `is_some` - discriminant checking
//! - `unwrap`, `expect` - value extraction
//!
//! Compound methods (`unwrap_or`, `unwrap_or_else`, `and_then`, `ok_or_else`,
//! `map`) are in `option_compound.rs`.
//!
//! Supports both flattened and native SMT datatype representations.
//! Shared helpers are in `option_helpers.rs`.

use super::StatementCodegen;
use crate::codegen_ay::names;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::{debug, warn};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen Option::is_none(&self).
    ///
    /// Supports both:
    /// - Flattened representation: discriminant in field `.0` (from checked_arith)
    /// - Native SMT datatype: `(declare-datatype Option ...)` (from ADT support)
    ///
    /// REQUIRES: `args[0]` is a reference to an Option type
    /// ENSURES: Stores boolean (discriminant == 0) to destination
    /// ENSURES: Returns target on success, None if Option layout not found
    pub(super) fn codegen_option_is_none(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Contract enforcement (#695): args[0] must be an Option reference
        debug_assert!(!args.is_empty(), "codegen_option_is_none: REQUIRES args.len() > 0");
        if args.is_empty() {
            return None;
        }

        let option_base = self.get_option_base_from_ref(&args[0])?;

        // Try flattened representation first: look up discriminant in field .0
        let discrim_name = crate::codegen_ay::names::discrim_name(option_base.as_ref());
        let is_none_result = if let Some(discrim_expr) = self.env_lookup(&discrim_name) {
            // Flattened: discriminant 0 = None, 1 = Some
            let zero = self.make_zero_for_discrim(discrim_expr)?;
            discrim_expr.clone().eq(zero)
        } else if let Some(option_expr) = self.env_lookup(option_base.as_ref()) {
            // Native SMT datatype: use is_constructor test (#262)
            let sort = option_expr.sort();
            if let Some(dt_name) = sort.datatype_name() {
                let none_ctor = crate::codegen_ay::names::option_none_constructor_name(dt_name);
                if !sort.datatype_has_constructor(&none_ctor) {
                    warn!(
                        "Option::is_none: datatype '{}' missing constructor '{}' for {}",
                        dt_name, none_ctor, option_base
                    );
                    return None;
                }
                debug!(
                    "AY codegen: Option::is_none using native datatype '{}' for {}",
                    dt_name, option_base
                );
                option_expr.clone().is_constructor(dt_name, none_ctor)
            } else if sort.is_bitvec() || sort.is_bool() || sort.is_int() {
                // Part of #3036: Flattened Some aggregate stores payload as bitvec/scalar
                // under the base key without a separate discriminant entry. When the base
                // is a scalar, the Option was constructed as Some via the flattened aggregate
                // codegen path (codegen_assign_flatten.rs). is_none = false.
                debug!(
                    "Option::is_none: {} is a scalar sort {:?}, treating as flattened Some (is_none=false)",
                    option_base, sort
                );
                ay_bindings::Expr::bool_const(false)
            } else {
                warn!("Option::is_none: {} is not a datatype, sort={:?}", option_base, sort);
                return None;
            }
        } else {
            warn!(
                "Option::is_none: could not find discriminant ({}.0) or Option value ({})",
                option_base, option_base
            );
            return None;
        };

        self.bind_ssa_result(destination, is_none_result);

        target
    }

    /// Codegen Option::is_some(&self).
    ///
    /// Supports both:
    /// - Flattened representation: discriminant in field `.0` (from checked_arith)
    /// - Native SMT datatype: `(declare-datatype Option ...)` (from ADT support)
    ///
    /// REQUIRES: `args[0]` is a reference to an Option type
    /// ENSURES: Stores boolean (discriminant != 0) to destination
    /// ENSURES: Returns target on success, None if Option layout not found
    pub(super) fn codegen_option_is_some(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Contract enforcement (#695): args[0] must be an Option reference
        debug_assert!(!args.is_empty(), "codegen_option_is_some: REQUIRES args.len() > 0");
        if args.is_empty() {
            return None;
        }

        let option_base = self.get_option_base_from_ref(&args[0])?;

        // Try flattened representation first: look up discriminant in field .0
        let discrim_name = crate::codegen_ay::names::discrim_name(option_base.as_ref());
        let is_some_result = if let Some(discrim_expr) = self.env_lookup(&discrim_name) {
            // Flattened: discriminant 0 = None, 1 = Some
            let zero = self.make_zero_for_discrim(discrim_expr)?;
            discrim_expr.clone().eq(zero).not()
        } else if let Some(option_expr) = self.env_lookup(option_base.as_ref()) {
            // Native SMT datatype: use is_constructor test (#262)
            let sort = option_expr.sort();
            if let Some(dt_name) = sort.datatype_name() {
                let some_ctor = crate::codegen_ay::names::option_some_constructor_name(dt_name);
                if !sort.datatype_has_constructor(&some_ctor) {
                    warn!(
                        "Option::is_some: datatype '{}' missing constructor '{}' for {}",
                        dt_name, some_ctor, option_base
                    );
                    return None;
                }
                debug!(
                    "AY codegen: Option::is_some using native datatype '{}' for {}",
                    dt_name, option_base
                );
                option_expr.clone().is_constructor(dt_name, some_ctor)
            } else if sort.is_bitvec() || sort.is_bool() || sort.is_int() {
                // Part of #3036: Flattened Some aggregate stores payload as bitvec/scalar
                // under the base key without a separate discriminant entry. When the base
                // is a scalar, the Option was constructed as Some via the flattened aggregate
                // codegen path (codegen_assign_flatten.rs). is_some = true.
                debug!(
                    "Option::is_some: {} is a scalar sort {:?}, treating as flattened Some (is_some=true)",
                    option_base, sort
                );
                ay_bindings::Expr::bool_const(true)
            } else {
                warn!("Option::is_some: {} is not a datatype, sort={:?}", option_base, sort);
                return None;
            }
        } else {
            warn!(
                "Option::is_some: could not find discriminant ({}.0) or Option value ({})",
                option_base, option_base
            );
            return None;
        };

        self.bind_ssa_result(destination, is_some_result);

        target
    }

    /// Codegen `Option::unwrap(self) -> T`.
    ///
    /// Extracts the inner value from `Option<T>`. Supports both:
    /// - Flattened representation: value in field `.1` (from checked_arith)
    /// - Native SMT datatype: use field_select with "value" selector
    ///
    /// Note: unwrap on None is UB in Rust - we just extract the value field without
    /// runtime panic since verification typically uses assume(is_some()) first.
    ///
    /// REQUIRES: `args[0]` is an `Option<T>` value (by value, not reference)
    /// REQUIRES: Caller assumes Option is Some (unwrap on None is UB)
    /// ENSURES: Stores inner `T` value to destination
    /// ENSURES: Returns target on success, None if Option layout not found
    pub(super) fn codegen_option_unwrap(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Contract enforcement (#695): args[0] must be an Option value
        debug_assert!(!args.is_empty(), "codegen_option_unwrap: REQUIRES args.len() > 0");
        if args.is_empty() {
            return None;
        }

        // unwrap(self) takes ownership, not a reference.
        // Try direct lookup first (for owned values), then fall back to ref lookup.
        let option_base = self
            .get_option_base_direct(&args[0])
            .or_else(|| self.get_option_base_from_ref(&args[0]))?;

        // Infer the result sort from the destination place
        let result_sort = self.infer_sort_from_place(destination)?;

        // Try flattened representation first: look up value in field .1
        let value_name = crate::codegen_ay::names::payload_name(option_base.as_ref());
        let value_expr = if let Some(value_expr) = self.env_lookup(&value_name) {
            // Flattened: .1 contains the value
            debug!("AY codegen: Option::unwrap using flattened representation for {}", option_base);
            value_expr.clone()
        } else if let Some(option_expr) = self.env_lookup(option_base.as_ref()) {
            // Native SMT datatype: use field_select to extract value
            let sort = option_expr.sort();
            if let Some(dt_name) = sort.datatype_name() {
                // Part of #3945: accessor name is scoped to avoid Z3 PDR
                // "Uninterpreted 'value'" collisions across Option datatypes.
                let val_field = names::option_value_field_name(dt_name);
                if !sort.datatype_has_field(&val_field) {
                    warn!(
                        "Option::unwrap: datatype '{}' missing field '{}' for {}",
                        dt_name, val_field, option_base
                    );
                    return None;
                }
                debug!(
                    "AY codegen: Option::unwrap using native datatype '{}' for {}",
                    dt_name, option_base
                );
                option_expr.clone().field_select(dt_name, &val_field, result_sort)
            } else if sort.is_bitvec() || sort.is_bool() || sort.is_int() {
                // Part of #3036: Flattened Some aggregate stores the payload directly
                // under the base key. The base expression IS the unwrapped value.
                debug!(
                    "Option::unwrap: {} is a scalar sort {:?}, treating as flattened Some payload",
                    option_base, sort
                );
                option_expr.clone()
            } else {
                warn!("Option::unwrap: {} is not a datatype, sort={:?}", option_base, sort);
                return None;
            }
        } else {
            warn!(
                "Option::unwrap: could not find value ({}.1) or Option value ({})",
                option_base, option_base
            );
            return None;
        };

        let base_name = self.ssa_base_name(destination);
        self.bind_ssa_result(destination, value_expr);

        // Propagate ref_pointees if the unwrapped value is a reference (#441, #703).
        // When Option<&T>::unwrap returns &T, we need to track what the reference points to.
        // The Option's value field has the ref_pointees entry (from ADT aggregate creation).
        //
        // Key insight: Rust's Option layout is enum { None = 0, Some(T) = 1 }.
        // When ref_pointees tracks multi-variant enums, the key format includes the
        // variant index: `{base}_variant_{idx}_field_{n}`. For Option<&T>, the Some
        // variant (index 1) contains the reference at field 0.
        //
        // Try patterns in order of specificity:
        // - variant_1_field_0 (enum variant field - standard for Option's Some)
        // - field_0 (simple ADT without variant indexing)
        // - .1 (legacy flattened tuple representation)
        let variant_field_key =
            crate::codegen_ay::names::base_variant_field_name(option_base.as_ref(), 1, 0);
        let value_field_key = crate::codegen_ay::names::indexed_field_name(option_base.as_ref(), 0);
        let alt_field_key = crate::codegen_ay::names::payload_name(option_base.as_ref());
        if let Some(pointee) = self
            .ref_pointees
            .get(variant_field_key.as_str())
            .or_else(|| self.ref_pointees.get(value_field_key.as_str()))
            .or_else(|| self.ref_pointees.get(alt_field_key.as_str()))
            .cloned()
        {
            debug!(
                "Option::unwrap: propagating ref_pointees {} -> {} (pointee={})",
                option_base, base_name, pointee
            );
            self.ref_pointees.insert(std::sync::Arc::from(base_name), pointee);
        }

        target
    }
}
