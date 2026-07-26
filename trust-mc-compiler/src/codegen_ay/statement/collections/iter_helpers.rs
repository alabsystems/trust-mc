// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Iterator helper methods for AY codegen.
//!
//! Extracted from iter.rs — Part of #2155.
//!
//! Contains iterator construction, field extraction, and utility methods:
//! - `make_map_iterator`: Create Map adapter wrapper
//! - `make_filter_iterator`: Create Filter adapter wrapper
//! - `advance_wrapped_iterator`: Advance inner iterator of wrapper
//! - `update_wrapped_iterator`: Update wrapper with new inner state
//! - `set_iter_field_select`: Extract field from set iterator
//! - `hashmap_iter_field_select`: Extract field from HashMap iterator
//! - `extract_option_value`: Extract value from Option<V>
//! - `make_tuple`: Create tuple expression
//! - `infer_iter_vec_sort`: Infer Vec sort from VecIntoIter
//! - `datatype_field_info`: Extract datatype field metadata
//! - `vec_iter_next_from_expr`: Advance VecIntoIter and return result
//! - `option_sort_for_value`: Resolve Option sort for value
//! - `codegen_iter_collect_vec`: Collect iterator into Vec
//! - `codegen_iter_flatten_from_vec_iter`: Flatten nested Vec iterator
//! - `make_vec_from_parts`: Construct Vec from parts
//! - `make_vec_into_iter`: Wrap Vec in VecIntoIter
//! - `make_flatten_iter`: Wrap iterator in Flatten
//! - `make_option_is_some`: Check if Option is Some
//! - `make_set_contains`: Check set membership

use crate::codegen_ay::names::{self, struct_sort};
use crate::codegen_ay::types::{CtorFieldExt, POINTER_WIDTH, bool_sort, ptr_sort};
use ay_bindings::{Expr, Sort};
use tracing::{error, warn};

use super::super::StatementCodegen;
use super::iter::BMC_ITERATOR_UNSOUND_SKIP_COUNT;
use std::sync::atomic::Ordering;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    #[must_use]
    fn prefixed_sort_name(prefix: &str, sort: &Sort) -> String {
        let short = names::sort_short_name(sort);
        let mut name = String::with_capacity(prefix.len() + 1 + short.len());
        name.push_str(prefix);
        name.push('_');
        name.push_str(&short);
        name
    }

    #[must_use]
    fn field_fallback_name(prefix: &str, field_name: &str) -> String {
        const SUFFIX: &str = "_fallback";
        let mut name = String::with_capacity(prefix.len() + field_name.len() + SUFFIX.len());
        name.push_str(prefix);
        name.push_str(field_name);
        name.push_str(SUFFIX);
        name
    }

    #[must_use]
    fn tuple2_sort_name(first: &Sort, second: &Sort) -> String {
        let first_short = names::sort_short_name(first);
        let second_short = names::sort_short_name(second);
        let mut name =
            String::with_capacity("Tuple2_".len() + first_short.len() + 1 + second_short.len());
        name.push_str("Tuple2_");
        name.push_str(&first_short);
        name.push('_');
        name.push_str(&second_short);
        name
    }

    /// Create a Map iterator wrapper around an inner iterator (Part of #1751).
    #[must_use]
    pub(in crate::codegen_ay::statement) fn make_map_iterator(&mut self, inner_iter: Expr) -> Expr {
        let inner_sort = inner_iter.sort().clone();
        let map_sort_name = Self::prefixed_sort_name("Map", &inner_sort);
        let map_sort = struct_sort(map_sort_name.as_str(), [("fld_iter", inner_sort)]);
        let ctor_name = crate::codegen_ay::names::resolve_ctor_name(&map_sort, &map_sort_name);
        Expr::datatype_constructor(map_sort_name, ctor_name, vec![inner_iter], map_sort)
    }

    /// Create a Filter iterator wrapper around an inner iterator (Part of #1751).
    #[must_use]
    pub(in crate::codegen_ay::statement) fn make_filter_iterator(
        &mut self,
        inner_iter: Expr,
    ) -> Expr {
        let inner_sort = inner_iter.sort().clone();
        let filter_sort_name = Self::prefixed_sort_name("Filter", &inner_sort);
        let filter_sort = struct_sort(filter_sort_name.as_str(), [("fld_iter", inner_sort)]);
        let ctor_name =
            crate::codegen_ay::names::resolve_ctor_name(&filter_sort, &filter_sort_name);
        Expr::datatype_constructor(filter_sort_name, ctor_name, vec![inner_iter], filter_sort)
    }

    /// Advance the wrapped inner iterator and return (new_inner, result) (Part of #1751).
    #[must_use]
    pub(in crate::codegen_ay::statement) fn advance_wrapped_iterator(
        &mut self,
        wrapper: &Expr,
        field_name: &str,
    ) -> Option<(Expr, Expr)> {
        let inner = crate::codegen_ay::types::datatype_field_select_by_name(
            wrapper.clone(),
            0,
            field_name,
        )?;

        // Try to advance the inner iterator using vec_iter_next_from_expr
        self.vec_iter_next_from_expr(&inner, None)
    }

    /// Update a wrapped iterator with new inner state (Part of #1751).
    #[must_use]
    pub(in crate::codegen_ay::statement) fn update_wrapped_iterator(
        &self,
        wrapper: &Expr,
        new_inner: Expr,
    ) -> Expr {
        let wrapper_dt = wrapper.sort().datatype_sort().and_then(|dt| {
            dt.constructors.first().map(|ctor| (dt.name.as_str(), ctor.name.as_str()))
        });
        let (dt_name, ctor_name) = wrapper_dt.unwrap_or(("Wrapper", "Wrapper_mk"));

        Expr::datatype_constructor(dt_name, ctor_name, vec![new_inner], wrapper.sort().clone())
    }

    /// Extract a field from a set iterator, with fallback for unknown sorts.
    #[must_use]
    pub(in crate::codegen_ay::statement) fn set_iter_field_select(
        &mut self,
        iter: &Expr,
        dt_name: &str,
        field_name: &str,
    ) -> Expr {
        if let Some(dt) = iter.sort().datatype_sort()
            && let Some(field) = dt.constructors.first().and_then(|ctor| ctor.field(field_name))
        {
            return iter.clone().field_select(dt_name, field_name, field.sort.clone());
        }
        // Fallback: create symbolic value with appropriate sort for each field type
        let name = self.ctx.fresh_name(&Self::field_fallback_name("set_iter_", field_name));
        let fallback_sort = match field_name {
            // fld_set: Array<K, Bool> - use Array<bv64, Bool> as fallback
            "fld_set" => Sort::array(ptr_sort(), bool_sort()),
            // fld_keys: Array<usize, K> - use Array<bv64, bv64> as fallback
            "fld_keys" => Sort::array(ptr_sort(), ptr_sort()),
            // fld_pos, fld_len: usize - bitvec
            _ => ptr_sort(), // non-enum: &str
        };
        self.ctx.declare_var(&name, fallback_sort)
    }

    /// Extract a field from a HashMap iterator, with fallback for unknown sorts.
    #[must_use]
    pub(in crate::codegen_ay::statement) fn hashmap_iter_field_select(
        &mut self,
        iter: &Expr,
        dt_name: &str,
        field_name: &str,
    ) -> Expr {
        if let Some(dt) = iter.sort().datatype_sort()
            && let Some(field) = dt.constructors.first().and_then(|ctor| ctor.field(field_name))
        {
            return iter.clone().field_select(dt_name, field_name, field.sort.clone());
        }
        // Fallback: create symbolic value with appropriate sort for each field type
        // Part of #3106: fld_data + fld_present per DT-free encoding (#3057).
        let name = self.ctx.fresh_name(&Self::field_fallback_name("iter_", field_name));
        let fallback_sort = match field_name {
            // fld_data: Array<K, V> - use Array<bv64, bv64> as fallback
            "fld_data" => Sort::array(ptr_sort(), ptr_sort()),
            // fld_present: Array<K, Bool> - use Array<bv64, Bool> as fallback
            "fld_present" => Sort::array(ptr_sort(), bool_sort()),
            // fld_keys: Array<usize, K> - use Array<bv64, bv64> as fallback
            "fld_keys" => Sort::array(ptr_sort(), ptr_sort()),
            // fld_pos, fld_len: usize - bitvec
            _ => ptr_sort(), // non-enum: &str
        };
        self.ctx.declare_var(&name, fallback_sort)
    }

    /// Extract the value from an Option<V>, assuming it's Some.
    /// For symbolic analysis, returns the value field if present.
    #[must_use]
    pub(in crate::codegen_ay::statement) fn extract_option_value(
        &mut self,
        option_expr: &Expr,
    ) -> Expr {
        if let Some(dt) = option_expr.sort().datatype_sort() {
            // Find the Some constructor's value field
            if let Some(some_ctor) =
                dt.constructors.iter().find(|c| names::is_some_constructor(&c.name))
                && let Some(value_field) = some_ctor.fields.first()
            {
                return option_expr.clone().field_select(
                    &dt.name,
                    "value",
                    value_field.sort.clone(),
                );
            }
        }
        // Fallback: return symbolic value
        let name = self.ctx.fresh_name("option_value_fallback");
        self.ctx.declare_var(&name, ptr_sort())
    }

    /// Create a tuple expression from two values.
    #[must_use]
    pub(in crate::codegen_ay::statement) fn make_tuple(
        &mut self,
        first: Expr,
        second: Expr,
    ) -> Expr {
        let first_sort = first.sort().clone();
        let second_sort = second.sort().clone();
        let tuple_sort_name = Self::tuple2_sort_name(&first_sort, &second_sort);
        let tuple_sort =
            struct_sort(tuple_sort_name.as_str(), [("fld_0", first_sort), ("fld_1", second_sort)]);
        let ctor_name = crate::codegen_ay::names::resolve_ctor_name(&tuple_sort, &tuple_sort_name);
        Expr::datatype_constructor(tuple_sort_name, ctor_name, vec![first, second], tuple_sort)
    }

    /// Infer the Vec sort from a VecIntoIter expression.
    /// Returns the sort of fld_vec field.
    #[must_use]
    pub(in crate::codegen_ay::statement) fn infer_iter_vec_sort(&self, iter: &Expr) -> Sort {
        // Try to extract from datatype sort
        if let Some(dt) = iter.sort().datatype_sort() {
            for ctor in &dt.constructors {
                for field in &ctor.fields {
                    if field.name == "fld_vec" {
                        return field.sort.clone();
                    }
                }
            }
        }
        // Fallback: create a generic Vec sort
        let elem_sort = ptr_sort();
        let vec_sort_name = names::vec_sort_name(&names::sort_short_name(&elem_sort));
        let array_sort = Sort::array(ptr_sort(), elem_sort);
        struct_sort(vec_sort_name, names::vec_fields(array_sort))
    }

    /// Extract datatype field metadata from a Sort reference.
    ///
    /// Caller must clone the Sort (O(1) Arc) and pass it to anchor
    /// the `&str` lifetimes. Part of #2267: eliminates 2 String clones.
    #[must_use]
    pub(in crate::codegen_ay::statement) fn datatype_field_info<'s>(
        sort: &'s Sort,
        field_name: &str,
    ) -> Option<(&'s str, &'s str, Sort)> {
        let dt = sort.datatype_sort()?;
        let ctor = dt.constructors.first()?;
        let field = ctor.field(field_name)?;
        Some((&dt.name, &ctor.name, field.sort.clone()))
    }

    pub(in crate::codegen_ay::statement) fn vec_iter_next_from_expr(
        &mut self,
        iter: &Expr,
        expected_option_sort: Option<Sort>,
    ) -> Option<(Expr, Expr)> {
        // Part of #1920: Explicit failure for non-datatype sort
        if !iter.sort().is_datatype() {
            let count = BMC_ITERATOR_UNSOUND_SKIP_COUNT.fetch_add(1, Ordering::Relaxed) + 1;
            error!(
                "UNSOUND: vec_iter_next_from_expr has non-datatype sort {:?} (hit #{}) - forcing verification failure",
                iter.sort(),
                count
            );
            self.record_violation_guarded(Expr::bool_const(true), "iterator_sort_mismatch_unsound");
            return None;
        }
        let iter_dt = iter.sort().datatype_sort().and_then(|dt| {
            dt.constructors.first().map(|ctor| (dt.name.as_str(), ctor.name.as_str()))
        });
        let (dt_name, ctor_name) = iter_dt.unwrap_or(("VecIntoIter", "VecIntoIter_mk"));

        let vec = iter.clone().field_select(dt_name, "fld_vec", self.infer_iter_vec_sort(iter));
        let pos = iter.clone().field_select(dt_name, "fld_pos", ptr_sort());

        let len = self.vec_field_select_declared(&vec, "fld_len", ptr_sort());
        let in_bounds = pos.clone().bvult(len);
        let data = self.extract_vec_data(&vec);
        let elem = data.select(pos.clone());
        let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
        let new_pos = Expr::ite(in_bounds.clone(), pos.clone().bvadd(one), pos);

        let new_iter =
            Expr::datatype_constructor(dt_name, ctor_name, vec![vec, new_pos], iter.sort().clone());

        let option_sort = self.option_sort_for_value(elem.sort(), expected_option_sort);
        let some_elem = self.make_option_some(&option_sort, elem);
        let none_val = self.make_option_none(&option_sort);
        let result = Expr::ite(in_bounds, some_elem, none_val);
        Some((new_iter, result))
    }

    #[must_use]
    pub(in crate::codegen_ay::statement) fn option_sort_for_value(
        &self,
        value_sort: &Sort,
        expected_option_sort: Option<Sort>,
    ) -> Sort {
        match expected_option_sort {
            Some(sort) if sort.is_datatype() => sort,
            _ => self.make_option_sort(value_sort.clone()), // non-enum: Option (make_option_sort fallback)
        }
    }

    // Flatten/collect operations moved to iter_flatten.rs (Part of #2246)

    /// Create an `is_some` check for an Option expression (Part of #1751).
    ///
    /// For SMT Option datatypes, uses the `is_constructor` tester.
    /// Returns `true` if the option is `Some`, `false` if `None`.
    #[must_use]
    pub(in crate::codegen_ay::statement) fn make_option_is_some(
        &mut self,
        option_expr: &Expr,
    ) -> Expr {
        let sort = option_expr.sort();
        if let Some(dt_name) = sort.datatype_name() {
            let some_ctor = crate::codegen_ay::names::option_some_constructor_name(dt_name);
            // Use the SMT datatype tester: (is Some option_expr)
            if sort.datatype_has_constructor(&some_ctor) {
                return option_expr.clone().is_constructor(dt_name, some_ctor);
            }
        }
        // Fallback: return symbolic boolean (conservative - allows both Some and None).
        warn!("make_option_is_some: unknown Option sort {:?}, returning symbolic", sort);
        let name = self.ctx.fresh_name("option_is_some_fallback");
        self.ctx.declare_var(&name, bool_sort())
    }

    /// Create an `is_true` check for a Bool set membership (Part of #1751).
    ///
    /// For sets modeled as Array<K, Bool>, the set[key] returns Bool indicating membership.
    #[must_use]
    pub(in crate::codegen_ay::statement) fn make_set_contains(
        &self,
        set: &Expr,
        key: &Expr,
    ) -> Expr {
        set.clone().select(key.clone())
    }
}
