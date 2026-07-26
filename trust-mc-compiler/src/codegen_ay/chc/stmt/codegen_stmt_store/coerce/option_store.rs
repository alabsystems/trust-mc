// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Option-like datatype coercion for array store values.

use ay_bindings::{DatatypeSort, Expr, Sort};

use crate::codegen_ay::types::{
    SignExtension, coerce_bitvec_width_safe, flatten_datatype_to_bitvec,
};
use trust_mc_codegen_types::types::{
    coerce_datatype_structural, flattenable_datatype_sort_width, unflatten_bitvec_to_datatype,
};

pub(super) fn coerce_option_like_store_value(
    value: &Expr,
    target_sort: &Sort,
    signed: bool,
) -> Option<Expr> {
    let target_dt = target_sort.datatype_sort()?;
    let (target_empty, target_payload) = option_like_constructors(&target_dt)?;
    if let Some(coerced) = coerce_niche_bitvec_to_option_like_store_value(
        value,
        target_sort,
        &target_dt,
        target_empty,
        target_payload,
        signed,
    ) {
        return Some(coerced);
    }

    let src_dt = value.sort().datatype_sort()?;
    let (_src_empty, src_payload) = option_like_constructors(&src_dt)?;
    if src_payload.fields.len() != 1 || target_payload.fields.len() != 1 {
        return None;
    }

    let src_field = src_payload.fields.first()?;
    let target_field = target_payload.fields.first()?;
    let src_payload_expr =
        value.clone().field_select(&src_dt.name, &src_field.name, src_field.sort.clone());
    let target_payload_expr =
        coerce_store_payload_to_sort(src_payload_expr, &target_field.sort, signed).or_else(
            || {
                is_zero_width_chc_payload_sort(&target_field.sort)
                    .then(|| default_expr_for_store_payload_sort(&target_field.sort))
                    .flatten()
            },
        )?;

    let target_some = Expr::datatype_constructor(
        &target_dt.name,
        &target_payload.name,
        vec![target_payload_expr],
        target_sort.clone(),
    );
    let target_none = Expr::datatype_constructor(
        &target_dt.name,
        &target_empty.name,
        vec![],
        target_sort.clone(),
    );
    let is_some = value.clone().is_constructor(&src_dt.name, &src_payload.name);
    Some(Expr::ite(is_some, target_some, target_none))
}

fn coerce_niche_bitvec_to_option_like_store_value(
    value: &Expr,
    target_sort: &Sort,
    target_dt: &DatatypeSort,
    target_empty: &ay_bindings::sort::DatatypeConstructor,
    target_payload: &ay_bindings::sort::DatatypeConstructor,
    signed: bool,
) -> Option<Expr> {
    if value.sort().datatype_sort().is_some()
        || target_payload.fields.len() != 1
        || !is_named_option_like(target_empty, target_payload)
    {
        return None;
    }

    let target_field = target_payload.fields.first()?;
    if !target_field.sort.is_bitvec() {
        return None;
    }

    let target_payload_expr =
        coerce_store_payload_to_sort(value.clone(), &target_field.sort, signed)?;
    let target_width = target_payload_expr.sort().bitvec_width()?;
    let target_some = Expr::datatype_constructor(
        &target_dt.name,
        &target_payload.name,
        vec![target_payload_expr.clone()],
        target_sort.clone(),
    );
    let target_none = Expr::datatype_constructor(
        &target_dt.name,
        &target_empty.name,
        vec![],
        target_sort.clone(),
    );
    let is_some = target_payload_expr.ne(Expr::bitvec_const(0u64, target_width));
    Some(Expr::ite(is_some, target_some, target_none))
}

fn option_like_constructors(
    dt: &DatatypeSort,
) -> Option<(&ay_bindings::sort::DatatypeConstructor, &ay_bindings::sort::DatatypeConstructor)> {
    if dt.constructors.len() != 2 {
        return None;
    }
    let first = dt.constructors.first()?;
    let second = dt.constructors.get(1)?;
    match (first.fields.is_empty(), second.fields.is_empty()) {
        (true, false) => Some((first, second)),
        (false, true) => Some((second, first)),
        _ => None,
    }
}

fn is_named_option_like(
    empty: &ay_bindings::sort::DatatypeConstructor,
    payload: &ay_bindings::sort::DatatypeConstructor,
) -> bool {
    empty.name.starts_with("None_") && payload.name.starts_with("Some_")
}

fn coerce_store_payload_to_sort(value: Expr, target_sort: &Sort, signed: bool) -> Option<Expr> {
    let source_sort = value.sort().clone();
    if source_sort == *target_sort {
        return Some(value);
    }

    if source_sort.is_bitvec()
        && target_sort.is_bitvec()
        && let Some(target_width) = target_sort.bitvec_width()
    {
        return Some(coerce_bitvec_width_safe(
            value,
            target_width,
            SignExtension::for_signedness(signed),
        ));
    }

    if source_sort.is_bool()
        && target_sort.is_bitvec()
        && let Some(target_width) = target_sort.bitvec_width()
    {
        return Some(Expr::ite(
            value,
            Expr::bitvec_const(1u64, target_width),
            Expr::bitvec_const(0u64, target_width),
        ));
    }

    if source_sort.is_bitvec()
        && target_sort.is_bool()
        && let Some(width) = source_sort.bitvec_width()
    {
        return Some(value.ne(Expr::bitvec_const(0u64, width)));
    }

    if source_sort.is_int()
        && let Some(target_width) = target_sort.bitvec_width()
    {
        return Some(value.int2bv(target_width));
    }

    if source_sort.is_bitvec() && target_sort.is_int() {
        return Some(if signed { value.bv2int_signed() } else { value.bv2int() });
    }

    if let (Some(src_dt), Some(target_dt)) =
        (source_sort.datatype_sort(), target_sort.datatype_sort())
    {
        if let Some(coerced) = coerce_datatype_structural(
            value.clone(),
            &src_dt,
            &target_dt,
            target_sort.clone(),
            SignExtension::for_signedness(signed),
        ) {
            return Some(coerced);
        }
    }

    if source_sort.is_datatype()
        && target_sort.is_bitvec()
        && let Some(target_width) = target_sort.bitvec_width()
    {
        return flatten_datatype_to_bitvec(&value, target_width);
    }

    if source_sort.is_bitvec() && target_sort.is_datatype() {
        return unflatten_bitvec_to_datatype(&value, target_sort);
    }

    None
}

fn is_zero_width_chc_payload_sort(sort: &Sort) -> bool {
    sort.is_array()
        || sort.datatype_sort().is_some_and(|_| flattenable_datatype_sort_width(sort) == Some(0))
}

fn default_expr_for_store_payload_sort(sort: &Sort) -> Option<Expr> {
    if let Some(width) = sort.bitvec_width() {
        return Some(Expr::bitvec_const(0u64, width));
    }
    if sort.is_bool() {
        return Some(Expr::bool_const(false));
    }
    if sort.is_int() {
        return Some(Expr::int_const(0));
    }
    if let Some(arr) = sort.array_sort() {
        let default_elem = default_expr_for_store_payload_sort(&arr.element_sort)?;
        return Some(Expr::const_array(arr.index_sort.clone(), default_elem));
    }
    let dt = sort.datatype_sort()?;
    let cons = dt.constructors.first()?;
    if dt.constructors.len() == 1 {
        let fields = cons
            .fields
            .iter()
            .map(|field| default_expr_for_store_payload_sort(&field.sort))
            .collect::<Option<Vec<_>>>()?;
        return Some(Expr::datatype_constructor(&dt.name, &cons.name, fields, sort.clone()));
    }
    None
}
