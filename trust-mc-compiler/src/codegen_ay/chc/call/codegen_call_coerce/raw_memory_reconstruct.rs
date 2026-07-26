// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Raw Rust-memory bitvector to datatype reconstruction helpers.

use ay_bindings::{Expr, Sort};

use crate::codegen_ay::types::{flattenable_datatype_sort_width, unflatten_bitvec_to_datatype};

pub(super) fn reconstruct_datatype_from_raw_memory_bits(
    value: &Expr,
    target_sort: &Sort,
) -> Option<Expr> {
    let total_width = value.sort().bitvec_width()?;
    let dt = target_sort.datatype_sort()?;

    if dt.constructors.len() == 1 {
        let cons = dt.constructors.first()?;
        if cons.fields.is_empty() {
            return Some(Expr::datatype_constructor(
                &dt.name,
                &cons.name,
                vec![],
                target_sort.clone(),
            ));
        }

        let field_widths = raw_memory_field_widths(cons, total_width)?;
        let field_total: u32 = field_widths.iter().sum();
        if field_total == 0 || field_total > total_width {
            return None;
        }

        // Keep parity with unflatten_bitvec_to_datatype: meaningful field data
        // occupies the high bits; any trailing padding is in low bits.
        let field_data = if total_width == field_total {
            value.clone()
        } else {
            value.clone().extract(total_width - 1, total_width - field_total)
        };

        let mut remaining = field_total;
        let mut field_exprs = Vec::with_capacity(cons.fields.len());
        for (field, width) in cons.fields.iter().zip(field_widths.iter().copied()) {
            if width == 0 {
                field_exprs.push(canonical_zero_width_value(&field.sort)?);
                continue;
            }
            remaining -= width;
            let field_bits = field_data.clone().extract(remaining + width - 1, remaining);
            field_exprs.push(rebuild_raw_memory_expr_from_bits(field_bits, &field.sort)?);
        }

        return Some(Expr::datatype_constructor(
            &dt.name,
            &cons.name,
            field_exprs,
            target_sort.clone(),
        ));
    }

    reconstruct_tag_free_option_from_raw_bits(value, target_sort, dt)
}

fn rebuild_raw_memory_expr_from_bits(bits: Expr, target_sort: &Sort) -> Option<Expr> {
    if let Some(target_width) = target_sort.bitvec_width() {
        let bits_width = bits.sort().bitvec_width()?;
        return Some(if bits_width == target_width {
            bits
        } else if bits_width > target_width {
            bits.extract(target_width - 1, 0)
        } else {
            bits.zero_extend(target_width - bits_width)
        });
    }

    if target_sort.is_bool() {
        let bits_width = bits.sort().bitvec_width()?;
        return Some(bits.ne(Expr::bitvec_const(0u64, bits_width)));
    }

    if let Some(rebuilt) = unflatten_bitvec_to_datatype(&bits, target_sort) {
        return Some(rebuilt);
    }
    reconstruct_datatype_from_raw_memory_bits(&bits, target_sort)
}

fn reconstruct_tag_free_option_from_raw_bits(
    value: &Expr,
    target_sort: &Sort,
    dt: &ay_bindings::DatatypeSort,
) -> Option<Expr> {
    let (empty_idx, payload_idx) = option_like_constructor_indices(dt)?;
    let empty_cons = dt.constructors.get(empty_idx)?;
    let payload_cons = dt.constructors.get(payload_idx)?;
    let total_width = value.sort().bitvec_width()?;
    let payload_widths = raw_memory_field_widths(payload_cons, total_width)?;
    let payload_width: u32 = payload_widths.iter().sum();
    if payload_width == 0 || payload_width > total_width {
        return None;
    }

    let payload_bits = if payload_width == total_width {
        value.clone()
    } else {
        value.clone().extract(payload_width - 1, 0)
    };

    let mut remaining = payload_width;
    let mut payload_fields = Vec::with_capacity(payload_cons.fields.len());
    for (field, width) in payload_cons.fields.iter().zip(payload_widths.iter().copied()) {
        if width == 0 {
            payload_fields.push(canonical_zero_width_value(&field.sort)?);
            continue;
        }
        remaining -= width;
        let field_bits = payload_bits.clone().extract(remaining + width - 1, remaining);
        payload_fields.push(rebuild_raw_memory_expr_from_bits(field_bits, &field.sort)?);
    }

    let payload_expr = Expr::datatype_constructor(
        &dt.name,
        &payload_cons.name,
        payload_fields,
        target_sort.clone(),
    );
    let empty_expr =
        Expr::datatype_constructor(&dt.name, &empty_cons.name, vec![], target_sort.clone());
    let is_payload = value.clone().ne(Expr::bitvec_const(0u64, total_width));
    Some(Expr::ite(is_payload, payload_expr, empty_expr))
}

fn raw_memory_field_widths(
    cons: &ay_bindings::sort::DatatypeConstructor,
    available_width: u32,
) -> Option<Vec<u32>> {
    let exact = cons
        .fields
        .iter()
        .map(|field| raw_memory_exact_width(&field.sort))
        .collect::<Option<Vec<_>>>();
    if let Some(exact) = exact {
        let exact_total: u32 = exact.iter().sum();
        if exact_total <= available_width {
            return Some(exact);
        }
    }

    let relaxed = cons
        .fields
        .iter()
        .map(|field| raw_memory_relaxed_width(&field.sort))
        .collect::<Option<Vec<_>>>()?;
    let relaxed_total: u32 = relaxed.iter().sum();
    (relaxed_total <= available_width).then_some(relaxed)
}

fn raw_memory_exact_width(sort: &Sort) -> Option<u32> {
    if sort.is_bitvec() {
        return sort.bitvec_width();
    }
    if sort.is_bool() {
        return Some(8);
    }
    if sort.is_array() {
        return Some(0);
    }
    flattenable_datatype_sort_width(sort)
}

fn raw_memory_relaxed_width(sort: &Sort) -> Option<u32> {
    if sort.is_bitvec() {
        return sort.bitvec_width();
    }
    if sort.is_bool() || sort.is_array() {
        return Some(0);
    }

    let dt = sort.datatype_sort()?;
    if dt.constructors.len() == 1 {
        let cons = dt.constructors.first()?;
        let mut total = 0u32;
        for field in &cons.fields {
            total = total.checked_add(raw_memory_relaxed_width(&field.sort)?)?;
        }
        return Some(total);
    }

    let (_empty_idx, payload_idx) = option_like_constructor_indices(dt)?;
    let payload_cons = dt.constructors.get(payload_idx)?;
    let mut total = 0u32;
    for field in &payload_cons.fields {
        total = total.checked_add(raw_memory_relaxed_width(&field.sort)?)?;
    }
    Some(total)
}

fn canonical_zero_width_value(sort: &Sort) -> Option<Expr> {
    if sort.is_bool() {
        return Some(Expr::bool_const(false));
    }
    if let Some(dt) = sort.datatype_sort()
        && dt.constructors.len() == 1
    {
        let cons = dt.constructors.first()?;
        let mut fields = Vec::with_capacity(cons.fields.len());
        for field in &cons.fields {
            if raw_memory_relaxed_width(&field.sort)? != 0 {
                return None;
            }
            fields.push(canonical_zero_width_value(&field.sort)?);
        }
        return Some(Expr::datatype_constructor(&dt.name, &cons.name, fields, sort.clone()));
    }
    None
}

fn option_like_constructor_indices(dt: &ay_bindings::DatatypeSort) -> Option<(usize, usize)> {
    if dt.constructors.len() != 2 {
        return None;
    }
    let c0_empty = dt.constructors.first()?.fields.is_empty();
    let c1_empty = dt.constructors.get(1)?.fields.is_empty();
    match (c0_empty, c1_empty) {
        (true, false) => Some((0, 1)),
        (false, true) => Some((1, 0)),
        _ => None,
    }
}
