// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Constructor wrapping helpers for call-result coercion.

use ay_bindings::{Expr, Sort};

/// Wrap a value into a DT constructor when its sort matches exactly one
/// single-field constructor's payload sort.
///
/// For `Result<T, E>`: if the value has sort matching `Ok_field_0`, returns
/// `Ok(value)`. For `Option<T>`: if matching `Some_field_0`, returns `Some(value)`.
/// Returns `None` if no unique match is found (ambiguous or no match).
pub(super) fn wrap_value_into_matching_constructor(
    value: &Expr,
    dt: &ay_bindings::DatatypeSort,
    dt_sort: &Sort,
) -> Option<Expr> {
    let value_sort = value.sort();
    let mut matching_ctor = None;
    for ctor in &dt.constructors {
        if ctor.fields.len() == 1 && ctor.fields[0].sort == *value_sort {
            if matching_ctor.is_some() {
                return None;
            }
            matching_ctor = Some(ctor);
        }
    }
    let ctor = matching_ctor?;
    Some(Expr::datatype_constructor(&dt.name, &ctor.name, vec![value.clone()], dt_sort.clone()))
}
