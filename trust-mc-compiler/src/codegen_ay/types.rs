// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Type Coercion Utilities for AY Expressions.
//!
//! Thin re-export from `trust_mc-codegen-types` crate.
//! Part of #2997: split codegen_ay into subcrates.

pub(super) use trust_mc_codegen_types::types::*;

use ay_bindings::{Expr, Sort, sort::SortInner};

use crate::codegen_ay::names::{
    coroutine_direct_fields_name, coroutine_discriminant_field_name, coroutine_field_name,
};

pub(super) fn is_coroutine_root_sort(sort: &Sort) -> bool {
    let SortInner::Datatype(dt) = sort.inner() else { return false };
    let Some(root_ctor) = dt.constructors.first() else { return false };
    let Some(direct_fields) = root_ctor.field(coroutine_direct_fields_name()) else {
        return false;
    };
    let SortInner::Datatype(direct_dt) = direct_fields.sort.inner() else { return false };
    let Some(direct_ctor) = direct_dt.constructors.first() else { return false };
    direct_ctor.has_field(coroutine_discriminant_field_name())
}

/// Select the MIR field `field_idx` of a coroutine root by field NAME.
///
/// Coroutine view datatypes (`build_view_info`) order their fields by
/// increasing byte OFFSET while naming them by MIR field index
/// (`coroutine_field_{idx}`). Positional selection picks the wrong slot
/// whenever the two orders differ — silently, when the swapped fields share a
/// sort — so both the variant and direct-fields paths resolve the field by
/// its index-encoding name. A name miss returns `None` (fail-closed).
pub(super) fn coroutine_root_select(
    container: Expr,
    cons_idx: Option<usize>,
    field_idx: usize,
) -> Option<Expr> {
    let sort = container.sort().clone();
    let (root_dt_name, root_ctor) = root_constructor(&sort)?;
    let mir_field_name = coroutine_field_name(field_idx);
    if let Some(variant_idx) = cons_idx {
        // Root fields are [direct_fields, variant0, variant1, ...] in
        // construction order (build_coroutine_sort_info) — never offset-sorted
        // — so positional variant lookup is exact.
        let variant_field = root_ctor.fields.get(variant_idx + 1)?;
        let field_name = variant_field.name.clone();
        let field_sort = variant_field.sort.clone();
        let variant_view = container.clone().field_select(root_dt_name, &*field_name, field_sort);
        if let Some(selected) = datatype_field_select_by_name(variant_view, 0, &mir_field_name) {
            return Some(selected);
        }
        // Variant does not save this field — the MIR field projection refers
        // to a captured upvar in direct_fields, not a variant-local variable.
        // This happens with niche-optimized coroutines where
        // Downcast(Suspend0)+Field(0) reads a captured variable that lives in
        // direct_fields across all yield points.
    }

    let direct_fields = root_ctor.field(coroutine_direct_fields_name())?;
    let direct_sort = direct_fields.sort.clone();
    let direct_view =
        container.field_select(root_dt_name, coroutine_direct_fields_name(), direct_sort);
    datatype_field_select_by_name(direct_view, 0, &mir_field_name)
}

/// Update the MIR field `field_idx` of a coroutine root by field NAME.
///
/// Same offset-order-vs-index-name rationale as [`coroutine_root_select`]:
/// positional update would rebuild the constructor with the new value in the
/// wrong slot whenever offset order differs from MIR index order.
pub(super) fn coroutine_root_update(
    container: &Expr,
    cons_idx: Option<usize>,
    field_idx: usize,
    new_val: Expr,
) -> Option<Expr> {
    let (root_dt_name, root_ctor) = root_constructor(container.sort())?;
    let mir_field_name = coroutine_field_name(field_idx);
    if let Some(variant_idx) = cons_idx {
        let variant_field = root_ctor.fields.get(variant_idx + 1)?;
        let variant_name = variant_field.name.as_ref();
        let variant_sort = root_ctor.field_sort(variant_name)?;
        let variant_view = container.clone().field_select(root_dt_name, variant_name, variant_sort);
        if let Some(updated_variant) =
            datatype_field_update_by_name(&variant_view, 0, &mir_field_name, new_val.clone())
        {
            return datatype_field_update_by_name(container, 0, variant_name, updated_variant);
        }
        // Variant does not save this field — fall through to direct_fields
        // (same rationale as coroutine_root_select: niche-optimized coroutines
        // store captured upvars in direct_fields, not per-variant).
    }

    let direct_name = coroutine_direct_fields_name();
    let direct_sort = root_ctor.field_sort(direct_name)?;
    let direct_view = container.clone().field_select(root_dt_name, direct_name, direct_sort);
    let updated_direct = datatype_field_update_by_name(&direct_view, 0, &mir_field_name, new_val)?;
    datatype_field_update_by_name(container, 0, direct_name, updated_direct)
}

pub(super) fn coroutine_discriminant_select(root: Expr) -> Option<Expr> {
    let sort = root.sort().clone();
    let (root_dt_name, root_ctor) = root_constructor(&sort)?;
    let direct_fields = root_ctor.field(coroutine_direct_fields_name())?;
    let direct_sort = direct_fields.sort.clone();
    let direct_view = root.field_select(root_dt_name, coroutine_direct_fields_name(), direct_sort);
    datatype_field_select_by_name(direct_view, 0, coroutine_discriminant_field_name())
}

pub(super) fn coroutine_discriminant_update(root: &Expr, discr: Expr) -> Option<Expr> {
    let (root_dt_name, root_ctor) = root_constructor(root.sort())?;
    let direct_fields = root_ctor.field(coroutine_direct_fields_name())?;
    let direct_view = root.clone().field_select(
        root_dt_name,
        coroutine_direct_fields_name(),
        direct_fields.sort.clone(),
    );
    let updated_direct =
        datatype_field_update_by_name(&direct_view, 0, coroutine_discriminant_field_name(), discr)?;
    datatype_field_update_by_name(root, 0, coroutine_direct_fields_name(), updated_direct)
}

fn root_constructor(sort: &Sort) -> Option<(&str, &ay_bindings::sort::DatatypeConstructor)> {
    let SortInner::Datatype(dt) = sort.inner() else { return None };
    Some((&dt.name, dt.constructors.first()?))
}

fn datatype_field_update_by_index(
    expr: &Expr,
    cons_idx: usize,
    field_idx: usize,
    new_val: Expr,
) -> Option<Expr> {
    let sort = expr.sort().clone();
    let SortInner::Datatype(dt) = sort.inner() else { return None };
    let cons = dt.constructors.get(cons_idx)?;
    let field = cons.fields.get(field_idx)?;
    let new_val = unwrap_single_field_datatype_to_sort(&new_val, &field.sort).unwrap_or(new_val);
    if new_val.sort() != &field.sort {
        return None;
    }

    let mut args = Vec::with_capacity(cons.fields.len());
    for (idx, cons_field) in cons.fields.iter().enumerate() {
        if idx == field_idx {
            args.push(new_val.clone());
        } else {
            args.push(expr.clone().field_select(
                &*dt.name,
                &*cons_field.name,
                cons_field.sort.clone(),
            ));
        }
    }

    Some(Expr::datatype_constructor(&*dt.name, &*cons.name, args, expr.sort().clone()))
}

fn datatype_field_update_by_name(
    expr: &Expr,
    cons_idx: usize,
    name: &str,
    new_val: Expr,
) -> Option<Expr> {
    let sort = expr.sort().clone();
    let SortInner::Datatype(dt) = sort.inner() else { return None };
    let cons = dt.constructors.get(cons_idx)?;
    let field_idx = cons.fields.iter().position(|field| field.name == name)?;
    datatype_field_update_by_index(expr, cons_idx, field_idx, new_val)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen_ay::names::struct_sort;

    /// Coroutine root sort whose views store fields in the REVERSE of MIR
    /// index order, with two SAME-sort fields — the exact shape where
    /// positional selection silently returns the wrong value.
    fn scrambled_coroutine_root() -> Sort {
        // Offset order: [coroutine_field_1, coroutine_field_0] — both BV64.
        let suspend0 = struct_sort(
            "Coroutine_T::Suspend0",
            [("coroutine_field_1", Sort::bv64()), ("coroutine_field_0", Sort::bv64())],
        );
        // Offset order: [coroutine_field_1, case, coroutine_field_0].
        let direct = struct_sort(
            "Coroutine_T::DirectFields",
            [
                ("coroutine_field_1", Sort::bv64()),
                (coroutine_discriminant_field_name(), Sort::bv32()),
                ("coroutine_field_0", Sort::bv64()),
            ],
        );
        struct_sort(
            "Coroutine_T",
            [(coroutine_direct_fields_name(), direct), ("coroutine_variant_Suspend0", suspend0)],
        )
    }

    #[test]
    fn scrambled_root_is_coroutine_root_sort() {
        assert!(is_coroutine_root_sort(&scrambled_coroutine_root()));
    }

    #[test]
    fn variant_select_resolves_mir_index_by_name_not_position() {
        let root = Expr::var("coro", scrambled_coroutine_root());
        let selected = coroutine_root_select(root, Some(0), 0).expect("select field 0");
        let rendered = format!("{selected}");
        // MIR field 0 must resolve to the selector NAMED coroutine_field_0
        // (stored at position 1), not the field at position 0.
        assert!(rendered.contains("coroutine_field_0"), "got: {rendered}");
        assert!(!rendered.contains("coroutine_field_1"), "got: {rendered}");
    }

    #[test]
    fn direct_select_resolves_mir_index_by_name_not_position() {
        let root = Expr::var("coro", scrambled_coroutine_root());
        let selected = coroutine_root_select(root, None, 1).expect("select field 1");
        let rendered = format!("{selected}");
        assert!(rendered.contains("coroutine_field_1"), "got: {rendered}");
        assert!(!rendered.contains("coroutine_field_0"), "got: {rendered}");
    }

    #[test]
    fn direct_select_of_discriminant_index_fails_closed() {
        // MIR index 2 would positionally hit coroutine_field_0; by name there
        // is no `coroutine_field_2` (that slot is the discriminant `case`),
        // so the select must fail closed instead of grabbing a wrong field.
        let root = Expr::var("coro", scrambled_coroutine_root());
        assert!(coroutine_root_select(root, None, 2).is_none());
    }

    #[test]
    fn variant_update_writes_named_slot_not_position() {
        let root = Expr::var("coro", scrambled_coroutine_root());
        let updated = coroutine_root_update(&root, Some(0), 0, Expr::bitvec_const(7, 64))
            .expect("update field 0");
        let rendered = format!("{updated}");
        // The rebuilt Suspend0 constructor stores [coroutine_field_1,
        // coroutine_field_0]; the new value must land in the SECOND slot
        // (named coroutine_field_0) and the first must be a preserving
        // select of coroutine_field_1.
        let ctor_args_start =
            rendered.find("Coroutine_T::Suspend0_mk").expect("variant ctor in output");
        let after_ctor = &rendered[ctor_args_start..];
        let field1_preserve = after_ctor.find("coroutine_field_1").expect("field_1 preserved");
        let new_val_pos = after_ctor.find("#x0000000000000007").expect("new value present");
        assert!(
            field1_preserve < new_val_pos,
            "new value must land in the coroutine_field_0 slot (after the \
             preserved coroutine_field_1): {rendered}"
        );
    }

    #[test]
    fn variant_select_missing_field_falls_through_to_direct_fields() {
        // Variant with NO saved fields: MIR Downcast+Field(0) must fall
        // through to direct_fields (captured upvar), resolved by name there.
        let empty_variant = struct_sort("Coroutine_U::Suspend0", Vec::<(&str, Sort)>::new());
        let direct = struct_sort(
            "Coroutine_U::DirectFields",
            [
                ("coroutine_field_1", Sort::bv64()),
                (coroutine_discriminant_field_name(), Sort::bv32()),
                ("coroutine_field_0", Sort::bv64()),
            ],
        );
        let root_sort = struct_sort(
            "Coroutine_U",
            [
                (coroutine_direct_fields_name(), direct),
                ("coroutine_variant_Suspend0", empty_variant),
            ],
        );
        let root = Expr::var("coro", root_sort);
        let selected = coroutine_root_select(root, Some(0), 0).expect("fall through");
        let rendered = format!("{selected}");
        assert!(rendered.contains("direct_fields"), "got: {rendered}");
        assert!(rendered.contains("coroutine_field_0"), "got: {rendered}");
    }
}
