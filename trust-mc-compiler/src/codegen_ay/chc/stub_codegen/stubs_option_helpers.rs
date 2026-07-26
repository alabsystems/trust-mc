// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Option/Result/Ordering datatype construction and introspection helpers.
//! Extracted from stubs_util.rs per #2164 for reviewability.
//! Converted from include!() to proper module per #2595.
//!
//! These are helper methods on ChcCtx used by stub translation functions
//! in stubs_util.rs, stubs_iterators.rs, stubs_hashmap.rs, etc.

use ay_bindings::{Expr, Sort, SortInner};
use std::borrow::Cow;
use std::sync::atomic::Ordering;
use tracing::warn;

use super::codegen_ctx::diagnostics::CellCounter;
use super::codegen_ctx::record_translation_drop_site_reason_for_fn;
use super::names::{self, enum_sort};
use super::stubs_util::extract_payload_from_option_reconstruction_ite;
use super::types::{SignExtension, bool_sort, coerce_bitvec_width_safe};
use super::{
    ChcCtx, UNDEF_COUNTER, chc_fresh_name, declare_pending_var, push_pending_datatype_sort,
};

/// Extension trait for Option/Result/Ordering datatype helpers on ChcCtx.
pub(in crate::codegen_ay::chc) trait OptionHelpers {
    #[must_use]
    fn option_unwrap_value(&self, option_expr: Expr) -> Option<Expr>;
    #[must_use]
    fn option_unwrap_value_on_some_path(&self, option_expr: Expr) -> Option<Expr>;
    #[must_use]
    fn make_none_expr(&self, inner_sort: &Sort) -> Expr;
    #[must_use]
    fn make_none_expr_for_option(&self, option_sort: &Sort) -> Option<Expr>;
    #[must_use]
    fn coerce_value_to_sort(&self, value: Expr, target_sort: &Sort, signed: bool) -> Option<Expr>;
    #[must_use]
    fn make_some_expr_for_option(&self, value: Expr, option_sort: &Sort) -> Option<Expr>;
    #[must_use]
    fn option_is_some(&self, option_expr: Expr) -> Expr;
    #[must_use]
    fn result_variant_tester(
        &self,
        result_expr: Expr,
        variant: &str,
        fallback_prefix: &str,
    ) -> Expr;
    #[must_use]
    fn wrap_ordering_int_in_option(&self, ordering_int: Expr, dest_sort: &Sort) -> Option<Expr>;
    #[must_use]
    fn convert_ordering_int_to_bv(&self, ordering_int: Expr, width: u32) -> Expr;
}

/// Creates an Option sort for the given inner value sort.
/// Option is encoded as enum: None | Some(value: T)
///
/// Uses `sort_short_name` (sort-based naming, e.g., `Option_bv64`) when only
/// Sort info is available. When Ty info is available, prefer
/// `option_sort_name_for_payload` (Rust-style, e.g., `Option_u64`).
/// #817 consolidation done; naming differs based on available type info.
#[must_use]
pub(in crate::codegen_ay::chc) fn make_option_sort(inner_sort: &Sort) -> Sort {
    let option_name = names::option_sort_name(&names::sort_short_name(inner_sort));
    enum_sort(&option_name, names::option_constructors(&option_name, inner_sort.clone()))
}

/// Extracts the inner value sort from an Option-like datatype sort.
/// First looks for "Some" constructor, then falls back to any single-field variant.
/// Fix for #821: Don't assume field name is "value".
#[must_use]
pub(in crate::codegen_ay::chc) fn option_value_sort(option_sort: &Sort) -> Option<Sort> {
    let SortInner::Datatype(dt) = option_sort.inner() else {
        return None;
    };
    for constructor in &dt.constructors {
        if names::is_some_constructor(&constructor.name) {
            return constructor.fields.first().map(|field| field.sort.clone());
        }
    }
    for constructor in &dt.constructors {
        if constructor.fields.len() == 1 && !names::is_none_constructor(&constructor.name) {
            return Some(constructor.fields[0].sort.clone());
        }
    }
    None
}

/// Payload variant name for an Option-like DT ("Some" or any single-field variant).
#[must_use]
pub(in crate::codegen_ay::chc) fn option_payload_variant_name(option_sort: &Sort) -> Option<&str> {
    let SortInner::Datatype(dt) = option_sort.inner() else {
        return None;
    };
    for constructor in &dt.constructors {
        if names::is_some_constructor(&constructor.name) {
            return Some(&constructor.name);
        }
    }
    for constructor in &dt.constructors {
        if constructor.fields.len() == 1 && !names::is_none_constructor(&constructor.name) {
            return Some(&constructor.name);
        }
    }
    None
}

/// Empty variant name for an Option-like DT ("None" or any zero-field variant).
#[must_use]
pub(in crate::codegen_ay::chc) fn option_empty_variant_name(option_sort: &Sort) -> Option<&str> {
    let SortInner::Datatype(dt) = option_sort.inner() else {
        return None;
    };
    for constructor in &dt.constructors {
        if names::is_none_constructor(&constructor.name) {
            return Some(&constructor.name);
        }
    }
    for constructor in &dt.constructors {
        if constructor.fields.is_empty() {
            return Some(&constructor.name);
        }
    }
    None
}

/// Fresh symbolic Bool over-approximation for non-Datatype receivers (#3902).
///
/// AUDIT (task #65, stub_approximation): keep counting, NOT SoundHavoc. The
/// fresh Bool decouples the is_some/is_ok-style discriminant from the payload
/// branch the program actually takes: both branches become reachable with
/// arbitrary payloads. Widening for proofs, but the discriminant/payload
/// decoupling means a Success may have been established on a branch pairing
/// the real program cannot exhibit — Step-C fail-closes it.
fn predicate_sort_fallback(
    diagnostics: &super::codegen_ctx::diagnostics::ChcDiagnostics,
    prefix: &str,
) -> Expr {
    diagnostics.stub_approximation.inc();
    declare_pending_var(chc_fresh_name(prefix), bool_sort())
}

fn option_like_struct_field_indices(dt: &ay_bindings::DatatypeSort) -> Option<(usize, usize)> {
    let ctor = dt.constructors.first()?;
    let discr_field = ctor.fields.first()?;
    let option_named =
        dt.name == "Option" || dt.name.starts_with("Option_") || dt.name.ends_with("::Option");
    (dt.constructors.len() == 1
        && ctor.fields.len() == 2
        && discr_field.sort.is_bool()
        && (discr_field.name == "is_some" || option_named))
        .then_some((0, 1))
}

/// Part of #4075: detect Option-like DTs by structure (2 ctors: 1 empty + 1 with fields).
fn find_structural_payload_constructor(
    dt: &ay_bindings::DatatypeSort,
) -> Option<&ay_bindings::DatatypeConstructor> {
    if dt.constructors.len() != 2 {
        return None;
    }
    let has_empty = dt.constructors.iter().any(|c| c.fields.is_empty());
    dt.constructors.iter().find(|c| has_empty && !c.fields.is_empty())
}

impl<'tcx, 'body> OptionHelpers for ChcCtx<'tcx, 'body> {
    fn option_unwrap_value(&self, option_expr: Expr) -> Option<Expr> {
        fn is_none_constructor_expr(expr: &Expr) -> bool {
            let ay_bindings::ExprValue::DatatypeConstructor { constructor_name, args, .. } =
                expr.value()
            else {
                return false;
            };
            args.is_empty() && names::is_none_constructor(constructor_name)
        }

        if let Some(payload) = extract_payload_from_option_reconstruction_ite(&option_expr) {
            return Some(payload);
        }

        let sort = option_expr.sort().clone();
        let SortInner::Datatype(dt) = sort.inner() else {
            warn!("option_unwrap_value called on non-datatype sort");
            return None;
        };

        // Struct-style handler: single-constructor Option layout with a Bool
        // discriminant and payload field. Some recovered Option values use
        // generic field names (`fld_0`, `fld_1`) instead of `is_some/value`.
        if let Some((_, value_idx)) = option_like_struct_field_indices(dt) {
            let value_field = &dt.constructors[0].fields[value_idx];
            // Part of #4053: ensure the DT is declared when field_select
            // is used from an immutable path (e.g. inline_option_unwrap_expr).
            push_pending_datatype_sort(sort.clone());
            return Some(option_expr.field_select(
                &*dt.name,
                &*value_field.name,
                value_field.sort.clone(),
            ));
        }

        let inner_sort = option_value_sort(&sort)?;
        let fresh_payload = || {
            self.record_aggregate_gap("option_unwrap_unchecked_symbolic");
            let name = chc_fresh_name("unwrap_unchecked");
            declare_pending_var(name, inner_sort.clone())
        };
        let coerce_payload = |payload: Expr| self.coerce_value_to_sort(payload, &inner_sort, false);

        match option_expr.value() {
            ay_bindings::ExprValue::Ite { cond, then_expr, else_expr } => {
                if is_none_constructor_expr(then_expr) ^ is_none_constructor_expr(else_expr) {
                    return self.option_unwrap_value_on_some_path(option_expr);
                }
                let then_payload = self
                    .option_unwrap_value(then_expr.clone())
                    .and_then(coerce_payload)
                    .unwrap_or_else(&fresh_payload);
                let else_payload = self
                    .option_unwrap_value(else_expr.clone())
                    .and_then(coerce_payload)
                    .unwrap_or_else(&fresh_payload);
                return Some(Expr::ite(cond.clone(), then_payload, else_payload));
            }
            ay_bindings::ExprValue::DatatypeConstructor { constructor_name, args, .. } => {
                if args.len() == 2 && args[0].sort().is_bool() {
                    return Some(coerce_payload(args[1].clone()).unwrap_or_else(&fresh_payload));
                }
                if names::is_some_constructor(constructor_name)
                    && let Some(payload) = args.first()
                {
                    return Some(coerce_payload(payload.clone()).unwrap_or_else(&fresh_payload));
                }
                return Some(fresh_payload());
            }
            _ => {}
        }

        // Find the payload constructor by name, or by structure (Part of #4075).
        let payload_ctor = dt
            .constructors
            .iter()
            .find(|c| names::is_some_constructor(&c.name) && !c.fields.is_empty())
            .or_else(|| find_structural_payload_constructor(dt));
        if let Some(ctor) = payload_ctor
            && let Some(field) = ctor.fields.first()
        {
            // Part of #4053: ensure the DT is declared for field_select.
            push_pending_datatype_sort(sort.clone());
            return Some(option_expr.field_select(&*dt.name, &*field.name, field.sort.clone()));
        }

        // Part of #3447: Record that Option unwrap value is unconstrained
        // (neither flattened payload nor DT field_select paths resolved).
        Some(fresh_payload())
    }

    fn option_unwrap_value_on_some_path(&self, option_expr: Expr) -> Option<Expr> {
        if let Some(payload) = extract_payload_from_option_reconstruction_ite(&option_expr) {
            return Some(payload);
        }

        let sort = option_expr.sort().clone();
        let SortInner::Datatype(dt) = sort.inner() else {
            warn!("option_unwrap_value_on_some_path called on non-datatype sort");
            return None;
        };

        if let Some((_, value_idx)) = option_like_struct_field_indices(dt) {
            let value_field = &dt.constructors[0].fields[value_idx];
            push_pending_datatype_sort(sort.clone());
            return Some(option_expr.field_select(
                &*dt.name,
                &*value_field.name,
                value_field.sort.clone(),
            ));
        }

        // Find the payload constructor by name, or by structure (Part of #4075).
        let payload_ctor = dt
            .constructors
            .iter()
            .find(|c| names::is_some_constructor(&c.name) && !c.fields.is_empty())
            .or_else(|| find_structural_payload_constructor(dt));
        if let Some(ctor) = payload_ctor
            && let Some(field) = ctor.fields.first()
        {
            push_pending_datatype_sort(sort.clone());
            return Some(option_expr.field_select(&*dt.name, &*field.name, field.sort.clone()));
        }

        None
    }

    fn make_none_expr(&self, inner_sort: &Sort) -> Expr {
        let opt_sort = make_option_sort(inner_sort);
        self.make_none_expr_for_option(&opt_sort).unwrap_or_else(|| {
            // Ensure the Option sort is declared even on the fallback path.
            push_pending_datatype_sort(opt_sort.clone());
            let option_name = opt_sort.datatype_name().unwrap_or("Option_fallback");
            let none_ctor = names::option_none_constructor_name(option_name);
            Expr::datatype_constructor(option_name, none_ctor, vec![], opt_sort.clone())
        })
    }

    fn make_none_expr_for_option(&self, option_sort: &Sort) -> Option<Expr> {
        let SortInner::Datatype(dt) = option_sort.inner() else {
            return None;
        };
        if let Some((_, value_idx)) = option_like_struct_field_indices(dt) {
            let value_sort = dt.constructors[0].fields.get(value_idx)?.sort.clone();
            // Part of #3447: None payload is unconstrained (don't-care value).
            self.record_aggregate_gap("option_none_payload_unconstrained");
            let undef_id = UNDEF_COUNTER.fetch_add(1, Ordering::SeqCst);
            let undef_name = crate::codegen_ay::names::undef_sym_name(&dt.name, undef_id);
            let undef_val = declare_pending_var(undef_name, value_sort);
            let cons_name: Cow<'_, str> = match option_sort.datatype_default_constructor() {
                Some(name) => Cow::Borrowed(name),
                None => Cow::Owned(crate::codegen_ay::names::cons_name(&dt.name)),
            };
            // Ensure the Option DT sort is declared when constructing None.
            push_pending_datatype_sort(option_sort.clone());
            return Some(Expr::datatype_constructor(
                &*dt.name,
                cons_name,
                vec![Expr::bool_const(false), undef_val],
                option_sort.clone(),
            ));
        }
        let empty_name: Cow<'_, str> = if let Some(name) = option_empty_variant_name(option_sort) {
            Cow::Borrowed(name)
        } else {
            warn!(sort = ?option_sort, "Option sort missing empty variant constructor");
            // Part of #3211: Track constraint drop via SOUND_APPROXIMATION counter.
            // Uses inc() directly since this method takes &self (not &mut).
            self.diagnostics.place_translation_drop.inc();
            record_translation_drop_site_reason_for_fn(
                &self.fn_name,
                "option_empty_variant_missing",
            );
            return None;
        };
        // Ensure the Option DT sort is declared when constructing None.
        push_pending_datatype_sort(option_sort.clone());
        Some(Expr::datatype_constructor(&*dt.name, empty_name, vec![], option_sort.clone()))
    }

    fn coerce_value_to_sort(&self, value: Expr, target_sort: &Sort, signed: bool) -> Option<Expr> {
        if value.sort() == target_sort {
            return Some(value);
        }
        if let Some(target_width) = target_sort.bitvec_width() {
            if value.sort().bitvec_width().is_some() {
                return Some(coerce_bitvec_width_safe(
                    value,
                    target_width,
                    SignExtension::for_signedness(signed),
                ));
            }
            // Int→BV: truncate integer to bitvector (Part of #2875).
            if value.sort().is_int() {
                return Some(value.int2bv(target_width));
            }
        }
        // BV→Int: lift using caller-specified signedness. Signed types use
        // bv2int_signed (preserves negative values), unsigned use bv2int
        // (preserves large positive values with MSB set). Part of #3055.
        if target_sort.is_int() && value.sort().is_bitvec() {
            return Some(if signed { value.bv2int_signed() } else { value.bv2int() });
        }
        warn!(
            value_sort = ?value.sort(),
            target_sort = ?target_sort,
            "Cannot coerce value to target sort - incompatible types"
        );
        None
    }

    fn make_some_expr_for_option(&self, value: Expr, option_sort: &Sort) -> Option<Expr> {
        let SortInner::Datatype(dt) = option_sort.inner() else {
            return None;
        };
        if let Some((_, value_idx)) = option_like_struct_field_indices(dt) {
            let inner_sort = dt.constructors[0].fields.get(value_idx)?.sort.clone();
            let coerced_value = self.coerce_value_to_sort(value, &inner_sort, false)?;
            let cons_name: Cow<'_, str> = match option_sort.datatype_default_constructor() {
                Some(name) => Cow::Borrowed(name),
                None => Cow::Owned(crate::codegen_ay::names::cons_name(&dt.name)),
            };
            // Ensure the Option DT sort is declared when constructing Some.
            push_pending_datatype_sort(option_sort.clone());
            return Some(Expr::datatype_constructor(
                &*dt.name,
                cons_name,
                vec![Expr::bool_const(true), coerced_value],
                option_sort.clone(),
            ));
        }
        let inner_sort = option_value_sort(option_sort)?;
        let coerced_value = self.coerce_value_to_sort(value, &inner_sort, false)?;
        let payload_name: Cow<'_, str> =
            if let Some(name) = option_payload_variant_name(option_sort) {
                Cow::Borrowed(name)
            } else {
                warn!(sort = ?option_sort, "Option sort missing payload variant constructor");
                self.diagnostics.place_translation_drop.inc();
                record_translation_drop_site_reason_for_fn(
                    &self.fn_name,
                    "option_payload_variant_missing",
                );
                return None;
            };
        // Ensure the Option DT sort is declared when constructing Some.
        push_pending_datatype_sort(option_sort.clone());
        Some(Expr::datatype_constructor(
            &*dt.name,
            payload_name,
            vec![coerced_value],
            option_sort.clone(),
        ))
    }

    fn option_is_some(&self, option_expr: Expr) -> Expr {
        let sort = option_expr.sort().clone();
        let SortInner::Datatype(dt) = sort.inner() else {
            warn!("option_is_some called on non-datatype sort");
            return predicate_sort_fallback(&self.diagnostics, "option_is_some");
        };

        if let Some((discr_idx, _)) = option_like_struct_field_indices(dt) {
            let discr_field = &dt.constructors[0].fields[discr_idx];
            // Part of #4053: ensure the DT is declared for field_select.
            push_pending_datatype_sort(sort.clone());
            option_expr.field_select(&*dt.name, &*discr_field.name, discr_field.sort.clone())
        } else {
            // Find payload ctor by name or by structure (#4075: inline-walked types).
            let payload_ctor = dt
                .constructors
                .iter()
                .find(|c| names::is_some_constructor(&c.name))
                .or_else(|| find_structural_payload_constructor(dt));
            let Some(payload_ctor) = payload_ctor else {
                let ctor_summary: Vec<_> = dt
                    .constructors
                    .iter()
                    .map(|c| format!("{}(f={})", c.name, c.fields.len()))
                    .collect();
                warn!(name = ?dt.name, ctors = ?ctor_summary, "Option DT missing Some-like ctor");
                self.diagnostics.place_translation_drop.inc();
                record_translation_drop_site_reason_for_fn(
                    &self.fn_name,
                    "option_some_ctor_missing",
                );
                // #3897: symbolic Bool over-approx instead of false (avoids false PROOF).
                return predicate_sort_fallback(&self.diagnostics, "option_some_ctor_missing");
            };
            push_pending_datatype_sort(sort.clone());
            option_expr.is_constructor(&*dt.name, &payload_ctor.name)
        }
    }

    fn result_variant_tester(
        &self,
        result_expr: Expr,
        variant: &str,
        fallback_prefix: &str,
    ) -> Expr {
        let result_sort = result_expr.sort().clone();
        let SortInner::Datatype(dt) = result_sort.inner() else {
            warn!(variant, "result_variant_tester called on non-datatype sort");
            // Over-approximate: fresh symbolic Bool preserves uncertainty when
            // upstream encoding loses the enum constructor. Part of #3902.
            return predicate_sort_fallback(&self.diagnostics, fallback_prefix);
        };

        // Part of #2631: Search for both bare and scoped constructor names.
        for ctor in &dt.constructors {
            let matches = match variant {
                "Ok" => crate::codegen_ay::names::is_ok_constructor(&ctor.name),
                "Err" => crate::codegen_ay::names::is_err_constructor(&ctor.name),
                _ => ctor.name == variant, // non-enum: &str
            };
            if matches {
                return result_expr.is_constructor(&*dt.name, &ctor.name);
            }
        }

        warn!(name = ?dt.name, variant, "Result datatype missing expected constructor");
        // Part of #3211: Track constraint drop via SOUND_APPROXIMATION counter.
        // Uses inc() directly since this method takes &self (not &mut).
        self.diagnostics.place_translation_drop.inc();
        record_translation_drop_site_reason_for_fn(&self.fn_name, "result_ctor_missing");
        // Part of #3897: fresh symbolic Bool instead of false — avoids
        // killing the branch and producing a false PROOF.
        predicate_sort_fallback(&self.diagnostics, "result_ctor_missing")
    }

    fn wrap_ordering_int_in_option(&self, ordering_int: Expr, dest_sort: &Sort) -> Option<Expr> {
        let inner_sort = option_value_sort(dest_sort)?;
        let bv_width = match inner_sort.inner() {
            SortInner::BitVec(bv) if bv.width == 8 || bv.width == 32 => bv.width,
            _ => return None, // external enum: SortInner
        };
        let bv_ordering = self.convert_ordering_int_to_bv(ordering_int, bv_width);
        self.make_some_expr_for_option(bv_ordering, dest_sort)
    }

    fn convert_ordering_int_to_bv(&self, ordering_int: Expr, width: u32) -> Expr {
        // Fix #4213: Less = -1 in two's complement at the given width.
        // For BV8: 0xFF. For BV32: 0xFFFFFFFF. Was hardcoded 0xFF which is
        // only correct for 8-bit but wrong for 32-bit (255 != -1 in BV32).
        let neg1 = (1u128 << width) - 1;
        Expr::ite(
            ordering_int.clone().int_lt(Expr::int_const(0)),
            Expr::bitvec_const(neg1, width),
            Expr::ite(
                ordering_int.eq(Expr::int_const(0)),
                Expr::bitvec_const(0u128, width),
                Expr::bitvec_const(1u128, width),
            ),
        )
    }
}
