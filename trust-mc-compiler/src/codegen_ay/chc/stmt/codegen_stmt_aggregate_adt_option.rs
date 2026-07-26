// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Option-like 2-variant enum aggregate construction for CHC encoding.
//!
//! Extracted from codegen_stmt_aggregate_adt.rs per #4130 (500 LOC threshold).
//! Handles enums with exactly 2 variants where one is empty and one has
//! a single field (e.g., Option<T>, NonZero<T>, Poll<T>).

use std::collections::HashSet;
use std::sync::atomic::Ordering;

use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;
use rustc_public::ty::{AdtDef, GenericArgs, RigidTy, TyKind};
use tracing::{debug, warn};

use crate::codegen_ay::chc::call::canonical_zst_expr_for_sort;
use crate::codegen_ay::chc::call::codegen_call_kani_model_dst::is_zst_ty;
use crate::codegen_ay::names::{self, enum_sort};
use crate::codegen_ay::types::{
    POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe, flatten_datatype_to_bitvec,
    flattenable_datatype_sort_width, unflatten_bitvec_to_datatype,
};

use super::codegen_expr_signedness::ty_signedness;
use super::codegen_types::CodegenTypes;
use super::codegen_types_adt_sort::CodegenTypesAdtSort;
use super::stubs_option_helpers::{option_empty_variant_name, option_payload_variant_name};
use super::{ChcCtx, UNDEF_COUNTER, declare_pending_var};
use crate::codegen_ay::shared::signedness_fallback_for_cast_or_coerce;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// `Option<&ZST>` is lowered value-semantically as `Option<ZST>`, so the
    /// payload must be the canonical ZST value rather than the reference address.
    pub(in crate::codegen_ay::chc) fn canonical_ref_to_zst_payload_expr(
        &self,
        operand: &Operand,
        payload_sort: &Sort,
    ) -> Option<Expr> {
        let operand_ty = self.resolve_body_ty(operand.ty(self.body.locals()).ok()?);
        let pointee_ty = match operand_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => self.resolve_body_ty(inner),
            _ => return None,
        };
        if !is_zst_ty(pointee_ty) {
            return None;
        }
        canonical_zst_expr_for_sort(pointee_ty, payload_sort)
    }

    /// Try to translate an Option-like 2-variant enum aggregate construction.
    ///
    /// Handles enums with one empty variant and one single-field payload variant
    /// (e.g., Option<T>, NonZero<T>, Poll<T>). Returns `Some(expr)` on success,
    /// `None` to fall through to the general enum path.
    ///
    /// Part of #4087: Returns `None` (instead of propagating inner `None`) when
    /// deref_ref_ty strips a reference to an untranslatable type, allowing the
    /// caller to fall through to the general enum path.
    pub(in crate::codegen_ay::chc) fn try_translate_option_like_aggregate(
        &mut self,
        def: AdtDef,
        variant_index: usize,
        args: &GenericArgs,
        operands: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let variants = def.variants();
        if variants.len() != 2 {
            return None;
        }
        let v0_fields = variants[0].fields().len();
        let v1_fields = variants[1].fields().len();
        if !((v0_fields == 0 && v1_fields == 1) || (v0_fields == 1 && v1_fields == 0)) {
            return None;
        }

        let some_idx = if v0_fields > 0 { 0 } else { 1 };
        let is_some = variant_index == some_idx;

        // Get the payload sort
        let some_variant = &variants[some_idx];
        let fields = some_variant.fields();
        let field = fields.first()?;
        let field_ty = field.ty();
        let concrete_ty = Self::resolve_generic_ty(field_ty, args)?;
        // Sized-only deref: Option<&str> / Option<&[T]> payloads keep the
        // BV128 fat-pointer representation, matching the declared sort.
        let (payload_ty, payload_is_ref) = Self::deref_ref_ty_sized_only(concrete_ty);
        let payload_sort = Self::translate_ty(payload_ty)?;
        let option_name = Self::option_like_sort_name(def, args, payload_ty);

        // Part of #788: Use enum-style Option (None | Some(value))
        let option_sort = enum_sort(
            &*option_name,
            names::option_constructors(&option_name, payload_sort.clone()),
        );

        // Part of #2980: Ensure the Option Datatype sort is declared
        // in the CHC preamble when constructed via MIR Aggregate.
        self.declare_datatype_sort_if_needed(&option_sort);

        let result_expr = if is_some && !operands.is_empty() {
            // Option-like refs are modeled value-semantically as Option<T>, not
            // Option<addr>. Prefer the normal operand translator so `Some(&b)`
            // in TLS/current-head paths becomes `Some(b)` and stays consistent
            // with constant decoding and later `as_ref` / `ok_or` wrappers.
            let mut value_expr = if payload_is_ref {
                self.canonical_ref_to_zst_payload_expr(&operands[0], &payload_sort)
            } else {
                None
            };
            if value_expr.is_none() {
                value_expr = self.translate_operand_with_modified(&operands[0], modified_locals);
            }
            if payload_is_ref
                && value_expr.as_ref().is_some_and(|expr| expr.sort() != &payload_sort)
            {
                value_expr = self.resolve_ref_operand(&operands[0], modified_locals).or(value_expr);
            }
            let value_expr = value_expr.or_else(|| {
                // Keep the old address fallback only when value-semantics
                // translation fails entirely.
                payload_is_ref
                    .then(|| self.resolve_ref_operand(&operands[0], modified_locals))
                    .flatten()
            })?;
            let value_expr = self.coerce_option_payload_expr(
                value_expr,
                &payload_sort,
                payload_ty,
                &option_name,
            );
            // Fix #825: Use dynamic variant names instead of hardcoded "Some"
            let payload_variant = option_payload_variant_name(&option_sort)
                .map_or_else(|| names::option_some_constructor_name(&option_name), str::to_owned);
            debug!(adt_name = %option_name, variant = %payload_variant, "translate_adt_aggregate: constructed payload variant");
            Expr::datatype_constructor(option_name, payload_variant, vec![value_expr], option_sort)
        } else {
            // Fix #825: Use dynamic variant names instead of hardcoded "None"
            let empty_variant = option_empty_variant_name(&option_sort)
                .map_or_else(|| names::option_none_constructor_name(&option_name), str::to_owned);
            debug!(adt_name = %option_name, variant = %empty_variant, "translate_adt_aggregate: constructed empty variant");
            Expr::datatype_constructor(option_name, empty_variant, vec![], option_sort)
        };

        Some(result_expr)
    }

    /// Coerce an Option payload expression to match the expected sort.
    ///
    /// Handles BV width coercion, BV->DT reconstruction (#3984),
    /// concrete DT->Dyn_Trait coercion (#4099), and general sort mismatch.
    fn coerce_option_payload_expr(
        &mut self,
        value_expr: Expr,
        payload_sort: &Sort,
        payload_ty: rustc_public::ty::Ty,
        option_name: &str,
    ) -> Expr {
        if value_expr.sort() == payload_sort {
            return value_expr;
        }

        let signed = ty_signedness(payload_ty)
            .unwrap_or_else(|| signedness_fallback_for_cast_or_coerce("adt_payload_coerce"));

        // BV->BV width coercion
        let coerced = payload_sort
            .bitvec_width()
            .and_then(|target_width| {
                value_expr.sort().bitvec_width().map(|_current_width| {
                    coerce_bitvec_width_safe(
                        value_expr.clone(),
                        target_width,
                        SignExtension::for_signedness(signed),
                    )
                })
            })
            .filter(|expr| expr.sort() == payload_sort);
        if let Some(coerced) = coerced {
            return coerced;
        }

        // Part of #3984: BV->DT reconstruction for flattened struct payloads.
        if value_expr.sort().is_bitvec() && payload_sort.is_datatype() {
            if let Some(unflat) = unflatten_bitvec_to_datatype(&value_expr, payload_sort) {
                return unflat;
            }
            // Zero-initialized BV -> Datatype with Vec/Array fields (e.g.,
            // Scheduler::new()). unflatten_bitvec_to_datatype fails for structs
            // containing Array sorts (Vec's fld_data). When the BV is zero,
            // construct the Datatype directly with zero/default field values.
            if is_zero_bitvec_const(&value_expr) {
                if let Some(zero_dt) = zero_initialized_datatype(payload_sort) {
                    debug!(
                        option_name = %option_name,
                        "Option payload: BV(0) -> zero-initialized Datatype reconstruction"
                    );
                    return zero_dt;
                }
            }
            warn!(
                option_name = %option_name,
                expected = ?payload_sort,
                actual = ?value_expr.sort(),
                "Option-like payload sort mismatch; using fresh symbolic"
            );
            self.record_aggregate_gap("adt_option_payload_sort_mismatch_unflatten");
            let undef_id = UNDEF_COUNTER.fetch_add(1, Ordering::Relaxed);
            let name = crate::codegen_ay::names::undef_sym_name(option_name, undef_id);
            return declare_pending_var(name, payload_sort.clone());
        }

        // Part of #4099: concrete DT -> Dyn_Trait coercion in Option payload.
        if value_expr.sort().is_datatype()
            && payload_sort.is_datatype()
            && payload_sort.datatype_sort().and_then(|dt| dt.constructors.first()).is_some_and(
                |cons| {
                    cons.fields.len() == 2
                        && cons.fields.iter().any(|f| f.name == "fld_ptr")
                        && cons.fields.iter().any(|f| f.name == "fld_vtable")
                },
            )
        {
            let (dt_name, cons_name) = {
                let tgt_dt = payload_sort
                    .datatype_sort()
                    .expect("invariant: guard checked is_datatype + has constructors");
                (tgt_dt.name.clone(), tgt_dt.constructors[0].name.clone())
            };
            let ptr_expr = if let Some(dt_width) =
                flattenable_datatype_sort_width(value_expr.sort())
                && let Some(flat) = flatten_datatype_to_bitvec(&value_expr, dt_width)
            {
                coerce_bitvec_width_safe(flat, POINTER_WIDTH, SignExtension::ZeroExtend)
            } else if value_expr.sort().bitvec_width().is_some() {
                coerce_bitvec_width_safe(
                    value_expr.clone(),
                    POINTER_WIDTH,
                    SignExtension::ZeroExtend,
                )
            } else {
                // Cannot flatten -- use symbolic pointer
                let undef_id = UNDEF_COUNTER.fetch_add(1, Ordering::Relaxed);
                let name = crate::codegen_ay::names::undef_sym_name(option_name, undef_id);
                declare_pending_var(name, Sort::bitvec(POINTER_WIDTH))
            };
            let vtable_expr = Expr::bitvec_const(0u64, POINTER_WIDTH);
            debug!(
                option_name = %option_name,
                concrete_sort = ?value_expr.sort(),
                "Option payload: concrete DT -> Dyn_Trait coercion"
            );
            return Expr::datatype_constructor(
                dt_name,
                cons_name,
                vec![ptr_expr, vtable_expr],
                payload_sort.clone(),
            );
        }

        // General sort mismatch fallback
        warn!(
            option_name = %option_name,
            expected = ?payload_sort,
            actual = ?value_expr.sort(),
            "Option-like payload sort mismatch; using fresh symbolic"
        );
        self.record_aggregate_gap("adt_option_payload_sort_mismatch");
        let undef_id = UNDEF_COUNTER.fetch_add(1, Ordering::Relaxed);
        let name = crate::codegen_ay::names::undef_sym_name(option_name, undef_id);
        declare_pending_var(name, payload_sort.clone())
    }
}

/// Check whether an expression is a zero-valued bitvec constant.
fn is_zero_bitvec_const(expr: &Expr) -> bool {
    use ay_bindings::ExprValue;
    matches!(
        expr.value(),
        ExprValue::BitVecConst { value, .. } if *value == num_bigint::BigInt::ZERO
    )
}

/// Construct a zero-initialized Datatype expression. Recursively handles
/// fields of BV, Bool, Datatype, and Array sorts.
///
/// Returns `None` if any field sort cannot be zero-initialized (e.g.,
/// uninterpreted sorts). This extends `sort_default_expr` with
/// Array support: `const_array(index_sort, default_element)`.
fn zero_initialized_datatype(sort: &Sort) -> Option<Expr> {
    zero_init_expr(sort)
}

/// Recursive zero-init for any supported sort.
fn zero_init_expr(sort: &Sort) -> Option<Expr> {
    if sort.is_bool() {
        return Some(Expr::bool_const(false));
    }
    if let Some(width) = sort.bitvec_width() {
        return Some(Expr::bitvec_const(0u64, width));
    }
    if sort.is_int() {
        return Some(Expr::int_const(0));
    }
    if let Some(arr) = sort.array_sort() {
        let default_elem = zero_init_expr(&arr.element_sort)?;
        return Some(Expr::const_array(arr.index_sort.clone(), default_elem));
    }
    if let Some(dt) = sort.datatype_sort() {
        if dt.constructors.len() != 1 {
            return None;
        }
        let ctor = dt.constructors.first()?;
        let fields: Vec<Expr> =
            ctor.fields.iter().map(|f| zero_init_expr(&f.sort)).collect::<Option<Vec<_>>>()?;
        return Some(Expr::datatype_constructor(&dt.name, &ctor.name, fields, sort.clone()));
    }
    None
}

#[cfg(test)]
mod tests {
    use crate::codegen_ay::chc::ChcConfig;
    use crate::codegen_ay::chc::codegen_ctx::diagnostics::GLOBAL_COUNTERS;
    use crate::codegen_ay::chc::mir_to_chc;
    use crate::codegen_ay::context::with_test_ay_ctx_for_source;
    use crate::codegen_ay::test_fixtures::find_instance_by_suffix;

    const OPTION_AS_MUT_SCHEDULER_SOURCE: &str = r#"
        #![allow(dead_code, static_mut_refs)]

        static mut SLOT: Option<Scheduler> = None;

        pub struct Scheduler {
            tasks: [u8; 2],
            num_running: usize,
        }

        impl Scheduler {
            pub const fn new() -> Scheduler {
                Scheduler { tasks: [0, 1], num_running: 0 }
            }
        }

        pub fn probe_static_mut_scheduler_as_mut() -> usize {
            unsafe {
                SLOT = Some(Scheduler::new());
                if let Some(executor) = SLOT.as_mut() {
                    executor.num_running += 1;
                    executor.num_running
                } else {
                    0
                }
            }
        }
    "#;

    #[test]
    fn test_option_like_aggregate_prefers_referent_for_ref_payloads() {
        let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let _ = crate::codegen_ay::take_aggregate_encoding_gap_count();
        let _ = crate::codegen_ay::take_aggregate_encoding_gap_by_fn();
        let _ = GLOBAL_COUNTERS.take_aggregate_gap_reasons_by_fn();

        with_test_ay_ctx_for_source(OPTION_AS_MUT_SCHEDULER_SOURCE, |ctx| {
            let fn_name = "probe_static_mut_scheduler_as_mut";
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("body");
            let _vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());
        });

        let gap_reasons = GLOBAL_COUNTERS.take_aggregate_gap_reasons_by_fn();
        let fn_gap_reasons =
            gap_reasons.get("probe_static_mut_scheduler_as_mut").cloned().unwrap_or_default();
        assert!(
            !fn_gap_reasons.contains_key("adt_option_payload_sort_mismatch")
                && !fn_gap_reasons.contains_key("adt_option_payload_sort_mismatch_unflatten"),
            "Option<Scheduler>::as_mut should resolve the referent payload instead of falling back to a symbolic aggregate gap; gap_reasons={fn_gap_reasons:?}"
        );
    }

    /// Option<&str> payloads use the BV128 fat-pointer representation
    /// (concat(len, data_ptr)) end to end: declared sort, aggregate values,
    /// and promoted `const Some("literal")` decoding. Sized pointees
    /// (Option<&[u8; N]>) keep the Array/value modeling. Regression guard for
    /// the ill-sorted `Some_Option_str(Array vs BV128)` export that AY's
    /// parser fail-closed on (kani/Whitespace).
    const OPTION_REF_STR_LITERAL_SOURCE: &str = r#"
        #![allow(dead_code)]

        pub const LIT: Option<&str> = Some("literal");

        pub fn probe_option_ref_str_some(o: Option<&str>, flag: bool) -> bool {
            let v: Option<&str> = if flag { Some("literal") } else { o };
            v.is_some()
        }

        pub fn probe_option_ref_str_const(flag: bool) -> bool {
            let v = if flag { LIT } else { None };
            v.is_some()
        }

        pub fn probe_option_ref_arr(o: Option<&[u8; 4]>) -> bool { o.is_some() }
    "#;

    #[test]
    fn test_option_ref_str_payload_is_bv128_and_literal_constructs_without_mismatch() {
        use super::super::codegen_types::CodegenTypes as _;
        use crate::codegen_ay::chc::ChcCtx;

        let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let _ = crate::codegen_ay::take_aggregate_encoding_gap_count();
        let _ = crate::codegen_ay::take_aggregate_encoding_gap_by_fn();
        let _ = GLOBAL_COUNTERS.take_aggregate_gap_reasons_by_fn();

        let fn_names = ["probe_option_ref_str_some", "probe_option_ref_str_const"];
        with_test_ay_ctx_for_source(OPTION_REF_STR_LITERAL_SOURCE, |ctx| {
            // Declared payload sort of Option<&str> == BV128 fat pointer.
            let instance = find_instance_by_suffix(ctx.tcx, "probe_option_ref_str_some");
            let body = instance.body().expect("body");
            let option_ty = body.locals()[1].ty;
            let sort = ChcCtx::translate_ty(option_ty).expect("Option<&str> should translate");
            let dt = sort.datatype_sort().expect("Option<&str> should be a datatype");
            let payload_sort = dt
                .constructors
                .iter()
                .find_map(|c| c.fields.first().map(|f| f.sort.clone()))
                .expect("Some variant should carry a payload field");
            assert_eq!(
                payload_sort.bitvec_width(),
                Some(128),
                "Option<&str> payload must be the BV128 fat pointer, got {payload_sort:?}"
            );

            // Sized pointee: Option<&[u8; 4]> payload stays Array-modeled.
            let arr_instance = find_instance_by_suffix(ctx.tcx, "probe_option_ref_arr");
            let arr_body = arr_instance.body().expect("body");
            let arr_option_ty = arr_body.locals()[1].ty;
            let arr_sort =
                ChcCtx::translate_ty(arr_option_ty).expect("Option<&[u8; 4]> should translate");
            let arr_dt = arr_sort.datatype_sort().expect("Option<&[u8; 4]> should be a datatype");
            let arr_payload = arr_dt
                .constructors
                .iter()
                .find_map(|c| c.fields.first().map(|f| f.sort.clone()))
                .expect("Some variant should carry a payload field");
            assert!(
                arr_payload.is_array(),
                "Option<&[u8; 4]> (sized pointee) payload should stay Array, got {arr_payload:?}"
            );

            // Aggregate Some("literal") and promoted const Some("literal")
            // both construct without a payload sort mismatch.
            for fn_name in fn_names {
                let instance = find_instance_by_suffix(ctx.tcx, fn_name);
                let body = instance.body().expect("body");
                let _vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());
            }
        });

        let gap_reasons = GLOBAL_COUNTERS.take_aggregate_gap_reasons_by_fn();
        for fn_name in fn_names {
            let fn_gaps = gap_reasons.get(fn_name).cloned().unwrap_or_default();
            assert!(
                !fn_gaps.contains_key("adt_option_payload_sort_mismatch")
                    && !fn_gaps.contains_key("adt_option_payload_sort_mismatch_unflatten"),
                "{fn_name}: Some(\"literal\") payload must match the declared BV128 sort \
                 (no symbolic fallback); gap_reasons={fn_gaps:?}"
            );
        }
    }
}
