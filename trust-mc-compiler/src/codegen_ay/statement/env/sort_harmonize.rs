// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Sort harmonization and conversion for phi node resolution.
//!
//! Handles sort mismatches when merging values from different codegen paths
//! (e.g., BigInt→Int vs BitVec fallback paths).
//!
//! Part of #2408: extracted from env.rs.

use std::fmt::Write;
use std::sync::atomic::Ordering;

use super::{Expr, Sort, SortInner, StatementCodegen};
use crate::codegen_ay::types::{SignExtension, int_sort};
use ay_bindings::ExprValue;
use tracing::{debug, warn};

use super::{BIGINT_CONVERT_CTR, record_sort_harmonize_fresh_var};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    pub(in crate::codegen_ay::statement) fn declare_fresh_fallback_var_if_needed(
        &mut self,
        expr: &Expr,
    ) {
        let ExprValue::Var { name } = expr.value() else {
            return;
        };
        if !(name.starts_with("dt_to_bv_phi_")
            || name.starts_with("bv_to_dt_phi_")
            || name.starts_with("sort_mismatch_phi_")
            || name.starts_with("vec_fld_"))
        {
            return;
        }
        if self.ctx.lookup_var(name).is_none() {
            let _ = self.ctx.declare_var(name, expr.sort().clone());
        }
    }

    pub(in crate::codegen_ay::statement) fn convert_expr_to_sort_declared(
        &mut self,
        expr: Expr,
        target_sort: &Sort,
        signed: Option<bool>,
    ) -> Expr {
        let converted = Self::convert_expr_to_sort(expr, target_sort, signed);
        self.declare_fresh_fallback_var_if_needed(&converted);
        converted
    }

    /// Harmonize incoming value sorts for phi resolution (#749).
    ///
    /// Different codegen paths can produce different sorts for the same variable:
    /// - BigInt operations return Int (via get_bigint_value/sort_inference)
    /// - Some fallback paths may return BitVec(32)
    ///
    /// This function determines a common target sort and converts all values to it.
    /// Int is preferred when mixing Int with BitVec to preserve arbitrary precision.
    pub(in crate::codegen_ay::statement) fn harmonize_incoming_sorts(
        incoming_vals: Vec<(Option<Expr>, Expr)>,
        signed: Option<bool>,
    ) -> (Sort, Vec<(Option<Expr>, Expr)>) {
        // Analyze sorts to determine target
        let mut has_int = false;
        let mut has_bigint_datatype = false;
        let mut has_non_bigint_datatype = false;
        let mut first_bitvec_width: Option<u32> = None;
        let mut first_bitvec_sort: Option<Sort> = None;
        let mut first_sort: Option<Sort> = None;

        for (_, val) in &incoming_vals {
            let sort = val.sort();
            if first_sort.is_none() {
                first_sort = Some(sort.clone());
            }
            if sort.is_int() {
                has_int = true;
            } else if sort.is_bitvec() {
                if first_bitvec_width.is_none() {
                    first_bitvec_width = sort.bitvec_width();
                    first_bitvec_sort = Some(sort.clone());
                }
            } else if let Some(name) = sort.datatype_name() {
                // Defensive: sort_inference.rs now returns Int for BigInt types,
                // so Datatype(BigInt) sorts should be rare. This detection alerts
                // us (via the warning at line 250) if this assumption is violated.
                if name.contains("BigInt") || name.contains("BigUint") || name.contains("Ratio") {
                    has_bigint_datatype = true;
                } else {
                    has_non_bigint_datatype = true;
                }
            }
        }

        // Determine target sort
        // Part of #3260: when mixing Datatype (e.g. Option<bool>) with BitVec, prefer
        // BitVec as target since flatten_datatype_to_bitvec is more reliable than unflatten.
        let needs_int = (has_int && (first_bitvec_width.is_some() || has_bigint_datatype))
            || (has_bigint_datatype && first_bitvec_width.is_some());
        let needs_bitvec = has_non_bigint_datatype
            && first_bitvec_width.is_some()
            && !has_int
            && !has_bigint_datatype;
        let target_sort = if needs_int {
            warn!(
                "Phi sort mismatch: Int/BigInt/Ratio mixed with other sorts (has_int={}, bitvec={:?}, bigint_dt={}) - converting to Int (#749, #752)",
                has_int, first_bitvec_width, has_bigint_datatype
            );
            int_sort()
        } else if needs_bitvec {
            debug!(
                "Phi sort mismatch: Datatype mixed with BitVec({:?}) - preferring BitVec (#3260)",
                first_bitvec_width
            );
            first_bitvec_sort.unwrap_or_else(|| first_sort.unwrap_or_else(Sort::int))
        } else {
            first_sort.unwrap_or_else(Sort::int)
        };

        // Convert all values to target sort
        let harmonized: Vec<(Option<Expr>, Expr)> = incoming_vals
            .into_iter()
            .map(|(cond, val)| {
                let converted = Self::convert_expr_to_sort(val, &target_sort, signed);
                (cond, converted)
            })
            .collect();

        (target_sort, harmonized)
    }

    /// Convert an expression to a target sort (#749, #752).
    ///
    /// Handles conversions for phi harmonization:
    /// - BitVec -> Int: use bv2int_signed for signed values, bv2int otherwise
    /// - Int -> BitVec: use int2bv with target width
    /// - Datatype(BigInt) -> Int: extract Int field or create fresh Int (#752)
    /// - Datatype(single-field) -> field sort: select inner field (#2295)
    /// - Other mismatches: return as-is with warning
    #[must_use]
    pub(in crate::codegen_ay::statement) fn convert_expr_to_sort(
        expr: Expr,
        target_sort: &Sort,
        signed: Option<bool>,
    ) -> Expr {
        // Check equality before cloning sort — the common case (matching sorts)
        // avoids the Arc clone entirely.
        if *expr.sort() == *target_sort {
            return expr;
        }
        let current_sort = expr.sort().clone();

        match (current_sort.inner(), target_sort.inner()) {
            // BitVec -> Int: preserve signedness when available.
            (_s, SortInner::Int) if current_sort.is_bitvec() => {
                if signed == Some(true) {
                    expr.bv2int_signed()
                } else {
                    expr.bv2int()
                }
            }

            // Datatype(BigInt/BigUint/Ratio) -> Int: extract Int field or create fresh Int (#752)
            // In BMC mode, BigInt may be encoded as a Datatype rather than Int.
            // This handles the conversion to avoid ITE sort mismatch panic.
            (SortInner::Datatype(dt), SortInner::Int)
                if dt.name.contains("BigInt")
                    || dt.name.contains("BigUint")
                    || dt.name.contains("Ratio") =>
            {
                // Part of #2267: pre-allocate instead of format!().
                let make_fresh_int = |reason: &str| {
                    let counter = BIGINT_CONVERT_CTR.fetch_add(1, Ordering::Relaxed);
                    let mut fresh_name = String::with_capacity(24);
                    fresh_name.push_str("bigint_phi_conv_");
                    let _ = write!(fresh_name, "{}", counter);
                    warn!(
                        "Datatype({}) conversion fallback: {} - creating fresh Int '{}' (#2432, #752)",
                        dt.name, reason, fresh_name
                    );
                    Expr::var(fresh_name, int_sort())
                };

                // Prefer constructor fields with concrete numeric payloads so conversion stays
                // constrained by the source expression rather than introducing a fresh symbol.
                // Collect candidate constructor/field pairs as references to avoid
                // cloning String/Sort from the datatype definition.
                let mut candidate_fields: Vec<(&str, &str, &Sort)> = Vec::new();
                for constructor in &dt.constructors {
                    if let Some(field) = constructor.fields.iter().find(|field| field.sort.is_int())
                    {
                        candidate_fields.push((&constructor.name, &field.name, &field.sort));
                        continue;
                    }
                    if let Some(field) =
                        constructor.fields.iter().find(|field| field.sort.is_bitvec())
                    {
                        candidate_fields.push((&constructor.name, &field.name, &field.sort));
                    }
                }

                if !candidate_fields.is_empty() {
                    let mut fallback = if candidate_fields.len() == dt.constructors.len() {
                        None
                    } else {
                        Some(make_fresh_int(
                            "not all constructors expose Int/BitVec payload fields",
                        ))
                    };

                    // Build an ITE chain over constructor tests so enum-like datatypes remain
                    // variant-precise instead of selecting fields from an arbitrary constructor.
                    for &(constructor_name, field_name, field_sort) in candidate_fields.iter().rev()
                    {
                        let selected =
                            expr.clone().field_select(&dt.name, field_name, field_sort.clone());
                        let converted = Self::convert_expr_to_sort(selected, &int_sort(), signed);
                        if !converted.sort().is_int() {
                            warn!(
                                "Datatype({}) field '{}' failed Int conversion; skipping candidate",
                                dt.name, field_name
                            );
                            continue;
                        }
                        debug!(
                            "Converting Datatype({}) constructor '{}' field '{}' to Int for phi harmonization",
                            dt.name, constructor_name, field_name
                        );
                        let is_constructor =
                            expr.clone().is_constructor(&dt.name, constructor_name);
                        fallback = Some(match fallback {
                            Some(else_expr) => Expr::ite(is_constructor, converted, else_expr),
                            None => converted,
                        });
                    }

                    if let Some(converted) = fallback {
                        return converted;
                    }
                }

                make_fresh_int("no Int/BitVec payload fields found")
            }

            // Int -> BitVec: use int2bv with target width
            (SortInner::Int, _) if target_sort.is_bitvec() => {
                let Some(width) = target_sort.bitvec_width() else {
                    warn!(?target_sort, "Int->BitVec: bitvec_width() returned None");
                    return expr;
                };
                expr.int2bv(width)
            }

            // Bool -> BitVec: true => 1, false => 0 (discriminant/predicate to Rust bool width)
            (SortInner::Bool, _) if target_sort.is_bitvec() => {
                let Some(bits) = target_sort.bitvec_width() else {
                    warn!(?target_sort, "Bool->BitVec: bitvec_width() returned None");
                    return expr;
                };
                Expr::ite(expr, Expr::bitvec_const(1u64, bits), Expr::bitvec_const(0u64, bits))
            }

            // BitVec -> Bool: bv != 0
            (_, SortInner::Bool) if current_sort.is_bitvec() => {
                let Some(width) = current_sort.bitvec_width() else {
                    warn!(?current_sort, "BitVec->Bool: bitvec_width() returned None");
                    return expr;
                };
                expr.ne(Expr::bitvec_const(0u64, width))
            }

            // BitVec -> BitVec width mismatch: sign-extend or zero-extend on widen.
            (_, _) if current_sort.is_bitvec() && target_sort.is_bitvec() => {
                let Some(tgt_width) = target_sort.bitvec_width() else {
                    warn!(?target_sort, "BitVec->BitVec: bitvec_width() returned None");
                    return expr;
                };
                crate::codegen_ay::types::coerce_bitvec_width(
                    expr,
                    tgt_width,
                    SignExtension::for_signedness(signed.unwrap_or_else(|| {
                        crate::codegen_ay::shared::signedness_fallback_for_cast_or_coerce(
                            "bmc_bv_coerce",
                        )
                    })),
                )
            }

            // Datatype(single-field) -> target field sort:
            // unwrap tuple-like wrappers used by rust-call ABI phi merges (#2295).
            (SortInner::Datatype(dt), _)
                if dt.constructors.len() == 1
                    && dt.constructors[0].fields.len() == 1
                    && dt.constructors[0].fields[0].sort == *target_sort =>
            {
                let field = &dt.constructors[0].fields[0];
                expr.field_select(&dt.name, &field.name, target_sort.clone())
            }

            // Datatype -> BitVec: flatten via flatten_datatype_to_bitvec.
            // Handles Option<bool> where Datatype and BitVec(1) meet at phi nodes.
            // Part of #3260.
            (SortInner::Datatype(dt), _) if target_sort.is_bitvec() => {
                let Some(target_w) = target_sort.bitvec_width() else {
                    warn!(?target_sort, "Datatype->BitVec: bitvec_width() returned None");
                    return expr;
                };
                if let Some(flat) =
                    crate::codegen_ay::types::flatten_datatype_to_bitvec(&expr, target_w)
                {
                    flat
                } else {
                    // Flatten failed (target width too narrow for this datatype).
                    // Fall back to fresh symbolic variable — sound over-approximation.
                    record_sort_harmonize_fresh_var(); // #3263
                    let counter = BIGINT_CONVERT_CTR.fetch_add(1, Ordering::Relaxed);
                    // Part of #2267: pre-allocate instead of format!().
                    let mut fresh_name = String::with_capacity(20);
                    fresh_name.push_str("dt_to_bv_phi_");
                    let _ = write!(fresh_name, "{}", counter);
                    warn!(
                        "Datatype({}) -> BitVec({}): flatten failed, using fresh symbolic '{}' (#3260)",
                        dt.name, target_w, fresh_name
                    );
                    Expr::var(fresh_name, target_sort.clone())
                }
            }

            // BitVec -> Datatype: unflatten via unflatten_bitvec_to_datatype.
            // Part of #3260.
            (_, SortInner::Datatype(dt)) if current_sort.is_bitvec() => {
                if let Some(unflat) =
                    crate::codegen_ay::types::unflatten_bitvec_to_datatype(&expr, target_sort)
                {
                    unflat
                } else {
                    // Unflatten failed (bitvec too narrow for datatype).
                    // Fall back to fresh symbolic variable — sound over-approximation.
                    record_sort_harmonize_fresh_var(); // #3263
                    let counter = BIGINT_CONVERT_CTR.fetch_add(1, Ordering::Relaxed);
                    // Part of #2267: pre-allocate instead of format!().
                    let mut fresh_name = String::with_capacity(20);
                    fresh_name.push_str("bv_to_dt_phi_");
                    let _ = write!(fresh_name, "{}", counter);
                    warn!(
                        "BitVec -> Datatype({}): unflatten failed, using fresh symbolic '{}' (#3260)",
                        dt.name, fresh_name
                    );
                    Expr::var(fresh_name, target_sort.clone())
                }
            }

            // Bool -> Int: true => 1, false => 0.
            // Part of #3266: prevents sort mismatch crash when Bool and Int
            // meet at phi nodes (e.g., comparison result used as integer).
            (SortInner::Bool, SortInner::Int) => {
                Expr::ite(expr, Expr::int_const(1), Expr::int_const(0))
            }

            // Int -> Bool: nonzero => true.
            // Part of #3266: prevents sort mismatch crash when Int and Bool
            // meet at phi nodes.
            (SortInner::Int, SortInner::Bool) => expr.ne(Expr::int_const(0)),

            // Other mismatches: create fresh symbolic variable of target sort.
            // Part of #3266: the previous code returned `expr` with the WRONG
            // sort, which causes AY sort mismatch crashes in downstream ITE
            // construction. A fresh symbolic is a sound over-approximation —
            // the variable is universally quantified in the CHC rule.
            (current, target) => {
                record_sort_harmonize_fresh_var(); // #3263
                let counter = BIGINT_CONVERT_CTR.fetch_add(1, Ordering::Relaxed);
                // Part of #2267: pre-allocate instead of format!().
                let mut fresh_name = String::with_capacity(24);
                fresh_name.push_str("sort_mismatch_phi_");
                let _ = write!(fresh_name, "{}", counter);
                warn!(
                    "Cannot convert sort {:?} to {:?} in phi harmonization — \
                     using fresh symbolic '{}' (sound over-approximation, #3266)",
                    current, target, fresh_name
                );
                Expr::var(fresh_name, target_sort.clone())
            }
        }
    }
}
