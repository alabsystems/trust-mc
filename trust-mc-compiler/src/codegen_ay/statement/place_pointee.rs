// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Pointee tracking for place translation.
//!
//! Extracted from place.rs as part of #2039 decomposition.
//! Functions for ensuring ref_pointees mappings and deriving pointee values.

use std::fmt::Write;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use super::{Expr, IndexedVal, IntoOption, Place, ProjectionElem, Sort, StatementCodegen};
use crate::codegen_ay::types::POINTER_WIDTH;
use tracing::{debug, warn};

/// Telemetry counter for pointee synthesis fallback hits (#3013).
/// Tracks when `synthesize_pointee_expr` creates unconstrained symbolic variables
/// for pointer dereferences with incomplete tracking. Each hit represents a
/// potential false-proof vector where the solver can choose arbitrary values.
pub(super) static POINTEE_SYNTHESIS_FALLBACK_COUNT: AtomicUsize = AtomicUsize::new(0);

/// Reset the pointee synthesis fallback counter, returning the previous value.
pub(in crate::codegen_ay) fn take_pointee_synthesis_fallback_count() -> usize {
    POINTEE_SYNTHESIS_FALLBACK_COUNT.swap(0, Ordering::Relaxed)
}

/// Non-destructive read of the pointee synthesis fallback counter (Part of #3080).
pub(in crate::codegen_ay) fn get_pointee_synthesis_fallback_count() -> usize {
    POINTEE_SYNTHESIS_FALLBACK_COUNT.load(Ordering::Relaxed)
}

/// Set pointee synthesis fallback counter for test isolation (Part of #3369).
#[cfg(test)]
#[allow(dead_code)]
pub(in crate::codegen_ay) fn set_pointee_synthesis_fallback_count_for_test(count: usize) {
    POINTEE_SYNTHESIS_FALLBACK_COUNT.store(count, Ordering::Relaxed);
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Ensure ref_pointees has a mapping for a reference place, deriving it from deref chains.
    ///
    /// Returns the derived pointee base name if a mapping is available or can be derived.
    pub(super) fn ensure_ref_pointee_for_place(&mut self, place: &Place) -> Option<Arc<str>> {
        let ref_base: Arc<str> = self.ssa_base_name(place).into();
        if let Some(pointee) = self.ref_pointees.get(ref_base.as_ref()).cloned() {
            return Some(pointee);
        }

        let append_suffix = |base: &mut String, proj: &ProjectionElem| match proj {
            ProjectionElem::Field(field, _) => {
                let _ = write!(base, "_field_{}", field);
            }
            ProjectionElem::Deref => {
                base.push_str("_deref");
            }
            ProjectionElem::Downcast(variant_idx) => {
                let _ = write!(base, "_variant_{}", variant_idx.to_index());
            }
            ProjectionElem::Index(local) => {
                let _ = write!(base, "_idx_by_{}", local);
            }
            ProjectionElem::ConstantIndex { offset, min_length: _, from_end } => {
                if *from_end {
                    let _ = write!(base, "_cidx_end_{}", offset);
                } else {
                    let _ = write!(base, "_cidx_{}", offset);
                }
            }
            ProjectionElem::Subslice { from, to, from_end } => {
                if *from_end {
                    let _ = write!(base, "_subslice_end_{}_{}", from, to);
                } else {
                    let _ = write!(base, "_subslice_{}_{}", from, to);
                }
            }
            ProjectionElem::OpaqueCast(_) => {
                base.push_str("_cast");
            }
        };

        for (proj_idx, proj) in place.projection.iter().enumerate() {
            if !matches!(proj, ProjectionElem::Deref) {
                continue;
            }

            let prefix_ref = self.ssa_base_name_for_prefix(place, proj_idx);
            let Some(pointee_base) = self.ref_pointees.get(prefix_ref.as_str()).cloned() else {
                continue;
            };

            let mut suffix_projections = place.projection.iter().skip(proj_idx + 1);
            if let Some(first_suffix) = suffix_projections.next() {
                let mut derived_base = String::with_capacity(
                    pointee_base.len()
                        + 16usize
                            .saturating_mul(place.projection.len().saturating_sub(proj_idx + 1)),
                );
                derived_base.push_str(pointee_base.as_ref());
                append_suffix(&mut derived_base, first_suffix);
                for suffix_proj in suffix_projections {
                    append_suffix(&mut derived_base, suffix_proj);
                }

                if let Some(derived_pointee) = self.ref_pointees.get(derived_base.as_str()).cloned()
                {
                    debug!(
                        "ensure_ref_pointee_for_place: {} -> {} via {}",
                        ref_base, derived_pointee, derived_base
                    );
                    self.ref_pointees.insert(Arc::clone(&ref_base), Arc::clone(&derived_pointee));
                    return Some(derived_pointee);
                }
            }

            if let Some(pointee_pointee) = self.ref_pointees.get(pointee_base.as_ref()).cloned() {
                let deref_base = self.ssa_base_name_for_prefix(place, proj_idx + 1);
                debug!(
                    "ensure_ref_pointee_for_place: {} -> {} via {}",
                    deref_base, pointee_pointee, pointee_base
                );
                let is_target = deref_base == ref_base.as_ref();
                self.ref_pointees.insert(Arc::from(deref_base), Arc::clone(&pointee_pointee));
                if is_target {
                    return Some(pointee_pointee);
                }
            }
        }

        None
    }

    /// Recover a reference pointee directly from SSA env when the reference local
    /// already stores value semantics (e.g., Slice/Vec datatypes) but ref_pointees
    /// mapping is unavailable.
    ///
    /// This is intentionally restricted to datatype/array pointee sorts to avoid
    /// conflating thin-pointer bitvectors (`&u64` as bv64) with pointee values.
    pub(super) fn try_ref_pointee_from_env_value(
        &self,
        ref_base: &str,
        ref_place: &Place,
    ) -> Option<Expr> {
        let ref_ty = ref_place.ty(self.body.locals()).into_option()?;
        let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Ref(_, pointee_ty, _)) =
            ref_ty.kind()
        else {
            return None;
        };
        let pointee_sort = Self::infer_sort_from_ty(pointee_ty)?;
        if !pointee_sort.is_datatype() && !pointee_sort.is_array() {
            return None;
        }
        let ref_expr = self.env_lookup(ref_base)?;
        (ref_expr.sort() == &pointee_sort).then(|| ref_expr.clone())
    }

    /// Ensure a derived pointee name has an env value by resolving deref chains.
    ///
    /// Names like `fn::local_30_deref_field_0` encode their derivation:
    /// - `local_30` is the base reference
    /// - `_deref` indicates a deref projection
    /// - `_field_0` indicates field projection 0
    ///
    /// When the name is not in env, this method:
    /// 1. Parses the structure from the name
    /// 2. Looks up the base reference in ref_pointees
    /// 3. Recursively ensures the pointee has an env value
    /// 4. Applies field projections to build the derived value
    /// 5. Stores the result in env
    ///
    /// Part of #468: Enable iterator support by fixing deref chain resolution.
    pub(super) fn ensure_derived_pointee_in_env(&mut self, pointee_base: &str) -> Option<Expr> {
        // Already in env? Return it.
        if let Some(expr) = self.env_lookup(pointee_base) {
            return Some(expr.clone());
        }

        // Durable pointee recovery (slice::get and other heap-tracked pointees).
        //
        // Opaque synthetic pointee names such as `::slice_get_pointee_N` carry no
        // `::local_` structure to reparse below, so before this check they fell
        // straight through to `synthesize_pointee_expr` (an UNCONSTRAINED symbolic
        // → the `pointee_synthesis_fallback` EncodingGap) whenever the SSA env
        // entry had been superseded by a later block / phi rebuild or an inline
        // boundary. `heap_pointees` holds the exact CONSTRAINED value published at
        // codegen time (for slice::get, `a[index]`); recover it here and republish
        // into env. env_lookup is tried FIRST above, so a fresher env value always
        // wins — this only fires on the fallback path. SOUNDNESS: this returns the
        // identical tracked expression, never a fresh/over-approximated symbolic,
        // so it strictly REMOVES an unconstrained value and adds no false-verify
        // surface. Part of #multi-hop-flattened-option / #3013.
        if let Some(expr) = self.heap_pointees.get(pointee_base).cloned() {
            self.env_update(pointee_base, expr.clone());
            return Some(expr);
        }

        // Parse the derived name to extract base local and projections.
        // Format: "fn::local_N_deref_field_M..." or "fn::local_N_field_M..."
        // We need to find the base local and track projections.

        // Extract fn::local_N part
        let Some(local_prefix_pos) = pointee_base.find("::local_") else {
            debug!("ensure_derived_pointee_in_env: no ::local_ in {}", pointee_base);
            return None;
        };
        let fn_prefix = &pointee_base[..local_prefix_pos + 8]; // includes "::local_"

        // Extract local number
        let after_local = &pointee_base[local_prefix_pos + 8..];
        let local_num_str: String = after_local.chars().take_while(char::is_ascii_digit).collect();
        let Ok(_local_num) = local_num_str.parse::<usize>() else {
            debug!("ensure_derived_pointee_in_env: cannot parse local num from {}", pointee_base);
            return None;
        };

        // Get the suffix after local number (e.g., "_deref_field_0")
        let suffix_start = local_prefix_pos + 8 + local_num_str.len();
        let suffix = &pointee_base[suffix_start..];

        fn parse_num(input: &str) -> Option<(usize, &str)> {
            let digits: String = input.chars().take_while(char::is_ascii_digit).collect();
            if digits.is_empty() {
                return None;
            }
            let value = digits.parse::<usize>().ok()?;
            Some((value, &input[digits.len()..]))
        }

        fn parse_subslice(input: &str) -> Option<((usize, usize), &str)> {
            let (from, rest) = parse_num(input)?;
            let rest = rest.strip_prefix('_')?;
            let (to, rest) = parse_num(rest)?;
            Some(((from, to), rest))
        }

        // Part of #2267: pre-allocate instead of format!().
        let mut current_base_name =
            String::with_capacity(fn_prefix.len() + local_num_str.len() + 16);
        current_base_name.push_str(fn_prefix);
        current_base_name.push_str(&local_num_str);
        let mut current_expr = self.env_lookup(&current_base_name).cloned();
        let mut active_variant: Option<usize> = None;
        let mut remaining = suffix;
        while !remaining.is_empty() {
            if let Some(rest) = remaining.strip_prefix("_cast") {
                current_base_name.push_str("_cast");
                remaining = rest;
                continue;
            }
            if let Some(rest) = remaining.strip_prefix("_variant_") {
                let Some((variant_idx, rest)) = parse_num(rest) else {
                    debug!(
                        "ensure_derived_pointee_in_env: cannot parse variant idx from {}",
                        remaining
                    );
                    return None;
                };
                let _ = write!(current_base_name, "_variant_{}", variant_idx);
                active_variant = Some(variant_idx);
                remaining = rest;
                continue;
            }
            if let Some(rest) = remaining.strip_prefix("_field_") {
                let Some((field_idx, rest)) = parse_num(rest) else {
                    debug!(
                        "ensure_derived_pointee_in_env: cannot parse field idx from {}",
                        remaining
                    );
                    return None;
                };
                let _ = write!(current_base_name, "_field_{}", field_idx);
                if let Some(expr) = self.env_lookup(&current_base_name) {
                    current_expr = Some(expr.clone());
                    active_variant = None;
                    remaining = rest;
                    continue;
                }
                let Some(expr) = current_expr else {
                    debug!(
                        "ensure_derived_pointee_in_env: no expr available for {}",
                        current_base_name
                    );
                    return None;
                };
                // Resolve constructor index from sort and active_variant.
                let cons_idx = match expr.sort().datatype_sort() {
                    Some(dt) if dt.constructors.len() > 1 => {
                        if let Some(idx) = active_variant {
                            idx
                        } else {
                            debug!(
                                "ensure_derived_pointee_in_env: missing variant for {}",
                                dt.name
                            );
                            return None;
                        }
                    }
                    // Single-constructor: variant 0 is the only valid index.
                    Some(_) => active_variant.unwrap_or(0),
                    None => {
                        debug!(
                            "ensure_derived_pointee_in_env: field select on non-datatype {:?}",
                            expr.sort()
                        );
                        return None;
                    }
                };
                let Some(selected) =
                    crate::codegen_ay::types::datatype_field_select(expr, cons_idx, field_idx)
                else {
                    debug!("ensure_derived_pointee_in_env: field {} out of range", field_idx);
                    return None;
                };
                current_expr = Some(selected);
                active_variant = None;
                remaining = rest;
                continue;
            }
            if let Some(rest) = remaining.strip_prefix("_deref") {
                if let Some(ref_pointee) =
                    self.ref_pointees.get(current_base_name.as_str()).cloned()
                {
                    debug!(
                        "ensure_derived_pointee_in_env: {} -> ref_pointees[{}] = {}",
                        pointee_base, current_base_name, ref_pointee
                    );
                    let base_expr = self.ensure_derived_pointee_in_env(&ref_pointee)?;
                    current_base_name.clear();
                    current_base_name.push_str(ref_pointee.as_ref());
                    current_expr = Some(base_expr);
                    active_variant = None;
                    remaining = rest;
                    continue;
                }
                // Fallback (#884): if ref_pointees doesn't have the base but env does,
                // the dereferenced value might have been stored directly under the base name.
                // This handles iterator patterns and complex assignments where the pointee
                // value gets stored without proper indirection tracking.
                if let Some(expr) = current_expr.clone() {
                    debug!(
                        "ensure_derived_pointee_in_env: {} not in ref_pointees, using env fallback (sort={:?})",
                        current_base_name,
                        expr.sort()
                    );
                    // The env value represents the dereferenced content - continue with remaining projections
                    current_base_name.push_str("_deref");
                    // current_expr stays the same - we treat the deref as resolved
                    remaining = rest;
                    continue;
                }
                debug!(
                    "ensure_derived_pointee_in_env: {} not in ref_pointees and no env fallback",
                    current_base_name
                );
                return None;
            }
            if let Some(rest) = remaining.strip_prefix("_idx_by_") {
                let Some((index_local, _rest)) = parse_num(rest) else {
                    debug!(
                        "ensure_derived_pointee_in_env: cannot parse index local from {}",
                        remaining
                    );
                    return None;
                };
                debug!(
                    "ensure_derived_pointee_in_env: unsupported index projection _idx_by_{}",
                    index_local
                );
                return None;
            }
            if let Some(rest) = remaining.strip_prefix("_cidx_end_") {
                let Some((offset, _rest)) = parse_num(rest) else {
                    debug!(
                        "ensure_derived_pointee_in_env: cannot parse const index from {}",
                        remaining
                    );
                    return None;
                };
                debug!(
                    "ensure_derived_pointee_in_env: unsupported const index from_end {}",
                    offset
                );
                return None;
            }
            if let Some(rest) = remaining.strip_prefix("_cidx_") {
                let Some((offset, _rest)) = parse_num(rest) else {
                    debug!(
                        "ensure_derived_pointee_in_env: cannot parse const index from {}",
                        remaining
                    );
                    return None;
                };
                debug!("ensure_derived_pointee_in_env: unsupported const index {}", offset);
                return None;
            }
            if let Some(rest) = remaining.strip_prefix("_subslice_end_") {
                let Some(((from, to), rest)) = parse_subslice(rest) else {
                    debug!(
                        "ensure_derived_pointee_in_env: cannot parse subslice from {}",
                        remaining
                    );
                    return None;
                };
                let _ = write!(current_base_name, "_subslice_end_{}_{}", from, to);
                // Part of #3306: SubSlice from_end derivation.
                // Identity case (from=0, to=0) = full array, pass through.
                if from == 0 && to == 0 {
                    debug!("ensure_derived_pointee_in_env: identity subslice from_end");
                    remaining = rest;
                    continue;
                }
                // Non-identity from_end: need array length from type info (unavailable here).
                debug!(
                    "ensure_derived_pointee_in_env: non-identity subslice from_end {}..{}",
                    from, to
                );
                return None;
            }
            if let Some(rest) = remaining.strip_prefix("_subslice_") {
                let Some(((from, to), rest)) = parse_subslice(rest) else {
                    debug!(
                        "ensure_derived_pointee_in_env: cannot parse subslice from {}",
                        remaining
                    );
                    return None;
                };
                let _ = write!(current_base_name, "_subslice_{}_{}", from, to);
                // Part of #3306: SubSlice derivation (from_end=false).
                let Some(ref expr) = current_expr else {
                    debug!(
                        "ensure_derived_pointee_in_env: no expr for subslice {}",
                        current_base_name
                    );
                    return None;
                };
                if !expr.sort().is_array() {
                    debug!(
                        "ensure_derived_pointee_in_env: subslice on non-array {:?}",
                        expr.sort()
                    );
                    return None;
                }
                let Some(result_len) = to.checked_sub(from) else {
                    debug!(
                        "ensure_derived_pointee_in_env: subslice end {} precedes start {}",
                        to, from
                    );
                    return None;
                };
                if result_len == 0 {
                    // `from_end=false` means `[from..to]`, so a zero-length
                    // range is EMPTY. This array-only fallback has no separate
                    // length carrier with which to represent that value safely.
                    return None;
                }
                if let Some(arr_sort) = expr.sort().array_sort() {
                    let elem_sort = arr_sort.element_sort.clone();
                    let result_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), elem_sort);
                    let name = self.ctx.fresh_name("subslice_pointee");
                    let _ = self.ctx.declare_var(&name, result_sort);
                    let mut result = Expr::var(&name, expr.sort().clone());
                    for i in 0..result_len {
                        let src_idx = Expr::bitvec_const((from + i) as u128, POINTER_WIDTH);
                        let dst_idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                        let elem = expr.clone().select(src_idx);
                        result = result.store(dst_idx, elem);
                    }
                    current_expr = Some(result);
                } else {
                    debug!(
                        "ensure_derived_pointee_in_env: subslice array_sort failed {:?}",
                        expr.sort()
                    );
                    return None;
                }
                active_variant = None;
                remaining = rest;
                continue;
            }
            debug!("ensure_derived_pointee_in_env: unexpected suffix in {}", remaining);
            return None;
        }

        if let Some(expr) = current_expr {
            self.env_update(pointee_base, expr.clone());
            return Some(expr);
        }

        debug!("ensure_derived_pointee_in_env: could not resolve {}", pointee_base);
        None
    }

    /// Synthesize a pointee value in the environment when tracking is missing.
    ///
    /// This creates a fresh symbolic variable for the pointee base using the
    /// inferred sort for the provided place (typically a deref prefix).
    pub(super) fn synthesize_pointee_expr(
        &mut self,
        pointee_base: &str,
        place: &Place,
    ) -> Option<Expr> {
        POINTEE_SYNTHESIS_FALLBACK_COUNT.fetch_add(1, Ordering::Relaxed);
        warn!(
            pointee_base,
            "synthesize_pointee_expr: created unconstrained symbolic for untracked pointee (#3013)"
        );
        let sort = self.infer_sort_from_place(place).unwrap_or_else(|| Sort::bitvec(32));
        let name = self.ssa_name_from_base(pointee_base, false);
        let expr = if let Some(expr) = self.ctx.lookup_var(&name) {
            expr.clone()
        } else {
            self.ctx.declare_var(&name, sort)
        };

        if let Some(v) = self.ssa_version.get_mut(pointee_base) {
            *v = (*v).max(1);
        } else {
            self.ssa_version.insert(std::sync::Arc::from(pointee_base), 1);
        }
        self.env_update(pointee_base, expr.clone());
        Some(expr)
    }
}
