// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Projection handling after deref resolution for place translation.
//!
//! Extracted from `place.rs` as part of #2246 decomposition.

use super::{
    Expr, IndexedVal, Place, ProjectionElem, Sort, StatementCodegen, constant_index_offset,
};
use crate::codegen_ay::provenance::is_transparent_pointer_wrapper_repr;
use crate::codegen_ay::types::{CtorFieldExt, POINTER_WIDTH};
use tracing::debug;

/// Result of applying post-deref projections.
pub(super) enum DerefProjectionResult {
    /// All projections applied successfully.
    Success(Expr),
    /// Could not complete; caller should try other resolution paths.
    Fallthrough,
    /// Hard failure reported via `ctx.unsupported`.
    Unsupported,
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    fn post_deref_backing_array(expr: &Expr) -> Option<Expr> {
        let dt_name = expr.sort().datatype_name()?;
        let dt = expr.sort().datatype_sort()?;
        let data_field = dt.constructors.first()?.field("fld_data")?;
        if !data_field.sort.is_array() {
            return None;
        }
        Some(expr.clone().field_select(dt_name, "fld_data", data_field.sort.clone()))
    }

    /// Apply post-deref projections (Downcast/Field/Index/ConstantIndex) to an expression.
    ///
    /// This consolidates the repeated projection-application pattern used in the deref-first
    /// path. The 6 original copies had minor behavioral differences controlled by:
    ///
    /// - `strict`: If true, multi-constructor enums require a prior Downcast before Field
    ///   access (returns Unsupported if missing). If false, defaults to variant 0.
    /// - `fallthrough_on_failure`: If true, unhandled projections return Fallthrough instead
    ///   of Unsupported, allowing the caller to try alternative resolution paths.
    /// - `context_label`: Label for `ctx.unsupported` diagnostic messages.
    ///
    /// All copies handle: transparent wrapper bv64 (field 0 on POINTER_WIDTH bitvec),
    /// ZST/marker bv32 types, and datatype field extraction.
    pub(super) fn apply_post_deref_projections(
        &mut self,
        mut expr: Expr,
        projections: &[ProjectionElem],
        strict: bool,
        fallthrough_on_failure: bool,
        context_label: &'static str,
    ) -> DerefProjectionResult {
        let mut active_variant: Option<usize> = None;
        // SwitchInt→variant bridge (#3017): the field-read place context, if the caller
        // staged one (only when facts are live). Taken (consumed) so it can never be
        // read stale by a later call that did not set it.
        let bridge_ctx = self.bridge_enum_read.take();
        for (proj_idx, proj) in projections.iter().enumerate() {
            match proj {
                ProjectionElem::Downcast(variant_idx) => {
                    // Part of #1100: Allow Downcast on bv64 from Try::branch stubs.
                    if !expr.sort().is_datatype() {
                        if is_transparent_pointer_wrapper_repr(expr.sort())
                            && variant_idx.to_index() == 0
                        {
                            active_variant = Some(0);
                            debug!("apply_post_deref: Downcast on bv64 to variant 0 - transparent");
                            continue;
                        }
                        if fallthrough_on_failure {
                            return DerefProjectionResult::Fallthrough;
                        }
                        self.ctx.unsupported(
                            context_label,
                            format!("Downcast on non-datatype {:?}", expr.sort()),
                        );
                        return DerefProjectionResult::Unsupported;
                    }
                    // An Option-like datatype is `[None_*, Some_*]` by PAYLOAD, not
                    // by MIR variant order (`Poll::Ready(T)` is variant 0 but lives
                    // in `Some_*`). A `Downcast` that is immediately FOLLOWED by a
                    // `Field` can only be reading the payload constructor — the
                    // fieldless one has no field 0 — so select it by arity, exactly.
                    let positional = variant_idx.to_index();
                    let next_is_field =
                        matches!(projections.get(proj_idx + 1), Some(ProjectionElem::Field(..)));
                    let option_like_payload_ctor = expr.sort().datatype_sort().and_then(|dt| {
                        if dt.constructors.len() != 2 || !next_is_field {
                            return None;
                        }
                        match (dt.constructors[0].fields.len(), dt.constructors[1].fields.len()) {
                            (0, 1) => Some(1usize),
                            (1, 0) => Some(0usize),
                            _ => None,
                        }
                    });
                    active_variant = Some(option_like_payload_ctor.unwrap_or(positional));
                    debug!(
                        "apply_post_deref: Downcast to variant {} (constructor {:?})",
                        positional, active_variant
                    );
                }
                ProjectionElem::Field(field, _ty) => {
                    // Part of #944: Handle transparent wrapper bv64 (NonNull/Unique).
                    // Part of #1100: Also allow active_variant == Some(0) for ControlFlow::Continue.
                    // Shares the one documented representation predicate with the CHC
                    // select/update pair, so all four copies of this test move together.
                    if is_transparent_pointer_wrapper_repr(expr.sort())
                        && *field == 0
                        && (active_variant.is_none() || active_variant == Some(0))
                    {
                        active_variant = None;
                        continue;
                    }
                    // Part of #1657: Handle ZST/marker types encoded as bv32.
                    if Self::is_marker_bv32_sort(expr.sort()) {
                        debug!(
                            "apply_post_deref: Field {} on bv32 (ZST/marker) - returning unchanged",
                            field
                        );
                        active_variant = None;
                        continue;
                    }
                    // A coroutine root keeps MIR fields by NAME under `direct_fields`
                    // / its variant views; positional selection on the root picked the
                    // whole `direct_fields` view for `(*pinned).0` (an upvar read
                    // through `Pin<&mut coroutine>`) and the query went ill-sorted.
                    // Same call the non-deref walker makes.
                    if let Some(selected) = crate::codegen_ay::types::coroutine_root_select(
                        expr.clone(),
                        active_variant,
                        *field,
                    ) {
                        expr = selected;
                        active_variant = None;
                        continue;
                    }
                    // Resolve constructor index from sort and active_variant.
                    let cons_idx = match expr.sort().datatype_sort() {
                        Some(dt) if dt.constructors.len() > 1 => {
                            // SwitchInt→variant bridge (#3017): parent-enum place key for
                            // THIS field's owning datatype term. `proj_base + proj_idx` is
                            // the absolute index of this Field within the full place.
                            let enum_key = match &bridge_ctx {
                                Some((pl, base)) if *base + proj_idx <= pl.projection.len() => {
                                    let parent = Place {
                                        local: pl.local,
                                        projection: pl.projection[..*base + proj_idx].to_vec(),
                                    };
                                    self.variant_fact_place_key(&parent)
                                }
                                _ => None,
                            };
                            match active_variant {
                                Some(idx) => Some(idx),
                                None if strict => {
                                    match self.bridge_variant_for_field(&expr, enum_key.as_ref()) {
                                        Some(ci) => Some(ci),
                                        None => {
                                            if fallthrough_on_failure {
                                                return DerefProjectionResult::Fallthrough;
                                            }
                                            self.ctx.unsupported(
                                                context_label,
                                                format!(
                                                    "Multi-variant enum '{}' requires Downcast before Field",
                                                    dt.name
                                                ),
                                            );
                                            return DerefProjectionResult::Unsupported;
                                        }
                                    }
                                }
                                None => {
                                    // Bridge: if a live fact provably pins the variant,
                                    // use it (asserting is_constructor on this exact term).
                                    match self.bridge_variant_for_field(&expr, enum_key.as_ref()) {
                                        Some(ci) => Some(ci),
                                        None => {
                                            // Lenient: default to variant 0 for multi-variant
                                            // enum without Downcast. Unsound if a non-zero
                                            // variant is active.
                                            self.ctx.unsupported_with_fallback(
                                                "Deref field projection (lenient)",
                                                "multi-variant enum field access without Downcast; \
                                                 defaulting to variant 0",
                                            );
                                            // Fail-closed: inject unconditional violation so
                                            // the solver reports CTREX instead of false PROOF
                                            // when variant 0 assumption is wrong. Part of #3017.
                                            self.record_violation_guarded(
                                                Expr::bool_const(true),
                                                "unsound_enum_variant_0_default",
                                            );
                                            Some(0)
                                        }
                                    }
                                }
                            }
                        }
                        // Single-constructor: variant 0 is the only valid index.
                        Some(_) => Some(active_variant.unwrap_or(0)),
                        None => None, // not a datatype
                    };
                    if let Some(ci) = cons_idx
                        && let Some(selected) = crate::codegen_ay::types::datatype_field_select(
                            expr.clone(),
                            ci,
                            *field,
                        )
                    {
                        expr = selected;
                        active_variant = None;
                        continue;
                    }
                    // Field projection failed
                    if fallthrough_on_failure {
                        return DerefProjectionResult::Fallthrough;
                    }
                    let msg = if expr.sort().is_datatype() {
                        format!(
                            "Field lookup failed (constructor/field index out of range) on {:?}",
                            expr.sort()
                        )
                    } else {
                        format!("Field projection on non-datatype sort {:?}", expr.sort())
                    };
                    self.ctx.unsupported(context_label, msg);
                    return DerefProjectionResult::Unsupported;
                }
                ProjectionElem::Index(local) => {
                    if !expr.sort().is_array() {
                        if let Some(backing_array) = Self::post_deref_backing_array(&expr) {
                            expr = backing_array;
                        } else if fallthrough_on_failure {
                            return DerefProjectionResult::Fallthrough;
                        } else {
                            self.ctx.unsupported(
                                context_label,
                                format!("Index on non-array {:?}", expr.sort()),
                            );
                            return DerefProjectionResult::Unsupported;
                        }
                    }

                    let idx_name =
                        crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), *local);
                    let idx_expr = if let Some(expr) = self.env_lookup(&idx_name).cloned() {
                        expr
                    } else {
                        let idx_ssa_name = self.ssa_name_from_base(&idx_name, false);
                        match self.ctx.lookup_var(&idx_ssa_name).cloned() {
                            Some(expr) => expr,
                            None if fallthrough_on_failure => {
                                return DerefProjectionResult::Fallthrough;
                            }
                            None => {
                                self.ctx.unsupported(
                                    context_label,
                                    format!("Index local not found: {}", idx_name),
                                );
                                return DerefProjectionResult::Unsupported;
                            }
                        }
                    };

                    let idx_coerced = match idx_expr.sort().bitvec_width() {
                        Some(w) if w == POINTER_WIDTH => idx_expr,
                        Some(w) if w < POINTER_WIDTH => idx_expr.zero_extend(POINTER_WIDTH - w),
                        _ if fallthrough_on_failure => return DerefProjectionResult::Fallthrough, // non-enum: Option<u32> bitvec width
                        _ => {
                            // non-enum: Option<u32> bitvec width
                            self.ctx.unsupported(
                                context_label,
                                format!("Index sort is not bitvector: {:?}", idx_expr.sort()),
                            );
                            return DerefProjectionResult::Unsupported;
                        }
                    };
                    expr = expr.select(idx_coerced);
                    debug!("apply_post_deref: Index projection on array");
                }
                ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
                    if !expr.sort().is_array() {
                        if let Some(backing_array) = Self::post_deref_backing_array(&expr) {
                            expr = backing_array;
                        } else if fallthrough_on_failure {
                            return DerefProjectionResult::Fallthrough;
                        } else {
                            self.ctx.unsupported(
                                context_label,
                                format!("ConstantIndex on non-array {:?}", expr.sort()),
                            );
                            return DerefProjectionResult::Unsupported;
                        }
                    }
                    let Some(actual_offset) =
                        constant_index_offset(*offset, *min_length, *from_end)
                    else {
                        if fallthrough_on_failure {
                            return DerefProjectionResult::Fallthrough;
                        }
                        self.ctx.unsupported(
                            context_label,
                            format!(
                                "ConstantIndex from_end requires runtime slice length: \
                                 offset={offset}, min_length={min_length}"
                            ),
                        );
                        return DerefProjectionResult::Unsupported;
                    };
                    let idx_expr = Expr::bitvec_const(actual_offset as i128, POINTER_WIDTH);
                    expr = expr.select(idx_expr);
                    debug!("apply_post_deref: ConstantIndex at offset {}", offset);
                }
                ProjectionElem::Subslice { from, to, from_end } => {
                    // Part of #3306: SubSlice array extraction.
                    if !expr.sort().is_array() {
                        if let Some(backing_array) = Self::post_deref_backing_array(&expr) {
                            expr = backing_array;
                        } else if fallthrough_on_failure {
                            return DerefProjectionResult::Fallthrough;
                        } else {
                            self.ctx.unsupported(
                                context_label,
                                format!("Subslice on non-array {:?}", expr.sort()),
                            );
                            return DerefProjectionResult::Unsupported;
                        }
                    }
                    // Identity only for `[0..len-0]`. For `from_end=false`,
                    // `[0..0]` is empty and must not alias the full source.
                    if *from == 0 && *to == 0 && *from_end {
                        debug!("apply_post_deref: identity Subslice (full array)");
                    } else if let Some(arr_sort) = expr.sort().array_sort() {
                        // General case: build result[i] = src[from + i].
                        // For from_end=true, we need a bounded iteration; use a
                        // safe upper bound derived from from/to.
                        let start = *from as usize;
                        let elem_sort = arr_sort.element_sort.clone();
                        let result_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), elem_sort);
                        let name = self.ctx.fresh_name("subslice_arr");
                        let _ = self.ctx.declare_var(&name, result_sort);
                        // Without runtime length, construct a shifted view for a
                        // bounded number of elements. For from_end=false, range is
                        // [from..to]. For from_end=true, we can't determine the
                        // upper bound statically — fall through.
                        if *from_end {
                            if fallthrough_on_failure {
                                return DerefProjectionResult::Fallthrough;
                            }
                            self.ctx.unsupported(
                                context_label,
                                format!("Subslice from_end with from={} to={}", from, to),
                            );
                            return DerefProjectionResult::Unsupported;
                        }
                        let end = *to as usize;
                        let Some(result_len) = end.checked_sub(start) else {
                            if fallthrough_on_failure {
                                return DerefProjectionResult::Fallthrough;
                            }
                            self.ctx.unsupported(
                                context_label,
                                format!("Subslice end {end} precedes start {start}"),
                            );
                            return DerefProjectionResult::Unsupported;
                        };
                        let mut result = Expr::var(&name, expr.sort().clone());
                        for i in 0..result_len {
                            let src_idx = Expr::bitvec_const((start + i) as u128, POINTER_WIDTH);
                            let dst_idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                            let elem = expr.clone().select(src_idx);
                            result = result.store(dst_idx, elem);
                        }
                        expr = result;
                    } else if fallthrough_on_failure {
                        return DerefProjectionResult::Fallthrough;
                    } else {
                        self.ctx.unsupported(
                            context_label,
                            format!("Subslice on unknown sort {:?}", expr.sort()),
                        );
                        return DerefProjectionResult::Unsupported;
                    }
                }
                _ => {
                    // external enum: ProjectionElem
                    if fallthrough_on_failure {
                        return DerefProjectionResult::Fallthrough;
                    }
                    self.ctx.unsupported(
                        context_label,
                        format!("Unsupported projection after Deref: {:?}", proj),
                    );
                    return DerefProjectionResult::Unsupported;
                }
            }
        }
        DerefProjectionResult::Success(expr)
    }
}
