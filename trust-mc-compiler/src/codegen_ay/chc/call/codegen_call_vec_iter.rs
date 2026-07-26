// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Vec iterator call handling — `codegen_call_vec_iter` impl.
//!
//! Split from `codegen_call_vec.rs` for module size (Part of #4135).
//! Handles `StubKind::Vec*Iter*` stubs that produce `Option<T>` results
//! via the `translate_vec_iter_call` core, including flattened and
//! non-flattened Option destination paths.

use std::sync::Arc;

use ay_bindings::Expr;
use rustc_public::mir::Operand;

use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{
    CtorFieldExt, flattenable_datatype_sort_width, unflatten_bitvec_to_datatype,
};

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_call_vec_iter_next::translate_vec_into_iter_next_branches;
use super::codegen_rules::CodegenRules;
use super::stubs_option_helpers::OptionHelpers;
use tracing::{debug, warn};

/// Vec iterator call implementation for `ChcCtx`.
///
/// This is the implementation body of `CallVec::codegen_call_vec_iter`.
/// Separated into its own module to keep `codegen_call_vec.rs` under 500 LOC.
pub(in crate::codegen_ay::chc) fn codegen_call_vec_iter_impl(
    ctx: &mut ChcCtx<'_, '_>,
    stub: StubKind,
    dcx: &DispatchCallContext<'_>,
) {
    let args = dcx.args;
    let destination = dcx.destination;
    let target = dcx.target;
    let from_app = dcx.from_app;
    let stmt_constraints = dcx.stmt_constraints;
    let modified_locals = dcx.modified_locals;
    let dest_local: usize = destination.local;
    let Some(dest_vec_idx) = ctx.try_state_idx_for_local(dest_local) else {
        debug!(dest_local, "CHC: vec_iter dest not in state map — sound over-approx");
        ctx.record_sound_fallback_reason("state_idx_missing_vec_iter_dest");
        if let Some(target) = target {
            emit_sound_fallback_goto(
                ctx,
                from_app,
                *target,
                modified_locals,
                &[dest_local],
                stmt_constraints,
            );
        }
        return;
    };
    debug!("vec_iter_stub stub={:?} has_target={} dest={}", stub, target.is_some(), dest_local);
    if let Some(target) = target {
        let results = if matches!(stub, StubKind::IntoIterNext)
            && let Some(branches) =
                translate_vec_into_iter_next_branches(ctx, args, modified_locals)
        {
            branches
        } else if let Some(result) =
            ctx.translate_vec_iter_call(stub, args, modified_locals, Some(dest_local))
        {
            vec![result]
        } else {
            // Sound over-approximation: unrecognized vec iterator call, leave unconstrained.
            let new_output_args = ctx.build_output_args(modified_locals, &[]);
            ctx.emit_goto_rule_extra(from_app, *target, &new_output_args, stmt_constraints, []);
            ctx.record_sound_fallback_reason("vec_iter_unrecognized");
            return;
        };

        let mut emitted_into_iter_pointer_check = false;
        for result in results {
            // Fail closed when the stub asked to. `CollectionCallResult::forced_failure()`
            // signals this through `force_error`, NOT through a body `false` constraint
            // (W4:4053 changed it — `constraints` is empty). Dropping the flag here left
            // this lane emitting an ordinary unconstrained successor transition while
            // `IteratorUnsoundness` sits in the driver's `FAIL_CLOSED_CATEGORIES`
            // ("these produce error rules ... so no demotion is needed",
            // trust-mc-driver/src/unsoundness_counts.rs) — i.e. a false-Safe channel:
            // counter incremented, no demotion applied, and no error rule in the VC.
            // Mirrors `codegen_call_collections.rs` / `codegen_call_hashmap_iter.rs`.
            if result.force_error {
                ctx.emit_untranslatable_assert_rule(
                    from_app,
                    stmt_constraints,
                    *target,
                    "Vec iter stub requested fail-closed error",
                );
                return;
            }

            // Part of #2486: collect extras instead of stmt_constraints.to_vec().
            let mut extra_constraints: Vec<Expr> = Vec::new();
            let mut extra_dests: Vec<usize> = Vec::new();

            // Part of #3386: consume any soundness constraints the stub attached.
            extra_constraints.extend(result.constraints);

            if let Some((iter_local, field_values)) = result.map_update_fields {
                ctx.collections.adapter_at_start.remove(&iter_local);
                if ctx.constrain_flattened_fields_for_call(
                    iter_local,
                    &field_values,
                    &mut extra_constraints,
                ) {
                    extra_dests.push(iter_local);
                } else {
                    ctx.record_sound_fallback_reason("flattened_fields_unconstrained");
                }
                debug!(
                    iter_local,
                    num_fields = field_values.len(),
                    "vec_iter: applied direct projected iterator update"
                );
            } else if let Some(new_iter) = result.map_update
                && !args.is_empty()
                && let Operand::Copy(place) | Operand::Move(place) = &args[0]
            {
                let ref_local: usize = place.local;
                let iter_local =
                    ctx.ref_resolution.ref_targets.get(&ref_local).map_or(ref_local, |rt| rt.local);
                ctx.collections.adapter_at_start.remove(&iter_local);
                // Part of #2874 Step 3: When the iter local is projected,
                // decompose the Datatype back into flattened field constraints.
                if let Some(kind) = ctx.collections.projection_locals.get(&iter_local).copied()
                    && let Some(field_values) =
                        ctx.decompose_projected_iterator_to_fields(&new_iter, kind)
                {
                    if ctx.constrain_flattened_fields_for_call(
                        iter_local,
                        &field_values,
                        &mut extra_constraints,
                    ) {
                        extra_dests.push(iter_local);
                    } else {
                        ctx.record_sound_fallback_reason("flattened_fields_unconstrained");
                    }
                    debug!(
                        iter_local,
                        ?kind,
                        num_fields = field_values.len(),
                        "vec_iter: decomposed projected iterator update (#2874)"
                    );
                } else {
                    // Non-projected path: use local_to_state_idx for correct index.
                    if let Some(iter_vec_idx) = ctx.try_state_idx_for_local(iter_local) {
                        if let Some((out_name, out_sort)) =
                            ctx.state_var_mgr.output_state_vars.get(iter_vec_idx).cloned()
                        {
                            let iter_var = Expr::var(&*out_name, out_sort.clone());
                            if let Some(eq) = ctx.make_coerced_eq_constraint(
                                &iter_var,
                                new_iter,
                                &out_sort,
                                iter_local,
                                "codegen_call_vec_iter::iter_update",
                            ) {
                                extra_constraints.push(eq);
                            }
                            extra_dests.push(iter_local);
                        } else {
                            debug!(
                                "Vec iter state update skipped - no output_state_var for local {}",
                                iter_local
                            );
                        }
                    } else {
                        ctx.record_sound_fallback_reason("state_idx_missing_vec_iter_update");
                        debug!(
                            "Vec iter state update skipped - local {} not in state map",
                            iter_local
                        );
                    }
                }
            }

            let result_is_some = result.result_is_some;
            let result_fields = result.result_fields;
            if let Some(result_expr) = result.result {
                let result_expr =
                    super::codegen_call_vec_array_iter::canonical_zst_option_payload_for_local(
                        ctx,
                        dest_local,
                        result_expr.sort(),
                    )
                    .unwrap_or(result_expr);
                // Part of #3057: DT-free — when result_is_some is provided and
                // destination is flattened, write (is_some, value) directly without
                // creating intermediate Option Datatype expressions.
                if let Some(is_some_expr) = result_is_some.clone()
                    && ctx.flatten.flattened_tuple_locals.contains(&dest_local)
                {
                    let mut field_values: Vec<Option<Expr>> = vec![Some(is_some_expr)];
                    if let Some(fields) = result_fields {
                        field_values.extend(fields.into_iter().map(Some));
                    } else if result_expr.sort().is_bitvec() {
                        let payload_slot_count = ctx.flattened_field_count(dest_local);
                        let total_width = result_expr
                            .sort()
                            .bitvec_width()
                            .expect("guarded by is_bitvec() above");
                        let mut consumed_width = 0u32;
                        let mut payload_fields: Vec<Option<Expr>> = Vec::new();
                        let mut split_ok = true;

                        for slot_offset in 1..payload_slot_count {
                            let Some((_, out_sort)) = ctx
                                .state_var_mgr
                                .output_state_vars
                                .get(dest_vec_idx + slot_offset)
                                .cloned()
                            else {
                                split_ok = false;
                                break;
                            };
                            let Some(field_width) = (if out_sort.is_bool() {
                                Some(1)
                            } else {
                                out_sort
                                    .bitvec_width()
                                    .or_else(|| flattenable_datatype_sort_width(&out_sort))
                            }) else {
                                split_ok = false;
                                break;
                            };
                            consumed_width += field_width;
                            if consumed_width > total_width {
                                split_ok = false;
                                break;
                            }
                            let lo = total_width - consumed_width;
                            let hi = lo + field_width - 1;
                            let field_bits =
                                if hi == total_width - 1 && lo == 0 && field_width == total_width {
                                    result_expr.clone()
                                } else {
                                    result_expr.clone().extract(hi, lo)
                                };
                            let field_expr = if out_sort.datatype_sort().is_some() {
                                unflatten_bitvec_to_datatype(&field_bits, &out_sort)
                            } else {
                                ctx.coerce_value_to_sort(field_bits, &out_sort, false)
                            };
                            if let Some(expr) = field_expr {
                                payload_fields.push(Some(expr));
                            } else {
                                split_ok = false;
                                break;
                            }
                        }

                        if split_ok && consumed_width == total_width {
                            field_values.extend(payload_fields);
                        } else {
                            let mut payload_fields = Vec::new();
                            super::codegen_stmt_flatten::collect_leaf_exprs(
                                &result_expr,
                                &mut payload_fields,
                            );
                            field_values.extend(payload_fields);
                        }
                    } else {
                        let mut payload_fields = Vec::new();
                        super::codegen_stmt_flatten::collect_leaf_exprs(
                            &result_expr,
                            &mut payload_fields,
                        );
                        field_values.extend(payload_fields);
                    }
                    while field_values.len() < ctx.flattened_field_count(dest_local) {
                        field_values.push(None);
                    }
                    if ctx.constrain_flattened_fields_for_call(
                        dest_local,
                        &field_values,
                        &mut extra_constraints,
                    ) {
                        extra_dests.push(dest_local);
                    } else {
                        ctx.record_sound_fallback_reason("flattened_fields_unconstrained");
                    }
                    debug!(dest_local, "vec_iter: DT-free flattened Option result (#3057)");
                } else if ctx.flatten.flattened_tuple_locals.contains(&dest_local)
                    && result_expr.sort().is_datatype()
                {
                    if ctx.flatten.flattened_enum_discr.contains_key(&dest_local) {
                        // Part of #2912: When dest is a flattened Option,
                        // decompose the actual result Datatype into (discriminant, payload)
                        // using option_is_some/option_unwrap_value — matching the
                        // HashMap get handler pattern (codegen_call_collections.rs).
                        // Previous code used fresh unconstrained adapter symbols,
                        // which discarded the stub's semantic result.
                        let mut field_values = vec![
                            Some(ctx.option_is_some(result_expr.clone())),
                            ctx.option_unwrap_value_on_some_path(result_expr),
                        ];
                        while field_values.len() < ctx.flattened_field_count(dest_local) {
                            field_values.push(None);
                        }
                        if ctx.constrain_flattened_fields_for_call(
                            dest_local,
                            &field_values,
                            &mut extra_constraints,
                        ) {
                            extra_dests.push(dest_local);
                        } else {
                            ctx.record_sound_fallback_reason("flattened_fields_unconstrained");
                        }
                        debug!(
                            dest_local,
                            "vec_iter: decomposed Option result to flattened fields (#2912)"
                        );
                    } else if let Some(kind) =
                        ctx.collections.projection_locals.get(&dest_local).copied()
                    {
                        // Part of #2912: When dest is a deep-flattened collection
                        // projection local (e.g. VecIntoIter with 5 scalar slots),
                        // decompose the Datatype result into per-field constraints.
                        // Without this, the Datatype sort (VecIntoIter_bv32) would
                        // be equated against the first flattened slot (bv64),
                        // causing a Z3 sort mismatch error.
                        if let Some(field_values) =
                            ctx.decompose_projected_iterator_to_fields(&result_expr, kind)
                        {
                            if ctx.constrain_flattened_fields_for_call(
                                dest_local,
                                &field_values,
                                &mut extra_constraints,
                            ) {
                                extra_dests.push(dest_local);
                            } else {
                                ctx.record_sound_fallback_reason("flattened_fields_unconstrained");
                            }
                            debug!(
                                dest_local,
                                ?kind,
                                num_fields = field_values.len(),
                                "vec_iter: decomposed projected collection result \
                                 to flattened fields (#2912)"
                            );
                        } else {
                            warn!(
                                dest_local,
                                ?kind,
                                "vec_iter: failed to decompose collection projection \
                                 result — flattened slots will be unconstrained"
                            );
                        }
                    }
                } else if let Some(is_some_expr) = result_is_some
                    && let Some((out_name, out_sort)) =
                        ctx.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
                {
                    let some_expr = ctx.make_some_expr_for_option(result_expr, &out_sort);
                    let none_expr = ctx.make_none_expr_for_option(&out_sort);
                    if let (Some(some_expr), Some(none_expr)) = (some_expr, none_expr) {
                        let option_result = Expr::ite(is_some_expr, some_expr, none_expr);
                        let dest_var = Expr::var(&*out_name, out_sort.clone());
                        if let Some(eq) = ctx.make_coerced_eq_constraint(
                            &dest_var,
                            option_result,
                            &out_sort,
                            dest_local,
                            "codegen_call_vec_iter::option_result",
                        ) {
                            extra_constraints.push(eq);
                        }
                        extra_dests.push(dest_local);
                    } else {
                        warn!(
                            dest_local,
                            ?out_sort,
                            "vec_iter: failed to rebuild non-flattened Option result"
                        );
                    }
                } else if let Some(out_name) = ctx
                    .state_var_mgr
                    .output_state_vars
                    .get(dest_vec_idx)
                    .map(|(n, _)| Arc::clone(n))
                {
                    let actual_sort = result_expr.sort().clone();
                    let dest_var = Expr::var(&*out_name, actual_sort.clone());
                    if let Some(eq) = ctx.make_coerced_eq_constraint(
                        &dest_var,
                        result_expr,
                        &actual_sort,
                        dest_local,
                        "codegen_call_vec_iter",
                    ) {
                        extra_constraints.push(eq);
                    }
                    extra_dests.push(dest_local);

                    // Keep state variable metadata aligned with iterator results.
                    // Vec iterator stubs can return datatypes even when the
                    // destination started with a scalar fallback sort.
                    if ctx.state_var_mgr.state_vars.get(dest_vec_idx).is_some() {
                        ctx.state_var_mgr.state_vars[dest_vec_idx].1 = actual_sort.clone();
                    }
                    ctx.state_var_mgr.output_state_vars[dest_vec_idx] = (out_name, actual_sort);
                } else {
                    debug!(
                        "Vec iter result storage skipped - no output_state_var for dest {}",
                        dest_local
                    );
                }
            }

            // When the iterator returns Option<&T> (e.g., slice::Iter<T>::next),
            // register the element value as a const_ref_value for the destination
            // local. This enables the subsequent MIR dereference `*val` to resolve
            // via const_ref_values instead of falling through to Mem-level memory
            // load (which would read unconstrained garbage from the heap).
            //
            // Use the INPUT state variable name for the payload field (not the raw
            // element expression). The raw expression references state variables
            // (e.g., `_main_2_fld3` for iterator pos) that are re-bound in each
            // CHC rule. By the time the dereference happens in a later block, the
            // pos variable has been incremented, making the symbolic expression
            // evaluate to the wrong array index. The input state variable name
            // (e.g., `_main_5_fld1`) is correctly bound in all subsequent rules.
            //
            // The Downcast+Field extraction `_18 = (_16 as Some).0` propagates
            // const_ref_values from _16 to _18 via the enum-payload-field path
            // in propagate_ref_metadata_for_assign.
            if matches!(stub, StubKind::IntoIterNext) {
                // For flattened destinations, the payload is at state index
                // dest_vec_idx + 1 (slot 0 = is_some discriminant, slot 1 = value).
                let payload_idx = dest_vec_idx + 1;
                if let Some((ref in_name, ref in_sort)) =
                    ctx.state_var_mgr.state_vars.get(payload_idx).cloned()
                {
                    let state_var_ref = Expr::var(&**in_name, in_sort.clone());
                    ctx.ref_resolution.const_ref_values.insert(dest_local, state_var_ref);
                }

                // Part of #4255: When extra_pointer_checks is on, emit provenance
                // error rule for the iterator's underlying Vec pointer. Vec::new()
                // invalidates obj_valid for dangling pointers (constructors.rs:46-88).
                // IntoIterNext uses abstract data[pos] instead of PtrAdd, so the
                // normal Check 4 path in stubs_ptr_overflow.rs never fires. We must
                // check provenance explicitly here.
                if !emitted_into_iter_pointer_check
                    && ctx.extra_pointer_checks
                    && !ctx.int_lift
                    && let Some(iter_arg) = args.first()
                    && let Some(iter) = ctx.get_collection_arg(iter_arg, modified_locals)
                {
                    let iter_sort = iter.sort().clone();
                    if let Some(iter_dt) = iter_sort.datatype_sort()
                        && let Some(iter_ctor) = iter_dt.constructors.first()
                        && let Some(vec_field) = iter_ctor.field("fld_vec")
                    {
                        let vec = iter.clone().field_select(
                            &iter_dt.name,
                            "fld_vec",
                            vec_field.sort.clone(),
                        );
                        let vec_sort = vec.sort().clone();
                        if let Some(vec_dt) = vec_sort.datatype_sort()
                            && let Some(vec_ctor) = vec_dt.constructors.first()
                            && let Some(ptr_field) = vec_ctor.field("fld_ptr")
                        {
                            let ptr =
                                vec.field_select(&vec_dt.name, "fld_ptr", ptr_field.sort.clone());
                            if let Some((obj_id, _offset)) = ctx.split_pointer(&ptr) {
                                let obj_valid = ctx.current_obj_valid_array();
                                // Part of #3221: track metadata access for pruning correctness.
                                ctx.mark_heap_metadata_read();
                                let is_valid = obj_valid.select(obj_id);
                                ctx.emit_error_rule_for_condition(
                                    from_app,
                                    is_valid,
                                    stmt_constraints,
                                    *target,
                                );
                                emitted_into_iter_pointer_check = true;
                                debug!(
                                    "CHC: emitted IntoIterNext provenance_valid error rule (#4255)"
                                );
                            }
                        }
                    }
                }
            }

            let new_output_args = ctx.build_output_args(modified_locals, &extra_dests);
            ctx.emit_goto_rule_extra(
                from_app,
                *target,
                &new_output_args,
                stmt_constraints,
                extra_constraints,
            );
        }
    } else {
        debug!("Vec iter stub {:?} has no target block (dest={})", stub, dest_local);
    }
}
