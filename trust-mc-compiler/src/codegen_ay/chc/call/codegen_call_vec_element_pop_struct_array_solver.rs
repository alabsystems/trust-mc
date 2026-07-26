// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `ArraySolver` helpers for struct-embedded Vec pop handling.

use ay_bindings::{Expr, Sort};

use super::ChcCtx;
use super::FieldProjection;
use super::codegen_call_vec::ChcVecFields;
use super::codegen_ctx::types::ArraySolverAuxState;
use super::codegen_stmt_flatten::collect_leaf_exprs;
use crate::codegen_ay::names::vec_layout;

pub(super) const ARRAYSOLVER_FIELD_ASSIGN_TERMS: usize = 0;
pub(super) const ARRAYSOLVER_FIELD_ASSIGN_VALUES: usize = 1;
pub(super) const ARRAYSOLVER_FIELD_TRAIL_TERMS: usize = 2;
pub(super) const ARRAYSOLVER_FIELD_TRAIL_PREV_PRESENT: usize = 3;
pub(super) const ARRAYSOLVER_FIELD_TRAIL_PREV_VALUES: usize = 4;
pub(super) const ARRAYSOLVER_FIELD_SCOPES: usize = 5;

pub(super) fn overwrite_flattened_vec_leaves(
    values: &mut [Option<Expr>],
    base: usize,
    vec_expr: &Expr,
) -> bool {
    let mut leaf_values = Vec::new();
    collect_leaf_exprs(vec_expr, &mut leaf_values);
    if leaf_values.len() != vec_layout::FIELD_COUNT || values.len() < base + vec_layout::FIELD_COUNT
    {
        return false;
    }
    for (offset, leaf) in leaf_values.into_iter().enumerate() {
        values[base + offset] = leaf;
    }
    true
}

pub(super) fn array_solver_pop_aux_for_scopes_field<'ctx, 'tcx, 'body>(
    ctx: &'ctx ChcCtx<'tcx, 'body>,
    _coll_local: usize,
    _field_projs: &[FieldProjection],
) -> Option<&'ctx ArraySolverAuxState> {
    // The legacy scopes-pop snapshot sidecar restored visible assign_terms /
    // assign_values Vecs from undeclared aux arrays. ArraySolver pop now routes
    // through the dedicated shadow dispatcher, so fallback Vec-pop helpers must
    // not reference the stale snapshot vars.
    let _ = ctx;
    None
}

pub(super) fn array_solver_pop_scope_snapshot_select(
    in_name: &str,
    element_sort: &Sort,
    depth: Expr,
) -> Expr {
    let snapshot_sort = Sort::array(Sort::bitvec(64), element_sort.clone());
    Expr::var(in_name, snapshot_sort).select(depth)
}

fn array_solver_rebuild_vec_with_len(vec_expr: Expr, new_len: Expr) -> Option<Expr> {
    let ChcVecFields { vec_sort, ptr, cap, data, .. } = ChcVecFields::extract(vec_expr)?;
    let dt_name = vec_sort.datatype_name()?.to_owned();
    let ctor_name = crate::codegen_ay::names::cons_name(&dt_name);
    Some(Expr::datatype_constructor(&dt_name, ctor_name, vec![ptr, new_len, cap, data], vec_sort))
}

pub(super) fn array_solver_pop_restored_struct_after_scopes_pop(
    struct_in: Expr,
    field_projs: &[FieldProjection],
    aux: &ArraySolverAuxState,
    new_scopes: Expr,
    marker: Expr,
    is_nonempty: Expr,
    new_depth: Expr,
) -> Option<Expr> {
    let current_assign_terms = ChcCtx::apply_field_selections(
        struct_in.clone(),
        &[FieldProjection {
            field_idx: ARRAYSOLVER_FIELD_ASSIGN_TERMS,
            cons_idx: None,
            field_ty: None,
        }],
    )?;
    let current_assign_values = ChcCtx::apply_field_selections(
        struct_in.clone(),
        &[FieldProjection {
            field_idx: ARRAYSOLVER_FIELD_ASSIGN_VALUES,
            cons_idx: None,
            field_ty: None,
        }],
    )?;
    let restored_assign_terms = Expr::ite(
        is_nonempty.clone(),
        array_solver_pop_scope_snapshot_select(
            &aux.scope_snap_assign_terms_var,
            current_assign_terms.sort(),
            new_depth.clone(),
        ),
        current_assign_terms,
    );
    let restored_assign_values = Expr::ite(
        is_nonempty.clone(),
        array_solver_pop_scope_snapshot_select(
            &aux.scope_snap_assign_values_var,
            current_assign_values.sort(),
            new_depth,
        ),
        current_assign_values,
    );

    let current_trail_terms = ChcCtx::apply_field_selections(
        struct_in.clone(),
        &[FieldProjection {
            field_idx: ARRAYSOLVER_FIELD_TRAIL_TERMS,
            cons_idx: None,
            field_ty: None,
        }],
    )?;
    let current_trail_prev_present = ChcCtx::apply_field_selections(
        struct_in.clone(),
        &[FieldProjection {
            field_idx: ARRAYSOLVER_FIELD_TRAIL_PREV_PRESENT,
            cons_idx: None,
            field_ty: None,
        }],
    )?;
    let current_trail_prev_values = ChcCtx::apply_field_selections(
        struct_in.clone(),
        &[FieldProjection {
            field_idx: ARRAYSOLVER_FIELD_TRAIL_PREV_VALUES,
            cons_idx: None,
            field_ty: None,
        }],
    )?;

    let current_trail_terms_len = ChcVecFields::extract(current_trail_terms.clone())?.len;
    let current_trail_prev_present_len =
        ChcVecFields::extract(current_trail_prev_present.clone())?.len;
    let current_trail_prev_values_len =
        ChcVecFields::extract(current_trail_prev_values.clone())?.len;
    let restored_trail_len = Expr::ite(is_nonempty.clone(), marker, current_trail_terms_len);
    let restored_trail_prev_present_len =
        Expr::ite(is_nonempty.clone(), restored_trail_len.clone(), current_trail_prev_present_len);
    let restored_trail_prev_values_len =
        Expr::ite(is_nonempty, restored_trail_len.clone(), current_trail_prev_values_len);

    let restored_trail_terms =
        array_solver_rebuild_vec_with_len(current_trail_terms, restored_trail_len)?;
    let restored_trail_prev_present = array_solver_rebuild_vec_with_len(
        current_trail_prev_present,
        restored_trail_prev_present_len,
    )?;
    let restored_trail_prev_values = array_solver_rebuild_vec_with_len(
        current_trail_prev_values,
        restored_trail_prev_values_len,
    )?;

    let with_scopes = ChcCtx::apply_projection_update(&struct_in, field_projs, new_scopes)?;
    let with_assign_terms = ChcCtx::apply_projection_update(
        &with_scopes,
        &[FieldProjection {
            field_idx: ARRAYSOLVER_FIELD_ASSIGN_TERMS,
            cons_idx: None,
            field_ty: None,
        }],
        restored_assign_terms,
    )?;
    let with_assign_values = ChcCtx::apply_projection_update(
        &with_assign_terms,
        &[FieldProjection {
            field_idx: ARRAYSOLVER_FIELD_ASSIGN_VALUES,
            cons_idx: None,
            field_ty: None,
        }],
        restored_assign_values,
    )?;
    let with_trail_terms = ChcCtx::apply_projection_update(
        &with_assign_values,
        &[FieldProjection {
            field_idx: ARRAYSOLVER_FIELD_TRAIL_TERMS,
            cons_idx: None,
            field_ty: None,
        }],
        restored_trail_terms,
    )?;
    let with_trail_prev_present = ChcCtx::apply_projection_update(
        &with_trail_terms,
        &[FieldProjection {
            field_idx: ARRAYSOLVER_FIELD_TRAIL_PREV_PRESENT,
            cons_idx: None,
            field_ty: None,
        }],
        restored_trail_prev_present,
    )?;
    ChcCtx::apply_projection_update(
        &with_trail_prev_present,
        &[FieldProjection {
            field_idx: ARRAYSOLVER_FIELD_TRAIL_PREV_VALUES,
            cons_idx: None,
            field_ty: None,
        }],
        restored_trail_prev_values,
    )
}
