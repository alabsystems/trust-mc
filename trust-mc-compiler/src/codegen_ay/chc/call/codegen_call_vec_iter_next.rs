// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Split VecIntoIter::next branch construction for CHC call emission.

use std::collections::HashSet;

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::Operand;
use tracing::debug;

use crate::codegen_ay::chc::CollectionCallResult;
use crate::codegen_ay::types::{CtorFieldExt, POINTER_WIDTH};

use super::ChcCtx;
use super::codegen_ctx::types::CollectionProjectionKind;
use super::stubs_option_helpers::OptionHelpers;

pub(super) fn translate_vec_into_iter_next_branches(
    ctx: &mut ChcCtx<'_, '_>,
    args: &[Operand],
    modified_locals: &HashSet<usize>,
) -> Option<Vec<CollectionCallResult>> {
    let iter_arg = args.first()?;
    let projected_state = projected_vec_into_iter_state(ctx, iter_arg, modified_locals);
    let (iter_and_vec, pos, len, data) = if let Some(state) = projected_state.as_ref() {
        (None, state.pos.clone(), state.len.clone(), state.data.clone())
    } else {
        let iter = ctx.get_collection_arg(iter_arg, modified_locals)?;
        let iter_sort = iter.sort().clone();
        let iter_dt = iter_sort.datatype_sort()?;
        let iter_ctor = iter_dt.constructors.first()?;
        let vec = constructor_field_expr(&iter, &iter_dt.name, iter_ctor, "fld_vec")?;
        let pos = constructor_field_expr(&iter, &iter_dt.name, iter_ctor, "fld_pos")?;
        let vec_sort = vec.sort().clone();
        let vec_dt = vec_sort.datatype_sort()?;
        let vec_ctor = vec_dt.constructors.first()?;

        let len = constructor_field_expr(&vec, &vec_dt.name, vec_ctor, "fld_len")?;
        let data = constructor_field_expr(&vec, &vec_dt.name, vec_ctor, "fld_data")?;
        (Some((iter, vec)), pos, len, data)
    };
    let data_sort = data.sort().array_sort()?;
    if &data_sort.index_sort != pos.sort() {
        return None;
    }

    if let Some(state) = projected_state.as_ref()
        && let Some((concrete_elems, concrete_len_constraint)) =
            concrete_vec_into_iter_elems(ctx, iter_arg, &len, &data_sort.element_sort)
        && let Some(branches) = projected_concrete_vec_into_iter_next_branches(
            state,
            &pos,
            &len,
            concrete_elems,
            concrete_len_constraint,
        )
    {
        debug!("vec_iter: emitting position-specialized concrete VecIntoIter::next branches");
        return Some(branches);
    }

    let (elem, concrete_constraints) =
        concrete_vec_into_iter_elem(ctx, iter_arg, &pos, &len, &data_sort.element_sort)
            .map_or_else(
                || (data.select(pos.clone()), Vec::new()),
                |(elem, constraint)| (elem, vec![constraint]),
            );
    let in_bounds = pos.clone().bvult(len.clone());
    let pos_in_range = pos.clone().bvule(len.clone());
    let one = Expr::bitvec_const(1u64, pos.sort().bitvec_width().unwrap_or(POINTER_WIDTH));
    let advanced_pos = pos.clone().bvadd(one);
    let advanced_pos_in_range = advanced_pos.clone().bvule(len.clone());
    let exhausted_pos_is_len = pos.eq(len.clone());

    let (advanced_iter, exhausted_iter, some_update_fields, none_update_fields) =
        if let Some(state) = projected_state {
            (
                None,
                None,
                Some((state.iter_local, state.fields_with_pos(advanced_pos.clone()))),
                Some((state.iter_local, state.fields_with_pos(len.clone()))),
            )
        } else {
            let (iter, vec) = iter_and_vec?;
            let iter_sort = iter.sort().clone();
            let iter_dt = iter_sort.datatype_sort()?;
            let iter_ctor = iter_dt.constructors.first()?;
            let iter_dt_name = iter_dt.name.clone();
            let iter_ctor_name = iter_ctor.name.clone();
            (
                Some(Expr::datatype_constructor(
                    &iter_dt_name,
                    &iter_ctor_name,
                    vec![vec.clone(), advanced_pos],
                    iter_sort.clone(),
                )),
                Some(Expr::datatype_constructor(
                    &iter_dt_name,
                    &iter_ctor_name,
                    vec![vec, len.clone()],
                    iter_sort,
                )),
                None,
                None,
            )
        };

    debug!("vec_iter: emitting split VecIntoIter::next branches");
    let mut some_constraints = vec![pos_in_range.clone(), in_bounds.clone(), advanced_pos_in_range];
    some_constraints.extend(concrete_constraints.clone());
    let mut none_constraints = vec![pos_in_range, in_bounds.not(), exhausted_pos_is_len];
    none_constraints.extend(concrete_constraints);
    Some(vec![
        CollectionCallResult {
            map_update: advanced_iter,
            map_update_fields: some_update_fields,
            result: Some(elem.clone()),
            result_is_some: Some(Expr::bool_const(true)),
            len_update: None,
            present_update: None,
            result_fields: None,
            constraints: some_constraints,
            force_error: false,
            aux_targets_dest: false,
        },
        CollectionCallResult {
            map_update: exhausted_iter,
            map_update_fields: none_update_fields,
            result: Some(elem),
            result_is_some: Some(Expr::bool_const(false)),
            len_update: None,
            present_update: None,
            result_fields: Some(Vec::new()),
            constraints: none_constraints,
            force_error: false,
            aux_targets_dest: false,
        },
    ])
}

struct ProjectedVecIntoIterState {
    iter_local: usize,
    fields: Vec<Option<Expr>>,
    pos: Expr,
    len: Expr,
    data: Expr,
}

impl ProjectedVecIntoIterState {
    fn fields_with_pos(&self, pos: Expr) -> Vec<Option<Expr>> {
        let mut fields = self.fields.clone();
        if let Some(last) = fields.last_mut() {
            *last = Some(pos);
        }
        fields
    }
}

fn projected_vec_into_iter_state(
    ctx: &ChcCtx<'_, '_>,
    iter_arg: &Operand,
    modified_locals: &HashSet<usize>,
) -> Option<ProjectedVecIntoIterState> {
    let iter_local = resolve_operand_local(ctx, iter_arg)?;
    if ctx.collections.projection_locals.get(&iter_local).copied()
        != Some(CollectionProjectionKind::VecIntoIter)
    {
        return None;
    }
    let field_count = ctx.flattened_field_count(iter_local);
    if field_count < 5 {
        return None;
    }
    let fields: Vec<Option<Expr>> = (0..field_count)
        .map(|field_idx| ctx.flattened_local_field_expr(iter_local, field_idx, modified_locals))
        .collect();
    let pos = fields.get(field_count - 1)?.as_ref()?.clone();
    let len = fields.get(1)?.as_ref()?.clone();
    let data = fields.get(3)?.as_ref()?.clone();
    Some(ProjectedVecIntoIterState { iter_local, fields, pos, len, data })
}

fn constructor_field_expr(
    expr: &Expr,
    dt_name: &str,
    ctor: &ay_bindings::DatatypeConstructor,
    field_name: &str,
) -> Option<Expr> {
    let field_idx = ctor.fields.iter().position(|field| &*field.name == field_name)?;
    if let ExprValue::DatatypeConstructor { args, .. } = expr.value()
        && let Some(arg) = args.get(field_idx)
    {
        return Some(arg.clone());
    }
    let field = ctor.field(field_name)?;
    Some(expr.clone().field_select(dt_name, field_name, field.sort.clone()))
}

fn projected_concrete_vec_into_iter_next_branches(
    state: &ProjectedVecIntoIterState,
    pos: &Expr,
    len: &Expr,
    concrete_elems: Vec<Expr>,
    concrete_len_constraint: Expr,
) -> Option<Vec<CollectionCallResult>> {
    let pos_width = pos.sort().bitvec_width()?;
    let mut branches = Vec::with_capacity(concrete_elems.len() + 1);

    for (idx, elem) in concrete_elems.iter().cloned().enumerate() {
        let idx_expr = Expr::bitvec_const(idx as u64, pos_width);
        let next_pos = Expr::bitvec_const((idx + 1) as u64, pos_width);
        branches.push(CollectionCallResult {
            map_update: None,
            map_update_fields: Some((state.iter_local, state.fields_with_pos(next_pos))),
            result: Some(elem),
            result_is_some: Some(Expr::bool_const(true)),
            len_update: None,
            present_update: None,
            result_fields: None,
            constraints: vec![concrete_len_constraint.clone(), pos.clone().eq(idx_expr)],
            force_error: false,
            aux_targets_dest: false,
        });
    }

    branches.push(CollectionCallResult {
        map_update: None,
        map_update_fields: Some((state.iter_local, state.fields_with_pos(len.clone()))),
        result: concrete_elems.last().cloned(),
        result_is_some: Some(Expr::bool_const(false)),
        len_update: None,
        present_update: None,
        result_fields: Some(Vec::new()),
        constraints: vec![concrete_len_constraint, pos.clone().eq(len.clone())],
        force_error: false,
        aux_targets_dest: false,
    });

    Some(branches)
}

fn concrete_vec_into_iter_elem(
    ctx: &ChcCtx<'_, '_>,
    iter_arg: &Operand,
    pos: &Expr,
    len: &Expr,
    elem_sort: &Sort,
) -> Option<(Expr, Expr)> {
    let (concrete_elems, len_constraint) =
        concrete_vec_into_iter_elems(ctx, iter_arg, len, elem_sort)?;
    let pos_width = pos.sort().bitvec_width()?;
    let mut result = concrete_elems.last()?.clone();
    for (idx, elem) in concrete_elems.iter().enumerate().rev() {
        let idx_expr = Expr::bitvec_const(idx as u64, pos_width);
        result = Expr::ite(pos.clone().eq(idx_expr), elem.clone(), result);
    }
    Some((result, len_constraint))
}

fn concrete_vec_into_iter_elems(
    ctx: &ChcCtx<'_, '_>,
    iter_arg: &Operand,
    len: &Expr,
    elem_sort: &Sort,
) -> Option<(Vec<Expr>, Expr)> {
    let iter_local = resolve_operand_local(ctx, iter_arg)?;
    let concrete_elems = ctx
        .collections
        .adapter_source_data
        .get(&iter_local)
        .and_then(|data| data.concrete_elems.as_ref())?;
    if concrete_elems.is_empty() {
        return None;
    }
    let len_width = len.sort().bitvec_width()?;
    let elems = concrete_elems
        .iter()
        .cloned()
        .map(|elem| ctx.coerce_value_to_sort(elem, elem_sort, false))
        .collect::<Option<Vec<_>>>()?;
    let count = Expr::bitvec_const(concrete_elems.len() as u64, len_width);
    debug!(
        iter_local,
        elem_count = concrete_elems.len(),
        "vec_iter: using concrete VecIntoIter element payload"
    );
    Some((elems, len.clone().eq(count)))
}

fn resolve_operand_local(ctx: &ChcCtx<'_, '_>, operand: &Operand) -> Option<usize> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            let ref_local = place.local;
            Some(ctx.ref_resolution.ref_targets.get(&ref_local).map_or(ref_local, |rt| rt.local))
        }
        _ => None,
    }
}
