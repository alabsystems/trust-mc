// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Array and slice `Ord::cmp` support for BMC comparison codegen.

use ay_bindings::{Constraint, Expr, ExprValue, Sort};
use num_bigint::BigInt;
use rustc_public::mir::{Operand, Place, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::super::{IntoOption, StatementCodegen};

/// Maximum fixed lanes to unroll for direct array/slice `Ord::cmp`.
const MAX_ORD_LEXICO_LANES: usize = 16;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    pub(in crate::codegen_ay::statement) fn codegen_slice_or_array_ord_cmp(
        &mut self,
        lhs_arg: &Operand,
        rhs_arg: &Operand,
        lhs_raw: &Expr,
        rhs_raw: &Expr,
        is_signed: bool,
    ) -> Option<Expr> {
        let lhs_value = self.ord_resolved_slice_value(lhs_raw);
        let rhs_value = self.ord_resolved_slice_value(rhs_raw);

        let lhs = extract_ord_array_data(&lhs_value).or_else(|| {
            self.resolve_ord_operand_to_array(lhs_arg)
                .and_then(|expr| extract_ord_array_data(&expr))
        })?;
        let rhs = extract_ord_array_data(&rhs_value).or_else(|| {
            self.resolve_ord_operand_to_array(rhs_arg)
                .and_then(|expr| extract_ord_array_data(&expr))
        })?;

        let lhs_arr = lhs.sort().array_sort()?;
        let rhs_arr = rhs.sort().array_sort()?;
        if lhs_arr.index_sort != rhs_arr.index_sort || lhs_arr.element_sort != rhs_arr.element_sort
        {
            return None;
        }
        if !lhs_arr.element_sort.is_bitvec() {
            return None;
        }

        let idx_width = lhs_arr.index_sort.bitvec_width()?;
        if let (Some(lhs_len_expr), Some(rhs_len_expr)) =
            (ord_len_bv_from_expr(&lhs_value), ord_len_bv_from_expr(&rhs_value))
        {
            let unknown_name = self.ctx.fresh_name("ay_ord_cmp_unrolled_overflow");
            let unknown = self.ctx.declare_var(&unknown_name, Sort::bv32());
            return build_ord_lexicographic_cmp_symbolic_len(
                &lhs,
                &rhs,
                &lhs_len_expr,
                &rhs_len_expr,
                idx_width,
                is_signed,
                MAX_ORD_LEXICO_LANES,
                unknown,
            );
        }

        let lhs_len =
            ord_len_from_expr(&lhs_value).or_else(|| self.ord_len_from_mir_arg(lhs_arg))?;
        let rhs_len =
            ord_len_from_expr(&rhs_value).or_else(|| self.ord_len_from_mir_arg(rhs_arg))?;
        if lhs_len.max(rhs_len) > MAX_ORD_LEXICO_LANES {
            return None;
        }

        debug!(lhs_len, rhs_len, is_signed, "codegen_ord_cmp: direct lexicographic array/slice");
        build_ord_lexicographic_cmp(&lhs, &rhs, lhs_len, rhs_len, idx_width, is_signed)
    }

    fn ord_resolved_slice_value(&self, expr: &Expr) -> Expr {
        if ord_len_from_expr(expr).is_some() && extract_ord_array_data(expr).is_some() {
            return expr.clone();
        }

        self.ctx
            .program
            .commands()
            .iter()
            .rev()
            .find_map(|command| match command {
                Constraint::Assert { expr: asserted, .. } => {
                    ord_slice_constructor_bound_to(asserted, expr)
                }
                _ => None,
            })
            .unwrap_or_else(|| expr.clone())
    }

    fn ord_len_from_mir_arg(&self, arg: &Operand) -> Option<usize> {
        let ty = arg.ty(self.body.locals()).into_option()?;
        let mut inner = ty;
        for _ in 0..3 {
            match inner.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => inner = pointee,
                _ => break,
            }
        }
        if let TyKind::RigidTy(RigidTy::Array(_, const_len)) = inner.kind() {
            return const_len.eval_target_usize().ok().map(|n| n as usize);
        }
        if let TyKind::RigidTy(RigidTy::Slice(elem_ty)) = inner.kind() {
            return self.ord_array_len_from_body_locals(elem_ty);
        }
        None
    }

    fn ord_array_len_from_body_locals(&self, elem_ty: rustc_public::ty::Ty) -> Option<usize> {
        let mut found_len = None;
        for local_decl in self.body.locals() {
            if let Some(len) = Self::ord_extract_array_len_from_ty(local_decl.ty, elem_ty) {
                match found_len {
                    None => found_len = Some(len),
                    Some(existing) if existing == len => {}
                    Some(_) => return None,
                }
            }
        }
        found_len
    }

    fn ord_extract_array_len_from_ty(
        ty: rustc_public::ty::Ty,
        elem_ty: rustc_public::ty::Ty,
    ) -> Option<usize> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Array(arr_elem, const_len)) if arr_elem == elem_ty => {
                const_len.eval_target_usize().ok().map(|n| n as usize)
            }
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
                Self::ord_extract_array_len_from_ty(inner, elem_ty)
            }
            TyKind::RigidTy(RigidTy::Adt(adt_def, args)) => {
                let variants = adt_def.variants();
                if variants.len() == 1 && variants[0].fields().len() == 1 {
                    let field_ty = variants[0].fields()[0].ty_with_args(&args);
                    Self::ord_extract_array_len_from_ty(field_ty, elem_ty)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn resolve_ord_operand_to_array(&mut self, arg: &Operand) -> Option<Expr> {
        let place = match arg {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => return None,
        };
        if !place.projection.is_empty() {
            return None;
        }

        let mut current_local: usize = place.local;
        let mut visited = std::collections::HashSet::new();
        for _ in 0..4 {
            if !visited.insert(current_local) {
                return None;
            }

            let local_place = Place { local: current_local, projection: vec![] };
            let ref_base = self.ssa_base_name(&local_place);
            if let Some(pointee_base) = self.ref_pointees.get(ref_base.as_str()).cloned()
                && let Some(expr) = self.env_lookup(&pointee_base)
                && expr.sort().is_array()
            {
                return Some(expr.clone());
            }

            if let Some(expr) = self.codegen_place(&local_place)
                && expr.sort().is_array()
            {
                return Some(expr);
            }

            if let Some(src_local) = self.find_ord_source_local_for_array(current_local) {
                current_local = src_local;
                continue;
            }

            return None;
        }
        None
    }

    fn find_ord_source_local_for_array(&self, dest_local: usize) -> Option<usize> {
        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                    continue;
                };
                if place.local != dest_local || !place.projection.is_empty() {
                    continue;
                }
                match rvalue {
                    Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _)
                    | Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                        if src.projection.is_empty() =>
                    {
                        return Some(src.local);
                    }
                    Rvalue::Ref(_, _, ref_place) if ref_place.projection.is_empty() => {
                        return Some(ref_place.local);
                    }
                    _ => {}
                }
            }
        }
        None
    }
}

fn extract_ord_array_data(expr: &Expr) -> Option<Expr> {
    if expr.sort().is_array() {
        return Some(expr.clone());
    }
    if let ExprValue::DatatypeConstructor { args, .. } = expr.value()
        && let Some(data) = args.get(2)
        && data.sort().is_array()
    {
        return Some(data.clone());
    }
    let dt = expr.sort().datatype_sort()?;
    if !dt.name.starts_with("Slice_") || dt.constructors.len() != 1 {
        return None;
    }
    let data_field = dt.constructors[0].fields.iter().find(|field| &*field.name == "fld_data")?;
    if !data_field.sort.is_array() {
        return None;
    }
    Some(expr.clone().field_select(&dt.name, "fld_data", data_field.sort.clone()))
}

fn ord_len_from_expr(expr: &Expr) -> Option<usize> {
    if let ExprValue::DatatypeConstructor { args, .. } = expr.value()
        && let Some(len) = args.get(1).and_then(concrete_ord_usize)
    {
        return Some(len);
    }

    let dt = expr.sort().datatype_sort()?;
    if !dt.name.starts_with("Slice_") || dt.constructors.len() != 1 {
        return None;
    }
    let len_field = dt.constructors[0].fields.iter().find(|field| &*field.name == "fld_len")?;
    let len = expr.clone().field_select(&dt.name, "fld_len", len_field.sort.clone());
    concrete_ord_usize(&len)
}

fn ord_len_bv_from_expr(expr: &Expr) -> Option<Expr> {
    if let ExprValue::DatatypeConstructor { args, .. } = expr.value()
        && let Some(len) = args.get(1)
        && len.sort().is_bitvec()
    {
        return Some(len.clone());
    }

    let dt = expr.sort().datatype_sort()?;
    if !dt.name.starts_with("Slice_") || dt.constructors.len() != 1 {
        return None;
    }
    let len_field = dt.constructors[0].fields.iter().find(|field| &*field.name == "fld_len")?;
    if !len_field.sort.is_bitvec() {
        return None;
    }
    Some(expr.clone().field_select(&dt.name, "fld_len", len_field.sort.clone()))
}

fn ord_slice_constructor_bound_to(asserted: &Expr, target: &Expr) -> Option<Expr> {
    match asserted.value() {
        ExprValue::Eq(lhs, rhs) if lhs == target && is_ord_slice_constructor(rhs) => {
            Some(rhs.clone())
        }
        ExprValue::Eq(lhs, rhs) if rhs == target && is_ord_slice_constructor(lhs) => {
            Some(lhs.clone())
        }
        ExprValue::And(items) => {
            items.iter().find_map(|item| ord_slice_constructor_bound_to(item, target))
        }
        _ => None,
    }
}

fn is_ord_slice_constructor(expr: &Expr) -> bool {
    matches!(
        expr.value(),
        ExprValue::DatatypeConstructor { datatype_name, args, .. }
            if datatype_name.starts_with("Slice_") && args.len() >= 3
    )
}

fn concrete_ord_usize(expr: &Expr) -> Option<usize> {
    match expr.value() {
        ExprValue::BitVecConst { value, .. } => usize::try_from(value.clone()).ok(),
        ExprValue::BvAdd(lhs, rhs) => {
            let lhs = concrete_ord_usize(lhs)?;
            let rhs = concrete_ord_usize(rhs)?;
            let sum = lhs.checked_add(rhs)?;
            if fits_ord_bitvec_width(sum, expr.sort().bitvec_width()?) { Some(sum) } else { None }
        }
        ExprValue::BvSub(lhs, rhs) => {
            let lhs = concrete_ord_usize(lhs)?;
            let rhs = concrete_ord_usize(rhs)?;
            let diff = lhs.checked_sub(rhs)?;
            if fits_ord_bitvec_width(diff, expr.sort().bitvec_width()?) { Some(diff) } else { None }
        }
        ExprValue::BvExtract { high, low, expr: inner } => {
            if let ExprValue::BitVecConst { value, .. } = inner.value() {
                let shifted = value >> (*low as usize);
                let width = high - low + 1;
                let mask = (BigInt::from(1) << (width as usize)) - 1;
                let extracted = shifted & mask;
                u64::try_from(&extracted).ok().map(|v| v as usize)
            } else {
                None
            }
        }
        ExprValue::BvZeroExtend { expr: inner, .. }
        | ExprValue::BvSignExtend { expr: inner, .. } => concrete_ord_usize(inner),
        _ => None,
    }
}

fn fits_ord_bitvec_width(value: usize, width: u32) -> bool {
    if width as usize >= usize::BITS as usize { true } else { value < (1usize << width) }
}

fn build_ord_lexicographic_cmp(
    lhs: &Expr,
    rhs: &Expr,
    lhs_len: usize,
    rhs_len: usize,
    idx_width: u32,
    is_signed: bool,
) -> Option<Expr> {
    let less = Expr::bitvec_const(0xFFFF_FFFFu128, 32);
    let equal = Expr::bitvec_const(0u128, 32);
    let greater = Expr::bitvec_const(1u128, 32);

    let mut result = match lhs_len.cmp(&rhs_len) {
        std::cmp::Ordering::Less => less.clone(),
        std::cmp::Ordering::Equal => equal,
        std::cmp::Ordering::Greater => greater.clone(),
    };

    for i in (0..lhs_len.min(rhs_len)).rev() {
        let idx = Expr::bitvec_const(i as u64, idx_width);
        let lhs_elem = lhs.clone().select(idx.clone());
        let rhs_elem = rhs.clone().select(idx);
        let (lhs_elem, rhs_elem) =
            StatementCodegen::coerce_to_match_widths_typed(lhs_elem, rhs_elem, is_signed);
        if !lhs_elem.sort().is_bitvec()
            || !rhs_elem.sort().is_bitvec()
            || lhs_elem.sort().bitvec_width() != rhs_elem.sort().bitvec_width()
        {
            return None;
        }
        let elem_lt = if is_signed {
            lhs_elem.clone().bvslt(rhs_elem.clone())
        } else {
            lhs_elem.clone().bvult(rhs_elem.clone())
        };
        let elem_gt = if is_signed { lhs_elem.bvsgt(rhs_elem) } else { lhs_elem.bvugt(rhs_elem) };
        result = Expr::ite(elem_lt, less.clone(), Expr::ite(elem_gt, greater.clone(), result));
    }

    Some(result)
}

fn build_ord_lexicographic_cmp_symbolic_len(
    lhs: &Expr,
    rhs: &Expr,
    lhs_len: &Expr,
    rhs_len: &Expr,
    idx_width: u32,
    is_signed: bool,
    max_lanes: usize,
    overflow_result: Expr,
) -> Option<Expr> {
    let len_width = lhs_len.sort().bitvec_width()?;
    if rhs_len.sort().bitvec_width() != Some(len_width) {
        return None;
    }

    let less = Expr::bitvec_const(0xFFFF_FFFFu128, 32);
    let equal = Expr::bitvec_const(0u128, 32);
    let greater = Expr::bitvec_const(1u128, 32);

    let max_len = Expr::bitvec_const(max_lanes as u64, len_width);
    let within_unroll = lhs_len.clone().bvule(max_len.clone()).and(rhs_len.clone().bvule(max_len));

    let mut result = equal;
    for i in (0..max_lanes).rev() {
        let len_idx = Expr::bitvec_const(i as u64, len_width);
        let lhs_in = len_idx.clone().bvult(lhs_len.clone());
        let rhs_in = len_idx.bvult(rhs_len.clone());

        let idx = Expr::bitvec_const(i as u64, idx_width);
        let lhs_elem = lhs.clone().select(idx.clone());
        let rhs_elem = rhs.clone().select(idx);
        let (lhs_elem, rhs_elem) =
            StatementCodegen::coerce_to_match_widths_typed(lhs_elem, rhs_elem, is_signed);
        if !lhs_elem.sort().is_bitvec()
            || !rhs_elem.sort().is_bitvec()
            || lhs_elem.sort().bitvec_width() != rhs_elem.sort().bitvec_width()
        {
            return None;
        }

        let elem_lt = if is_signed {
            lhs_elem.clone().bvslt(rhs_elem.clone())
        } else {
            lhs_elem.clone().bvult(rhs_elem.clone())
        };
        let elem_gt = if is_signed { lhs_elem.bvsgt(rhs_elem) } else { lhs_elem.bvugt(rhs_elem) };
        let both_in = lhs_in.clone().and(rhs_in.clone());
        let lhs_only = lhs_in.clone().and(rhs_in.clone().not());
        let rhs_only = lhs_in.not().and(rhs_in);
        let elem_order =
            Expr::ite(elem_lt, less.clone(), Expr::ite(elem_gt, greater.clone(), result.clone()));
        result = Expr::ite(
            both_in,
            elem_order,
            Expr::ite(lhs_only, greater.clone(), Expr::ite(rhs_only, less.clone(), result)),
        );
    }

    Some(Expr::ite(within_unroll, result, overflow_result))
}
