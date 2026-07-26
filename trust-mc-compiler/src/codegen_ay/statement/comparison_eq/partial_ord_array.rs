// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Array and slice `PartialOrd` support for BMC comparison codegen.

use ay_bindings::{Expr, ExprValue};
use num_bigint::BigInt;
use rustc_public::mir::{Operand, Place, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::super::{IntoOption, StatementCodegen};

/// Maximum fixed lanes to unroll for direct array/slice PartialOrd comparisons.
const MAX_PARTIAL_ORD_LEXICO_LANES: usize = 16;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    pub(in crate::codegen_ay::statement) fn codegen_slice_or_array_partial_ord_cmp(
        &mut self,
        lhs_arg: &Operand,
        rhs_arg: &Operand,
        lhs_raw: &Expr,
        rhs_raw: &Expr,
        op: &str,
    ) -> Option<Expr> {
        let lhs = self.partial_ord_array_data(lhs_arg, lhs_raw)?;
        let rhs = self.partial_ord_array_data(rhs_arg, rhs_raw)?;

        let lhs_arr = lhs.sort().array_sort()?;
        let rhs_arr = rhs.sort().array_sort()?;
        if lhs_arr.index_sort != rhs_arr.index_sort || lhs_arr.element_sort != rhs_arr.element_sort
        {
            return None;
        }
        if !lhs_arr.element_sort.is_bitvec() {
            return None;
        }

        let lhs_len = self.partial_ord_len_from_operand_or_expr(lhs_arg, lhs_raw)?;
        let rhs_len = self.partial_ord_len_from_operand_or_expr(rhs_arg, rhs_raw)?;
        if lhs_len.max(rhs_len) > MAX_PARTIAL_ORD_LEXICO_LANES {
            return None;
        }

        let is_signed = self.partial_ord_element_signedness(lhs_arg).unwrap_or(false);
        let idx_width = lhs_arr.index_sort.bitvec_width()?;
        let cmp =
            build_partial_ord_lexicographic_cmp(&lhs, &rhs, lhs_len, rhs_len, idx_width, is_signed);
        let less = Expr::bitvec_const(0xFFFF_FFFFu128, 32);
        let equal = Expr::bitvec_const(0u128, 32);
        let greater = Expr::bitvec_const(1u128, 32);

        debug!(
            lhs_len,
            rhs_len, is_signed, op, "codegen_partial_ord_cmp: direct lexicographic array/slice"
        );

        match op {
            "lt" => Some(cmp.eq(less)),
            "le" => Some(cmp.clone().eq(less).or(cmp.eq(equal))),
            "gt" => Some(cmp.eq(greater)),
            "ge" => Some(cmp.clone().eq(greater).or(cmp.eq(equal))),
            _ => None,
        }
    }

    fn partial_ord_array_data(&mut self, arg: &Operand, raw: &Expr) -> Option<Expr> {
        extract_partial_ord_array_data(raw).or_else(|| {
            self.resolve_partial_ord_operand_to_array(arg)
                .and_then(|expr| extract_partial_ord_array_data(&expr))
        })
    }

    fn partial_ord_len_from_operand_or_expr(&self, arg: &Operand, raw: &Expr) -> Option<usize> {
        slice_len_from_expr(raw).or_else(|| self.partial_ord_len_from_mir_arg(arg))
    }

    fn partial_ord_len_from_mir_arg(&self, arg: &Operand) -> Option<usize> {
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
            return self.partial_ord_array_len_from_body_locals(elem_ty);
        }
        None
    }

    fn partial_ord_array_len_from_body_locals(
        &self,
        elem_ty: rustc_public::ty::Ty,
    ) -> Option<usize> {
        let mut found_len = None;
        for local_decl in self.body.locals() {
            if let Some(len) = Self::partial_ord_extract_array_len_from_ty(local_decl.ty, elem_ty) {
                match found_len {
                    None => found_len = Some(len),
                    Some(existing) if existing == len => {}
                    Some(_) => return None,
                }
            }
        }
        found_len
    }

    fn partial_ord_extract_array_len_from_ty(
        ty: rustc_public::ty::Ty,
        elem_ty: rustc_public::ty::Ty,
    ) -> Option<usize> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Array(arr_elem, const_len)) if arr_elem == elem_ty => {
                const_len.eval_target_usize().ok().map(|n| n as usize)
            }
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
                Self::partial_ord_extract_array_len_from_ty(inner, elem_ty)
            }
            TyKind::RigidTy(RigidTy::Adt(adt_def, args)) => {
                let variants = adt_def.variants();
                if variants.len() == 1 && variants[0].fields().len() == 1 {
                    let field_ty = variants[0].fields()[0].ty_with_args(&args);
                    Self::partial_ord_extract_array_len_from_ty(field_ty, elem_ty)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn partial_ord_element_signedness(&self, arg: &Operand) -> Option<bool> {
        let ty = arg.ty(self.body.locals()).into_option()?;
        let mut inner = ty;
        for _ in 0..3 {
            match inner.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => inner = pointee,
                _ => break,
            }
        }
        match inner.kind() {
            TyKind::RigidTy(RigidTy::Array(elem, _) | RigidTy::Slice(elem)) => {
                Self::ty_signedness(elem)
            }
            TyKind::RigidTy(RigidTy::Str) => Some(false),
            _ => Self::ty_signedness(inner),
        }
    }

    fn resolve_partial_ord_operand_to_array(&mut self, arg: &Operand) -> Option<Expr> {
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

            if let Some(src_local) = self.find_partial_ord_source_local_for_array(current_local) {
                current_local = src_local;
                continue;
            }

            return None;
        }
        None
    }

    fn find_partial_ord_source_local_for_array(&self, dest_local: usize) -> Option<usize> {
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

fn extract_partial_ord_array_data(expr: &Expr) -> Option<Expr> {
    if expr.sort().is_array() {
        return Some(expr.clone());
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

fn slice_len_from_expr(expr: &Expr) -> Option<usize> {
    if let ExprValue::DatatypeConstructor { args, .. } = expr.value()
        && let Some(len) = args.get(1).and_then(concrete_usize)
    {
        return Some(len);
    }

    let dt = expr.sort().datatype_sort()?;
    if !dt.name.starts_with("Slice_") || dt.constructors.len() != 1 {
        return None;
    }
    let len_field = dt.constructors[0].fields.iter().find(|field| &*field.name == "fld_len")?;
    let len = expr.clone().field_select(&dt.name, "fld_len", len_field.sort.clone());
    concrete_usize(&len)
}

fn concrete_usize(expr: &Expr) -> Option<usize> {
    match expr.value() {
        ExprValue::BitVecConst { value, .. } => usize::try_from(value.clone()).ok(),
        ExprValue::BvAdd(lhs, rhs) => {
            let lhs = concrete_usize(lhs)?;
            let rhs = concrete_usize(rhs)?;
            let sum = lhs.checked_add(rhs)?;
            if fits_bitvec_width(sum, expr.sort().bitvec_width()?) { Some(sum) } else { None }
        }
        ExprValue::BvSub(lhs, rhs) => {
            let lhs = concrete_usize(lhs)?;
            let rhs = concrete_usize(rhs)?;
            let diff = lhs.checked_sub(rhs)?;
            if fits_bitvec_width(diff, expr.sort().bitvec_width()?) { Some(diff) } else { None }
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
        | ExprValue::BvSignExtend { expr: inner, .. } => concrete_usize(inner),
        _ => None,
    }
}

fn fits_bitvec_width(value: usize, width: u32) -> bool {
    if width as usize >= usize::BITS as usize { true } else { value < (1usize << width) }
}

fn build_partial_ord_lexicographic_cmp(
    lhs: &Expr,
    rhs: &Expr,
    lhs_len: usize,
    rhs_len: usize,
    idx_width: u32,
    is_signed: bool,
) -> Expr {
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
        let elem_lt = if is_signed {
            lhs_elem.clone().bvslt(rhs_elem.clone())
        } else {
            lhs_elem.clone().bvult(rhs_elem.clone())
        };
        let elem_gt = if is_signed { lhs_elem.bvsgt(rhs_elem) } else { lhs_elem.bvugt(rhs_elem) };
        result = Expr::ite(elem_lt, less.clone(), Expr::ite(elem_gt, greater.clone(), result));
    }

    result
}
