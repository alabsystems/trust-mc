// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native bounds for authenticated iterator receivers. Chars counts bytes;
//! Take limits its stream. Their layouts do not establish exact cardinality.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, Sort};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{LocalDecl, Operand};
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};

use super::super::ChcCtx;
use super::super::codegen_types::CodegenTypes;
use super::super::stubs_option_helpers::OptionHelpers;
use crate::codegen_ay::types::{POINTER_WIDTH, bool_sort};
use crate::kani_middle::std_abstraction::{
    IteratorSizeHintKind, NativeIteratorQuery, iterator_size_hint_kind, native_iterator_query,
};

#[derive(Clone)]
struct Bounds {
    lower: Expr,
    upper: Expr,
}

fn field(value: &Expr, name: &str) -> Option<Expr> {
    let dt = value.sort().datatype_sort()?;
    if dt.constructors.len() != 1 {
        return None;
    }
    let field = dt.constructors[0].fields.iter().find(|field| field.name == name)?;
    value.clone().try_field_select(&dt.name, name, field.sort.clone()).ok()
}

fn minimum(a: Expr, b: Expr) -> Expr {
    Expr::ite(a.clone().bvule(b.clone()), a, b)
}

fn chars_bounds(bytes: Expr) -> Bounds {
    let width = bytes.sort().bitvec_width().unwrap_or(POINTER_WIDTH);
    let four = Expr::bitvec_const(4u64, width);
    // `bytes + 3` can overflow; native usize::div_ceil does not.
    let rounded = Expr::ite(
        bytes.clone().bvurem(four.clone()).eq(Expr::bitvec_const(0u64, width)),
        Expr::bitvec_const(0u64, width),
        Expr::bitvec_const(1u64, width),
    );
    Bounds { lower: bytes.clone().bvudiv(four).bvadd(rounded), upper: bytes }
}

fn receiver_and_inner(ctx: &ChcCtx<'_, '_>, mut ty: Ty) -> Option<(Ty, Option<Ty>)> {
    ty = ctx.resolve_body_ty(ty);
    while let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = ty.kind() {
        ty = ctx.resolve_body_ty(inner);
    }
    let TyKind::RigidTy(RigidTy::Adt(_, args)) = ty.kind() else { return None };
    let inner = args.0.iter().find_map(|arg| match arg {
        GenericArgKind::Type(inner) => Some(ctx.resolve_body_ty(*inner)),
        _ => None,
    });
    Some((ty, inner))
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn native_iterator_size_hint_call(
        &self,
        func: &Operand,
    ) -> bool {
        self.native_iterator_query_instance(func, self.body.locals()).is_some_and(|instance| {
            native_iterator_query(self.tcx, &instance) == Some(NativeIteratorQuery::SizeHint)
        })
    }

    /// Resolve against the operand's body, including nested walker bodies.
    pub(in crate::codegen_ay::chc) fn native_iterator_query_instance(
        &self,
        func: &Operand,
        locals: &[LocalDecl],
    ) -> Option<Instance> {
        let TyKind::RigidTy(RigidTy::FnDef(def, generics)) =
            self.resolve_body_ty(func.ty(locals).ok()?).kind()
        else {
            return None;
        };
        let instance = Instance::resolve(def, &generics).ok()?;
        native_iterator_query(self.tcx, &instance)?;
        Some(instance)
    }

    /// The same native bounds and exact-cardinality model used at top level,
    /// returning the actual callee's result sort. No adapter is peeled until
    /// both its Rust identity and the complete receiver value sort agree.
    pub(in crate::codegen_ay::chc) fn native_iterator_query_expr(
        &self,
        instance: &Instance,
        receiver: &Expr,
    ) -> Option<Expr> {
        let query = native_iterator_query(self.tcx, instance)?;
        let signature = instance.ty().kind().fn_sig()?.skip_binder();
        let [receiver_ty] = signature.inputs() else { return None };
        let (owner_ty, _) = receiver_and_inner(self, *receiver_ty)?;
        if receiver.sort() != &Self::translate_ty(owner_ty)? {
            return None;
        }
        let output_sort = Self::translate_ty(self.resolve_body_ty(signature.output()))?;
        match query {
            NativeIteratorQuery::SizeHint => {
                let bounds = self.iterator_size_hint_bounds(receiver, *receiver_ty, 0)?;
                self.iterator_size_hint_value(bounds, &output_sort)
            }
            NativeIteratorQuery::Len => {
                let remaining = self.typed_iterator_remaining_len(receiver, *receiver_ty)?;
                (remaining.sort() == &output_sort).then_some(remaining)
            }
        }
    }

    fn iterator_size_hint_value(&self, bounds: Bounds, output_sort: &Sort) -> Option<Expr> {
        let dt = output_sort.datatype_sort()?;
        let [ctor] = dt.constructors.as_slice() else { return None };
        let [lower, upper] = ctor.fields.as_slice() else { return None };
        let lower = self.coerce_value_to_sort(bounds.lower, &lower.sort, false)?;
        let upper = self.make_some_expr_for_option(bounds.upper, &upper.sort)?;
        Some(Expr::datatype_constructor(
            &dt.name,
            &ctor.name,
            vec![lower, upper],
            output_sort.clone(),
        ))
    }

    fn iterator_size_hint_bounds(&self, iter: &Expr, ty: Ty, depth: usize) -> Option<Bounds> {
        if depth > 8 {
            return None;
        }
        let (ty, inner_ty) = receiver_and_inner(self, ty)?;
        match iterator_size_hint_kind(self.tcx, ty)? {
            IteratorSizeHintKind::Exact => {
                let remaining = self.try_extract_iterator_remaining_len(iter)?;
                Some(Bounds { lower: remaining.clone(), upper: remaining })
            }
            IteratorSizeHintKind::Chars => {
                let bytes = self.try_extract_iterator_remaining_len(&field(iter, "fld_iter")?)?;
                Some(chars_bounds(bytes))
            }
            IteratorSizeHintKind::Transparent(inner_field) => {
                self.iterator_size_hint_bounds(&field(iter, inner_field)?, inner_ty?, depth + 1)
            }
            IteratorSizeHintKind::Take => {
                let n = field(iter, "fld_n")?;
                if n.sort() != &Sort::bitvec(POINTER_WIDTH) {
                    return None;
                }
                // Native Take does not call the inner size_hint at n == 0.
                if Self::try_eval_const_bv(&n) == Some(0) {
                    return Some(Bounds { lower: n.clone(), upper: n });
                }
                let inner = self.iterator_size_hint_bounds(
                    &field(iter, "fld_iter")?,
                    inner_ty?,
                    depth + 1,
                )?;
                Some(Bounds {
                    lower: minimum(inner.lower, n.clone()),
                    upper: minimum(inner.upper, n),
                })
            }
        }
    }

    /// Exact item cardinality for sidecars. Chars bytes are only an upper
    /// bound; traverse wrappers only after authenticating each receiver type.
    pub(in crate::codegen_ay::chc) fn typed_iterator_remaining_len(
        &self,
        iter: &Expr,
        ty: Ty,
    ) -> Option<Expr> {
        if crate::kani_middle::transform::unit_has_stubs() {
            return None;
        }
        self.exact_iterator_remaining_len(iter, ty, 0)
    }

    fn exact_iterator_remaining_len(&self, iter: &Expr, ty: Ty, depth: usize) -> Option<Expr> {
        if depth > 8 {
            return None;
        }
        let (ty, inner_ty) = receiver_and_inner(self, ty)?;
        match iterator_size_hint_kind(self.tcx, ty)? {
            IteratorSizeHintKind::Exact => self.try_extract_iterator_remaining_len(iter),
            IteratorSizeHintKind::Transparent(inner_field) => {
                self.exact_iterator_remaining_len(&field(iter, inner_field)?, inner_ty?, depth + 1)
            }
            IteratorSizeHintKind::Take => {
                let n = field(iter, "fld_n")?;
                if n.sort() != &Sort::bitvec(POINTER_WIDTH) {
                    return None;
                }
                if Self::try_eval_const_bv(&n) == Some(0) {
                    return Some(n);
                }
                self.exact_iterator_remaining_len(&field(iter, "fld_iter")?, inner_ty?, depth + 1)
                    .map(|remaining| minimum(remaining, n))
            }
            IteratorSizeHintKind::Chars => None,
        }
    }

    pub(in crate::codegen_ay::chc) fn codegen_iter_size_hint(
        &mut self,
        func: Option<&Operand>,
        args: &[Operand],
        modified_locals: &std::collections::HashSet<usize>,
        dest_local: usize,
        dest_vec_idx: usize,
        result_expr: &mut Option<Expr>,
        flattened_result_fields: &mut Option<Vec<Option<Expr>>>,
    ) {
        let bounds = (|| {
            if !self.native_iterator_size_hint_call(func?) {
                return None;
            }
            let receiver_ty = args.first()?.ty(self.body.locals()).ok()?;
            let (iter, _) = self.iterator_receiver_expr_and_local(args, modified_locals)?;
            self.iterator_size_hint_bounds(&iter, receiver_ty, 0)
        })();
        let Some(bounds) = bounds else {
            self.record_sound_fallback_reason("iter_size_hint_receiver_unmodelled");
            return;
        };

        if self.flatten.flattened_tuple_locals.contains(&dest_local) {
            let fields: Option<Vec<_>> = (0..self.flattened_field_count(dest_local))
                .map(|index| {
                    let (_, sort) =
                        self.state_var_mgr.output_state_vars.get(dest_vec_idx + index)?;
                    let value = if sort.bitvec_width().is_some() {
                        let bound = if index == 0 { &bounds.lower } else { &bounds.upper };
                        self.coerce_value_to_sort(bound.clone(), sort, false)?
                    } else if *sort == bool_sort() {
                        Expr::bool_const(true)
                    } else {
                        self.make_some_expr_for_option(bounds.upper.clone(), sort)?
                    };
                    Some(Some(value))
                })
                .collect();
            if let Some(fields) = fields.filter(|fields| fields.len() >= 2) {
                *flattened_result_fields = Some(fields);
                return;
            }
        } else if let Some((_, out_sort)) = self.state_var_mgr.output_state_vars.get(dest_vec_idx)
            && let Some(value) = self.iterator_size_hint_value(bounds, out_sort)
        {
            *result_expr = Some(value);
            return;
        }
        self.record_sound_fallback_reason("iter_size_hint_result_unmodelled");
    }
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
mod tests;
