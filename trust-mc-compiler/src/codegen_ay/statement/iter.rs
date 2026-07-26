// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! Iterator codegen for AY - Part of #1354.
//!
//! Contains functions for codegen of iterator types (IntoIter, PolymorphicIter, IndexRange).

use std::sync::Arc;

use ay_bindings::SortInner;
use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::{debug, warn};

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::names::{self, struct_sort};
use crate::codegen_ay::types::POINTER_WIDTH;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Extract the length N from array iterator types like `&IntoIter<T, N>`.
    ///
    /// This function extracts N from references like `&IntoIter<T, N>` or `&mut IntoIter<T, N>`.
    ///
    /// ENSURES: Returns Some(N) if ty is a reference to IntoIter<T, N> with known N
    /// ENSURES: Returns None if ty is not an array iterator or length is unknown
    pub(super) fn extract_array_iter_len(ty: rustc_public::ty::Ty) -> Option<u64> {
        // Unwrap reference types to get the underlying iterator type
        let inner_ty = match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
            _ => ty, // external enum: TyKind
        };

        // Check if it's an ADT (struct) with generic args
        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = inner_ty.kind() {
            let name = def.0.name();
            // Check for array::IntoIter or any IntoIter-like type
            if name.contains("IntoIter") || name.contains("iter_inner") {
                // Look for const generic in the args (the array length N)
                for arg in &args.0 {
                    if let GenericArgKind::Const(const_val) = arg {
                        // Try to evaluate the const to a usize
                        if let Some(len) = const_val.eval_target_usize().into_option() {
                            debug!("extract_array_iter_len: found length {} for {}", len, name);
                            return Some(len);
                        }
                    }
                }
            }
        }

        None
    }

    /// Build an IndexRange struct expression from start/end expressions.
    pub(super) fn build_index_range_expr(
        &self,
        range_ty: rustc_public::ty::Ty,
        start_expr: Expr,
        end_expr: Expr,
    ) -> Option<Expr> {
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = range_ty.kind() else {
            return None;
        };
        let adt_name = Self::adt_sort_name(def, &args);
        let sort = Self::infer_adt_sort(def, args)?;
        let (start_expr, end_expr) = if let Some(width) = end_expr.sort().bitvec_width() {
            (Self::coerce_to_width(start_expr, width), Self::coerce_to_width(end_expr, width))
        } else {
            (start_expr, end_expr)
        };
        let cons_name = names::resolve_ctor_name(&sort, &adt_name);
        Some(Expr::datatype_constructor(adt_name, cons_name, vec![start_expr, end_expr], sort))
    }

    /// Build a PolymorphicIter struct expression from alive/data expressions.
    pub(super) fn build_polymorphic_iter_expr(
        &self,
        iter_ty: rustc_public::ty::Ty,
        alive_expr: Expr,
        data_expr: Expr,
    ) -> Option<Expr> {
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = iter_ty.kind() else {
            return None;
        };
        // Get adt_name before moving args into infer_adt_sort
        let adt_name = Self::adt_sort_name(def, &args);
        let sort = Self::infer_adt_sort(def, args)?;
        let cons_name = names::resolve_ctor_name(&sort, &adt_name);
        Some(Expr::datatype_constructor(adt_name, cons_name, vec![alive_expr, data_expr], sort))
    }

    /// Build an `IntoIter` expression for array iteration.
    ///
    /// #468: Creates the `IntoIter<T, N>` struct from an array `[T; N]`.
    /// The `IntoIter` struct contains:
    /// - data: `ManuallyDrop<PolymorphicIter<[MaybeUninit<T>; N]>>`
    ///   where `PolymorphicIter` has `(alive: IndexRange, data: [MaybeUninit<T>; N])`
    ///
    /// For zero-length arrays, creates an exhausted iterator (alive range is empty).
    pub(super) fn build_array_into_iter_expr(
        &mut self,
        _dest_ty: rustc_public::ty::Ty,
        array_arg: &Operand,
        _elem_ty: rustc_public::ty::Ty,
        len: u64,
    ) -> Option<Expr> {
        debug!("build_array_into_iter_expr: len={}", len);
        let array_expr = self.codegen_operand(array_arg)?;

        // IndexRange [0, len) — zero-length arrays get [0, 0) (exhausted)
        let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let end = Expr::bitvec_const(len as u128, POINTER_WIDTH);
        let index_range_sort = names::index_range_sort();
        let alive_cons_name =
            index_range_sort.datatype_default_constructor().unwrap_or("IndexRange_mk");
        let alive_expr = Expr::datatype_constructor(
            "IndexRange",
            alive_cons_name,
            vec![zero, end],
            index_range_sort.clone(),
        );

        // MaybeUninit<T> is repr(transparent), treat as T for SMT
        let data_expr = array_expr;
        let poly_iter_sort = struct_sort(
            "PolymorphicIter",
            [("fld_alive", index_range_sort), ("fld_data", data_expr.sort().clone())],
        );
        let poly_cons_name =
            poly_iter_sort.datatype_default_constructor().unwrap_or("PolymorphicIter_mk");
        let poly_iter_expr = Expr::datatype_constructor(
            "PolymorphicIter",
            poly_cons_name,
            vec![alive_expr, data_expr],
            poly_iter_sort.clone(),
        );

        // ManuallyDrop is repr(transparent)
        let manually_drop_sort = struct_sort("ManuallyDrop", [("fld_0", poly_iter_sort)]);
        let md_cons_name =
            manually_drop_sort.datatype_default_constructor().unwrap_or("ManuallyDrop_mk");
        let manually_drop_expr = Expr::datatype_constructor(
            "ManuallyDrop",
            md_cons_name,
            vec![poly_iter_expr],
            manually_drop_sort.clone(),
        );

        let into_iter_sort = struct_sort("IntoIter", [("fld_data", manually_drop_sort)]);
        let ii_cons_name = into_iter_sort.datatype_default_constructor().unwrap_or("IntoIter_mk");
        Some(Expr::datatype_constructor(
            "IntoIter",
            ii_cons_name,
            vec![manually_drop_expr],
            into_iter_sort.clone(),
        ))
    }

    /// Extract iterator base name and iterator type from an operand (usually &mut PolymorphicIter).
    pub(super) fn iter_base_from_operand(
        &mut self,
        operand: Option<&Operand>,
    ) -> Option<(Arc<str>, rustc_public::ty::Ty)> {
        let operand = operand?;
        let (Operand::Copy(place) | Operand::Move(place)) = operand else {
            return None;
        };
        let ref_base: Arc<str> = self.ssa_base_name(place).into();
        let iter_base = self.ref_pointees.get(ref_base.as_ref()).cloned().unwrap_or(ref_base);
        let iter_ty = place.ty(self.body.locals()).into_option()?;
        let iter_ty = match iter_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
            _ => iter_ty, // external enum: TyKind
        };
        Some((iter_base, iter_ty))
    }

    /// Extract the base name and sort for the pointee of a reference operand.
    /// Returns (pointee_base_name, pointee_sort) if successful.
    ///
    /// Fix #967: This function ONLY succeeds when ref_pointees has a tracked mapping
    /// for the reference AND the pointee is in the environment with a Datatype sort.
    /// Returning None signals to callers that they should not attempt iterator handling
    /// on this reference.
    pub(super) fn get_ref_pointee_sort(&mut self, operand: &Operand) -> Option<(Arc<str>, Sort)> {
        let (Operand::Copy(place) | Operand::Move(place)) = operand else {
            warn!("get_ref_pointee_sort: operand is not Copy/Move, returning None");
            return None;
        };
        let ref_base = self.ssa_base_name(place);

        // Only succeed if we have a tracked pointee for this reference
        let Some(pointee_base) = self.ref_pointees.get(ref_base.as_str()).cloned() else {
            warn!(
                "get_ref_pointee_sort: ref_base '{}' not in ref_pointees (have {} entries)",
                ref_base,
                self.ref_pointees.len()
            );
            return None;
        };

        // Get the expression from the environment
        let Some(expr) = self.env_lookup(pointee_base.as_ref()) else {
            warn!("get_ref_pointee_sort: pointee_base '{}' not in env", pointee_base);
            return None;
        };
        let sort = expr.sort().clone();

        // Fix #967: Only return if the pointee has a Datatype sort.
        // If it's BitVec (e.g., pointer fallback), the calling code can't do field_select.
        if !sort.is_datatype() {
            warn!(
                "get_ref_pointee_sort: pointee {} has non-Datatype sort {:?}, returning None",
                pointee_base, sort
            );
            return None;
        }

        Some((pointee_base, sort))
    }

    /// Compute len() for PolymorphicIter by reading alive range.
    pub(super) fn polymorphic_iter_len_expr(
        &self,
        iter_expr: &Expr,
        iter_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = iter_ty.kind() else {
            return None;
        };
        let adt_name = Self::adt_sort_name(def, &args);
        // Guard: iter_expr must be a Datatype to use field_select (#967)
        if !iter_expr.sort().is_datatype() {
            return None;
        }
        if !Self::datatype_expr_has_fields(iter_expr, &["fld_alive"]) {
            return None;
        }
        let fields = def.variants()[0].fields();
        if fields.is_empty() {
            return None;
        }
        let alive_field = &fields[0];
        let alive_ty = Self::resolve_generic_ty(alive_field.ty(), &args)?;
        let alive_sort = Self::infer_sort_from_ty(alive_ty)?;
        let alive_expr = iter_expr.clone().field_select(adt_name, "fld_alive", alive_sort.clone());
        self.index_range_len_expr(&alive_expr, &alive_sort, false) // array indices: unsigned
    }

    /// Compute `next()` for `PolymorphicIter`, returning `(Option<T>, updated_iter)`.
    pub(super) fn polymorphic_iter_next_expr(
        &self,
        iter_expr: &Expr,
        iter_ty: rustc_public::ty::Ty,
        destination: &rustc_public::mir::Place,
    ) -> Option<(Expr, Expr)> {
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = iter_ty.kind() else {
            return None;
        };
        let adt_name = Self::adt_sort_name(def, &args);
        // Guard: iter_expr must be a Datatype to use field_select (#967)
        if !iter_expr.sort().is_datatype() {
            return None;
        }
        if !Self::datatype_expr_has_fields(iter_expr, &["fld_alive", "fld_data"]) {
            return None;
        }
        let fields = def.variants()[0].fields();
        if fields.len() < 2 {
            return None;
        }
        let alive_field = &fields[0];
        let data_field = &fields[1];
        let alive_ty = Self::resolve_generic_ty(alive_field.ty(), &args)?;
        let data_ty = Self::resolve_generic_ty(data_field.ty(), &args)?;
        let alive_sort = Self::infer_sort_from_ty(alive_ty)?;
        let data_sort = Self::infer_sort_from_ty(data_ty)?;
        let alive_expr =
            iter_expr.clone().field_select(&*adt_name, "fld_alive", alive_sort.clone());
        let data_expr = iter_expr.clone().field_select(&*adt_name, "fld_data", data_sort);

        let (start_expr, _end_expr, has_next, updated_alive) =
            self.index_range_next_expr(&alive_expr, &alive_sort, false)?; // array: unsigned

        // Compute elem from data_expr via clone, then move data_expr into constructor
        let elem_expr = match data_expr.sort().inner() {
            SortInner::Array(arr_sort) => {
                let idx = if let Some(width) = arr_sort.index_sort.bitvec_width() {
                    Self::coerce_to_width(start_expr, width)
                } else {
                    start_expr
                };
                data_expr.clone().select(idx)
            }
            _ => data_expr.clone(), // external enum: SortInner (ay_bindings crate)
        };

        let option_expr = self.build_option_expr(destination, has_next, elem_expr)?;
        let iter_sort = Self::infer_adt_sort(def, args)?;
        let cons_name = names::resolve_ctor_name(&iter_sort, &adt_name);
        // Last use of `data_expr` — move instead of clone
        let updated_iter = Expr::datatype_constructor(
            adt_name,
            cons_name,
            vec![updated_alive, data_expr],
            iter_sort,
        );

        Some((option_expr, updated_iter))
    }

    fn datatype_expr_has_fields(expr: &Expr, fields: &[&str]) -> bool {
        let Some(dt) = expr.sort().datatype_sort() else {
            return false;
        };
        let Some(ctor) = dt.constructors.first() else {
            return false;
        };
        fields.iter().all(|field| ctor.fields.iter().any(|candidate| candidate.name == *field))
    }

    /// Compute len for an IndexRange: max(end - start, 0).
    /// Part of #3272: `signed` selects `bvsge`/`bvuge` for the BV guard.
    pub(super) fn index_range_len_expr(
        &self,
        alive_expr: &Expr,
        alive_sort: &Sort,
        signed: bool,
    ) -> Option<Expr> {
        let SortInner::Datatype(dt_sort) = alive_sort.inner() else {
            return None;
        };
        // Fix #4297: The alive sort must be a 2-field (start, end) IndexRange-shaped
        // datatype. Iterator adapters like `Take<Iter>` or `Map<Iter, F>` are sometimes
        // passed to IndexRange helpers via `polymorphic_iter_next_expr`; their inner
        // datatype shape differs (e.g. single-field adapters, or zero-variant ADTs)
        // and indexing `constructors[0].fields[1]` would panic. Guard with bounds.
        if dt_sort.constructors.is_empty() || dt_sort.constructors[0].fields.len() < 2 {
            warn!(
                "index_range_len_expr: alive sort {} is not a 2-field IndexRange shape \
                 (constructors={}, fields={}); falling back to None",
                dt_sort.name,
                dt_sort.constructors.len(),
                dt_sort.constructors.first().map_or(0, |c| c.fields.len()),
            );
            return None;
        }
        let adt_name = &dt_sort.name;
        let start_sort = dt_sort.constructors[0].fields[0].sort.clone();
        let end_sort = dt_sort.constructors[0].fields[1].sort.clone();
        let start_expr = alive_expr.clone().field_select(adt_name, "fld_start", start_sort);
        let end_expr = alive_expr.clone().field_select(adt_name, "fld_end", end_sort.clone());
        if let Some(width) = end_sort.bitvec_width() {
            let diff = end_expr.clone().bvsub(start_expr.clone());
            let zero = Expr::bitvec_const(0, width);
            let guard =
                if signed { end_expr.bvsge(start_expr) } else { end_expr.bvuge(start_expr) };
            Some(Expr::ite(guard, diff, zero))
        } else if end_sort.is_int() {
            let diff = end_expr.clone().int_sub(start_expr.clone());
            let zero = Expr::int_const(0);
            let guard = end_expr.int_ge(start_expr);
            Some(Expr::ite(guard, diff, zero))
        } else {
            None
        }
    }

    /// Compute next() for IndexRange, returning (start, end, has_next, updated_alive).
    /// Part of #3272: `signed` selects `bvslt`/`bvult` for the has_next guard.
    pub(super) fn index_range_next_expr(
        &self,
        alive_expr: &Expr,
        alive_sort: &Sort,
        signed: bool,
    ) -> Option<(Expr, Expr, Expr, Expr)> {
        let SortInner::Datatype(dt_sort) = alive_sort.inner() else {
            return None;
        };
        // Fix #4297: Bounds-check the datatype shape before indexing. Previously this
        // panicked with `index out of bounds: the len is 1 but the index is 1` on
        // iterator chains such as `[CHAR_POOL[a], CHAR_POOL[b]].iter().take(n).collect()`,
        // where the adapter's "alive" sort is not a 2-field IndexRange. Returning None
        // here causes callers (e.g. `polymorphic_iter_next_expr`) to bail gracefully
        // instead of ICEing, which in turn lets the higher-level dispatcher mark the
        // call as unsupported (trust_mc verdict) rather than crashing rustc.
        if dt_sort.constructors.is_empty() || dt_sort.constructors[0].fields.len() < 2 {
            warn!(
                "index_range_next_expr: alive sort {} is not a 2-field IndexRange shape \
                 (constructors={}, fields={}); falling back to None",
                dt_sort.name,
                dt_sort.constructors.len(),
                dt_sort.constructors.first().map_or(0, |c| c.fields.len()),
            );
            return None;
        }
        let adt_name = &dt_sort.name;
        let start_sort = dt_sort.constructors[0].fields[0].sort.clone();
        let end_sort = dt_sort.constructors[0].fields[1].sort.clone();
        let start_expr = alive_expr.clone().field_select(adt_name, "fld_start", start_sort.clone());
        let end_expr = alive_expr.clone().field_select(adt_name, "fld_end", end_sort);
        let (has_next, next_start) = if let Some(width) = start_sort.bitvec_width() {
            let has_next = if signed {
                start_expr.clone().bvslt(end_expr.clone())
            } else {
                start_expr.clone().bvult(end_expr.clone())
            };
            let one = Expr::bitvec_const(1u128, width);
            let next_start = start_expr.clone().bvadd(one);
            (has_next, next_start)
        } else if start_sort.is_int() {
            let has_next = start_expr.clone().int_lt(end_expr.clone());
            let next_start = start_expr.clone().int_add(Expr::int_const(1));
            (has_next, next_start)
        } else {
            return None;
        };
        let updated_start = Expr::ite(has_next.clone(), next_start, start_expr.clone());
        let cons_name = names::resolve_ctor_name(alive_sort, &adt_name);
        let updated_alive = Expr::datatype_constructor(
            adt_name.as_str(),
            cons_name,
            vec![updated_start, end_expr.clone()],
            alive_sort.clone(),
        );
        Some((start_expr, end_expr, has_next, updated_alive))
    }

    /// Codegen Step::forward_unchecked or Step::backward_unchecked.
    ///
    /// Part of #1478: Iterator stepping intrinsics.
    /// forward_unchecked(start, n) -> start + n; backward_unchecked(start, n) -> start - n.
    /// The caller guarantees no overflow; we emit a violation if it does (Part of #3406).
    ///
    /// REQUIRES: args.len() >= 2 (start, step)
    /// ENSURES: destination gets result of arithmetic operation
    pub(super) fn codegen_step_unchecked(
        &mut self,
        args: &[Operand],
        destination: &rustc_public::mir::Place,
        target: Option<usize>,
        is_forward: bool,
    ) -> Option<usize> {
        if args.len() < 2 {
            warn!("codegen_step_unchecked: insufficient args (need 2, got {})", args.len());
            return None;
        }

        let start = self.codegen_operand(&args[0])?;
        let step = self.codegen_operand(&args[1])?;

        debug!(
            "codegen_step_unchecked: start.sort={:?}, step.sort={:?}, forward={}",
            start.sort(),
            step.sort(),
            is_forward
        );

        // Coerce step to match start's width if needed
        let (start, step) = if start.sort().is_bitvec() && step.sort().is_bitvec() {
            let width = start.sort().bitvec_width().unwrap_or(POINTER_WIDTH);
            (start, Self::coerce_to_width(step, width))
        } else {
            (start, step)
        };

        // Part of #3406: Step::forward/backward_unchecked have UB on overflow.
        if start.sort().is_bitvec() && step.sort().is_bitvec() {
            let signed = self.operand_signedness(&args[0]).unwrap_or(false);
            let ok = match (is_forward, signed) {
                (true, true) => start.clone().bvadd_no_overflow_signed(step.clone()),
                (true, false) => start.clone().bvadd_no_overflow_unsigned(step.clone()),
                (false, true) => start.clone().bvsub_no_overflow_signed(step.clone()),
                (false, false) => start.clone().bvsub_no_underflow_unsigned(step.clone()),
            };
            self.record_violation_guarded(ok.not(), "step_unchecked_overflow");
        }

        // Compute result: start + step (forward) or start - step (backward)
        let result = if is_forward {
            if start.sort().is_bitvec() {
                start.bvadd(step)
            } else if start.sort().is_int() {
                start.int_add(step)
            } else {
                warn!(
                    "codegen_step_unchecked: unsupported sort {:?} for forward step",
                    start.sort()
                );
                // Part of #3211: Track constraint drop in demotion pipeline.
                self.ctx.unsupported_with_fallback(
                    "step_unchecked_sort_drop",
                    "unsupported sort for forward step",
                );
                return None;
            }
        } else if start.sort().is_bitvec() {
            start.bvsub(step)
        } else if start.sort().is_int() {
            start.int_sub(step)
        } else {
            warn!("codegen_step_unchecked: unsupported sort {:?} for backward step", start.sort());
            // Part of #3211: Track constraint drop in demotion pipeline.
            self.ctx.unsupported_with_fallback(
                "step_unchecked_sort_drop",
                "unsupported sort for backward step",
            );
            return None;
        };

        self.assign_value_to_place(destination, result);
        target
    }

    /// Build `Option<T>` expression from a predicate and payload.
    pub(super) fn build_option_expr(
        &self,
        destination: &rustc_public::mir::Place,
        is_some: Expr,
        payload: Expr,
    ) -> Option<Expr> {
        let option_ty = destination.ty(self.body.locals()).into_option()?;
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = option_ty.kind() else {
            return None;
        };
        let variants = def.variants();
        if variants.len() != 2 {
            return None;
        }
        let v0_fields = variants[0].fields().len();
        let v1_fields = variants[1].fields().len();
        if !((v0_fields == 0 && v1_fields == 1) || (v0_fields == 1 && v1_fields == 0)) {
            return None;
        }
        // Get adt_name before moving args into infer_adt_sort
        let adt_name = Self::adt_sort_name(def, &args);
        let sort = Self::infer_adt_sort(def, args)?;
        // Part of #2549: Use scoped constructor names to avoid Z3
        // "ambiguous function declaration" with multiple Option instantiations.
        let some_name = names::option_some_constructor_name(&adt_name);
        let none_name = names::option_none_constructor_name(&adt_name);
        let some_expr =
            Expr::datatype_constructor(&*adt_name, some_name, vec![payload], sort.clone());
        let none_expr = Expr::datatype_constructor(adt_name, none_name, vec![], sort);
        Some(Expr::ite(is_some, some_expr, none_expr))
    }
}
