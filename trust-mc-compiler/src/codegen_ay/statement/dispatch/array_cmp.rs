// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Array/slice comparison dispatch for BMC path.
//!
//! Intercepts `<[T] as PartialOrd>::partial_cmp` on array-sorted operands
//! and `Option::is_some_and` with Ordering comparison methods.
//!
//! Part of #3806: lexicographic comparison support for SIMD PartialOrd.

mod range_contains;
mod range_full;

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place, Rvalue, StatementKind};
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::statement::StatementCodegen;
use crate::rustc_public::CrateDef;

use self::range_contains::is_range_contains_call;
use self::range_full::is_range_full_index_call;
use super::super::IntoOption;

/// Maximum lanes for unrolled lexicographic comparison in BMC path.
const MAX_LEXICO_LANES: usize = 16;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Try to handle array/slice comparison calls and `is_some_and` with
    /// Ordering methods in the BMC dispatch chain.
    ///
    /// Returns `Some(next_bb)` if handled, `None` to continue dispatch.
    pub(in crate::codegen_ay::statement) fn try_codegen_array_cmp_call(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let callee_path = self.resolve_callee_path(func)?;

        if is_range_contains_call(&callee_path)
            && let Some(bb) = self.try_codegen_range_contains(args, destination, target)
        {
            return Some(bb);
        }

        if is_range_full_index_call(&callee_path, args, self.body.locals()) {
            if let Some(bb) = self.try_codegen_range_full_index(args, destination, target) {
                return Some(bb);
            }
        }

        if callee_path.contains("PartialOrd") && callee_path.ends_with("partial_cmp") {
            if let Some(bb) = self.try_codegen_slice_partial_cmp(args, destination, target) {
                return Some(bb);
            }
        }

        if callee_path.contains("Option") && callee_path.contains("is_some_and") {
            return self.try_codegen_is_some_and_ordering(func, args, destination, target);
        }

        None
    }

    /// Handle `<[T] as PartialOrd>::partial_cmp(&self, &other)` by building
    /// lexicographic comparison when operands are array-sorted.
    fn try_codegen_slice_partial_cmp(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        let lhs_raw = self.get_value_through_ref(&args[0])?;
        let rhs_raw = self.get_value_through_ref(&args[1])?;

        // Extract array data from the resolved operands.
        // Operands may be:
        // 1. Direct Array sort (simple case)
        // 2. Slice_* Datatype with fld_data: Array (from Unsize coercion chain)
        // 3. BV64 pointer (need MIR tracing fallback)
        let lhs = extract_array_data(&lhs_raw).or_else(|| {
            self.resolve_operand_to_array(&args[0]).and_then(|e| extract_array_data(&e))
        });
        let rhs = extract_array_data(&rhs_raw).or_else(|| {
            self.resolve_operand_to_array(&args[1]).and_then(|e| extract_array_data(&e))
        });
        let (lhs, rhs) = match (lhs, rhs) {
            (Some(l), Some(r)) => (l, r),
            _ => return None,
        };

        // Both operands must be array-sorted
        let lhs_arr = lhs.sort().array_sort()?;
        let rhs_arr = rhs.sort().array_sort()?;
        if lhs_arr.element_sort != rhs_arr.element_sort {
            return None;
        }
        if !lhs_arr.element_sort.is_bitvec() {
            return None;
        }

        let len = self.array_len_from_mir_args(&args[0])?;
        if len == 0 || len > MAX_LEXICO_LANES {
            return None;
        }

        let is_signed = self.operand_signedness(&args[0]).unwrap_or(false);
        let idx_width = lhs_arr.index_sort.bitvec_width()?;

        debug!(len, is_signed, "array_cmp: building lexicographic partial_cmp (#3806)");

        // Build lexicographic ordering: -1 (Less), 0 (Equal), 1 (Greater)
        let ordering_bv = build_lexicographic_ordering(&lhs, &rhs, len, idx_width, is_signed);

        // Wrap in Option<Ordering>: always Some since both arrays are the same length.
        // Ordering is encoded as bitvec(32). Option<Ordering> is a Datatype.
        // Infer the destination sort to get the exact Option<Ordering> Datatype name.
        let dest_ty = destination.ty(self.body.locals()).into_option()?;
        let dest_sort = Self::infer_sort_from_ty(dest_ty)?;

        if let Some(dt) = dest_sort.datatype_sort() {
            // Find the Some constructor (1 field)
            let some_cons = dt.constructors.iter().find(|c| c.fields.len() == 1)?;
            let result = Expr::datatype_constructor(
                &dt.name,
                &some_cons.name,
                vec![ordering_bv],
                dest_sort.clone(),
            );
            self.bind_ssa_result(destination, result);
            return target;
        }

        // Fallback: if dest is not a Datatype (e.g., flattened), just assign the raw ordering
        self.bind_ssa_result(destination, ordering_bv);
        target
    }

    /// Handle `Option::is_some_and(self, f)` where `f` is a known Ordering method.
    ///
    /// Recognizes `Ordering::is_gt`, `is_ge`, `is_lt`, `is_le`, `is_eq`, `is_ne`
    /// as the closure argument and produces a boolean result.
    fn try_codegen_is_some_and_ordering(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            return None;
        }

        // Extract the closure/fn type from generic args to determine which Ordering method
        let func_ty = func.ty(self.body.locals()).into_option()?;
        let fn_args = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(_, substs)) => substs,
            _ => return None,
        };

        // The second generic arg is the closure/fn type
        let ordering_method = fn_args.0.iter().find_map(|arg| {
            if let GenericArgKind::Type(ty) = arg
                && let TyKind::RigidTy(RigidTy::FnDef(def, _)) = ty.kind()
            {
                let name = def.name();
                if name.contains("Ordering") {
                    if name.ends_with("is_gt") {
                        return Some("gt");
                    }
                    if name.ends_with("is_ge") {
                        return Some("ge");
                    }
                    if name.ends_with("is_lt") {
                        return Some("lt");
                    }
                    if name.ends_with("is_le") {
                        return Some("le");
                    }
                    if name.ends_with("is_eq") {
                        return Some("eq");
                    }
                    if name.ends_with("is_ne") {
                        return Some("ne");
                    }
                }
            }
            None
        })?;

        debug!(
            ordering_method,
            "array_cmp: handling is_some_and(Ordering::{}) (#3806)", ordering_method
        );

        // args[0] is the Option<Ordering> (self), args[1] is the closure/fn
        let option_val = self.codegen_operand(&args[0])?;

        // Extract the Ordering bitvec from the Option Datatype
        let option_sort = option_val.sort().clone();
        let ordering_bv = if let Some(dt) = option_sort.datatype_sort() {
            // Option<Ordering> Datatype: check if Some, extract payload
            let some_cons = dt.constructors.iter().find(|c| c.fields.len() == 1)?;
            let is_some = option_val.clone().is_constructor(&dt.name, &some_cons.name);
            let payload = option_val.field_select(
                &*dt.name,
                &*some_cons.fields[0].name,
                some_cons.fields[0].sort.clone(),
            );
            // If None, the comparison is false (partial_cmp returned None)
            Some((is_some, payload))
        } else if option_sort.is_bitvec() {
            // Flattened `Option<Ordering>` stores the payload in the base local
            // and the discriminant in the sibling `.0` projection.
            let is_some = self.flattened_option_is_some_guard(&args[0])?;
            Some((is_some, option_val))
        } else {
            return None;
        };

        let (is_some, payload) = ordering_bv?;

        // Ordering encoding: Less=0xFFFFFFFF (-1 in BV32), Equal=0, Greater=1
        // Fix #4213: was 0xFF (255) which never matched SwitchInt's 0xFFFFFFFF.
        let result = match ordering_method {
            "gt" => is_some.and(payload.eq(Expr::bitvec_const(1u128, 32))),
            "ge" => is_some.and(
                payload
                    .clone()
                    .eq(Expr::bitvec_const(1u128, 32))
                    .or(payload.eq(Expr::bitvec_const(0u128, 32))),
            ),
            "lt" => is_some.and(payload.eq(Expr::bitvec_const(0xFFFF_FFFFu128, 32))),
            "le" => is_some.and(
                payload
                    .clone()
                    .eq(Expr::bitvec_const(0xFFFF_FFFFu128, 32))
                    .or(payload.eq(Expr::bitvec_const(0u128, 32))),
            ),
            "eq" => is_some.and(payload.eq(Expr::bitvec_const(0u128, 32))),
            "ne" => is_some.and(payload.ne(Expr::bitvec_const(0u128, 32))),
            _ => return None,
        };

        self.bind_ssa_result(destination, result);
        target
    }

    fn flattened_option_is_some_guard(&mut self, option_arg: &Operand) -> Option<Expr> {
        let place = match option_arg {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => return None,
        };
        if !place.projection.is_empty() {
            return None;
        }

        let discr_base = format!("{}.0", self.ssa_base_name(place));
        let discr = self.env_lookup(&discr_base)?;
        if discr.sort().is_bool() {
            return Some(discr.clone());
        }
        let width = discr.sort().bitvec_width()?;
        Some(discr.clone().eq(Expr::bitvec_const(1u128, width)))
    }

    /// Extract the array length from MIR argument types.
    ///
    /// Handles both `&[T; N]` (direct array ref) and `&[T]` (slice ref from
    /// unsizing coercion). For slices, scans body locals for `[T; N]` types.
    fn array_len_from_mir_args(&self, arg: &Operand) -> Option<usize> {
        let ty = arg.ty(self.body.locals()).into_option()?;
        // Peel through multiple reference levels (handles &&[T; N] from blanket
        // `<&A as PartialOrd<&B>>::partial_cmp` which produces double-refs).
        // Part of #3806.
        let mut inner = ty;
        for _ in 0..3 {
            match inner.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => inner = pointee,
                _ => break,
            }
        }
        // Direct [T; N]
        if let TyKind::RigidTy(RigidTy::Array(_, const_len)) = inner.kind() {
            return const_len.eval_target_usize().ok().map(|n| n as usize);
        }
        // Slice: scan body locals for matching [T; N]
        if let TyKind::RigidTy(RigidTy::Slice(elem_ty)) = inner.kind() {
            return self.array_len_from_body_locals(elem_ty);
        }
        None
    }

    /// Scan body locals for `[T; N]` declarations matching the given element type.
    ///
    /// Also scans through SIMD ADT types (single-field `#[repr(simd)]` structs)
    /// and peels references to find embedded `[T; N]` types. Part of #3806.
    fn array_len_from_body_locals(&self, elem_ty: rustc_public::ty::Ty) -> Option<usize> {
        let mut found_len: Option<usize> = None;
        for local_decl in self.body.locals() {
            if let Some(len) = Self::extract_array_len_from_ty(local_decl.ty, elem_ty) {
                match found_len {
                    None => found_len = Some(len),
                    Some(existing) if existing == len => {}
                    Some(_) => return None, // ambiguous
                }
            }
        }
        found_len
    }

    /// Extract `[elem_ty; N]` length from a type, peeling through references,
    /// SIMD ADT wrappers, and raw pointers.
    fn extract_array_len_from_ty(
        ty: rustc_public::ty::Ty,
        elem_ty: rustc_public::ty::Ty,
    ) -> Option<usize> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Array(arr_elem, const_len)) => {
                if arr_elem == elem_ty {
                    return const_len.eval_target_usize().ok().map(|n| n as usize);
                }
                None
            }
            TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
                Self::extract_array_len_from_ty(inner, elem_ty)
            }
            TyKind::RigidTy(RigidTy::Adt(adt_def, args)) => {
                // SIMD types: single-variant, single-field ADTs wrapping [T; N]
                let variants = adt_def.variants();
                if variants.len() == 1 && variants[0].fields().len() == 1 {
                    let field_ty = variants[0].fields()[0].ty_with_args(&args);
                    Self::extract_array_len_from_ty(field_ty, elem_ty)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Resolve an operand to its underlying array-sorted SSA value.
    ///
    /// When `get_value_through_ref` returns a BV64 pointer (e.g., `&[i64]` from
    /// an Unsize coercion), this traces back through MIR assignments to find the
    /// source local that has array sort, then returns its SSA value.
    ///
    /// Handles chains like: `_N = Cast(Unsize, _M)` where `_M` has array sort.
    /// Also follows `_N = Use(_M)` and `_N = Ref(_, _M)` patterns.
    ///
    /// Part of #3806.
    fn resolve_operand_to_array(&mut self, arg: &Operand) -> Option<Expr> {
        let place = match arg {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => return None,
        };
        if !place.projection.is_empty() {
            return None;
        }

        let mut current_local: usize = place.local;
        let mut visited = std::collections::HashSet::new();
        for _hop in 0..4 {
            if !visited.insert(current_local) {
                return None; // cycle
            }

            let local_place = Place { local: current_local, projection: vec![] };

            // Check if ref_pointees has a mapping for this local
            let ref_base = self.ssa_base_name(&local_place);
            if let Some(pointee_base) = self.ref_pointees.get(ref_base.as_str()).cloned() {
                if let Some(expr) = self.env_lookup(&pointee_base) {
                    if expr.sort().is_array() {
                        return Some(expr.clone());
                    }
                }
            }

            // Check if this local's SSA value is already array-sorted
            if let Some(expr) = self.codegen_place(&local_place) {
                if expr.sort().is_array() {
                    return Some(expr);
                }
            }

            // Scan MIR for the source of this assignment
            if let Some(src_local) = self.find_mir_source_local_for_array(current_local) {
                current_local = src_local;
                continue;
            }

            return None;
        }
        None
    }

    /// Scan MIR body to find the source local of an assignment to `dest_local`.
    ///
    /// Returns `Some(source_local)` for Cast/Use/Ref patterns.
    /// Part of #3806.
    fn find_mir_source_local_for_array(&self, dest_local: usize) -> Option<usize> {
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
                        if src.projection.is_empty() =>
                    {
                        return Some(src.local);
                    }
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
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

/// Extract the array data from an expression.
///
/// Handles:
/// - Direct Array sort: returns as-is
/// - Slice_* Datatype: extracts the `fld_data` field (Array sort)
///
/// Part of #3806.
fn extract_array_data(expr: &Expr) -> Option<Expr> {
    if expr.sort().is_array() {
        return Some(expr.clone());
    }
    // Slice Datatype: Slice_bvN { fld_ptr: BV64, fld_len: BV64, fld_data: Array<BV64, BVN> }
    let dt = expr.sort().datatype_sort()?;
    if !dt.name.starts_with("Slice_") || dt.constructors.len() != 1 {
        return None;
    }
    let cons = &dt.constructors[0];
    let data_field = cons.fields.iter().find(|f| &*f.name == "fld_data")?;
    if !data_field.sort.is_array() {
        return None;
    }
    Some(expr.clone().field_select(&*dt.name, "fld_data", data_field.sort.clone()))
}

/// Build a lexicographic ordering ITE chain for fixed-size arrays.
///
/// Returns BV32: Less=0xFFFFFFFF (-1), Equal=0, Greater=1 (matching Rust Ordering).
/// Fix #4213: was 0xFF (255) which never matched SwitchInt's 0xFFFFFFFF.
fn build_lexicographic_ordering(
    lhs: &Expr,
    rhs: &Expr,
    len: usize,
    idx_width: u32,
    is_signed: bool,
) -> Expr {
    let neg1 = Expr::bitvec_const(0xFFFF_FFFFu128, 32); // Less = -1 in BV32
    let pos1 = Expr::bitvec_const(1u128, 32); // Greater

    let mut result = Expr::bitvec_const(0u128, 32); // Equal
    for i in (0..len).rev() {
        let idx = Expr::bitvec_const(i as u64, idx_width);
        let l = lhs.clone().select(idx.clone());
        let r = rhs.clone().select(idx);
        let lt = if is_signed { l.clone().bvslt(r.clone()) } else { l.clone().bvult(r.clone()) };
        let gt = if is_signed { l.bvsgt(r) } else { l.bvugt(r) };
        result = Expr::ite(lt, neg1.clone(), Expr::ite(gt, pos1.clone(), result));
    }
    result
}
