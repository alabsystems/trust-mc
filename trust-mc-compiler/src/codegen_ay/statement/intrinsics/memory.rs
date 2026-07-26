// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Memory intrinsics for AY codegen.
//!
//! This module implements Rust memory intrinsics:
//! - align_of_val: return alignment of the type behind a pointer
//! - size_of_val: return size of the type behind a pointer
//!
//! Part of #1479 and #1487.
//!
//! Extracted from intrinsics.rs per #1735.

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::IntoOption;
use crate::codegen_ay::statement::StatementCodegen;
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};
use crate::kani_middle::abi::LayoutOf;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen align_of_val - return alignment of the type behind a pointer.
    ///
    /// Part of #1479 and #1487.
    ///
    /// For statically-sized types, returns compile-time alignment.
    /// For DSTs, returns a symbolic value constrained to be >= 1.
    ///
    /// REQUIRES: args.len() >= 1, args[0] is a pointer/reference
    /// ENSURES: destination gets usize value for alignment
    pub(in crate::codegen_ay::statement) fn codegen_align_of_val(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let base_name = self.ssa_base_name(destination);
        let dest_name = self.ssa_name_from_base(&base_name, true);
        let dest_expr = self.ctx.declare_var(&dest_name, ptr_sort());

        // Try to get the pointee type to determine static alignment
        if let Some(arg) = args.first() {
            let arg_ty = arg.ty(self.body.locals()).into_option();
            if let Some(ty) = arg_ty {
                // For pointers/references, get the pointee type
                if let TyKind::RigidTy(rigid_ty) = ty.kind() {
                    let pointee_ty = match rigid_ty {
                        RigidTy::Ref(_, pointee, _) => Some(pointee),
                        RigidTy::RawPtr(pointee, _) => Some(pointee),
                        _ => None, // external enum: RigidTy
                    };

                    if let Some(pointee) = pointee_ty {
                        // Part of #3210 Dir 4: Use LayoutOf::align_of() which returns
                        // None for dyn-trait DSTs (alignment needs runtime vtable lookup).
                        // Sized types and slice-tail DSTs get compile-time alignment.
                        if pointee.layout().is_ok() {
                            let layout = LayoutOf::new(pointee);
                            if let Some(align) = layout.align_of() {
                                let align_val = Expr::bitvec_const(align as u128, POINTER_WIDTH);
                                self.assert_ssa_def(dest_expr.clone(), align_val, &base_name);
                                self.env_update(base_name, dest_expr);
                                debug!(
                                    "codegen_align_of_val: static alignment {} for {:?}",
                                    align, pointee
                                );
                                return target;
                            }
                        }
                    }
                }
            }
        }

        // Fall back to symbolic alignment for DSTs
        // Constraint: align >= 1 (minimal alignment guarantee)
        // Note: Real alignments are powers of 2, but enforcing that adds complexity
        // without significant verification benefit in most cases.
        let one = Expr::bitvec_const(1u128, POINTER_WIDTH);
        self.assert_guarded(dest_expr.clone().bvuge(one));
        self.env_update(base_name, dest_expr);
        debug!("codegen_align_of_val: using symbolic alignment (DST or unknown type)");
        target
    }

    /// Codegen checked_size_of_raw / checked_align_of_raw intrinsics.
    ///
    /// Part of #2076: These Kani intrinsics return `Option<usize>`:
    /// - `checked_size_of_raw<T>(ptr: *const T) -> Option<usize>`
    /// - `checked_align_of_raw<T>(ptr: *const T) -> Option<usize>`
    ///
    /// For sized types, returns `Some(size_of::<T>())` or `Some(align_of::<T>())`.
    /// For unsized/foreign types, returns a symbolic `Option<usize>`.
    ///
    /// The `is_size` parameter selects between size (true) and alignment (false).
    pub(in crate::codegen_ay::statement) fn codegen_checked_size_or_align(
        &mut self,
        args: &[Operand],
        destination: &Place,
        is_size: bool,
    ) {
        let base_name = self.ssa_base_name(destination);

        // Extract pointee type from the pointer argument
        if let Some(arg) = args.first()
            && let Some(ty) = arg.ty(self.body.locals()).into_option()
        {
            let pointee_ty = match ty.kind() {
                TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => Some(pointee),
                TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => Some(pointee),
                _ => None, // external enum: TyKind
            };
            if let Some(pointee) = pointee_ty
                && pointee.layout().is_ok()
            {
                // Part of #3210 Dir 4: Use LayoutOf to gate on sized/slice-tail types.
                // size_of() returns None for unsized; align_of() returns None for dyn-trait.
                let layout = LayoutOf::new(pointee);
                let val = if is_size {
                    layout.size_of().map(|s| s as u128)
                } else {
                    layout.align_of().map(|a| a as u128)
                };
                if let Some(val) = val {
                    let val_expr = Expr::bitvec_const(val, POINTER_WIDTH);

                    // Part of #2076: Use flat bitvec representation instead of SMT datatypes
                    // to avoid DT+BV theory mixing (ay#1766). Store the payload value directly
                    // under the base name (Discriminant handler recognizes Option bitvec → returns 1),
                    // and under the piecewise key for Downcast→Field extraction.
                    let lhs_name = self.ssa_name_from_base(&base_name, true);
                    let lhs_var = self.ctx.declare_var(&lhs_name, ptr_sort());
                    self.assert_ssa_def(lhs_var.clone(), val_expr.clone(), &base_name);
                    self.env_update(base_name.clone(), lhs_var);

                    // Store under piecewise key: {base}_variant_1_field_0
                    // Option::Some is variant 1 (None=0, Some=1)
                    let field_key =
                        crate::codegen_ay::names::base_variant_field_name(&base_name, 1, 0);
                    let field_name = self.ssa_name_from_base(&field_key, true);
                    let field_var = self.ctx.declare_var(&field_name, ptr_sort());
                    self.assert_ssa_def(field_var.clone(), val_expr, &field_key);
                    self.env_update(field_key, field_var);

                    let kind = if is_size { "size" } else { "align" };
                    debug!(
                        "codegen_checked_{}: flat Some({}) for {:?} (Part of #2076)",
                        kind, val, pointee
                    );
                    return;
                }
            }
        }

        // Fallback: symbolic Option<usize> for unsized/foreign types
        let option_sort = self.make_option_sort(ptr_sort());
        self.ctx.ensure_datatype_declared(&option_sort);
        let name = self.ssa_name_from_base(&base_name, true);
        let symbolic = self.ctx.declare_var(&name, option_sort);
        self.env_update(base_name, symbolic);
        let kind = if is_size { "size" } else { "align" };
        debug!("codegen_checked_{}: symbolic fallback (unsized type)", kind);
    }

    /// Codegen size_of_val - return size of the type behind a pointer.
    ///
    /// Part of #1479 and #1487.
    ///
    /// For statically-sized types, returns compile-time size.
    /// For DSTs, returns a symbolic value (conservative overapproximation).
    ///
    /// REQUIRES: args.len() >= 1, args[0] is a pointer/reference
    /// ENSURES: destination gets usize value for size
    pub(in crate::codegen_ay::statement) fn codegen_size_of_val(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let base_name = self.ssa_base_name(destination);
        let dest_name = self.ssa_name_from_base(&base_name, true);
        let dest_expr = self.ctx.declare_var(&dest_name, ptr_sort());

        // Try to get the pointee type to determine static size
        if let Some(arg) = args.first() {
            let arg_ty = arg.ty(self.body.locals()).into_option();
            if let Some(ty) = arg_ty {
                // For pointers/references, get the pointee type
                if let TyKind::RigidTy(rigid_ty) = ty.kind() {
                    let pointee_ty = match rigid_ty {
                        RigidTy::Ref(_, pointee, _) => Some(pointee),
                        RigidTy::RawPtr(pointee, _) => Some(pointee),
                        _ => None, // external enum: RigidTy
                    };

                    if let Some(pointee) = pointee_ty {
                        // Part of #3210 Dir 4: Use LayoutOf::size_of() which returns
                        // None for unsized types. Previously layout.shape().size.bytes()
                        // returned head-only size for DSTs, causing incorrect constants.
                        if pointee.layout().is_ok() {
                            let layout = LayoutOf::new(pointee);
                            if let Some(size) = layout.size_of() {
                                let size_val = Expr::bitvec_const(size as u128, POINTER_WIDTH);
                                self.assert_ssa_def(dest_expr.clone(), size_val, &base_name);
                                self.env_update(base_name, dest_expr);
                                debug!(
                                    "codegen_size_of_val: static size {} for {:?}",
                                    size, pointee
                                );
                                return target;
                            }
                        }
                    }
                }
            }
        }

        // Fall back to symbolic size for DSTs
        // Note: For unsigned bitvectors, size >= 0 is implicit.
        // The symbolic value represents any valid size for the DST.
        self.env_update(base_name, dest_expr);
        debug!("codegen_size_of_val: using symbolic size (DST or unknown type)");
        target
    }
}
