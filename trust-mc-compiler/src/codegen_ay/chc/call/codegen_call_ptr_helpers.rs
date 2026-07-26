// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pointer call helpers: metadata propagation, unsized size_of_val_raw,
//! ptr.add definedness constraints, and element-size extraction.
//!
//! Extracted from `codegen_call_ptr.rs` — Part of #4206.

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};

use super::ChcCtx;
use super::codegen_call_kani_model_dst::extract_fat_ptr_len;
use crate::codegen_ay::chc::get_ptr_metadata_unconstrained_count;
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};
use crate::kani_middle::abi::LayoutOf;
use tracing::debug;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Compute dynamic size for `size_of_val_raw` on unsized types (str, [T]).
    ///
    /// For unsized types, `get_type_size()` returns the element size (1 for str,
    /// sizeof(T) for [T]), but `size_of_val_raw` should return `elem_size * len`
    /// where `len` is the fat pointer metadata. This helper extracts the dynamic
    /// length from the call arguments and computes the total size.
    ///
    /// Returns `None` if the type is sized. For unsized types where the fat
    /// pointer metadata is unresolved, returns an expression built from the
    /// `PtrMetadata` fallback path so downstream dealloc size checks stay
    /// aligned with the dedicated `ptr_metadata_unconstrained` counter.
    ///
    /// Part of #3655: fixes Box<str> dealloc CTREX caused by Layout{size:1}
    /// (element size) instead of Layout{size:len} (allocation size).
    pub(in crate::codegen_ay::chc) fn try_unsized_size_of_val_raw(
        &mut self,
        func: &Operand,
        args: &[Operand],
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<Expr> {
        let ty = self.mem_intrinsic_type_arg(func)?;
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Str) => {
                // str: size_of_val_raw = ptr metadata (byte length)
                // Part of #3655: Track whether extract_fat_ptr_len fell through
                // to the unconstrained PtrMetadata symbolic path. If it did,
                // the result is an over-approximation (universally quantified
                // in CHC — must hold for ALL lengths), not a concrete resolution.
                let before = get_ptr_metadata_unconstrained_count();
                let len = extract_fat_ptr_len(self, args, modified_locals)?;
                let after = get_ptr_metadata_unconstrained_count();
                let used_unconstrained_fallback = after > before;
                if used_unconstrained_fallback {
                    // extract_fat_ptr_len returned a fresh symbolic from
                    // translate_ptr_metadata — this is an over-approximation.
                    self.record_sound_fallback_categorized("ptr_metadata_unconstrained");
                    debug!("try_unsized_size_of_val_raw: str — PtrMetadata unconstrained fallback");
                }
                let len = coerce_bitvec_width_safe(len, POINTER_WIDTH, SignExtension::ZeroExtend);
                debug!("try_unsized_size_of_val_raw: str — using dynamic length");
                Some(len)
            }
            TyKind::RigidTy(RigidTy::Slice(elem_ty)) => {
                // [T]: size_of_val_raw = sizeof(T) * len
                let elem_size = self.get_type_size(elem_ty)? as u64;
                // Part of #3655: Same unconstrained-fallback detection as str.
                let before = get_ptr_metadata_unconstrained_count();
                let len = extract_fat_ptr_len(self, args, modified_locals)?;
                let after = get_ptr_metadata_unconstrained_count();
                if after > before {
                    self.record_sound_fallback_categorized("ptr_metadata_unconstrained");
                    debug!("try_unsized_size_of_val_raw: [T] — PtrMetadata unconstrained fallback");
                }
                let len = coerce_bitvec_width_safe(len, POINTER_WIDTH, SignExtension::ZeroExtend);
                let elem_size_expr = Expr::bitvec_const(elem_size, POINTER_WIDTH);
                debug!(
                    elem_size,
                    "try_unsized_size_of_val_raw: [T] — using dynamic elem_size * len"
                );
                Some(elem_size_expr.bvmul(len))
            }
            TyKind::RigidTy(RigidTy::Adt(..)) => {
                // Custom DST: struct with unsized tail (str or [T]).
                // Part of #3768: Reuse slice-tail infrastructure from
                // codegen_call_kani_model_dst (compute_slice_tail_size_val pattern).
                let layout = LayoutOf::new(ty);
                if !layout.has_slice_tail() {
                    return None; // Not a slice-tail DST (might be dyn-trait tail).
                }
                let elem_ty = layout.unsized_tail_elem_ty()?;
                let elem_size_val = LayoutOf::new(elem_ty).size_of()? as u64;
                let head_size_val = layout.size_of_head() as u64;
                let align_val = layout.align_of()? as u64;

                let before = get_ptr_metadata_unconstrained_count();
                let len = extract_fat_ptr_len(self, args, modified_locals)?;
                let after = get_ptr_metadata_unconstrained_count();
                if after > before {
                    self.record_sound_fallback_categorized("ptr_metadata_unconstrained");
                    debug!("try_unsized_size_of_val_raw: ADT slice-tail — unconstrained fallback");
                }
                let len = coerce_bitvec_width_safe(len, POINTER_WIDTH, SignExtension::ZeroExtend);

                let elem_size = Expr::bitvec_const(elem_size_val, POINTER_WIDTH);
                let head_size = Expr::bitvec_const(head_size_val, POINTER_WIDTH);
                let align = Expr::bitvec_const(align_val, POINTER_WIDTH);
                let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
                let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);

                // size = round_up(elem_size * len + head_size, align)
                let total = elem_size.bvmul(len).bvadd(head_size);
                let adjust = total.bvadd(align.clone().bvsub(one));
                let adjusted_size = adjust.bvand(zero.bvsub(align));
                debug!(
                    elem_size_val,
                    head_size_val,
                    align_val,
                    "try_unsized_size_of_val_raw: ADT slice-tail resolved"
                );
                Some(adjusted_size)
            }
            _ => None,
        }
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn ptr_add_definedness_constraints(
        &mut self,
        args: &[Operand],
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Vec<Expr> {
        if args.len() < 2 {
            return Vec::new();
        }
        let ptr_op = &args[0];
        let count_op = &args[1];

        let Some(ptr) = self.translate_operand_with_modified(ptr_op, modified_locals) else {
            return Vec::new();
        };
        let ptr = coerce_bitvec_width_safe(ptr, POINTER_WIDTH, SignExtension::ZeroExtend);
        let Some(count) = self.translate_operand_with_modified(count_op, modified_locals) else {
            return Vec::new();
        };
        let count = coerce_bitvec_width_safe(count, POINTER_WIDTH, SignExtension::ZeroExtend);

        let elem_size = ptr_element_size(self, ptr_op).unwrap_or(1) as u128;
        let elem_size_expr = Expr::bitvec_const(elem_size, POINTER_WIDTH);
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        let isize_max = Expr::bitvec_const((1i128 << (POINTER_WIDTH - 1)) - 1, POINTER_WIDTH);
        let offset_bytes = count.clone().bvmul(elem_size_expr.clone());

        vec![
            count.clone().bvsge(zero),
            count.clone().bvsle(isize_max),
            count.bvmul_no_overflow_unsigned(elem_size_expr),
            ptr.bvadd_no_overflow_unsigned(offset_bytes),
        ]
    }
}

fn ptr_element_size(ctx: &ChcCtx<'_, '_>, operand: &Operand) -> Option<usize> {
    let ty = operand.ty(ctx.body.locals()).ok()?;
    match ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
        | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => ctx.get_type_size(pointee),
        TyKind::RigidTy(RigidTy::Adt(def, generic_args))
            if def.trimmed_name() == "NonNull" || def.trimmed_name() == "Unique" =>
        {
            generic_args.0.iter().find_map(|arg| {
                if let GenericArgKind::Type(pointee) = arg {
                    ctx.get_type_size(*pointee)
                } else {
                    None
                }
            })
        }
        _other => None,
    }
}
