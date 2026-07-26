// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Extended pointer arithmetic and utility stubs for AY codegen (#2671).
//!
//! Extracted from alloc_ptr.rs — PtrSub, PtrWrapping{Add,Sub,Offset},
//! PtrWithMetadataOf, NonNull::cast.

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use super::alloc::FALLBACK_PTR;
use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::kani_middle::abi::LayoutOf;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen `*mut T::sub(count) -> *mut T`.
    ///
    /// Pointer arithmetic: returns ptr - count * sizeof(T).
    /// The offset is in units of T, not bytes.
    ///
    /// REQUIRES: args.len() >= 2 (self ptr, count)
    /// ENSURES: destination receives ptr - offset_bytes
    pub(in crate::codegen_ay::statement) fn codegen_ptr_sub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            warn!("codegen_ptr_sub: insufficient args (need ptr, count), skipping");
            // Part of #3211: Track constraint drop in demotion pipeline.
            self.ctx.unsupported_with_fallback("ptr_sub_insufficient_args", "need ptr + count");
            return None;
        }

        let ptr = self.codegen_operand(&args[0]).unwrap_or_else(|| {
            debug!("codegen_ptr_sub: ptr arg failed");
            Expr::bitvec_const(FALLBACK_PTR, POINTER_WIDTH)
        });

        let count = self.codegen_operand(&args[1]).unwrap_or_else(|| {
            debug!("codegen_ptr_sub: count arg failed");
            Expr::bitvec_const(0, POINTER_WIDTH)
        });

        let elem_size = args[0]
            .ty(self.body.locals())
            .into_option()
            .and_then(|ty| match ty.kind() {
                TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
                | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => {
                    Some(LayoutOf::new(pointee).size_of_head())
                }
                _ => None, // external enum: TyKind
            })
            .unwrap_or(1);

        let ptr_coerced = self.coerce_to_ptr_width(ptr);
        let count_coerced = self.coerce_to_ptr_width(count);
        let elem_size_expr = Expr::bitvec_const(elem_size as u128, POINTER_WIDTH);
        let offset_bytes = count_coerced.bvmul(elem_size_expr);

        let new_ptr = ptr_coerced.bvsub(offset_bytes);
        self.assign_value_to_place(destination, new_ptr);
        debug!("codegen_ptr_sub: ptr - {} * {} = new_ptr", "count", elem_size);
        target
    }

    /// Codegen `*mut T::wrapping_add(count) -> *mut T`.
    ///
    /// Wrapping pointer arithmetic: ptr + count * sizeof(T) with wrapping.
    /// At the bitvector level, wrapping is the natural behavior.
    ///
    /// REQUIRES: args.len() >= 2 (self ptr, count)
    /// ENSURES: destination receives ptr + offset_bytes (wrapping)
    pub(in crate::codegen_ay::statement) fn codegen_ptr_wrapping_add(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Wrapping add is identical to regular add at the bitvector level
        self.codegen_ptr_add(args, destination, target)
    }

    /// Codegen `*mut T::wrapping_sub(count) -> *mut T`.
    ///
    /// Wrapping pointer arithmetic: ptr - count * sizeof(T) with wrapping.
    /// At the bitvector level, wrapping is the natural behavior.
    ///
    /// REQUIRES: args.len() >= 2 (self ptr, count)
    /// ENSURES: destination receives ptr - offset_bytes (wrapping)
    pub(in crate::codegen_ay::statement) fn codegen_ptr_wrapping_sub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Wrapping sub is identical to regular sub at the bitvector level
        self.codegen_ptr_sub(args, destination, target)
    }

    /// Codegen `*mut T::wrapping_offset(count) -> *mut T`.
    ///
    /// Wrapping pointer offset: ptr + count * sizeof(T) with signed count.
    /// At the bitvector level, signed addition wraps naturally.
    ///
    /// REQUIRES: args.len() >= 2 (self ptr, count)
    /// ENSURES: destination receives ptr + offset_bytes (wrapping)
    pub(in crate::codegen_ay::statement) fn codegen_ptr_wrapping_offset(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        // Wrapping offset with signed count — bitvector add handles both signs
        self.codegen_ptr_add(args, destination, target)
    }

    /// Codegen `*mut T::wrapping_byte_offset(count) -> *mut T`.
    ///
    /// Wrapping byte offset: ptr + count (byte-level, no sizeof(T) scaling).
    /// Part of #3510: split from PtrWrappingOffset which uses element-sized steps.
    ///
    /// REQUIRES: args.len() >= 2 (self ptr, count)
    /// ENSURES: destination receives ptr + byte_count (wrapping)
    pub(in crate::codegen_ay::statement) fn codegen_ptr_wrapping_byte_offset(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            warn!(
                "codegen_ptr_wrapping_byte_offset: insufficient args (need ptr, count), skipping"
            );
            self.ctx.unsupported_with_fallback(
                "ptr_wrapping_byte_offset_insufficient_args",
                "need ptr + count",
            );
            return None;
        }

        let ptr = self.codegen_operand(&args[0]).unwrap_or_else(|| {
            debug!("codegen_ptr_wrapping_byte_offset: ptr arg failed");
            Expr::bitvec_const(FALLBACK_PTR, POINTER_WIDTH)
        });

        let byte_count = self.codegen_operand(&args[1]).unwrap_or_else(|| {
            debug!("codegen_ptr_wrapping_byte_offset: count arg failed");
            Expr::bitvec_const(0, POINTER_WIDTH)
        });

        // Byte-level add — no sizeof(T) scaling
        let ptr_coerced = self.coerce_to_ptr_width(ptr);
        let count_coerced = self.coerce_to_ptr_width(byte_count);
        let new_ptr = ptr_coerced.bvadd(count_coerced);

        self.assign_value_to_place(destination, new_ptr);
        debug!("codegen_ptr_wrapping_byte_offset: ptr + byte_count = new_ptr");
        target
    }

    /// Codegen `*mut T::wrapping_byte_add(count) -> *mut T`.
    ///
    /// Wrapping byte add: ptr + count (byte-level, no sizeof(T) scaling).
    /// Part of #3514: split from PtrWrappingAdd which uses element-sized steps.
    ///
    /// REQUIRES: args.len() >= 2 (self ptr, count)
    /// ENSURES: destination receives ptr + byte_count (wrapping)
    pub(in crate::codegen_ay::statement) fn codegen_ptr_wrapping_byte_add(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            warn!("codegen_ptr_wrapping_byte_add: insufficient args (need ptr, count), skipping");
            self.ctx.unsupported_with_fallback(
                "ptr_wrapping_byte_add_insufficient_args",
                "need ptr + count",
            );
            return None;
        }

        let ptr = self.codegen_operand(&args[0]).unwrap_or_else(|| {
            debug!("codegen_ptr_wrapping_byte_add: ptr arg failed");
            Expr::bitvec_const(FALLBACK_PTR, POINTER_WIDTH)
        });

        let byte_count = self.codegen_operand(&args[1]).unwrap_or_else(|| {
            debug!("codegen_ptr_wrapping_byte_add: count arg failed");
            Expr::bitvec_const(0, POINTER_WIDTH)
        });

        // Byte-level add — no sizeof(T) scaling
        let ptr_coerced = self.coerce_to_ptr_width(ptr);
        let count_coerced = self.coerce_to_ptr_width(byte_count);
        let new_ptr = ptr_coerced.bvadd(count_coerced);

        self.assign_value_to_place(destination, new_ptr);
        debug!("codegen_ptr_wrapping_byte_add: ptr + byte_count = new_ptr");
        target
    }

    /// Codegen `*mut T::wrapping_byte_sub(count) -> *mut T`.
    ///
    /// Wrapping byte sub: ptr - count (byte-level, no sizeof(T) scaling).
    /// Part of #3514: split from PtrWrappingSub which uses element-sized steps.
    ///
    /// REQUIRES: args.len() >= 2 (self ptr, count)
    /// ENSURES: destination receives ptr - byte_count (wrapping)
    pub(in crate::codegen_ay::statement) fn codegen_ptr_wrapping_byte_sub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            warn!("codegen_ptr_wrapping_byte_sub: insufficient args (need ptr, count), skipping");
            self.ctx.unsupported_with_fallback(
                "ptr_wrapping_byte_sub_insufficient_args",
                "need ptr + count",
            );
            return None;
        }

        let ptr = self.codegen_operand(&args[0]).unwrap_or_else(|| {
            debug!("codegen_ptr_wrapping_byte_sub: ptr arg failed");
            Expr::bitvec_const(FALLBACK_PTR, POINTER_WIDTH)
        });

        let byte_count = self.codegen_operand(&args[1]).unwrap_or_else(|| {
            debug!("codegen_ptr_wrapping_byte_sub: count arg failed");
            Expr::bitvec_const(0, POINTER_WIDTH)
        });

        // Byte-level sub — no sizeof(T) scaling
        let ptr_coerced = self.coerce_to_ptr_width(ptr);
        let count_coerced = self.coerce_to_ptr_width(byte_count);
        let new_ptr = ptr_coerced.bvsub(count_coerced);

        self.assign_value_to_place(destination, new_ptr);
        debug!("codegen_ptr_wrapping_byte_sub: ptr - byte_count = new_ptr");
        target
    }

    /// Codegen `*const T::with_addr(addr) -> *const T`.
    ///
    /// `ptr.with_addr(addr)` returns a pointer with the given address.
    /// Semantically: `self.wrapping_byte_offset((addr as isize).wrapping_sub(self.addr() as isize))`
    /// which simplifies to just returning `addr` as a pointer.
    /// Part of #3532: BMC parity with CHC encoding (stubs_util_intrinsics.rs:659).
    ///
    /// REQUIRES: args.len() >= 2 (self ptr, addr)
    /// ENSURES: destination receives addr coerced to pointer width
    pub(in crate::codegen_ay::statement) fn codegen_ptr_with_addr(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            warn!("codegen_ptr_with_addr: insufficient args (need ptr, addr), skipping");
            self.ctx
                .unsupported_with_fallback("ptr_with_addr_insufficient_args", "need ptr + addr");
            return None;
        }

        let addr = self.codegen_operand(&args[1]).unwrap_or_else(|| {
            debug!("codegen_ptr_with_addr: addr arg failed, using fallback");
            Expr::bitvec_const(FALLBACK_PTR, POINTER_WIDTH)
        });

        let ptr = self.coerce_to_ptr_width(addr);
        self.assign_value_to_place(destination, ptr);
        debug!("codegen_ptr_with_addr: returning addr as pointer");
        target
    }

    /// Codegen `*mut T::with_metadata_of(ptr) -> *mut T`.
    ///
    /// For thin pointers (the common case), this is an identity operation.
    /// For fat pointers, it copies the metadata (vtable/length) from the
    /// second argument. Since we model pointers as bv64 without metadata,
    /// we return the first pointer argument directly.
    ///
    /// REQUIRES: args.len() >= 2 (self, metadata_source)
    /// ENSURES: destination receives self pointer value
    pub(in crate::codegen_ay::statement) fn codegen_ptr_with_metadata_of(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("codegen_ptr_with_metadata_of: missing ptr arg, skipping");
            // Part of #3211: Track constraint drop in demotion pipeline.
            self.ctx
                .unsupported_with_fallback("ptr_with_metadata_of_missing_arg", "missing ptr arg");
            return None;
        }

        let ptr = self.codegen_operand(&args[0]).unwrap_or_else(|| {
            debug!("codegen_ptr_with_metadata_of: ptr arg failed");
            Expr::bitvec_const(FALLBACK_PTR, POINTER_WIDTH)
        });

        let ptr = self.coerce_to_ptr_width(ptr);
        self.assign_value_to_place(destination, ptr);
        debug!("codegen_ptr_with_metadata_of: identity (thin pointer)");
        target
    }

    /// Codegen `NonNull::<T>::cast<U>() -> NonNull<U>`.
    ///
    /// Pointer type cast that changes the pointee type but not the address.
    /// At the verification level, this is an identity operation since we
    /// model all pointers as bv64 regardless of pointee type.
    ///
    /// REQUIRES: args.len() >= 1 (self)
    /// ENSURES: destination receives same pointer value
    pub(in crate::codegen_ay::statement) fn codegen_nonnull_cast(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            warn!("codegen_nonnull_cast: missing self arg, skipping");
            // Part of #3211: Track constraint drop in demotion pipeline.
            self.ctx.unsupported_with_fallback("nonnull_cast_missing_arg", "missing self arg");
            return None;
        }

        let ptr = self.codegen_operand(&args[0]).unwrap_or_else(|| {
            debug!("codegen_nonnull_cast: codegen_operand failed, using fallback");
            Expr::bitvec_const(FALLBACK_PTR, POINTER_WIDTH)
        });

        let ptr = self.coerce_to_ptr_width(ptr);
        self.assign_value_to_place(destination, ptr);
        debug!("codegen_nonnull_cast: type cast (identity at bv64 level)");
        target
    }
}
