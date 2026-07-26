// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Copy/copy_nonoverlapping intrinsics (converted from include!() per #2595).

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::kani_middle::abi::LayoutOf;
use ay_bindings::Expr;
use rustc_public::mir::Operand;
use rustc_public::ty::{Allocation, ConstantKind, RigidTy, Span, TyConstKind, TyKind};
use tracing::{debug, warn};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen copy_nonoverlapping intrinsic.
    ///
    /// Copies `count` elements from `src` to `dst`. Elements are typed T,
    /// so this copies `count * size_of::<T>()` bytes total.
    ///
    /// Part of #1478: Implement copy/copy_nonoverlapping intrinsics.
    ///
    /// Memory model:
    /// - For constant counts with small total bytes: unroll byte-by-byte
    /// - For symbolic counts: guarded unrolled copy (Part of #3104)
    ///
    /// Soundness: We trust the caller that src and dst don't overlap.
    pub(super) fn codegen_copy_nonoverlapping(
        &mut self,
        src: &Operand,
        dst: &Operand,
        count: &Operand,
        span: Span,
    ) {
        // Get the element size from the src pointer type
        let element_size = src.ty(self.body.locals())
            .into_option()
            .and_then(|ty| {
                // src is a pointer *const T or *mut T - get the pointee type
                if let TyKind::RigidTy(RigidTy::RawPtr(pointee_ty, _)) = ty.kind() {
                    LayoutOf::new(pointee_ty).size_of()
                } else {
                    None
                }
            })
            .unwrap_or_else(|| {
                // Warn when we can't determine element size - defaulting to 1 could be wrong
                warn!(
                    "codegen_copy_nonoverlapping: couldn't determine element size, defaulting to 1 byte"
                );
                1
            });

        // Try to get constant count
        let count_const = self.try_eval_const_operand(count);

        debug!(
            "codegen_copy_nonoverlapping: element_size={}, span={:?}, count_const={:?}, count={:?}",
            element_size, span, count_const, count
        );

        // Defer location formatting until an error path needs it (Part of #2267).
        let location = || format!("{:?}", span);

        // Get src and dst pointer expressions
        let (Some(src_val), Some(dst_val)) = (self.codegen_operand(src), self.codegen_operand(dst))
        else {
            self.ctx.unsupported("CopyNonOverlapping: failed to codegen pointers", location());
            return;
        };

        // Coerce to pointer width
        let src_ptr = self.coerce_to_ptr_width(src_val);
        let dst_ptr = self.coerce_to_ptr_width(dst_val);

        // Maximum bytes to unroll (avoid explosion for large copies)
        const MAX_UNROLL_BYTES: usize = 128;

        match count_const {
            Some(count_val) => {
                // Constant count - unroll the copy
                let total_bytes = count_val.saturating_mul(element_size);

                if total_bytes == 0 {
                    // Zero-byte copy is a no-op
                    debug!("codegen_copy_nonoverlapping: zero-byte copy, skipping");
                    return;
                }

                if total_bytes <= MAX_UNROLL_BYTES {
                    // Unroll byte-by-byte
                    debug!("codegen_copy_nonoverlapping: unrolling {} bytes", total_bytes);
                    for i in 0..total_bytes {
                        let offset = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                        let src_addr = src_ptr.clone().bvadd(offset.clone());
                        let dst_addr = dst_ptr.clone().bvadd(offset);

                        // Load byte from src, store to dst
                        let byte = self.ctx.load_memory(src_addr);
                        self.ctx.store_memory(dst_addr, byte);
                    }
                } else {
                    // Too large to unroll - treat as unsupported with warning
                    self.ctx.unsupported_with_fallback(
                        "CopyNonOverlapping with large constant count",
                        format!(
                            "{} ({} bytes > {} limit)",
                            location(),
                            total_bytes,
                            MAX_UNROLL_BYTES
                        ),
                    );
                }
            }
            None => {
                // Symbolic count - guarded unrolled copy (Part of #3104).
                //
                // For each byte offset i in 0..MAX_UNROLL_BYTES, conditionally copy
                // src[i] to dst[i] when i < count * element_size. When the guard is
                // false, the destination byte is left unchanged.
                //
                // Soundness: correct for total_bytes <= MAX_UNROLL_BYTES. If the
                // solver explores paths where count * element_size > MAX_UNROLL_BYTES,
                // bytes beyond the limit are unchanged (truncation). For harnesses
                // with assume(count <= N) where N * element_size <= 128, this is
                // exact. Falls back to unsupported_with_fallback when even count=1
                // exceeds the limit (element_size > MAX_UNROLL_BYTES).
                if element_size > MAX_UNROLL_BYTES {
                    self.ctx.unsupported_with_fallback(
                        "CopyNonOverlapping with symbolic count (element too large for unroll)",
                        format!(
                            "{} (element_size={} > {} limit)",
                            location(),
                            element_size,
                            MAX_UNROLL_BYTES
                        ),
                    );
                    return;
                }
                let count_expr = self.codegen_operand(count);
                if let Some(count_bv) = count_expr {
                    let count_bv = self.coerce_to_ptr_width(count_bv);
                    let elem_size_bv = Expr::bitvec_const(element_size as u128, POINTER_WIDTH);
                    let total_bv = count_bv.bvmul(elem_size_bv);

                    debug!(
                        "codegen_copy_nonoverlapping: guarded unroll for symbolic count, \
                         element_size={}, max_bytes={}",
                        element_size, MAX_UNROLL_BYTES
                    );

                    for i in 0..MAX_UNROLL_BYTES {
                        let offset = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                        // Guard: total bytes > i (i.e., this byte is within the copy range)
                        let guard = total_bv.clone().bvugt(offset.clone());
                        let src_addr = src_ptr.clone().bvadd(offset.clone());
                        let dst_addr = dst_ptr.clone().bvadd(offset);

                        let src_byte = self.ctx.load_memory(src_addr);
                        let dst_byte = self.ctx.load_memory(dst_addr.clone());
                        // If guard: copy src byte; else: preserve dst byte
                        let value = Expr::ite(guard, src_byte, dst_byte);
                        self.ctx.store_memory(dst_addr, value);
                    }
                } else {
                    // Count operand failed to codegen - fall back to unsupported
                    self.ctx.unsupported_with_fallback(
                        "CopyNonOverlapping with symbolic count (operand codegen failed)",
                        location(),
                    );
                }
            }
        }
    }

    /// Codegen copy intrinsic (overlapping allowed).
    ///
    /// Copies `count` elements from `src` to `dst` with memmove semantics.
    /// Elements are typed T, so this copies `count * size_of::<T>()` bytes total.
    ///
    /// Part of #1479: Implement copy intrinsic for function call paths.
    ///
    /// Memory model:
    /// - For constant counts with small total bytes: load into temporaries, then store
    /// - For symbolic counts: two-phase guarded unrolled copy (Part of #3104)
    pub(super) fn codegen_copy(
        &mut self,
        src: &Operand,
        dst: &Operand,
        count: &Operand,
        span: Span,
    ) {
        // Get the element size from the src pointer type
        let element_size = src
            .ty(self.body.locals())
            .into_option()
            .and_then(|ty| {
                // src is a pointer *const T or *mut T - get the pointee type
                if let TyKind::RigidTy(RigidTy::RawPtr(pointee_ty, _)) = ty.kind() {
                    LayoutOf::new(pointee_ty).size_of()
                } else {
                    None
                }
            })
            .unwrap_or_else(|| {
                warn!("codegen_copy: couldn't determine element size, defaulting to 1 byte");
                1
            });

        // Try to get constant count
        let count_const = self.try_eval_const_operand(count);

        debug!(
            "codegen_copy: element_size={}, span={:?}, count_const={:?}, count={:?}",
            element_size, span, count_const, count
        );

        // Defer location formatting until an error path needs it (Part of #2267).
        let location = || format!("{:?}", span);

        // Get src and dst pointer expressions
        let (Some(src_val), Some(dst_val)) = (self.codegen_operand(src), self.codegen_operand(dst))
        else {
            self.ctx.unsupported("Copy: failed to codegen pointers", location());
            return;
        };

        let src_ptr = self.coerce_to_ptr_width(src_val);
        let dst_ptr = self.coerce_to_ptr_width(dst_val);

        // Maximum bytes to unroll (avoid explosion for large copies)
        const MAX_UNROLL_BYTES: usize = 128;

        match count_const {
            Some(count_val) => {
                let total_bytes = count_val.saturating_mul(element_size);

                if total_bytes == 0 {
                    debug!("codegen_copy: zero-byte copy, skipping");
                    return;
                }

                if total_bytes <= MAX_UNROLL_BYTES {
                    debug!("codegen_copy: unrolling {} bytes", total_bytes);

                    let mut temp_bytes = Vec::with_capacity(total_bytes);
                    for i in 0..total_bytes {
                        let offset = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                        let src_addr = src_ptr.clone().bvadd(offset);
                        let byte = self.ctx.load_memory(src_addr);
                        temp_bytes.push(byte);
                    }

                    for (i, byte) in temp_bytes.into_iter().enumerate() {
                        let offset = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                        let dst_addr = dst_ptr.clone().bvadd(offset);
                        self.ctx.store_memory(dst_addr, byte);
                    }
                } else {
                    self.ctx.unsupported_with_fallback(
                        "Copy with large constant count",
                        format!(
                            "{} ({} bytes > {} limit)",
                            location(),
                            total_bytes,
                            MAX_UNROLL_BYTES
                        ),
                    );
                }
            }
            None => {
                // Symbolic count - guarded unrolled copy with overlap safety (Part of #3104).
                //
                // For overlapping copy (memmove semantics), load ALL source bytes first
                // into temporaries, then conditionally store to destination. This prevents
                // reads from seeing partially-written destination values.
                //
                // Soundness: see codegen_copy_nonoverlapping for truncation caveat.
                if element_size > MAX_UNROLL_BYTES {
                    self.ctx.unsupported_with_fallback(
                        "Copy with symbolic count (element too large for unroll)",
                        format!(
                            "{} (element_size={} > {} limit)",
                            location(),
                            element_size,
                            MAX_UNROLL_BYTES
                        ),
                    );
                    return;
                }
                let count_expr = self.codegen_operand(count);
                if let Some(count_bv) = count_expr {
                    let count_bv = self.coerce_to_ptr_width(count_bv);
                    let elem_size_bv = Expr::bitvec_const(element_size as u128, POINTER_WIDTH);
                    let total_bv = count_bv.bvmul(elem_size_bv);

                    debug!(
                        "codegen_copy: guarded unroll for symbolic count, \
                         element_size={}, max_bytes={}",
                        element_size, MAX_UNROLL_BYTES
                    );

                    // Phase 1: Load all source bytes into temporaries
                    let mut temp_bytes = Vec::with_capacity(MAX_UNROLL_BYTES);
                    for i in 0..MAX_UNROLL_BYTES {
                        let offset = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                        let src_addr = src_ptr.clone().bvadd(offset);
                        temp_bytes.push(self.ctx.load_memory(src_addr));
                    }

                    // Phase 2: Conditionally store to destination
                    for (i, src_byte) in temp_bytes.into_iter().enumerate() {
                        let offset = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                        let guard = total_bv.clone().bvugt(offset.clone());
                        let dst_addr = dst_ptr.clone().bvadd(offset);
                        let dst_byte = self.ctx.load_memory(dst_addr.clone());
                        let value = Expr::ite(guard, src_byte, dst_byte);
                        self.ctx.store_memory(dst_addr, value);
                    }
                } else {
                    self.ctx.unsupported_with_fallback(
                        "Copy with symbolic count (operand codegen failed)",
                        location(),
                    );
                }
            }
        }
    }

    /// Try to evaluate an operand as a constant usize.
    pub(super) fn try_eval_const_operand(&self, operand: &Operand) -> Option<usize> {
        match operand {
            Operand::Constant(const_op) => {
                let mir_const = &const_op.const_;
                let ty = mir_const.ty();

                // Helper to extract value from allocation based on type
                let extract_from_alloc =
                    |alloc: &Allocation, ty: rustc_public::ty::Ty| -> Option<usize> {
                        match ty.kind() {
                            TyKind::RigidTy(RigidTy::Uint(_)) => {
                                alloc.read_uint().into_option().and_then(|v| v.try_into().ok())
                            }
                            TyKind::RigidTy(RigidTy::Int(_)) => {
                                // Also handle signed integers (for completeness)
                                let v = alloc.read_int().into_option()?;
                                if v >= 0 { usize::try_from(v).ok() } else { None }
                            }
                            _ => None, // external enum: TyKind
                        }
                    };

                // Extract value from constant
                match mir_const.kind() {
                    ConstantKind::Allocated(alloc) => extract_from_alloc(alloc, ty),
                    ConstantKind::Ty(ty_const) => match ty_const.kind() {
                        TyConstKind::Value(value_ty, alloc) => extract_from_alloc(alloc, *value_ty),
                        _ => None, // external enum: TyConstKind
                    },
                    _ => None, // external enum: ConstantKind
                }
            }
            Operand::Copy(_) | Operand::Move(_) => {
                // Copy/Move operands are not constants
                None
            }
        }
    }
}

// write_bytes intrinsic moved to codegen_write_bytes.rs per #4206.
