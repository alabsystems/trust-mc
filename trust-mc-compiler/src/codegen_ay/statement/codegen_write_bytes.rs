// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! write_bytes intrinsic codegen.
//!
//! Extracted from `codegen_copy.rs` — Part of #4206.

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::kani_middle::abi::LayoutOf;
use ay_bindings::Expr;
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, Span, TyKind};
use tracing::{debug, warn};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen write_bytes intrinsic.
    ///
    /// Sets `count * size_of::<T>()` bytes of memory starting at `dst` to `val`.
    ///
    /// Part of #1478: Implement write_bytes intrinsic.
    ///
    /// Memory model:
    /// - For constant counts with small total bytes: unroll byte-by-byte stores
    /// - For symbolic counts: guarded unrolled write (Part of #3104)
    pub(super) fn codegen_write_bytes(
        &mut self,
        dst: &Operand,
        val: &Operand,
        count: &Operand,
        span: Span,
    ) {
        // Get the element size from the dst pointer type
        let element_size = dst
            .ty(self.body.locals())
            .into_option()
            .and_then(|ty| {
                // dst is a pointer *mut T - get the pointee type
                if let TyKind::RigidTy(RigidTy::RawPtr(pointee_ty, _)) = ty.kind() {
                    LayoutOf::new(pointee_ty).size_of()
                } else {
                    None
                }
            })
            .unwrap_or_else(|| {
                warn!("codegen_write_bytes: couldn't determine element size, defaulting to 1 byte");
                1
            });

        // Try to get constant count
        let count_const = self.try_eval_const_operand(count);

        debug!(
            "codegen_write_bytes: element_size={}, span={:?}, count_const={:?}",
            element_size, span, count_const
        );

        // UB when count * size_of::<T>() overflows a usize. Shared with the
        // copy intrinsics — see `emit_copy_byte_count_overflow_check`.
        self.emit_copy_byte_count_overflow_check(count, element_size, "write_bytes");

        // `write_bytes` requires `dst` be non-null EVEN WHEN `count == 0`
        // (std docs: the pointer must be non-null and properly aligned even
        // if the effectively copied size is zero). This is also the only
        // obligation a zero-count write leaves behind, so without it such a
        // harness emitted NO verification conditions and the vacuity gate
        // refused the proof (corpus: valid-value-checks/write_bytes
        // check_zero_count_write_to_niche_is_noop reported VACUOUS
        // no-checks).
        if let Some(dst_ptr) = self.codegen_operand(dst) {
            let dst_bv = self.coerce_to_ptr_width(dst_ptr);
            let zero_ptr = Expr::bitvec_const(0u128, POINTER_WIDTH);
            self.record_violation_guarded_with_message(
                dst_bv.eq(zero_ptr),
                "null_pointer_check",
                Some("memset destination pointer is null".to_string()),
            );
        }

        // write_bytes has only a destination, but the same alignment rule.
        if let Some(align) = self.pointee_align(dst) {
            self.emit_copy_alignment_check(dst, count, align, "dst");
        }

        self.emit_copy_region_validity_check(
            dst, count, element_size, "memset destination region writeable",
        );

        // Defer location formatting until an error path needs it (Part of #2267).
        let location = || format!("{:?}", span);

        // Get dst pointer expression
        let Some(dst_val) = self.codegen_operand(dst) else {
            self.ctx.unsupported("WriteBytes: failed to codegen dst pointer", location());
            return;
        };
        let val_expr = self.codegen_operand(val);

        let dst_ptr = self.coerce_to_ptr_width(dst_val);

        // Get the byte value to write (should be a u8)
        let byte_val = if let Some(val) = val_expr {
            // Coerce to 8-bit value
            if let Some(w) = val.sort().bitvec_width() {
                if w == 8 {
                    val
                } else if w > 8 {
                    // Truncate to 8 bits
                    val.extract(7, 0)
                } else {
                    // Zero-extend to 8 bits
                    val.zero_extend(8 - w)
                }
            } else {
                // Non-bitvector value - treat as u8
                self.ctx.unsupported("WriteBytes: non-bitvector value", location());
                return;
            }
        } else {
            self.ctx.unsupported("WriteBytes: failed to codegen value", location());
            return;
        };

        // Maximum bytes to unroll (avoid explosion for large writes)
        const MAX_UNROLL_BYTES: usize = 128;

        match count_const {
            Some(count_val) => {
                let total_bytes = count_val.saturating_mul(element_size);
                if total_bytes <= MAX_UNROLL_BYTES {
                    debug!(
                        "codegen_write_bytes: unrolling {} elements ({} bytes)",
                        count_val, total_bytes
                    );
                    for i in 0..total_bytes {
                        let offset = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                        let addr = dst_ptr.clone().bvadd(offset);
                        // Store the byte value at this address
                        self.ctx.store_memory(addr, byte_val.clone());
                    }
                } else {
                    // Too large to unroll - treat as unsupported with warning
                    self.ctx.unsupported_with_fallback(
                        "WriteBytes with large constant count",
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
                // Symbolic count - guarded unrolled write (Part of #3104).
                //
                // Soundness: see codegen_copy_nonoverlapping for truncation caveat.
                if element_size > MAX_UNROLL_BYTES {
                    self.ctx.unsupported_with_fallback(
                        "WriteBytes with symbolic count (element too large for unroll)",
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
                        "codegen_write_bytes: guarded unroll for symbolic count, \
                         element_size={}, max_bytes={}",
                        element_size, MAX_UNROLL_BYTES
                    );

                    for i in 0..MAX_UNROLL_BYTES {
                        let offset = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                        let guard = total_bv.clone().bvugt(offset.clone());
                        let dst_addr = dst_ptr.clone().bvadd(offset);
                        let dst_byte = self.ctx.load_memory(dst_addr.clone());
                        let value = Expr::ite(guard, byte_val.clone(), dst_byte);
                        self.ctx.store_memory(dst_addr, value);
                    }
                } else {
                    self.ctx.unsupported_with_fallback(
                        "WriteBytes with symbolic count (operand codegen failed)",
                        location(),
                    );
                }
            }
        }
    }
}
