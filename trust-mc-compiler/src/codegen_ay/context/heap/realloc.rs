// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Heap reallocation with data copy for BMC verification.
//!
//! Extracted from heap/mod.rs to stay within file size limits.
//! Part of #2716.

use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::{Expr, ExprValue};

use super::super::AYCtx;

impl<'tcx, 't> AYCtx<'tcx, 't> {
    /// Reallocate memory on the heap.
    ///
    /// Per design:
    /// - Allocates new memory with new_size
    /// - Copies min(old_size, new_size) bytes from old to new (Part of #2716)
    /// - Marks old allocation as invalid
    /// - Returns pointer to new allocation
    ///
    /// # Arguments
    /// - `old_ptr`: Pointer to reallocate
    /// - `old_size`: Previous allocation size (validated against recorded size)
    /// - `align`: Alignment for new allocation
    /// - `new_size`: New size in bytes
    ///
    /// # Returns
    /// A pointer-width bitvector representing the new allocation ID.
    ///
    /// # Contracts
    /// REQUIRES: old_ptr.sort() == ptr_sort()
    /// REQUIRES: new_size.sort() == ptr_sort()
    /// REQUIRES: old_ptr was previously allocated
    /// ENSURES: result.sort() == ptr_sort()
    /// ENSURES: result != 0 (non-null pointer)
    /// ENSURES: violation recorded if obj_size[obj_id(old_ptr)] != old_size (Part of #2817)
    /// ENSURES: obj_valid[obj_id(old_ptr)] == false (dealloc emits SSA constraint)
    /// ENSURES: obj_valid[result] == true (new allocation valid)
    /// ENSURES: obj_size[result] == new_size (new size recorded)
    /// ENSURES: memory[result+i] == memory[old_ptr+i] for i in 0..min(old_size, new_size)
    ///          when both sizes are concrete (Part of #2716)
    #[must_use]
    pub(in crate::codegen_ay) fn heap_realloc(
        &mut self,
        old_ptr: Expr,
        old_size: Expr,
        align: Expr,
        new_size: Expr,
    ) -> Expr {
        self.ensure_heap_arrays_initialized();

        // Part of #2817: Validate old_size matches recorded allocation size.
        let ptr_obj = self.heap_pointer_object(old_ptr.clone());
        if let Some(ref size_arr) = self.heap_state.obj_size {
            let recorded_size = size_arr.clone().select(ptr_obj);
            let size_mismatch = recorded_size.eq(old_size.clone()).not();
            self.record_property_violation(size_mismatch, "dealloc_size_mismatch");
        }

        // Save old_ptr before deallocation for data copy (Part of #2716).
        // Dealloc only updates obj_valid metadata — byte memory is preserved.
        let saved_old_ptr = old_ptr.clone();

        // Deallocate old — ptr-only variant handles double-free and base-pointer checks.
        self.heap_dealloc_ptr_only(old_ptr);

        // Allocate new
        let new_ptr = self.heap_alloc(new_size.clone(), align);

        // Part of #2716: Copy data from old allocation to new allocation.
        // Per realloc semantics, min(old_size, new_size) bytes are preserved.
        self.heap_realloc_copy_data(saved_old_ptr, &old_size, new_ptr.clone(), &new_size);

        new_ptr
    }

    /// Maximum bytes to copy during heap_realloc (matches copy_nonoverlapping limit).
    const MAX_REALLOC_COPY_BYTES: usize = 128;

    /// Copy preserved bytes from old allocation to new allocation during realloc.
    ///
    /// Per C/Rust realloc semantics, `min(old_size, new_size)` bytes from the old
    /// allocation are preserved in the new allocation.
    ///
    /// Requires concrete sizes for loop unrolling (matching the pattern used by
    /// `codegen_copy_nonoverlapping`). Symbolic sizes record an unsupported note.
    ///
    /// Part of #2716.
    fn heap_realloc_copy_data(
        &mut self,
        old_ptr: Expr,
        old_size: &Expr,
        new_ptr: Expr,
        new_size: &Expr,
    ) {
        // Skip copy if byte memory is not initialized — no data has been written.
        if self.memory.is_none() {
            return;
        }

        let old_concrete = Self::try_extract_concrete_usize(old_size);
        let new_concrete = Self::try_extract_concrete_usize(new_size);

        match (old_concrete, new_concrete) {
            (Some(old_sz), Some(new_sz)) => {
                let copy_bytes = old_sz.min(new_sz);
                if copy_bytes == 0 {
                    return;
                }
                if copy_bytes > Self::MAX_REALLOC_COPY_BYTES {
                    self.unsupported_with_fallback(
                        "heap_realloc_data_copy_large",
                        format!(
                            "realloc copy size {} exceeds limit {}",
                            copy_bytes,
                            Self::MAX_REALLOC_COPY_BYTES
                        ),
                    );
                    return;
                }
                // Byte-by-byte copy from old to new.
                // Old bytes are still in the memory array (dealloc only updates obj_valid).
                for i in 0..copy_bytes {
                    let offset = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                    let src_addr = old_ptr.clone().bvadd(offset.clone());
                    let dst_addr = new_ptr.clone().bvadd(offset);
                    let byte = self.load_memory(src_addr);
                    self.store_memory(dst_addr, byte);
                }
                tracing::debug!(
                    "heap_realloc: copied {} bytes from old to new allocation",
                    copy_bytes
                );
            }
            _ => {
                // Symbolic sizes — can't unroll the copy loop.
                // New allocation content remains unconstrained (over-approximation).
                self.unsupported_with_fallback(
                    "heap_realloc_symbolic_copy",
                    "realloc with symbolic sizes: data copy requires concrete sizes for unrolling",
                );
            }
        }
    }

    /// Try to extract a concrete usize from a bitvec constant expression.
    ///
    /// Returns `None` for symbolic (non-constant) expressions or values
    /// that don't fit in a `usize`.
    pub(super) fn try_extract_concrete_usize(expr: &Expr) -> Option<usize> {
        if let ExprValue::BitVecConst { value, .. } = expr.value() {
            u64::try_from(value).ok().map(|v| v as usize)
        } else {
            None
        }
    }
}
