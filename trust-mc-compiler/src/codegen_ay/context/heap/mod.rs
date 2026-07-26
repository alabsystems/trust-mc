// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Heap allocation model for AY codegen context.
//!
//! Extracted from context.rs as part of #2093.

use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};
use ay_bindings::{Expr, Sort};

use super::AYCtx;

mod realloc;

/// Heap allocation model state for BMC verification (#1100).
///
/// Heap allocation model:
/// - Ptr: (PtrId, offset) where PtrId is a unique allocation ID
/// - Heap: map from PtrId to Object metadata (size, alive)
/// - Allocation never fails (sound over-approximation)
///
/// The model uses SMT arrays to track object validity and sizes:
/// - obj_valid: Array<BV<POINTER_WIDTH>, Bool> - tracks which allocations are alive
/// - obj_size: Array<BV<POINTER_WIDTH>, BV<POINTER_WIDTH>> - tracks allocation sizes
///
/// Address space partitioning: Each allocation gets a non-overlapping region
/// in the byte-addressed memory model. Base address = id * HEAP_STRIDE.
/// This prevents overlapping when allocation IDs are used as memory addresses.
#[derive(Debug, Clone)]
pub(in crate::codegen_ay) struct HeapState {
    /// Next allocation ID (counter, never reuses).
    /// ID 0 is reserved for null pointer representation.
    pub(super) next_alloc_id: u64,
    /// Object validity array: obj_valid[ptr_id] = alive
    /// Sort: (Array (_ BitVec POINTER_WIDTH) Bool)
    pub(super) obj_valid: Option<Expr>,
    /// Object size array: obj_size[ptr_id] = size_in_bytes
    /// Sort: (Array (_ BitVec POINTER_WIDTH) (_ BitVec POINTER_WIDTH))
    pub(super) obj_size: Option<Expr>,
}

/// Stride between heap allocations in address space (1MB).
///
/// Each allocation ID gets HEAP_STRIDE bytes of address space.
/// This ensures allocations don't overlap when used with the byte-addressed memory model.
/// 1MB is chosen to be large enough for typical allocations while leaving room for many allocations.
pub(super) const HEAP_STRIDE: u64 = 0x100000; // 1MB

impl Default for HeapState {
    fn default() -> Self {
        Self::new()
    }
}

impl HeapState {
    /// Create a new heap state.
    ///
    /// ID 0 is reserved for null pointer representation.
    pub(in crate::codegen_ay) fn new() -> Self {
        Self {
            next_alloc_id: 1, // 0 reserved for null
            obj_valid: None,
            obj_size: None,
        }
    }

    /// Get a fresh allocation ID.
    ///
    /// Each allocation gets a unique ID that is never reused.
    /// Returns `None` if allocation ID would overflow (recoverable error).
    pub(in crate::codegen_ay) fn fresh_alloc_id(&mut self) -> Option<u64> {
        let id = self.next_alloc_id;
        self.next_alloc_id = id.checked_add(1)?;
        Some(id)
    }
}

impl<'tcx, 't> AYCtx<'tcx, 't> {
    #[must_use]
    fn heap_object_expr_from_alloc_id(id: u64) -> Expr {
        Expr::bitvec_const(id as u128, POINTER_WIDTH)
    }

    #[must_use]
    pub(in crate::codegen_ay::context) fn declare_ssa_var_eq_expr(
        &mut self,
        name_prefix: &str,
        expr: Expr,
    ) -> Expr {
        let name = self.fresh_name(name_prefix);
        let var = self.declare_var(&name, expr.sort().clone());
        self.assert(var.clone().eq(expr));
        var
    }

    // ========================================================================
    // Heap Allocation Model (#1100)
    // Heap Allocation Model
    // ========================================================================

    /// Allocate memory on the heap.
    ///
    /// Per design:
    /// - Returns a fresh address in a non-overlapping region
    /// - Tracks allocation validity and size in heap state keyed by allocation ID
    /// - Allocation never fails (sound over-approximation)
    ///
    /// Address space partitioning: Each allocation ID gets HEAP_STRIDE bytes.
    /// Base address = id * HEAP_STRIDE (e.g., id=1 → 0x100000, id=2 → 0x200000).
    /// This ensures allocations don't overlap in the byte-addressed memory model.
    ///
    /// # Arguments
    /// - `size`: Size in bytes (must be > 0 per Rust allocator semantics)
    /// - `_align`: Alignment (power of two, currently not enforced)
    ///
    /// # Returns
    /// A pointer-width bitvector representing the base address of the allocation.
    ///
    /// # Contracts
    /// REQUIRES: size.sort() == ptr_sort() (size must match array element sort)
    /// ENSURES: result.sort() == ptr_sort() (pointer-width bitvector)
    /// ENSURES: result % HEAP_STRIDE == 0 (pointer aligned to stride boundary)
    ///
    /// # Normal case (no overflow)
    /// ENSURES: result != 0 (non-null pointer; first alloc at HEAP_STRIDE, not 0)
    /// ENSURES: obj_valid[obj_id(result)] == true (allocation tracked as valid, SSA constraint emitted)
    /// ENSURES: obj_size[obj_id(result)] == size (allocation size recorded, SSA constraint emitted)
    ///
    /// # Overflow case (recorded via unsupported())
    /// Returns null pointer (0) and records "heap_alloc_id_overflow" or "heap_address_overflow".
    /// Heap arrays are NOT updated for the null pointer - it is not a valid allocation.
    #[must_use]
    pub(in crate::codegen_ay) fn heap_alloc(&mut self, size: Expr, _align: Expr) -> Expr {
        // Get fresh allocation ID, handling overflow gracefully
        let id = if let Some(id) = self.heap_state.fresh_alloc_id() {
            id
        } else {
            self.unsupported_with_fallback(
                "heap_alloc_id_overflow",
                "allocation ID overflow (exceeds u64::MAX)",
            );
            return Expr::bitvec_const(0u128, POINTER_WIDTH); // null pointer
        };
        // Compute non-overlapping base address: id * HEAP_STRIDE
        let base_addr = if let Some(addr) = id.checked_mul(HEAP_STRIDE) {
            addr
        } else {
            self.unsupported_with_fallback(
                "heap_address_overflow",
                "heap address overflow (id * HEAP_STRIDE)",
            );
            return Expr::bitvec_const(0u128, POINTER_WIDTH); // null pointer
        };
        let ptr = Expr::bitvec_const(base_addr as u128, POINTER_WIDTH);
        let ptr_obj = Self::heap_object_expr_from_alloc_id(id);

        // Initialize heap arrays lazily if needed
        self.ensure_heap_arrays_initialized();

        // Assert size <= HEAP_STRIDE to prevent allocations from aliasing
        // adjacent regions in the address space. Without this, a symbolic size
        // exceeding HEAP_STRIDE would silently overlap neighboring allocations.
        // Part of #2532.
        let stride_limit = Expr::bitvec_const(HEAP_STRIDE as u128, POINTER_WIDTH);
        self.assert(size.clone().bvule(stride_limit));

        // Update heap validity array and emit constraint
        if let Some(valid_arr) = self.heap_state.obj_valid.take() {
            let new_valid = valid_arr.store(ptr_obj.clone(), Expr::bool_const(true));
            self.heap_state.obj_valid = Some(self.declare_ssa_var_eq_expr("heap_valid", new_valid));
        }

        // Update heap size array and emit constraint
        if let Some(size_arr) = self.heap_state.obj_size.take() {
            let new_size = size_arr.store(ptr_obj, size);
            self.heap_state.obj_size = Some(self.declare_ssa_var_eq_expr("heap_size", new_size));
        }

        tracing::debug!("heap_alloc: allocated id={} at base_addr=0x{:x}", id, base_addr);
        ptr
    }

    /// Deallocate memory from the heap.
    ///
    /// Per design:
    /// - Asserts allocation is valid (double-free detection, Part of #2718)
    /// - Asserts dealloc pointer is allocation base (offset == 0, Part of #2725)
    /// - Asserts dealloc size matches allocation size (Part of #2718)
    /// - Marks allocation as invalid
    ///
    /// # Arguments
    /// - `ptr`: Pointer to deallocate (allocation ID)
    /// - `size`: Size for validation (checked against obj_size)
    /// - `_align`: Alignment (currently ignored)
    ///
    /// # Contracts
    /// REQUIRES: ptr.sort() == ptr_sort() (pointer-width bitvector)
    /// REQUIRES: size.sort() == ptr_sort() (size must match array element sort)
    /// ENSURES: violation recorded if obj_valid[obj_id(ptr)] == false (double-free, Part of #2718)
    /// ENSURES: violation recorded if offset(ptr) != 0 (non-base-pointer free, Part of #2725)
    /// ENSURES: violation recorded if obj_size[obj_id(ptr)] != size (size mismatch, Part of #2718)
    /// ENSURES: obj_valid[obj_id(ptr)] == false (SSA constraint emitted to solver)
    /// ENSURES: obj_size[obj_id(ptr)] unchanged (size metadata preserved for debugging)
    pub(in crate::codegen_ay) fn heap_dealloc(&mut self, ptr: Expr, size: Expr, _align: Expr) {
        self.ensure_heap_arrays_initialized();
        let ptr_obj = self.heap_pointer_object(ptr.clone());

        // Part of #2718: Check dealloc size matches allocation size.
        // CHC path has this at stubs_alloc_heap_ops.rs:206-208.
        if let Some(ref size_arr) = self.heap_state.obj_size {
            let recorded_size = size_arr.clone().select(ptr_obj);
            let size_mismatch = recorded_size.eq(size).not();
            self.record_property_violation(size_mismatch, "dealloc_size_mismatch");
        }

        self.heap_dealloc_ptr_only(ptr);
    }

    /// Deallocate by pointer only — avoids requiring (and cloning) unused size/align.
    ///
    /// Called by `heap_realloc` where size/align are not needed for deallocation
    /// but align is needed for the subsequent allocation.
    ///
    /// Fix for #2531: now emits SSA constraints so the solver can reason about
    /// deallocation (use-after-free / double-free detection). Previously, the
    /// validity update was internal-only and invisible to the solver.
    fn heap_dealloc_ptr_only(&mut self, ptr: Expr) {
        self.ensure_heap_arrays_initialized();
        let ptr_obj = self.heap_pointer_object(ptr.clone());
        let ptr_offset = self.heap_pointer_offset(ptr);

        // Part of #2725: Deallocation requires base pointer (offset == 0).
        // CHC parity: stubs_alloc_heap_ops.rs / codegen_rules_helpers.rs.
        let is_base_pointer = ptr_offset.eq(Expr::bitvec_const(0u128, POINTER_WIDTH));
        self.record_property_violation(is_base_pointer.not(), "dealloc_base_pointer_check");

        // Part of #2718: Double-free detection — assert obj_valid[obj_id(ptr)] == true before
        // invalidating.
        // CHC path has this at stubs_alloc_heap_ops.rs:202-204.
        // The violation is satisfiable when ptr was already freed (obj_valid[obj_id(ptr)] == false).
        if let Some(ref valid_arr) = self.heap_state.obj_valid {
            let is_valid = valid_arr.clone().select(ptr_obj.clone());
            self.record_property_violation(is_valid.not(), "double_free_check");
        }

        // Mark allocation as invalid: obj_valid[obj_id(ptr)] = false
        // Emit SSA constraint so the solver sees the deallocation.
        if let Some(valid_arr) = self.heap_state.obj_valid.take() {
            let new_valid = valid_arr.store(ptr_obj, Expr::bool_const(false));
            self.heap_state.obj_valid =
                Some(self.declare_ssa_var_eq_expr("heap_dealloc_valid", new_valid));
        }

        tracing::debug!("heap_dealloc: deallocated ptr");
    }

    /// #3350: Invalidate obj_valid for a pointer without allocation provenance.
    ///
    /// Called when a raw pointer is created from an integer cast
    /// (PointerWithExposedProvenance). These pointers were never allocated,
    /// so obj_valid should be false to prevent false proofs.
    pub(in crate::codegen_ay) fn heap_invalidate_no_provenance(&mut self, ptr: Expr) {
        self.ensure_heap_arrays_initialized();
        if let Some(valid_arr) = self.heap_state.obj_valid.take() {
            let obj_id = self.heap_pointer_object(ptr);
            let new_valid = valid_arr.store(obj_id, Expr::bool_const(false));
            self.heap_state.obj_valid =
                Some(self.declare_ssa_var_eq_expr("heap_no_provenance_valid", new_valid));
        }
    }

    /// Conditionally invalidate provenance for a pointer.
    ///
    /// When `condition` is true, marks the pointer's object as invalid
    /// (no provenance). When false, the validity array is unchanged.
    /// Uses ITE on the validity array to encode the conditional update.
    pub(in crate::codegen_ay) fn heap_invalidate_no_provenance_if(
        &mut self,
        ptr: Expr,
        condition: Expr,
    ) {
        self.ensure_heap_arrays_initialized();
        if let Some(valid_arr) = self.heap_state.obj_valid.take() {
            let obj_id = self.heap_pointer_object(ptr);
            let invalidated = valid_arr.clone().store(obj_id, Expr::bool_const(false));
            let new_valid = Expr::ite(condition, invalidated, valid_arr);
            self.heap_state.obj_valid =
                Some(self.declare_ssa_var_eq_expr("heap_no_provenance_cond_valid", new_valid));
        }
    }

    /// Ensure heap tracking arrays are initialized.
    ///
    /// Creates SMT arrays for tracking object validity and sizes
    /// if they haven't been created yet.
    pub(super) fn ensure_heap_arrays_initialized(&mut self) {
        if self.heap_state.obj_valid.is_none() {
            // Initialize validity array to all-true (sound over-approximation).
            // Stack and heap memory are "allocated" by default. heap_dealloc sets
            // entries to false. This ensures kani::mem predicates (can_write,
            // can_dereference, same_allocation) don't produce false positives on
            // valid stack or heap pointers. Part of #1229.
            let valid_arr = Expr::const_array(ptr_sort(), Expr::bool_const(true));
            self.heap_state.obj_valid = Some(valid_arr);
        }

        if self.heap_state.obj_size.is_none() {
            // Create (Array (_ BitVec POINTER_WIDTH) (_ BitVec POINTER_WIDTH)) for size tracking
            let size_sort = Sort::array(ptr_sort(), ptr_sort());
            let size_name = self.fresh_name("heap_size");
            let size_arr = self.declare_var(&size_name, size_sort);
            self.heap_state.obj_size = Some(size_arr);
        }
    }

    /// Get the allocation object ID for a pointer (Part of #1410).
    ///
    /// In the Ptr(id, offset) model, each allocation gets HEAP_STRIDE bytes.
    /// The object ID is computed as: `ptr / HEAP_STRIDE`.
    ///
    /// This maps directly to the allocation ID used by `heap_alloc`.
    ///
    /// # Contracts
    /// REQUIRES: ptr.sort() == ptr_sort() (pointer-width bitvector)
    /// ENSURES: result.sort() == ptr_sort() (same width as input)
    /// ENSURES: result == ptr / HEAP_STRIDE (unsigned division via bvudiv)
    #[must_use]
    pub(in crate::codegen_ay) fn heap_pointer_object(&self, ptr: Expr) -> Expr {
        let stride = Expr::bitvec_const(HEAP_STRIDE as u128, POINTER_WIDTH);
        ptr.bvudiv(stride)
    }

    /// Get the offset within an allocation for a pointer (Part of #1410).
    ///
    /// In the Ptr(id, offset) model, the offset is: `ptr % HEAP_STRIDE`.
    ///
    /// This gives the byte offset from the allocation's base address.
    ///
    /// # Contracts
    /// REQUIRES: ptr.sort() == ptr_sort() (pointer-width bitvector)
    /// ENSURES: result.sort() == ptr_sort() (same width as input)
    /// ENSURES: result == ptr % HEAP_STRIDE (unsigned modulo)
    /// ENSURES: result < HEAP_STRIDE (offset within allocation bounds)
    #[must_use]
    pub(in crate::codegen_ay) fn heap_pointer_offset(&self, ptr: Expr) -> Expr {
        let stride = Expr::bitvec_const(HEAP_STRIDE as u128, POINTER_WIDTH);
        ptr.bvurem(stride)
    }

    /// Check if a pointer range is allocated in the heap model.
    ///
    /// Verifies that the range `[ptr, ptr+size)` is within a valid allocation:
    /// 1. Check `obj_valid[heap_pointer_object(ptr)]`
    /// 2. When size > 0, verify `ptr` and `ptr + size - 1` have the same allocation ID
    ///
    /// If the heap arrays are not initialized, returns `true` (over-approximation)
    /// to maintain soundness.
    ///
    /// # Arguments
    /// * `ptr` - Start of the memory range to check
    /// * `size` - Size of the range in bytes (if None, only checks ptr validity)
    ///
    /// # Contracts
    /// REQUIRES: ptr.sort() == ptr_sort() (pointer-width bitvector)
    /// REQUIRES: `size` is `None` or its inner sort is `ptr_sort()`
    /// REQUIRES: size expressions are pointer-width bitvectors when provided
    /// ENSURES: result.sort() == Sort::Bool (boolean validity predicate)
    /// ENSURES: obj_valid array is initialized after call (via ensure_heap_arrays_initialized)
    /// ENSURES: result == obj_valid[ptr_obj] when size.is_none()
    /// ENSURES: when size.is_some(), result gates boundary check with `size == 0`
    ///          to avoid underflow on zero-sized ranges
    #[must_use]
    pub(in crate::codegen_ay) fn heap_is_allocated(
        &mut self,
        ptr: Expr,
        size: Option<Expr>,
    ) -> Expr {
        self.ensure_heap_arrays_initialized();

        let ptr_obj = self.heap_pointer_object(ptr.clone());
        let base_valid = if let Some(ref valid_arr) = self.heap_state.obj_valid {
            valid_arr.clone().select(ptr_obj.clone())
        } else {
            return Expr::bool_const(true);
        };

        match size {
            None => base_valid,
            Some(size_expr) => {
                let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);
                let one = Expr::bitvec_const(1u128, POINTER_WIDTH);
                let size_is_zero = size_expr.clone().eq(zero);

                // Use ite(size==0, 1, size) before subtracting 1 so symbolic
                // zero never underflows in the end-pointer arithmetic.
                let checked_size = Expr::ite(size_is_zero.clone(), one.clone(), size_expr);
                let end_ptr = ptr.bvadd(checked_size).bvsub(one);
                let end_obj = self.heap_pointer_object(end_ptr);
                let same_alloc = ptr_obj.eq(end_obj);

                // For size==0, skip the boundary check and rely on base validity only.
                let range_ok = Expr::ite(size_is_zero, Expr::bool_const(true), same_alloc);
                base_valid.and(range_ok)
            }
        }
    }

    /// Constrain a symbolic address to lie within a single heap region.
    ///
    /// Stack-local addresses are symbolic with only alignment and wrap-around
    /// constraints. Without an additional region constraint, the solver can
    /// place a stack variable across a HEAP_STRIDE boundary, causing the
    /// `use_after_free_check` (same-allocation check) to report a spurious
    /// counterexample when a raw pointer derived from `&mut local` is
    /// dereferenced.
    ///
    /// This method asserts:
    ///   `addr / HEAP_STRIDE == (addr + size - 1) / HEAP_STRIDE`
    /// ensuring the entire object fits in one region.
    ///
    /// # Arguments
    /// * `addr` - Symbolic address of the stack local (pointer-width BV)
    /// * `size` - Size of the object in bytes (must be > 0)
    ///
    /// # Contracts
    /// REQUIRES: addr.sort() == ptr_sort()
    /// REQUIRES: size > 0
    /// ENSURES: Adds one assertion to the constraint set
    pub(in crate::codegen_ay) fn heap_constrain_within_region(&mut self, addr: Expr, size: u64) {
        if size <= 1 {
            return; // Single-byte objects can never straddle a boundary.
        }
        let start_obj = self.heap_pointer_object(addr.clone());
        let end_addr = addr.bvadd(Expr::bitvec_const((size - 1) as u128, POINTER_WIDTH));
        let end_obj = self.heap_pointer_object(end_addr);
        self.assert(start_obj.eq(end_obj));
    }
}

#[cfg(test)]
mod tests;
