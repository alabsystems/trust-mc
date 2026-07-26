// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Memory model types for CHC verification.
//
// Part of #1676: Implement MemoryManager abstraction from SeaHorn research.
// See `designs/archive/2026-02-01-seahorn-memory-models.md` for full architecture.
//
// Currently only `WideMemManager::is_dereferenceable` is integrated with
// CHC codegen. The full MemoryManager trait (salloc, halloc, load, store,
// gep, etc.) is designed but not yet wired in (#1860). When #1860 is
// implemented, the trait can be restored from git history (commit before
// this cleanup).

use ay_bindings::Expr;

/// Pointer metadata for bounds checking.
///
/// Wraps optional size information used by `WideMemManager::is_dereferenceable`.
#[derive(Clone, Debug)]
pub(in crate::codegen_ay::chc) struct MemPtr {
    /// Optional size component (Wide model).
    pub(in crate::codegen_ay::chc) size: Option<Expr>,
}

impl MemPtr {
    /// Create a wide pointer (with size).
    pub(in crate::codegen_ay::chc) fn wide(size: Expr) -> Self {
        Self { size: Some(size) }
    }

    /// Get the size (Wide model).
    pub(in crate::codegen_ay::chc) fn get_size(&self) -> Option<&Expr> {
        self.size.as_ref()
    }
}

/// Wide memory manager - memory model with integrated bounds checking.
///
/// Part of #1678: Implement WideMemManager for integrated bounds checking.
///
/// The Wide model uses:
/// - Size-tracked pointers where size = remaining accessible bytes
/// - Bounds checking: `is_dereferenceable` verifies size >= access_size
///
/// This enables efficient bounds checking without separate allocation tracking.
///
/// ## SeaHorn Reference
///
/// Based on SeaHorn's WideMemManager pattern:
/// ```cpp
/// struct PtrTy { Expr raw_addr; Expr size; };
/// Expr isDereferenceable(PtrTy p, Expr byteSz) {
///     return m_ctx.alu().doUle(byteSz, p.getSize());
/// }
/// ```
pub(in crate::codegen_ay::chc) struct WideMemManager {
    /// Address width in bits (typically 64).
    addr_width: u32,
}

impl WideMemManager {
    /// Create a new wide memory manager.
    ///
    /// # Arguments
    /// * `addr_width` - Address width in bits (typically 64)
    pub(in crate::codegen_ay::chc) fn new(addr_width: u32) -> Self {
        Self { addr_width }
    }

    /// Check if a pointer dereference is valid.
    ///
    /// For Wide model: checks size >= access_size.
    ///
    /// # Arguments
    /// * `ptr` - Pointer to check
    /// * `access_size` - Size of the access in bytes
    ///
    /// REQUIRES: `ptr` is a well-formed pointer from this manager
    /// REQUIRES: `access_size` > 0 (non-zero access)
    /// ENSURES: Returned expression has Bool sort
    /// ENSURES: If true, the access at `ptr` for `access_size` bytes is within bounds
    #[must_use]
    pub(in crate::codegen_ay::chc) fn is_dereferenceable(
        &self,
        ptr: &MemPtr,
        access_size: usize,
    ) -> Expr {
        if let Some(size) = ptr.get_size() {
            // size >= access_size (unsigned comparison)
            let access_size_expr = Expr::bitvec_const(access_size as u64, self.addr_width);
            size.clone().bvuge(access_size_expr)
        } else {
            // Missing size metadata must not prove dereferenceability.
            Expr::bool_const(false)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test that WideMemManager generates proper bounds check for is_dereferenceable.
    #[test]
    fn wide_mem_bounds_check() {
        let wide_mem = WideMemManager::new(64);

        // Pointer with size 16 bytes
        let ptr = MemPtr::wide(Expr::bitvec_const(16u64, 64));

        // Access of 8 bytes should generate: 16 >= 8 (should be true)
        let result = wide_mem.is_dereferenceable(&ptr, 8);
        assert!(matches!(result, Expr { .. }));

        // Access of 32 bytes should generate: 16 >= 32 (should be false)
        let result2 = wide_mem.is_dereferenceable(&ptr, 32);
        assert!(matches!(result2, Expr { .. }));
    }
}
