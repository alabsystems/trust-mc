// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Memory model for AY codegen context.
//!
//! Byte-addressed array memory with little-endian multi-byte operations.
//! Extracted from context.rs as part of #2093.

use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};
use ay_bindings::{Expr, Sort};
use trust_mc_core::decl::Decl;

use super::AYCtx;

impl<'tcx, 't> AYCtx<'tcx, 't> {
    /// Initialize the memory model with a symbolic array.
    ///
    /// Must be called before any memory operations. Uses SMT array theory
    /// with 64-bit bitvector addresses and 8-bit bitvector values.
    ///
    /// Dual-writes to both `program` and `bmc_vc` for emit_bmc path.
    pub(in crate::codegen_ay) fn init_memory(&mut self) {
        if self.memory.is_none() {
            // Dual-write: add to both program and bmc_vc
            self.bmc_vc.add_decl(Decl::constant("memory", Sort::memory()));
            self.memory = Some(self.program.declare_const("memory", Sort::memory()));
        }
    }

    /// Get the current memory array expression.
    ///
    /// # Panics
    /// Panics if memory has not been initialized via `init_memory`.
    /// Upstream guard: `AYCtx::translate()` calls `init_memory()` before any
    /// statement codegen (chc/mod.rs), and `codegen_function()` does the same
    /// for BMC (codegen_results.rs). All callers go through these entry points.
    pub(in crate::codegen_ay) fn memory(&self) -> &Expr {
        self.memory.as_ref().expect("Memory not initialized")
    }

    #[must_use]
    fn coerce_memory_addr(addr: Expr) -> Expr {
        let addr = coerce_bitvec_width_safe(addr, POINTER_WIDTH, SignExtension::ZeroExtend);
        assert!(addr.sort().bitvec_width().is_some(), "memory address must be a bitvector");
        addr
    }

    /// Store a value at an address in memory.
    ///
    /// Updates the memory array with a new store operation.
    ///
    /// # Panics
    /// Panics if memory has not been initialized via `init_memory`.
    /// Upstream guard: same as `memory()` — all codegen entry points call
    /// `init_memory()` before statement processing.
    pub(in crate::codegen_ay) fn store_memory(&mut self, addr: Expr, value: Expr) {
        let addr = Self::coerce_memory_addr(addr);
        // Coerce Bool to BV(8) for byte-addressed memory storage.
        // Bool sort values (e.g., from bool arrays) must be widened to the
        // memory element sort before array store. Part of #1739.
        let value = if value.sort().is_bool() {
            Expr::ite(value, Expr::bitvec_const(1, 8), Expr::bitvec_const(0, 8))
        } else {
            value
        };
        let mem = self.memory.take().expect("Memory not initialized");
        let new_mem = mem.store(addr, value);
        self.memory = Some(new_mem);
    }

    /// Load a single byte from memory at the given address.
    ///
    /// # Panics
    /// - Panics if memory has not been initialized via `init_memory`.
    /// - Panics if `addr` was previously written with a non-bitvec symbolic store
    ///   (Int/Array/Datatype). Byte reads from such addresses are unsound because
    ///   the symbolic value is not materialized into the byte-addressed memory array.
    ///   Part of #2599.
    #[must_use]
    #[allow(clippy::panic)] // Fail-closed guard against unsound symbolic-store loads
    pub(in crate::codegen_ay) fn load_memory(&self, addr: Expr) -> Expr {
        let addr = Self::coerce_memory_addr(addr);
        if let Some(symbolic_value) = self.symbolic_memory_stores.get(&addr) {
            panic!(
                "load_memory at address previously written symbolically as {:?}; byte load would be unsound",
                symbolic_value.sort()
            );
        }
        self.memory().clone().select(addr)
    }

    /// Load a multi-byte value from memory (little-endian).
    ///
    /// Reads `num_bytes` consecutive bytes starting at `addr` and concatenates
    /// them into a single bitvector of width `num_bytes * 8`.
    ///
    /// # Panics
    /// Panics if memory has not been initialized via `init_memory`.
    #[must_use]
    pub(in crate::codegen_ay) fn load_memory_bytes(&self, addr: Expr, num_bytes: u32) -> Expr {
        // Zero-byte loads are invalid - return 1-bit zero as distinguishable error marker.
        // Caller should validate size > 0 before calling.
        if num_bytes == 0 {
            return Expr::bitvec_const(0, 1);
        }
        // Note: symbolic_memory_stores guard is enforced inside load_memory (Part of #2599).
        // Each byte-level read (including base addr and offsets) is checked individually.
        if num_bytes == 1 {
            return self.load_memory(addr);
        }
        // Little-endian: byte 0 is LSB, byte n-1 is MSB
        // Result is concat(byte[n-1], ..., concat(byte[1], byte[0]))
        let ptr_width = POINTER_WIDTH;
        let mut result = self.load_memory(addr.clone());
        for i in 1..num_bytes {
            let offset = Expr::bitvec_const(i as u128, ptr_width);
            let byte_addr = addr.clone().bvadd(offset);
            let byte = self.load_memory(byte_addr);
            // concat(high_bits, low_bits) - byte becomes new high bits
            result = byte.concat(result);
        }
        result
    }

    /// Recover symbolic non-bitvec value that was previously stored at this address.
    ///
    /// Returns `None` when no symbolic store is tracked for `addr`.
    #[must_use]
    pub(in crate::codegen_ay) fn load_symbolic_memory_value(&self, addr: Expr) -> Option<Expr> {
        let addr = Self::coerce_memory_addr(addr);
        self.symbolic_memory_stores.get(&addr).cloned()
    }

    /// Store a multi-byte value to memory (little-endian).
    ///
    /// Writes the value as consecutive bytes starting at `addr`, with the
    /// least significant byte at the lowest address.
    ///
    /// For Int sort values (e.g., BigInt), the byte-addressed memory model cannot
    /// be used because Int has no fixed width. These values are tracked symbolically
    /// rather than stored in memory. This supports CHC reasoning on arbitrary-precision
    /// integers. Part of #744.
    ///
    /// # Panics
    /// - Panics if the value sort is not bitvector, Bool, Int, Array, or Datatype
    ///   (unsupported sort indicates a codegen bug).
    /// - Panics if memory has not been initialized via `init_memory` (for
    ///   bitvector and Bool values that are written to byte-addressed memory).
    #[allow(clippy::panic)] // Defensive panic for internal consistency - unsupported sort is a codegen bug
    pub(in crate::codegen_ay) fn store_memory_bytes(&mut self, addr: Expr, value: Expr) {
        let addr = Self::coerce_memory_addr(addr);
        // Handle non-bitvector sorts (Int, Array, Datatype) - cannot use byte-addressed
        // memory model. Track symbolically instead. This supports:
        // - BigInt (Int sort): arbitrary precision integers for CHC reasoning
        // - Vec/slice (Array sort): BigInt's internal digit storage
        // - ADTs (Datatype sort): complex structs
        // Part of #744.
        //
        // NOTE: The symbolic variable remains independent of byte memory, but we now
        // track the originating address and fail closed in `load_memory_bytes` if that
        // address is later read as bytes. This avoids silently returning unconstrained
        // garbage from byte-addressed memory.
        let sort = value.sort();
        if sort.is_int() || sort.is_array() || sort.is_datatype() {
            // Non-bitvector values are tracked symbolically; `addr` is recorded for
            // fail-closed load detection.
            let name = self.fresh_name("mem_symbolic");
            tracing::debug!(
                "store_memory_bytes: {:?} sort value stored symbolically as {} at addr {:?}",
                sort,
                name,
                addr
            );
            let var = self.declare_var(&name, sort.clone());
            self.assert(var.clone().eq(value));
            self.symbolic_memory_stores.insert(addr, var);
            return;
        }

        let Some(width) = value.sort().bitvec_width() else {
            // Bool sort - convert to bitvec(8) for memory storage
            if value.sort().is_bool() {
                let bv_value = Expr::ite(value, Expr::bitvec_const(1, 8), Expr::bitvec_const(0, 8));
                self.store_memory(addr, bv_value);
                return;
            }
            panic!(
                "store_memory_bytes expects bitvector, Int, Array, or Datatype value, got {:?}",
                value.sort()
            );
        };
        let num_bytes = width.div_ceil(8);
        let target_width = num_bytes * 8;
        let ptr_width = POINTER_WIDTH;
        let value =
            if width < target_width { value.zero_extend(target_width - width) } else { value };

        for i in 0..num_bytes {
            let offset = Expr::bitvec_const(i as u128, ptr_width);
            let byte_addr = addr.clone().bvadd(offset);
            // Extract byte i (LSB is byte 0)
            let low = i * 8;
            let high = low + 7;
            let byte = value.clone().extract(high, low);
            self.store_memory(byte_addr, byte);
        }
    }
}

#[cfg(test)]
mod tests;
