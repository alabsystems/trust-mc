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
            let memory = self.program.declare_const("memory", Sort::memory());
            self.initial_memory = Some(memory.clone());
            self.memory = Some(memory);
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
                symbolic_value.value.sort()
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
        Self::read_bytes(addr, num_bytes, |at| self.load_memory(at))
    }

    fn read_bytes(addr: Expr, num_bytes: u32, load_byte: impl Fn(Expr) -> Expr) -> Expr {
        // Zero-byte loads are invalid - return 1-bit zero as distinguishable error marker.
        // Caller should validate size > 0 before calling.
        if num_bytes == 0 {
            return Expr::bitvec_const(0, 1);
        }
        // Little-endian: byte 0 is LSB, byte n-1 is MSB
        // Result is concat(byte[n-1], ..., concat(byte[1], byte[0]))
        let ptr_width = POINTER_WIDTH;
        let mut result = load_byte(addr.clone());
        for i in 1..num_bytes {
            let offset = Expr::bitvec_const(i as u128, ptr_width);
            let byte_addr = addr.clone().bvadd(offset);
            let byte = load_byte(byte_addr);
            // concat(high_bits, low_bits) - byte becomes new high bits
            result = byte.concat(result);
        }
        result
    }

    /// Compare a typed logical read with current byte memory even if a
    /// completed typed store also kept its whole value at the same address.
    /// The caller must establish that this range is a typed value, since
    /// layout padding can stay unconstrained. An opaque symbolic entry
    /// anywhere in the range still disallows the read.
    pub(in crate::codegen_ay) fn load_materialized_memory_bytes(
        &self,
        addr: Expr,
        num_bytes: u32,
    ) -> Option<Expr> {
        let addr = Self::coerce_memory_addr(addr);
        let opaque_store = |at: &Expr| {
            self.symbolic_memory_stores.get(at).is_some_and(|store| !store.has_byte_image)
        };
        if num_bytes == 0
            || opaque_store(&addr)
            || (0..num_bytes).any(|offset| {
                opaque_store(&addr.clone().bvadd(Expr::bitvec_const(offset, POINTER_WIDTH)))
            })
        {
            return None;
        }
        let memory = self.memory();
        Some(Self::read_bytes(addr, num_bytes, |at| memory.clone().select(at)))
    }

    /// Record the completion of a typed byte store at this exact address.
    /// An opaque replacement of the whole value creates a new entry.
    pub(in crate::codegen_ay) fn mark_symbolic_store_byte_image(&mut self, addr: Expr) {
        let addr = Self::coerce_memory_addr(addr);
        if let Some(store) = self.symbolic_memory_stores.get_mut(&addr) {
            store.has_byte_image = true;
        }
    }

    /// Recover symbolic non-bitvec value that was previously stored at this address.
    ///
    /// Returns `None` when no symbolic store is tracked for `addr`.
    #[must_use]
    pub(in crate::codegen_ay) fn load_symbolic_memory_value(&self, addr: Expr) -> Option<Expr> {
        let addr = Self::coerce_memory_addr(addr);
        self.symbolic_memory_stores.get(&addr).map(|store| store.value.clone())
    }

    /// Record a non-bitvector value stored at `addr` for whole-value readers
    /// (`load_symbolic_memory_value`); byte memory is not touched.
    pub(in crate::codegen_ay) fn track_symbolic_store(&mut self, addr: Expr, value: Expr) {
        let addr = Self::coerce_memory_addr(addr);
        let name = self.fresh_name("mem_symbolic");
        let var = self.declare_var(&name, value.sort().clone());
        self.assert(var.clone().eq(value));
        self.symbolic_memory_stores
            .insert(addr, super::SymbolicMemoryStore { value: var, has_byte_image: false });
    }

    /// Replace the `len` bytes at `addr` with fresh values; every other byte of
    /// memory keeps its value. Records nothing: the caller decides whether the
    /// fresh bytes stand in for program values.
    pub(in crate::codegen_ay) fn havoc_memory_range(&mut self, addr: Expr, len: u64) {
        let addr = Self::coerce_memory_addr(addr);
        let fresh_name = self.fresh_name("memory_object_havoc");
        let fresh = self.declare_var(&fresh_name, Sort::memory());
        let mut mem = self.memory.take().expect("Memory not initialized");
        for i in 0..len {
            let off = Expr::bitvec_const(i as u128, POINTER_WIDTH);
            mem = mem.store(addr.clone().bvadd(off.clone()), fresh.clone().select(off));
        }
        self.memory = Some(mem);
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
    /// `store_memory_bytes` for a value with no byte image (Int, Array,
    /// Datatype), written only where `on_path` holds.
    ///
    /// The address's symbolic value becomes `ite(on_path, value, previous)`.
    /// Without an earlier symbolic value of that sort at the address, `previous`
    /// is unconstrained, and a counterexample through it is not certified.
    pub(in crate::codegen_ay) fn store_memory_symbolic_on_path(
        &mut self,
        addr: Expr,
        value: Expr,
        on_path: Expr,
    ) {
        let addr = Self::coerce_memory_addr(addr);
        let sort = value.sort().clone();
        let previous = match self.symbolic_memory_stores.get(&addr) {
            Some(previous) if *previous.value.sort() == sort => previous.value.clone(),
            _ => {
                self.bmc_sound_havoc("conditional_symbolic_store_prior");
                let name = self.fresh_name("mem_symbolic_prior");
                self.declare_var(&name, sort.clone())
            }
        };
        let name = self.fresh_name("mem_symbolic");
        let var = self.declare_var(&name, sort);
        self.assert(var.clone().eq(Expr::ite(on_path.clone(), value, previous)));
        self.symbolic_memory_stores
            .insert(addr, super::SymbolicMemoryStore { value: var, has_byte_image: false });
        // As in `store_memory_bytes`: the value's bytes were not written, so a
        // byte read of this object on the store's path would see a stale image
        // (a static's pinned initializer, a stack local's materialized bytes).
        // On that path byte memory becomes a fresh array; off it, unchanged.
        let fresh_name = self.fresh_name("memory_after_symbolic_store");
        let fresh = self.declare_var(&fresh_name, Sort::memory());
        self.memory = Some(match self.memory.take() {
            Some(mem) => Expr::ite(on_path, fresh, mem),
            None => fresh,
        });
        self.bmc_sound_havoc("symbolic_store_havocs_byte_memory");
    }

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
            tracing::debug!(
                "store_memory_bytes: {:?} sort value stored symbolically at addr {:?}",
                sort,
                addr
            );
            self.track_symbolic_store(addr, value);
            // The value's BYTES were not written, so bytes read from this object
            // afterwards (a field read at an offset, a copy through another
            // pointer) would see whatever was there before: a stack local's
            // materialized bytes or a static's initializer — stale values that
            // can prove a false assertion. Replace byte memory with a fresh
            // array: every byte read after this store is unconstrained, which
            // only adds behaviours, and the record keeps a counterexample that
            // reads one uncertified.
            let fresh_name = self.fresh_name("memory_after_symbolic_store");
            let fresh = self.declare_var(&fresh_name, Sort::memory());
            self.memory = Some(fresh);
            self.bmc_sound_havoc("symbolic_store_havocs_byte_memory");
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

mod exact_read;

#[cfg(test)]
mod tests;
