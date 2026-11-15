// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! Byte-memory stores made on one path, and reads folded at codegen time.

use super::StatementCodegen;
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::{Expr, ExprValue};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// `e` with every byte-memory read codegen can decide folded away; see
    /// `ByteMemoryFacts::fold`.
    pub(super) fn fold_memory_reads(&self, e: &Expr) -> Expr {
        self.ctx.byte_memory_facts(&self.ssa_concrete_values).fold(e)
    }

    /// `fold_memory_reads` for a term used only on the current path, such as a
    /// check `record_violation_guarded` conjoins with that path.
    pub(super) fn fold_memory_reads_on_path(&self, e: &Expr) -> Expr {
        self.ctx
            .byte_memory_facts(&self.ssa_concrete_values)
            .fold_assuming(e, self.current_path_condition.as_ref())
    }

    /// Whether a byte of `[addr, addr + num_bytes)` holds a symbolic store, which
    /// a byte load must not read. Byte 0 is checked under both of its keys:
    /// `store_memory_bytes` files a symbolic value at `addr`, and writes byte 0
    /// at `addr + 0`.
    pub(super) fn memory_bytes_hold_symbolic_store(&self, addr: &Expr, num_bytes: u32) -> bool {
        self.ctx.load_symbolic_memory_value(addr.clone()).is_some()
            || (0..num_bytes).any(|byte| {
                let at = addr.clone().bvadd(Expr::bitvec_const(u128::from(byte), POINTER_WIDTH));
                self.ctx.load_symbolic_memory_value(at).is_some()
            })
    }

    /// The condition a store made now executes under; `None` on every path,
    /// including a condition the asserted facts already make true (the
    /// alignment and non-null checks on a constant heap pointer).
    pub(super) fn store_path_condition(&self) -> Option<Expr> {
        let on_path = self.current_path_condition.clone()?;
        let folded = self.fold_memory_reads(&on_path);
        (!matches!(folded.value(), ExprValue::BoolConst(true))).then_some(on_path)
    }

    /// `bytes` folded for the path the store executes on, `previous` for the
    /// paths it does not.
    fn fold_store_sides(&self, on_path: &Expr, bytes: &Expr, previous: &Expr) -> (Expr, Expr) {
        let facts = self.ctx.byte_memory_facts(&self.ssa_concrete_values);
        let off_path = on_path.clone().not();
        (facts.fold_assuming(bytes, Some(on_path)), facts.fold_assuming(previous, Some(&off_path)))
    }

    /// Write `value` to byte memory at `addr`, on the current path only.
    ///
    /// Byte memory is one store chain for every path, so an unguarded store made
    /// in a branch overwrote the bytes on all of them: after
    /// `if c { a.store(1, SeqCst) }`, `a.load(SeqCst)` read 1 with `c` false, and
    /// the safe harness FAILED with a Genuine counterexample. The bytes written
    /// are `ite(path, value, previous)`. A value with no byte image goes to the
    /// symbolic side table under the same condition. Bytes that already hold a
    /// symbolic store cannot be loaded, so that store stays unconditional and no
    /// verdict may rest on it.
    pub(super) fn store_memory_bytes_on_path(
        &mut self,
        addr: Expr,
        value: Expr,
        construct: &'static str,
    ) {
        let Some(on_path) = self.store_path_condition() else {
            self.ctx.store_memory_bytes(addr, value);
            return;
        };
        let sort = value.sort().clone();
        if sort.is_int() || sort.is_array() || sort.is_datatype() {
            self.ctx.store_memory_symbolic_on_path(addr, value, on_path);
            return;
        }
        let bytes = if sort.is_bool() {
            Expr::ite(value, Expr::bitvec_const(1u128, 8), Expr::bitvec_const(0u128, 8))
        } else {
            value
        };
        let Some(width) = bytes.sort().bitvec_width().filter(|width| *width > 0) else {
            // Every other sort is rejected by `store_memory_bytes` itself.
            self.ctx.store_memory_bytes(addr, bytes);
            return;
        };
        let num_bytes = width.div_ceil(8);
        if self.memory_bytes_hold_symbolic_store(&addr, num_bytes) {
            self.ctx.unsupported_with_fallback(
                construct,
                "conditional byte store over a symbolic store",
            );
            self.ctx.store_memory_bytes(addr, bytes);
            return;
        }
        let bytes =
            if width == num_bytes * 8 { bytes } else { bytes.zero_extend(num_bytes * 8 - width) };
        let previous = self.ctx.load_memory_bytes(addr.clone(), num_bytes);
        let (bytes, previous) = self.fold_store_sides(&on_path, &bytes, &previous);
        self.ctx.store_memory_bytes(addr, Expr::ite(on_path, bytes, previous));
    }

    /// Write one byte to byte memory at `addr`, on the current path only; see
    /// `store_memory_bytes_on_path`.
    pub(super) fn store_memory_byte_on_path(
        &mut self,
        addr: Expr,
        byte: Expr,
        construct: &'static str,
    ) {
        let Some(on_path) = self.store_path_condition() else {
            self.ctx.store_memory(addr, byte);
            return;
        };
        if self.memory_bytes_hold_symbolic_store(&addr, 1) {
            self.ctx.unsupported_with_fallback(
                construct,
                "conditional byte store over a symbolic store",
            );
            self.ctx.store_memory(addr, byte);
            return;
        }
        let byte = if byte.sort().is_bool() {
            Expr::ite(byte, Expr::bitvec_const(1u128, 8), Expr::bitvec_const(0u128, 8))
        } else {
            byte
        };
        let previous = self.ctx.load_memory(addr.clone());
        let (byte, previous) = self.fold_store_sides(&on_path, &byte, &previous);
        self.ctx.store_memory(addr, Expr::ite(on_path, byte, previous));
    }
}
