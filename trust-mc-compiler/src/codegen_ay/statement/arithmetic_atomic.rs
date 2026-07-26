// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! Atomic intrinsic codegen for AY.
//!
//! Extracted from arithmetic.rs — Part of #2153.
//!
//! Atomic operations are modeled as sequential operations for single-threaded
//! verification. Memory orderings are ignored since trust_mc verifies sequential behavior.
//!
//! Contains:
//! - `codegen_atomic_load`: Load value from memory through pointer
//! - `codegen_atomic_store`: Store value to memory through pointer
//! - `codegen_atomic_exchange`: Atomically swap value
//! - `codegen_atomic_cxchg`: Compare-and-exchange
//! - `codegen_atomic_fetch_binop`: Fetch-and-binop (add, sub, and, or, xor)
//! - `codegen_atomic_fetch_nand`: Fetch-and-NAND
//! - `codegen_atomic_fetch_minmax`: Fetch-and-min/max
//! - `codegen_typed_swap`: typed_swap_nonoverlapping / std::mem::swap (Part of #3477)

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, BinOp, Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::types::bv8_sort;
use crate::kani_middle::abi::LayoutOf;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen atomic_load - load value from memory through pointer.
    ///
    /// Models atomic_load as a regular memory read for single-threaded verification.
    /// The ordering parameter is ignored (SC assumed).
    ///
    /// REQUIRES: args[0] = pointer to value
    /// ENSURES: destination gets the value loaded from memory
    pub(super) fn codegen_atomic_load(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            debug!("codegen_atomic_load: no arguments");
            return None;
        }

        // Get pointer expression from args[0]
        let ptr_expr = self.codegen_operand(&args[0])?;
        debug!("codegen_atomic_load: ptr_expr sort={:?}", ptr_expr.sort());

        // Get destination type to determine the size to load
        let dest_ty = destination.ty(self.body.locals()).into_option()?;
        let size = LayoutOf::new(dest_ty).size_of().unwrap_or(1);
        debug!("codegen_atomic_load: loading {} bytes for type {:?}", size, dest_ty);

        // Load value from memory
        let loaded = self.ctx.load_memory_bytes(ptr_expr, size as u32);

        // Handle bool type specially (byte to bool conversion)
        let result = if matches!(dest_ty.kind(), TyKind::RigidTy(RigidTy::Bool)) {
            loaded.ne(Expr::bitvec_const(0, 8))
        } else {
            loaded
        };

        // Assign to destination
        self.bind_ssa_result(destination, result);
        target
    }

    /// Codegen atomic_store - store value to memory through pointer.
    ///
    /// Models atomic_store as a regular memory write for single-threaded verification.
    /// The ordering parameter is ignored (SC assumed).
    ///
    /// REQUIRES: args[0] = pointer to location, args[1] = value to store
    /// ENSURES: Memory is updated with the stored value
    pub(super) fn codegen_atomic_store(
        &mut self,
        args: &[Operand],
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            debug!(
                "codegen_atomic_store: insufficient args ({}) — fail-closed (#2497)",
                args.len()
            );
            return None;
        }

        // Get pointer and value expressions
        let ptr_expr = self.codegen_operand(&args[0])?;
        let val_expr = self.codegen_operand(&args[1])?;
        debug!(
            "codegen_atomic_store: ptr_sort={:?}, val_sort={:?}",
            ptr_expr.sort(),
            val_expr.sort()
        );

        // Store value to memory
        self.ctx.store_memory_bytes(ptr_expr, val_expr);
        target
    }

    /// Codegen atomic_xchg (exchange) - atomically swap value.
    ///
    /// Returns the old value and stores the new value.
    /// Models as: old = load(ptr); store(ptr, new); return old
    ///
    /// REQUIRES: args[0] = pointer to location, args[1] = new value
    /// ENSURES: destination gets old value, memory updated with new value
    pub(super) fn codegen_atomic_exchange(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            debug!("codegen_atomic_exchange: insufficient args ({})", args.len());
            return None;
        }

        // Get pointer and new value expressions
        let ptr_expr = self.codegen_operand(&args[0])?;
        let new_val = self.codegen_operand(&args[1])?;
        debug!(
            "codegen_atomic_exchange: ptr_sort={:?}, new_val_sort={:?}",
            ptr_expr.sort(),
            new_val.sort()
        );

        // Get destination type to determine size
        let dest_ty = destination.ty(self.body.locals()).into_option()?;
        let size = LayoutOf::new(dest_ty).size_of().unwrap_or(1);

        // Load old value from memory
        let old_val = self.ctx.load_memory_bytes(ptr_expr.clone(), size as u32);

        // Handle bool type specially
        let result = if matches!(dest_ty.kind(), TyKind::RigidTy(RigidTy::Bool)) {
            old_val.ne(Expr::bitvec_const(0, 8))
        } else {
            old_val
        };

        // Store new value to memory
        self.ctx.store_memory_bytes(ptr_expr, new_val);

        // Assign old value to destination
        self.bind_ssa_result(destination, result);
        target
    }

    /// Codegen atomic_cxchg and atomic_cxchgweak - compare-and-exchange.
    ///
    /// Returns (old_value, success: bool) tuple. For verification purposes, we model
    /// this as always succeeding when `current == expected` and returning the old value.
    ///
    /// REQUIRES: args[0] = pointer to value, args[1] = expected, args[2] = new value
    /// ENSURES: destination.0 = old value (from pointer)
    /// ENSURES: destination.1 = true if old == expected, false otherwise
    pub(super) fn codegen_atomic_cxchg(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 3 {
            debug!("codegen_atomic_cxchg: insufficient args ({})", args.len());
            return None;
        }

        // Get pointer and expected/new values
        let ptr_expr = self.codegen_operand(&args[0])?;
        let expected = self.codegen_operand(&args[1])?;
        let new_val = self.codegen_operand(&args[2])?;
        debug!(
            "codegen_atomic_cxchg: ptr_sort={:?}, expected_sort={:?}",
            ptr_expr.sort(),
            expected.sort()
        );

        // Determine size from expected value's width
        let expected_sort = expected.sort();
        let Some(width) = expected_sort.bitvec_width() else {
            warn!(
                sort = ?expected_sort,
                "codegen_atomic_cxchg expects bitvec expected operand; skipping intrinsic"
            );
            return None;
        };
        let size = width / 8;

        // Load old value from memory
        let old_val = self.ctx.load_memory_bytes(ptr_expr.clone(), size);

        // Success if old == expected
        let success = old_val.clone().eq(expected);
        let base_name = self.ssa_base_name(destination);

        // Store old value (field 0)
        let old_name = crate::codegen_ay::names::discrim_name(&base_name);
        let old_ssa = self.ssa_name_from_base(&old_name, true);
        let old_var = self.ctx.declare_var(&old_ssa, old_val.sort().clone());
        self.assert_ssa_def(old_var.clone(), old_val.clone(), &old_name);
        self.env_update(old_name, old_var);

        // Store success flag (field 1) as 8-bit bool
        let success_name = crate::codegen_ay::names::payload_name(&base_name);
        let success_ssa = self.ssa_name_from_base(&success_name, true);
        let success_var = self.ctx.declare_var(&success_ssa, bv8_sort());
        let success_byte =
            Expr::ite(success.clone(), Expr::bitvec_const(1, 8), Expr::bitvec_const(0, 8));
        self.assert_ssa_def(success_var.clone(), success_byte, &success_name);
        self.env_update(success_name, success_var);

        // If successful, store new value to memory
        // Model as: if (old == expected) { *ptr = new; }
        // Using ITE at memory level: mem' = ite(success, store(mem, ptr, new), mem)
        // Simplified: just do the conditional store
        let cond_new = Expr::ite(success, new_val, old_val);
        self.ctx.store_memory_bytes(ptr_expr, cond_new);

        target
    }

    /// Codegen stable `compare_exchange`/`compare_exchange_weak`.
    ///
    /// Returns `Result<T, T>` instead of raw cxchg's `(T, bool)`.
    /// Field 0 (discrim_name) = BV8 discriminant (0 = Ok/success, 1 = Err/failure).
    /// Field 1 (payload_name) = old/previous value (always the old value, same for Ok and Err).
    ///
    /// REQUIRES: args[0] = &self, args[1] = current/expected, args[2] = new,
    ///           args[3..] = orderings (ignored)
    ///
    /// Part of #3452: stable compare_exchange returns Result, not (T, bool).
    pub(super) fn codegen_atomic_compare_exchange(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 3 {
            debug!("codegen_atomic_compare_exchange: insufficient args ({})", args.len());
            return None;
        }

        let ptr_expr = self.codegen_operand(&args[0])?;
        let expected = self.codegen_operand(&args[1])?;
        let new_val = self.codegen_operand(&args[2])?;
        debug!(
            "codegen_atomic_compare_exchange: ptr_sort={:?}, expected_sort={:?}",
            ptr_expr.sort(),
            expected.sort()
        );

        // Determine size from expected value's width.
        let expected_sort = expected.sort();
        let Some(width) = expected_sort.bitvec_width() else {
            warn!(
                sort = ?expected_sort,
                "codegen_atomic_compare_exchange expects bitvec expected; skipping"
            );
            return None;
        };
        let size = width / 8;

        // Load old value from memory.
        let old_val = self.ctx.load_memory_bytes(ptr_expr.clone(), size);

        // Success if old == expected.
        let success = old_val.clone().eq(expected);
        let base_name = self.ssa_base_name(destination);

        // Field 0 (discrim_name): Result discriminant.
        // 0 = Ok (success), 1 = Err (failure).
        let discrim_name = crate::codegen_ay::names::discrim_name(&base_name);
        let discrim_ssa = self.ssa_name_from_base(&discrim_name, true);
        let discrim_var = self.ctx.declare_var(&discrim_ssa, bv8_sort());
        let discrim_byte =
            Expr::ite(success.clone(), Expr::bitvec_const(0u64, 8), Expr::bitvec_const(1u64, 8));
        self.assert_ssa_def(discrim_var.clone(), discrim_byte, &discrim_name);
        self.env_update(discrim_name, discrim_var);

        // Field 1 (payload_name): old/previous value (both Ok and Err carry it).
        let payload_name = crate::codegen_ay::names::payload_name(&base_name);
        let payload_ssa = self.ssa_name_from_base(&payload_name, true);
        let payload_var = self.ctx.declare_var(&payload_ssa, old_val.sort().clone());
        self.assert_ssa_def(payload_var.clone(), old_val.clone(), &payload_name);
        self.env_update(payload_name, payload_var);

        // Conditional store: *self = ite(success, new, old).
        let cond_new = Expr::ite(success, new_val, old_val);
        self.ctx.store_memory_bytes(ptr_expr, cond_new);

        target
    }

    /// Codegen atomic fetch-and-binop operations.
    ///
    /// Atomic fetch operations return the old value and compute a new value.
    /// For verification, we model this as: old = *ptr; *ptr = op(old, arg); return old;
    ///
    /// REQUIRES: args[0] = pointer, args[1] = operand
    /// ENSURES: destination = old value loaded from memory
    /// ENSURES: memory updated with new value
    pub(super) fn codegen_atomic_fetch_binop(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        op: BinOp,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            debug!("codegen_atomic_fetch_binop: insufficient args ({})", args.len());
            return None;
        }

        // Get pointer and operand
        let ptr_expr = self.codegen_operand(&args[0])?;
        let operand = self.codegen_operand(&args[1])?;
        let operand_sort = operand.sort();
        let Some(width) = operand_sort.bitvec_width() else {
            warn!(
                sort = ?operand_sort,
                "codegen_atomic_fetch_binop expects bitvec operand; skipping intrinsic"
            );
            return None;
        };
        let size = width / 8;
        debug!(
            "codegen_atomic_fetch_binop: ptr_sort={:?}, operand_sort={:?}, op={:?}",
            ptr_expr.sort(),
            operand.sort(),
            op
        );

        // Load old value from memory
        let old_val = self.ctx.load_memory_bytes(ptr_expr.clone(), size);

        // Clone old_val once for the binary op; move the original into bind_ssa_result.
        let old_for_op = old_val.clone();
        let new_val = match op {
            BinOp::Add => old_for_op.bvadd(operand),
            BinOp::Sub => old_for_op.bvsub(operand),
            BinOp::BitAnd => old_for_op.bvand(operand),
            BinOp::BitOr => old_for_op.bvor(operand),
            BinOp::BitXor => old_for_op.bvxor(operand),
            _ => return None, // external enum: BinOp
        };

        // Store new value to memory, then bind the old value as result (move last)
        self.ctx.store_memory_bytes(ptr_expr, new_val);
        self.bind_ssa_result(destination, old_val);
        target
    }

    /// Codegen atomic fetch-and-NAND.
    ///
    /// NAND: result = !(old & operand)
    ///
    /// REQUIRES: args[0] = pointer, args[1] = operand
    /// ENSURES: destination = old value loaded from memory
    /// ENSURES: memory updated with NAND result
    pub(super) fn codegen_atomic_fetch_nand(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            debug!("codegen_atomic_fetch_nand: insufficient args ({})", args.len());
            return None;
        }

        // Get pointer and operand
        let ptr_expr = self.codegen_operand(&args[0])?;
        let operand = self.codegen_operand(&args[1])?;
        let operand_sort = operand.sort();
        let Some(width) = operand_sort.bitvec_width() else {
            warn!(
                sort = ?operand_sort,
                "codegen_atomic_fetch_nand expects bitvec operand; skipping intrinsic"
            );
            return None;
        };
        let size = width / 8;
        debug!(
            "codegen_atomic_fetch_nand: ptr_sort={:?}, operand_sort={:?}",
            ptr_expr.sort(),
            operand.sort()
        );

        // Load old value from memory
        let old_val = self.ctx.load_memory_bytes(ptr_expr.clone(), size);

        // Compute NAND: !(old & operand)
        let new_val = old_val.clone().bvand(operand).bvnot();

        // Store new value to memory
        self.ctx.store_memory_bytes(ptr_expr, new_val);

        // Return the old value
        self.bind_ssa_result(destination, old_val);
        target
    }

    /// Codegen atomic fetch-and-min/max.
    ///
    /// Computes min or max of old value and operand.
    ///
    /// REQUIRES: args[0] = pointer, args[1] = operand
    /// ENSURES: destination = old value loaded from memory
    /// ENSURES: memory updated with min/max result
    ///
    /// `is_max`: true for max, false for min
    /// `is_signed`: true for signed comparison (atomic_max/min), false for unsigned (atomic_umax/umin)
    pub(super) fn codegen_atomic_fetch_minmax(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        is_max: bool,
        is_signed: bool,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 2 {
            debug!("codegen_atomic_fetch_minmax: insufficient args ({})", args.len());
            return None;
        }

        // Get pointer and operand
        let ptr_expr = self.codegen_operand(&args[0])?;
        let operand = self.codegen_operand(&args[1])?;
        let operand_sort = operand.sort();
        let Some(width) = operand_sort.bitvec_width() else {
            warn!(
                sort = ?operand_sort,
                "codegen_atomic_fetch_minmax expects bitvec operand; skipping intrinsic"
            );
            return None;
        };
        let size = width / 8;
        debug!(
            "codegen_atomic_fetch_minmax: ptr_sort={:?}, operand_sort={:?}, is_max={}, is_signed={}",
            ptr_expr.sort(),
            operand.sort(),
            is_max,
            is_signed
        );

        // Load old value from memory
        let old_val = self.ctx.load_memory_bytes(ptr_expr.clone(), size);

        // Clone old_val once for comparison and once for ITE; move original into bind.
        // Clone operand once for comparison; move original into ITE else-branch.
        let old_for_cmp = old_val.clone();
        let operand_for_cmp = operand.clone();
        let old_wins = match (is_max, is_signed) {
            (true, true) => old_for_cmp.bvsgt(operand_for_cmp),
            (true, false) => old_for_cmp.bvugt(operand_for_cmp),
            (false, true) => old_for_cmp.bvslt(operand_for_cmp),
            (false, false) => old_for_cmp.bvult(operand_for_cmp),
        };
        let old_for_ite = old_val.clone();
        let new_val = Expr::ite(old_wins, old_for_ite, operand);
        self.bind_ssa_result(destination, old_val);

        // Store new value to memory
        self.ctx.store_memory_bytes(ptr_expr, new_val);
        target
    }

    /// Codegen `Atomic*::new(val)` — stable API constructor.
    ///
    /// Atomic types are `repr(transparent)` over their inner value, so the
    /// constructor simply assigns the initial value to the destination.
    /// Part of #3452, #3487.
    pub(super) fn codegen_atomic_new(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            debug!("codegen_atomic_new: no arguments");
            return None;
        }
        let init_val = self.codegen_operand(&args[0])?;
        debug!("codegen_atomic_new: init_val sort={:?}", init_val.sort());
        self.bind_ssa_result(destination, init_val);
        target
    }
}
