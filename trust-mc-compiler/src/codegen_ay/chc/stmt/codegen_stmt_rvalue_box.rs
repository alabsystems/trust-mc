// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! ShallowInitBox rvalue translation for CHC statement encoding.
//!
//! Extracted from `codegen_stmt_rvalue.rs` per #3920 to reduce merge-conflict
//! contention. Handles Box<T> initialization from exchange_malloc pointer.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use tracing::{debug, warn};

use crate::codegen_ay::types::POINTER_WIDTH;

use super::ChcCtx;
use super::codegen_expr_heap::{obj_size_in, obj_size_out, obj_valid_in, obj_valid_out};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Translate `Rvalue::ShallowInitBox(operand, ty)` to a CHC expression.
    ///
    /// Part of #2075: ShallowInitBox wraps an already-allocated pointer in Box<T>.
    ///
    /// In MIR, `Box::new(42)` desugars to:
    ///   `_ptr = exchange_malloc(size, align)`   // allocates memory
    ///   `*_ptr = 42`                            // writes initial value
    ///   `_box = ShallowInitBox(_ptr, T)`        // wraps pointer in Box
    ///
    /// The exchange_malloc stub (`stubs_alloc.rs`) already handles:
    ///   - Fresh pointer allocation (`obj_id << 32 | 0`)
    ///   - `obj_valid[obj_id] = true`
    ///   - `obj_size[obj_id] = size`
    ///
    /// ShallowInitBox must NOT allocate a new obj_id. It should pass through
    /// the operand pointer so that subsequent `*_box = value` writes to the
    /// same address that exchange_malloc returned.
    ///
    /// Part of #3920: extracted from `translate_rvalue_with_modified`.
    pub(in crate::codegen_ay::chc) fn translate_rvalue_shallow_init_box(
        &mut self,
        operand: &Operand,
        ty: rustc_public::ty::Ty,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let type_size = self.get_type_size(ty);

        // ZST: known zero-size types return a null pointer
        if type_size == Some(0) {
            debug!(?ty, "ShallowInitBox: ZST returns zero pointer");
            return Some(Expr::bitvec_const(0, POINTER_WIDTH));
        }

        // Pass through the allocation pointer from exchange_malloc.
        // The operand is the raw pointer returned by the allocator.
        // exchange_malloc already set the correct obj_size, so this
        // path is sound regardless of whether we know the type size.
        if let Some(ptr_expr) = self.translate_operand_with_modified(operand, modified_locals) {
            debug!(?ty, ?type_size, "ShallowInitBox: passing through exchange_malloc pointer");
            return Some(ptr_expr);
        }

        // Fallback: operand not translatable (no prior exchange_malloc).
        // Part of #3099: Reclassified to SOUND_APPROXIMATION — allocates
        // a fresh heap object with a fresh ID, which is a sound
        // over-approximation (any possible allocation).
        warn!(?ty, "ShallowInitBox: operand not translatable, allocating fresh object");
        self.record_sound_fallback_reason("shallow_init_box_fallback");

        let obj_id = match self.heap_state.next_heap_alloc_id() {
            Some(id) => id,
            None => {
                warn!("ShallowInitBox: allocation ID overflow; skipping allocation");
                // Part of #3369: Reclassified SOUND_APPROXIMATION → DEMOTED.
                // Returning None triggers caller's self-loop (identity).
                self.record_fallback();
                return None;
            }
        };
        let obj_id_expr = Expr::bitvec_const(obj_id as i128, 32);
        let zero_offset = Expr::bitvec_const(0, 32);
        let ptr = obj_id_expr.clone().concat(zero_offset);

        let obj_valid_in = obj_valid_in();
        let obj_valid_out = obj_valid_out();
        let obj_size_in = obj_size_in();
        let obj_size_out = obj_size_out();

        let valid_constraint =
            obj_valid_out.eq(obj_valid_in.store(obj_id_expr.clone(), Expr::bool_const(true)));
        self.heap_state.pending_updates.push(valid_constraint);

        // Soundness fix (#2465): When type_size is unknown, use size=0
        // instead of an unconstrained symbolic variable. An unconstrained
        // size lets the solver pick any value — including one large enough
        // to make all bounds checks trivially pass, hiding real bugs.
        // Size=0 is a sound over-approximation: any non-zero access
        // (offset + access_size) bvule 0 fails, so the verifier reports
        // a potential issue. This may produce false counterexamples but
        // never false proofs.
        let size_expr = Expr::bitvec_const(type_size.unwrap_or(0) as i128, 32);
        self.record_known_heap_alloc_size_expr(obj_id, &size_expr);
        let size_constraint = obj_size_out.eq(obj_size_in.store(obj_id_expr, size_expr));
        self.heap_state.pending_updates.push(size_constraint);

        self.mark_heap_metadata_modified();

        debug!(obj_id, ?type_size, "ShallowInitBox: fallback fresh allocation");
        Some(ptr)
    }
}
