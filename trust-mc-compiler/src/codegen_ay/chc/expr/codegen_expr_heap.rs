// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Heap pointer operations and memory safety checks for CHC codegen.
//!
//! Extracted from codegen_expr.rs per #2129 decomposition.
//! Handles: heap metadata arrays, bitvector utilities for allocation checks,
//! pointer splitting, heap access validity checks, and error rule emission.
//!
//! Migrated from include!() to proper module.
//! Part of #2306: include!() to proper module migration.

use ay_bindings::{Expr, ExprValue, Sort};
use std::sync::Arc;
use std::sync::atomic::Ordering;
use tracing::{debug, warn};
use trust_mc_core::chc::{RelationApp, Rule, RuleBody};
use trust_mc_core::violation::PropertyKind;

use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, bool_sort, coerce_bitvec_width_safe};

use super::ChcCtx;
use super::codegen_ctx::diagnostics::{CellCounter, GLOBAL_COUNTERS};
use super::memory_model::MemPtr;

/// Get the current number of untranslatable heap safety check conservative error rules.
/// Delegates to GLOBAL_COUNTERS (Part of #2906).
pub(in crate::codegen_ay) fn get_chc_heap_check_untranslatable_count() -> usize {
    GLOBAL_COUNTERS.heap_check_untranslatable.load(Ordering::Relaxed)
}

/// Get the current number of conservative heap checks due to unknown type layout.
/// Delegates to GLOBAL_COUNTERS (Part of #2906).
pub(in crate::codegen_ay) fn get_chc_heap_check_unknown_layout_count() -> usize {
    GLOBAL_COUNTERS.heap_check_unknown_layout.load(Ordering::Relaxed)
}

// =========================================================================
// Heap metadata array sort and variable constructors.
//
// The split-pointer heap model uses two metadata arrays:
//   obj_valid: Array(BV32, Bool)  — tracks which allocations are alive
//   obj_size:  Array(BV32, BV32)  — tracks allocation sizes
//
// CHC rules thread these through SSA-style in/out pairs. These helpers
// centralise the sort and variable construction that was previously
// repeated 20+ times across stubs_alloc, codegen_stmt_rvalue,
// codegen_rules_entry, codegen_rules_helpers, and codegen_decl_state_vars.
// Part of #2267: allocation debt reduction.
// =========================================================================

/// Sort for the obj_valid metadata array: `(Array (_ BitVec 32) Bool)`.
#[must_use]
pub(in crate::codegen_ay::chc) fn obj_valid_sort() -> Sort {
    Sort::array(Sort::bitvec(32), bool_sort())
}

/// Sort for the obj_size metadata array: `(Array (_ BitVec 32) (_ BitVec 32))`.
#[must_use]
pub(in crate::codegen_ay::chc) fn obj_size_sort() -> Sort {
    Sort::array(Sort::bitvec(32), Sort::bitvec(32))
}

/// Input `obj_valid` variable for the current CHC rule.
#[must_use]
pub(in crate::codegen_ay::chc) fn obj_valid_in() -> Expr {
    Expr::var("obj_valid", obj_valid_sort())
}

/// Output `obj_valid__out` variable for the current CHC rule.
#[must_use]
pub(in crate::codegen_ay::chc) fn obj_valid_out() -> Expr {
    Expr::var("obj_valid__out", obj_valid_sort())
}

/// Input `obj_size` variable for the current CHC rule.
#[must_use]
pub(in crate::codegen_ay::chc) fn obj_size_in() -> Expr {
    Expr::var("obj_size", obj_size_sort())
}

/// Output `obj_size__out` variable for the current CHC rule.
#[must_use]
pub(in crate::codegen_ay::chc) fn obj_size_out() -> Expr {
    Expr::var("obj_size__out", obj_size_sort())
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Returns the current obj_valid array expression (uses __out when modified).
    #[must_use]
    pub(in crate::codegen_ay::chc) fn current_obj_valid_array(&self) -> Expr {
        if self.heap_state.are_metadata_arrays_modified() {
            obj_valid_out()
        } else {
            obj_valid_in()
        }
    }

    /// Returns the current obj_size array expression (uses __out when modified).
    #[must_use]
    pub(in crate::codegen_ay::chc) fn current_obj_size_array(&self) -> Expr {
        if self.heap_state.are_metadata_arrays_modified() { obj_size_out() } else { obj_size_in() }
    }

    /// Coerces a bitvec expression to 32-bit for the split-pointer heap model.
    ///
    /// The heap metadata arrays (`obj_size`, `obj_valid`) use BV32 indices and values
    /// because the split-pointer model represents object IDs and sizes as 32-bit.
    /// This function is intentionally lossy for widths > 32 (truncates high bits).
    /// Returns `None` if the expression is not a bitvec sort.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn coerce_to_heap_bv32(&self, expr: Expr) -> Option<Expr> {
        let expr = coerce_bitvec_width_safe(expr, 32, SignExtension::ZeroExtend);
        expr.sort().bitvec_width().map(|_| expr)
    }

    /// Builds a check that the upper bits of a bitvector are zero when width > 32.
    ///
    /// Used alongside [`coerce_to_heap_bv32`] in the split-pointer heap model:
    /// the coercion truncates, and this function produces the safety assertion
    /// that the truncation was lossless (high bits were zero).
    #[must_use]
    pub(in crate::codegen_ay::chc) fn fits_in_bv32_check(&self, expr: &Expr) -> Option<Expr> {
        let width = expr.sort().bitvec_width()?;
        if width <= 32 {
            return None;
        }
        let high = expr.clone().extract(width - 1, 32);
        let zero = Expr::bitvec_const(0, width - 32);
        Some(high.eq(zero))
    }

    /// Builds a non-zero check for a bitvector expression.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn nonzero_bv_check(
        &self,
        expr: Expr,
        width: u32,
    ) -> Option<Expr> {
        let expr = coerce_bitvec_width_safe(expr, width, SignExtension::ZeroExtend);
        expr.sort().bitvec_width()?;
        let zero = Expr::bitvec_const(0, width);
        Some(expr.eq(zero).not())
    }

    /// Builds a power-of-two check for a bitvector expression.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn power_of_two_bv_check(
        &self,
        expr: Expr,
        width: u32,
    ) -> Option<Expr> {
        let expr = coerce_bitvec_width_safe(expr, width, SignExtension::ZeroExtend);
        expr.sort().bitvec_width()?;
        let one = Expr::bitvec_const(1, width);
        let minus_one = expr.clone().bvsub(one);
        let and_mask = expr.bvand(minus_one);
        let zero = Expr::bitvec_const(0, width);
        Some(and_mask.eq(zero))
    }

    /// Splits a pointer into (obj_id, offset) using the split-pointer model.
    ///
    /// The split-pointer model is designed for 64-bit pointers:
    /// - Upper 32 bits: object ID
    /// - Lower 32 bits: offset within object
    ///
    /// Non-64-bit pointers return None. 32-bit pointers cannot be sensibly
    /// split (zero-extending would make all obj_ids = 0, which is unsound).
    /// See #1205.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn split_pointer(&self, addr: &Expr) -> Option<(Expr, Expr)> {
        let width = addr.sort().bitvec_width()?;
        if width != 64 {
            return None;
        }
        Some((addr.clone().extract(63, 32), addr.clone().extract(31, 0)))
    }

    pub(in crate::codegen_ay::chc) fn const_obj_id_u32(obj_id: &Expr) -> Option<u32> {
        super::codegen_expr_heap_bv_eval::const_obj_id_u32(obj_id)
    }

    /// Generates heap validity/bounds checks for a memory access.
    ///
    /// Part of #1860: When wide memory model is enabled, also generates
    /// WideMemManager bounds checks using `is_dereferenceable`.
    pub(in crate::codegen_ay::chc) fn heap_access_checks(
        &self,
        addr: Expr,
        pointee_ty: rustc_public::ty::Ty,
    ) -> Vec<Expr> {
        let Some((obj_id, offset)) = self.split_pointer(&addr) else {
            // Part of #2965: Fail-closed when pointer cannot be split (non-64-bit).
            // Emit `false` so the solver produces CTREX rather than an unconstrained
            // proof. Consistent with the unknown-alignment fail-closed pattern below.
            let count = self.diagnostics.heap_check_untranslatable.inc_get();
            warn!(
                count,
                addr_sort = ?addr.sort(),
                "heap_access_checks: cannot split non-64-bit pointer, emitting fail-closed check"
            );
            return vec![Expr::bool_const(false)];
        };

        let mut checks = Vec::new();
        // Stack locals are allocated at function entry and tracked in local_addresses.
        // For those IDs, derive bounds directly from local layout and avoid dependency
        // on metadata array propagation through unrelated calls.
        let const_obj_id = Self::const_obj_id_u32(&obj_id);
        let stack_obj_size = const_obj_id
            .and_then(|id| self.heap_state.local_idx_for_obj_id(id))
            .and_then(|local_idx| self.body.locals().get(local_idx))
            .and_then(|local_decl| self.get_type_size(local_decl.ty))
            .and_then(|size| u32::try_from(size).ok());

        // Stack locals are valid for the whole function and are not represented
        // by heap dealloc state. If this remains as obj_valid[obj_id], later
        // scalarization rewrites non-tracked constant IDs to an unconstrained
        // select_any value, which creates spurious UAF counterexamples.
        //
        // The same spurious-UAF hazard applies to the fresh backing buffer of a
        // provably-valid over-approximated collection constructor (into_vec /
        // bounded_any …): its `obj_valid[id]` select rides a free
        // `obj_valid__out` in the check rule. These allocations are known-live
        // under safe-Rust preconditions, so treat them as trivially valid.
        // SOUNDNESS: `Vec::from_raw_parts` pointers are never registered as
        // provably-valid backings, so a genuinely-dangling Vec still fails.
        let is_provably_valid_backing =
            const_obj_id.is_some_and(|id| self.heap_state.is_provably_valid_backing(id));
        if stack_obj_size.is_some() || is_provably_valid_backing {
            checks.push(Expr::bool_const(true));
        } else {
            let obj_valid = self.current_obj_valid_array();
            checks.push(obj_valid.select(obj_id.clone()));
        }

        // Part of #3159: Detect dyn Trait pointee types. Dyn trait types are
        // unsized — their layout is resolved at runtime via the vtable, not at
        // compile time. The allocation side already records obj_size = 0 for
        // these (with zero-size exemptions). The access side must skip the
        // fail-closed checks to avoid unconditional Genuine CTREX.
        let is_dyn_trait_pointee = matches!(
            pointee_ty.kind(),
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Dynamic(..))
        );

        // Part of #3495: Detect Slice(T) pointee types. Slices are unsized —
        // get_type_size/get_type_align return None for [T]. But element accesses
        // have known size/alignment from the element type T. Extract T and use
        // its layout instead of emitting fail-closed false.
        // Part of #3655: str is layout-identical to [u8] — treat it as
        // Slice(u8) for heap access checks (element size=1, alignment=1).
        // Without this, heap_access_checks emits fail-closed false for str,
        // causing unconditional Genuine CTREX on Box<str> drop.
        let slice_elem_ty = match pointee_ty.kind() {
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Slice(elem_ty)) => {
                Some(elem_ty)
            }
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Str) => {
                // str is [u8] under the hood — use u8 as the element type.
                Some(rustc_public::ty::Ty::unsigned_ty(rustc_public::ty::UintTy::U8))
            }
            _ => None,
        };

        // Resolve effective alignment: use element type for slices.
        let effective_align = self
            .get_type_align(pointee_ty)
            .or_else(|| slice_elem_ty.and_then(|ety| self.get_type_align(ety)));

        match effective_align {
            Some(align) if align > 1 => {
                let align_expr = Expr::bitvec_const(align as i128, 32);
                let rem = offset.clone().bvurem(align_expr);
                let zero = Expr::bitvec_const(0, 32);
                checks.push(rem.eq(zero));
            }
            Some(_) => {} // align <= 1: no alignment check needed
            None if is_dyn_trait_pointee => {
                // Part of #3159: dyn Trait alignment is unknown at compile time
                // but guaranteed correct by the vtable-resolved concrete type.
                // Skip instead of emitting fail-closed `false`.
                debug!("heap alignment check: dyn Trait pointee — skipping (vtable-resolved)");
            }
            None => {
                // #2501: Unknown alignment — emit conservative `false` (fail-closed).
                // Prevents false proofs for unknown-layout types.
                let count = self.diagnostics.heap_check_unknown_layout.inc_get();
                warn!(
                    count,
                    "heap alignment check: unknown type alignment, emitting fail-closed check"
                );
                checks.push(Expr::bool_const(false));
            }
        }

        // Resolve effective size: use element type for slices. Part of #3495.
        let effective_size = self
            .get_type_size(pointee_ty)
            .or_else(|| slice_elem_ty.and_then(|ety| self.get_type_size(ety)));

        match effective_size {
            Some(access_size) if access_size > 0 && u32::try_from(access_size).is_ok() => {
                let size_expr = Expr::bitvec_const(access_size as i128, 32);
                let end_offset = offset.clone().bvadd(size_expr);
                let no_wrap = end_offset.clone().bvuge(offset.clone());
                checks.push(no_wrap);

                // Part of #3159: Exempt zero-size allocations from bounds
                // checks. Dyn trait allocations record obj_size = 0 because
                // the size is resolved at runtime via the vtable. The check
                // becomes: obj_size[id] == 0 || end_offset <= obj_size[id].
                // For unconstrained obj_ids, skip entirely (obj_size lookup
                // would be unconstrained → false CTREX).
                let alloc_size = if let Some(size) = stack_obj_size {
                    Some(Expr::bitvec_const(size as i128, 32))
                } else if let Some(size) =
                    const_obj_id.and_then(|id| self.heap_state.heap_alloc_size(id))
                {
                    Some(Expr::bitvec_const(size as i128, 32))
                } else if const_obj_id.is_some() {
                    let heap_obj_size = self.current_obj_size_array();
                    Some(heap_obj_size.select(obj_id))
                } else {
                    None // unconstrained obj_id — skip bounds check
                };
                if let Some(ref alloc_size) = alloc_size {
                    let zero = Expr::bitvec_const(0u64, 32);
                    let is_zero_size = alloc_size.clone().eq(zero);
                    let bounds_ok = end_offset.bvule(alloc_size.clone());
                    checks.push(Expr::or(is_zero_size, bounds_ok));
                }

                // Part of #1860: WideMemManager bounds check integration.
                // Part of #3159: Only when alloc_size is known.
                if let (Some(wide_mem), Some(alloc_size)) =
                    (self.wide_mem_manager.as_ref(), alloc_size)
                {
                    let remaining_size = {
                        let zero = Expr::bitvec_const(0u64, 32);
                        let underflow = offset.clone().bvugt(alloc_size.clone());
                        let diff = alloc_size.bvsub(offset);
                        Expr::ite(underflow, zero, diff)
                    };

                    let extend_bits = POINTER_WIDTH - 32;
                    let remaining_size_wide = remaining_size.zero_extend(extend_bits);
                    let wide_ptr = MemPtr::wide(remaining_size_wide);

                    let deref_check = wide_mem.is_dereferenceable(&wide_ptr, access_size);
                    checks.push(deref_check);

                    debug!(
                        access_size,
                        "CHC: heap_access_checks - WideMemManager bounds check added (#1860)"
                    );
                }
            }
            Some(_) => {
                // Fix #1206: access_size == 0 or > u32::MAX — skip bounds check
                // (zero-size is trivially safe; >4GB would wrap in bv32 arithmetic).
            }
            None if is_dyn_trait_pointee => {
                // Part of #3159: dyn Trait size is unknown at compile time.
                // The allocation side already uses obj_size = 0 with a zero-size
                // exemption (line 298: is_zero_size || bounds_ok). Emitting
                // fail-closed `false` here would unconditionally trigger CTREX
                // on every dyn trait dereference. Skip the bounds check — the
                // concrete type's size is correct by construction via vtable dispatch.
                debug!("heap bounds check: dyn Trait pointee — skipping (vtable-resolved)");
            }
            None => {
                // #2501: Unknown size — emit conservative `false` (fail-closed).
                // Prevents false proofs for unknown-layout types.
                let count = self.diagnostics.heap_check_unknown_layout.inc_get();
                warn!(count, "heap bounds check: unknown type size, emitting fail-closed check");
                checks.push(Expr::bool_const(false));
            }
        }

        checks
    }

    /// Emits an error rule for a condition that must hold.
    ///
    /// A check `cond` generates: `from_rel(state) ∧ stmt_constraints ∧ !cond → error()`.
    ///
    /// If `cond` cannot be converted to a boolean expression (unsupported sort),
    /// emits a conservative unconditional error rule instead of silently dropping
    /// the check. This is sound: it may produce false counterexamples but never
    /// false proofs. See #2314.
    pub(in crate::codegen_ay::chc) fn emit_error_rule_for_condition(
        &mut self,
        from_app: &RelationApp,
        cond: Expr,
        stmt_constraints: &[Expr],
        bb_idx: usize,
    ) {
        self.emit_error_rule_for_condition_with_kind(
            from_app,
            cond,
            stmt_constraints,
            bb_idx,
            PropertyKind::MemorySafety,
            None,
        );
    }

    /// Emit a memory-safety error rule for a copy / copy_nonoverlapping /
    /// write_bytes SPAN-access UB obligation, TAGGING the per-property relation
    /// so `translate()` can later detect whether the check const-folded to a
    /// definite (unconditional) violation once scalarization resolves a
    /// fully-concrete access. These span checks (alignment / count-overflow /
    /// allocation-bound) are PRECISE and PROVENANCE-INDEPENDENT, so a folded
    /// violation is a genuine bug — see
    /// `ChcDiagnostics::intrinsic_span_property_ids`.
    ///
    /// The tag is the property id `register_error_head` will assign, which is
    /// `self.vc.properties.len()` at registration; a per-property head is
    /// registered iff the check is non-trivial (not skipped as trivially true)
    /// and the per-harness property budget is not exhausted, so we record the
    /// id only when the property count actually advanced.
    pub(in crate::codegen_ay::chc) fn emit_intrinsic_span_ub_check(
        &mut self,
        from_app: &RelationApp,
        cond: Expr,
        stmt_constraints: &[Expr],
        bb_idx: usize,
    ) {
        let id_before = self.vc.properties.len();
        self.emit_error_rule_for_condition(from_app, cond, stmt_constraints, bb_idx);
        if self.vc.properties.len() == id_before + 1 {
            self.diagnostics.intrinsic_span_property_ids.push(id_before as u32);
        }
    }

    /// Like [`Self::emit_error_rule_for_condition`], but with an explicit
    /// property kind and optional Kani-parity description for the per-property
    /// report line (e.g. `DivisionByZero` / "attempt to compute simd_div which
    /// would overflow"). The default `MemorySafety`+`None` wrapper above keeps
    /// the 70-odd existing heap-check call sites unchanged.
    pub(in crate::codegen_ay::chc) fn emit_error_rule_for_condition_with_kind(
        &mut self,
        from_app: &RelationApp,
        cond: Expr,
        stmt_constraints: &[Expr],
        bb_idx: usize,
        kind: PropertyKind,
        message: Option<String>,
    ) {
        let from_app = self.refresh_block_relation_app(from_app);
        let Some(bool_cond) = self.to_bool_expr(cond, bb_idx) else {
            // #2314: Emit conservative error rule instead of silently dropping.
            // Same pattern as emit_untranslatable_assert_rule in codegen_expr_assert.rs.
            let count = self.diagnostics.heap_check_untranslatable.inc_get();
            warn!(
                ?bb_idx,
                count,
                "cannot convert heap safety condition to bool; \
                 emitting conservative error rule"
            );
            // BSEM-18: per-property head (fail-closed conservative check).
            let error_app = self.register_error_head(kind, bb_idx, message);
            // Part of #2486: avoid stmt_constraints.to_vec() via from_base_and_extra.
            let body = RuleBody::from_base_and_extra(Some(from_app), stmt_constraints, []);
            let rule = Rule::new(body, error_app);
            self.vc.add_rule(rule);
            return;
        };

        if matches!(bool_cond.value(), ExprValue::BoolConst(true)) {
            debug!(?bb_idx, "skipping trivially true memory safety error rule");
            return;
        }

        let violation = bool_cond.not();
        // BSEM-18: per-property error head bridged into the aggregate `error`.
        let error_app = self.register_error_head(kind, bb_idx, message);

        // Part of #2486: avoid stmt_constraints.to_vec() + push via from_base_and_extra.
        let error_body =
            RuleBody::from_base_and_extra(Some(from_app), stmt_constraints, [violation]);

        let error_rule = Rule::new(error_body, error_app);
        self.vc.add_rule(error_rule);
        debug!(?bb_idx, "emitted memory safety error rule");
    }

    /// Shared-constraint variant of [`Self::emit_error_rule_for_condition`].
    ///
    /// Uses `RuleBody::from_shared_base` so repeated safety checks emitted from
    /// one block reuse the same `Arc<[Expr]>` base instead of cloning the full
    /// constraint vector per rule. Part of #2507.
    pub(in crate::codegen_ay::chc) fn emit_error_rule_for_condition_shared(
        &mut self,
        from_app: &RelationApp,
        cond: Expr,
        shared_constraints: &Arc<[Expr]>,
        bb_idx: usize,
    ) {
        let from_app = self.refresh_block_relation_app(from_app);
        let Some(bool_cond) = self.to_bool_expr(cond, bb_idx) else {
            let count = self.diagnostics.heap_check_untranslatable.inc_get();
            warn!(
                ?bb_idx,
                count,
                "cannot convert heap safety condition to bool; \
                 emitting conservative error rule"
            );
            // BSEM-18: per-property head (fail-closed conservative check).
            let error_app = self.register_error_head(PropertyKind::MemorySafety, bb_idx, None);
            let body =
                RuleBody::from_shared_base(Some(from_app), Arc::clone(shared_constraints), []);
            self.vc.add_rule(Rule::new(body, error_app));
            return;
        };

        if matches!(bool_cond.value(), ExprValue::BoolConst(true)) {
            debug!(?bb_idx, "skipping trivially true memory safety error rule");
            return;
        }

        let violation = bool_cond.not();
        // BSEM-18: per-property error head bridged into the aggregate `error`.
        let error_app = self.register_error_head(PropertyKind::MemorySafety, bb_idx, None);
        let error_body =
            RuleBody::from_shared_base(Some(from_app), Arc::clone(shared_constraints), [violation]);

        let error_rule = Rule::new(error_body, error_app);
        self.vc.add_rule(error_rule);
        debug!(?bb_idx, "emitted shared memory safety error rule");
    }
}
