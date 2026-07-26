// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Scalar shadow-memory encoding for per-byte memory-initialization tracking.
//!
//! Part of MEMUB-24/25/27: the `check_uninit` instrumentation injects calls to
//! the `kani_core::mem_init` model functions (`Is*PtrInitialized`,
//! `Set*PtrInitialized`, `CopyInitState*`, `Load/StoreArgument`,
//! `InitializeMemoryInitializationState`). The library bodies mutate a
//! `static mut MEM_INIT_STATE` which neither backend models, so both codegens
//! intercept the calls and encode Kani's *scalar* shadow state directly:
//!
//! - one non-deterministically tracked byte, identified by
//!   `(tracked_obj, tracked_off)`,
//! - a single `tracked_init: Bool` holding that byte's initialization state.
//!
//! For proofs the tracked byte is universally quantified (every byte is
//! checked); for counterexamples the solver picks the byte that exhibits the
//! bug. This is a pure BV+Bool fragment that AY decides.
//!
//! This module hosts the backend-independent expression builders plus the MIR
//! helper that recovers the compile-time `[bool; N]` layout mask created by
//! `mk_layout_operand`. The CHC handlers live in
//! `chc/call/codegen_call_kani_model_mem_init.rs`; the BMC handlers in
//! `statement/codegen_kani_call.rs`.

use ay_bindings::Expr;
use rustc_public::mir::{AggregateKind, Body, ConstOperand, Operand, Rvalue, StatementKind};
use rustc_public::ty::{ConstantKind, RigidTy, TyKind};

/// The scalar shadow state for one program point: the tracked byte's
/// coordinates and its current initialization value.
///
/// Sorts are backend-chosen: CHC uses BV32 obj/off (split-pointer model),
/// BMC uses BV64 (stride model). All builders below only require that
/// `obj`/`off` widths agree with the pointer-derived exprs passed in.
#[derive(Clone, Debug)]
pub(in crate::codegen_ay) struct ShadowMemExprs {
    /// Currently tracked object id.
    pub obj: Expr,
    /// Currently tracked byte offset within the object.
    pub off: Expr,
    /// Initialization state of the tracked byte.
    pub init: Expr,
}

impl ShadowMemExprs {
    /// `tracked_obj == obj && (tracked_off - off) <u total_bytes`.
    ///
    /// The subtract-and-compare form is equivalent to Kani's
    /// `tracked_off >= off && tracked_off < off + total` on the byte ranges
    /// that matter (offsets never straddle the modulus in either backend's
    /// object model) and avoids a second comparison.
    fn in_range(&self, obj: &Expr, off: &Expr, total_bytes: &Expr) -> Expr {
        let delta = self.off.clone().bvsub(off.clone());
        self.obj.clone().eq(obj.clone()).and(delta.bvult(total_bytes.clone()))
    }

    /// `(tracked_off - off) % layout_len`, the tracked byte's index into the
    /// per-element layout mask. Single-element accesses (`multi_elt == false`)
    /// skip the modulo — the mask covers the whole range — keeping the
    /// encoding in the linear BV fragment PDR handles best.
    fn mask_index(&self, off: &Expr, layout_len: usize, multi_elt: bool) -> Expr {
        let delta = self.off.clone().bvsub(off.clone());
        if multi_elt && layout_len > 1 {
            let width = delta.sort().bitvec_width().unwrap_or(32);
            delta.bvurem(Expr::bitvec_const(layout_len as u64, width))
        } else {
            delta
        }
    }

    /// Whether the tracked byte hits a *data* (non-padding) byte of the mask.
    ///
    /// Contiguous `true` runs compress to range tests
    /// (`idx - start <u len`, or `idx == start` for singleton runs), so the
    /// typical struct mask (data prefix + padding tail) costs one or two
    /// comparisons instead of an O(size) disjunction — this keeps the
    /// certificate-discharge re-check inside its solver budget. All-true masks
    /// fold to `true` and all-false masks to `false`.
    fn mask_hit(idx: &Expr, mask: &[bool]) -> Expr {
        if mask.iter().all(|b| *b) {
            return Expr::bool_const(true);
        }
        let width = idx.sort().bitvec_width().unwrap_or(32);
        let mut hits: Vec<Expr> = Vec::new();
        let mut k = 0;
        while k < mask.len() {
            if !mask[k] {
                k += 1;
                continue;
            }
            let start = k;
            while k < mask.len() && mask[k] {
                k += 1;
            }
            let run_len = k - start;
            let run = if run_len == 1 {
                idx.clone().eq(Expr::bitvec_const(start as u64, width))
            } else {
                idx.clone()
                    .bvsub(Expr::bitvec_const(start as u64, width))
                    .bvult(Expr::bitvec_const(run_len as u64, width))
            };
            hits.push(run);
        }
        if hits.is_empty() { Expr::bool_const(false) } else { Expr::or_many(hits) }
    }

    /// Kani `MemoryInitializationState::get{,_slice}`: the value returned by
    /// `Is*PtrInitialized(ptr, mask, num_elts)`.
    ///
    /// `!(in_range && mask_hit) || tracked_init` — bytes outside the tracked
    /// range (or padding bytes the mask ignores) read as initialized; the
    /// tracked data byte reads its shadow value. `multi_elt` marks slice-style
    /// accesses whose mask repeats per element.
    pub(in crate::codegen_ay) fn get_expr(
        &self,
        obj: &Expr,
        off: &Expr,
        mask: &[bool],
        total_bytes: &Expr,
        multi_elt: bool,
    ) -> Expr {
        let idx = self.mask_index(off, mask.len(), multi_elt);
        let relevant = self.in_range(obj, off, total_bytes).and(Self::mask_hit(&idx, mask));
        relevant.not().or(self.init.clone())
    }

    /// Kani `MemoryInitializationState::set{,_slice}`: the tracked byte's new
    /// shadow value after `Set*PtrInitialized(ptr, mask, num_elts, value)`.
    ///
    /// `ite(in_range, mask_hit && value, tracked_init)` — padding bytes are
    /// (re-)marked uninitialized whenever the range is written, matching
    /// `self.value = layout[..] && value`.
    pub(in crate::codegen_ay) fn set_expr(
        &self,
        obj: &Expr,
        off: &Expr,
        mask: &[bool],
        total_bytes: &Expr,
        multi_elt: bool,
        value: &Expr,
    ) -> Expr {
        let idx = self.mask_index(off, mask.len(), multi_elt);
        let written = Self::mask_hit(&idx, mask).and(value.clone());
        Expr::ite(self.in_range(obj, off, total_bytes), written, self.init.clone())
    }

    /// Kani `MemoryInitializationState::bless`: tracked byte's new value after
    /// unconditionally marking `total_bytes` at `(obj, off)` initialized.
    pub(in crate::codegen_ay) fn bless_expr(
        &self,
        obj: &Expr,
        off: &Expr,
        total_bytes: &Expr,
    ) -> Expr {
        Expr::ite(self.in_range(obj, off, total_bytes), Expr::bool_const(true), self.init.clone())
    }

    /// Kani `MemoryInitializationState::copy`: the full post-state of
    /// `CopyInitState(from, to, num_elts)`.
    ///
    /// If the tracked byte lies in the source range, a fresh nondet bool
    /// (`should_reset`) decides whether tracking is re-pointed at the
    /// corresponding destination byte (value preserved). Otherwise the first
    /// `elem_bytes` of the destination are blessed, mirroring the library's
    /// `bless::<LAYOUT_SIZE>(to_ptr, 1)` fallback.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::codegen_ay) fn copy_exprs(
        &self,
        from_obj: &Expr,
        from_off: &Expr,
        to_obj: &Expr,
        to_off: &Expr,
        total_bytes: &Expr,
        elem_bytes: &Expr,
        should_reset: &Expr,
    ) -> ShadowMemExprs {
        let in_from = self.in_range(from_obj, from_off, total_bytes);
        let retarget = in_from.clone().and(should_reset.clone());
        let moved_off = self.off.clone().bvadd(to_off.clone().bvsub(from_off.clone()));
        let blessed = self.bless_expr(to_obj, to_off, elem_bytes);
        ShadowMemExprs {
            obj: Expr::ite(retarget.clone(), to_obj.clone(), self.obj.clone()),
            off: Expr::ite(retarget, moved_off, self.off.clone()),
            init: Expr::ite(in_from, self.init.clone(), blessed),
        }
    }
}

/// Recover the compile-time `[bool; N]` layout mask that
/// `mk_layout_operand` materializes as
/// `_n = [const b0, const b1, ...]; call model(ptr, move _n, ...)`.
///
/// Returns `None` when the operand is not a plain move/copy of a local whose
/// unique aggregate definition consists solely of constant bools — callers
/// must fail open (skip the check / bless) in that case.
pub(in crate::codegen_ay) fn layout_mask_from_operand(
    body: &Body,
    operand: &Operand,
) -> Option<Vec<bool>> {
    let place = match operand {
        Operand::Move(place) | Operand::Copy(place) => place,
        Operand::Constant(_) => return None,
    };
    if !place.projection.is_empty() {
        return None;
    }
    layout_mask_from_local(body, place.local)
}

/// Scan `body` for the unique constant-bool aggregate assignment to `local`.
pub(in crate::codegen_ay) fn layout_mask_from_local(
    body: &Body,
    local: usize,
) -> Option<Vec<bool>> {
    let mut found: Option<Vec<bool>> = None;
    for block in body.blocks.iter() {
        for stmt in &block.statements {
            let StatementKind::Assign(place, rvalue) = &stmt.kind else { continue };
            if place.local != local || !place.projection.is_empty() {
                continue;
            }
            let Rvalue::Aggregate(AggregateKind::Array(elem_ty), elems) = rvalue else {
                return None;
            };
            if !matches!(elem_ty.kind(), TyKind::RigidTy(RigidTy::Bool)) {
                return None;
            }
            let mask: Option<Vec<bool>> = elems.iter().map(const_bool_from_operand).collect();
            match (&found, mask) {
                (None, Some(mask)) => found = Some(mask),
                // Multiple assignments (or a non-constant element): ambiguous.
                _ => return None,
            }
        }
    }
    found
}

fn const_bool_from_operand(op: &Operand) -> Option<bool> {
    let Operand::Constant(ConstOperand { const_, .. }) = op else { return None };
    match const_.kind() {
        ConstantKind::Allocated(alloc) => alloc.read_bool().ok(),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_bindings::{ExprValue, Sort};
    use num_bigint::BigInt;

    fn bv(v: u64, w: u32) -> Expr {
        Expr::bitvec_const(v, w)
    }

    fn state(obj: u64, off: u64, init: bool) -> ShadowMemExprs {
        ShadowMemExprs { obj: bv(obj, 32), off: bv(off, 32), init: Expr::bool_const(init) }
    }

    /// Value domain for the closed-expression evaluator below.
    #[derive(Debug, Clone, PartialEq)]
    enum V {
        B(bool),
        Bv(BigInt, u32),
    }

    fn wrap(value: BigInt, width: u32) -> BigInt {
        let modulus = BigInt::from(1) << width;
        ((value % &modulus) + &modulus) % modulus
    }

    /// Minimal big-step evaluator for the closed Bool/BV exprs the shadow
    /// encoding produces. Panics on open terms — tests only use constants.
    fn eval(expr: &Expr) -> V {
        match expr.value() {
            ExprValue::BoolConst(b) => V::B(*b),
            ExprValue::BitVecConst { value, width } => V::Bv(value.clone(), *width),
            ExprValue::Not(e) => match eval(e) {
                V::B(b) => V::B(!b),
                V::Bv(..) => panic!("not on bv"),
            },
            ExprValue::And(es) => V::B(es.iter().all(|e| matches!(eval(e), V::B(true)))),
            ExprValue::Or(es) => V::B(es.iter().any(|e| matches!(eval(e), V::B(true)))),
            ExprValue::Eq(a, b) => V::B(eval(a) == eval(b)),
            ExprValue::Ite { cond, then_expr, else_expr } => match eval(cond) {
                V::B(true) => eval(then_expr),
                V::B(false) => eval(else_expr),
                V::Bv(..) => panic!("ite cond not bool"),
            },
            ExprValue::BvAdd(a, b) => bv_binop(a, b, |x, y| x + y),
            ExprValue::BvSub(a, b) => bv_binop(a, b, |x, y| x - y),
            ExprValue::BvMul(a, b) => bv_binop(a, b, |x, y| x * y),
            ExprValue::BvURem(a, b) => bv_binop(a, b, |x, y| x % y),
            ExprValue::BvULt(a, b) => bv_cmp(a, b, |x, y| x < y),
            ExprValue::BvULe(a, b) => bv_cmp(a, b, |x, y| x <= y),
            other => panic!("evaluator: unsupported node {other:?}"),
        }
    }

    fn bv_binop(a: &Expr, b: &Expr, f: impl Fn(BigInt, BigInt) -> BigInt) -> V {
        match (eval(a), eval(b)) {
            (V::Bv(x, w), V::Bv(y, w2)) => {
                assert_eq!(w, w2, "width mismatch");
                V::Bv(wrap(f(x, y), w), w)
            }
            _ => panic!("bv binop on non-bv"),
        }
    }

    fn bv_cmp(a: &Expr, b: &Expr, f: impl Fn(BigInt, BigInt) -> bool) -> V {
        match (eval(a), eval(b)) {
            (V::Bv(x, w), V::Bv(y, w2)) => {
                assert_eq!(w, w2, "width mismatch");
                V::B(f(x, y))
            }
            _ => panic!("bv cmp on non-bv"),
        }
    }

    fn assert_bool_expr(expr: &Expr, expected: bool) {
        assert_eq!(eval(expr), V::B(expected), "from {expr:?}");
    }

    #[test]
    fn get_tracked_data_byte_returns_shadow_value() {
        // Tracked byte (7, 5), uninit. Read 8 bytes at (7, 0) with all-data mask.
        let s = state(7, 5, false);
        let mask = vec![true; 8];
        let got = s.get_expr(&bv(7, 32), &bv(0, 32), &mask, &bv(8, 32), false);
        assert_bool_expr(&got, false);
    }

    #[test]
    fn get_padding_byte_reads_initialized() {
        // Tracked byte (7, 5) is padding under mask [t,t,t,t,t,f,f,f]? idx 5 = false.
        let s = state(7, 5, false);
        let mask = vec![true, true, true, true, true, false, false, false];
        let got = s.get_expr(&bv(7, 32), &bv(0, 32), &mask, &bv(8, 32), false);
        assert_bool_expr(&got, true);
    }

    #[test]
    fn get_outside_range_reads_initialized() {
        let s = state(7, 100, false);
        let mask = vec![true; 4];
        let got = s.get_expr(&bv(7, 32), &bv(0, 32), &mask, &bv(4, 32), false);
        assert_bool_expr(&got, true);
        // Different object entirely.
        let s2 = state(9, 1, false);
        let got2 = s2.get_expr(&bv(7, 32), &bv(0, 32), &mask, &bv(4, 32), false);
        assert_bool_expr(&got2, true);
    }

    #[test]
    fn set_marks_data_byte_and_padding_byte() {
        // S(u32, u8): mask [t,t,t,t,t,f,f,f], write value=true at (3, 0).
        let mask = vec![true, true, true, true, true, false, false, false];
        // Tracked data byte 2 becomes initialized.
        let s = state(3, 2, false);
        let set =
            s.set_expr(&bv(3, 32), &bv(0, 32), &mask, &bv(8, 32), false, &Expr::bool_const(true));
        assert_bool_expr(&set, true);
        // Tracked padding byte 5 is (re-)marked uninitialized even by a write.
        let s = state(3, 5, true);
        let set =
            s.set_expr(&bv(3, 32), &bv(0, 32), &mask, &bv(8, 32), false, &Expr::bool_const(true));
        assert_bool_expr(&set, false);
        // Untracked range: unchanged.
        let s = state(4, 5, true);
        let set =
            s.set_expr(&bv(3, 32), &bv(0, 32), &mask, &bv(8, 32), false, &Expr::bool_const(true));
        assert_bool_expr(&set, true);
    }

    #[test]
    fn set_deinitializes_with_false_value() {
        let mask = vec![true; 4];
        let s = state(3, 1, true);
        let set =
            s.set_expr(&bv(3, 32), &bv(0, 32), &mask, &bv(4, 32), false, &Expr::bool_const(false));
        assert_bool_expr(&set, false);
    }

    #[test]
    fn slice_mask_wraps_per_element() {
        // 2-byte element mask [t, f], 3 elements => bytes 0,2,4 data; 1,3,5 padding.
        let mask = vec![true, false];
        let total = bv(6, 32);
        let data_byte = state(1, 4, false);
        assert_bool_expr(&data_byte.get_expr(&bv(1, 32), &bv(0, 32), &mask, &total, true), false);
        let padding_byte = state(1, 3, false);
        assert_bool_expr(&padding_byte.get_expr(&bv(1, 32), &bv(0, 32), &mask, &total, true), true);
    }

    #[test]
    fn copy_retargets_or_blesses() {
        // Tracked in source range, should_reset=true: tracking moves to dest,
        // value preserved.
        let s = state(1, 2, false);
        let copied = s.copy_exprs(
            &bv(1, 32),
            &bv(0, 32),
            &bv(2, 32),
            &bv(16, 32),
            &bv(4, 32),
            &bv(4, 32),
            &Expr::bool_const(true),
        );
        assert_bool_expr(&copied.obj.eq(bv(2, 32)), true);
        assert_bool_expr(&copied.off.eq(bv(18, 32)), true);
        assert_bool_expr(&copied.init, false);

        // Tracked in dest range (not source): blessed.
        let s = state(2, 17, false);
        let copied = s.copy_exprs(
            &bv(1, 32),
            &bv(0, 32),
            &bv(2, 32),
            &bv(16, 32),
            &bv(4, 32),
            &bv(4, 32),
            &Expr::bool_const(false),
        );
        assert_bool_expr(&copied.init, true);

        // Tracked elsewhere: untouched.
        let s = state(5, 0, false);
        let copied = s.copy_exprs(
            &bv(1, 32),
            &bv(0, 32),
            &bv(2, 32),
            &bv(16, 32),
            &bv(4, 32),
            &bv(4, 32),
            &Expr::bool_const(false),
        );
        assert_bool_expr(&copied.init, false);
    }

    #[test]
    fn mask_hit_all_true_folds() {
        let idx = Expr::var("i", Sort::bitvec(32));
        assert_eq!(ShadowMemExprs::mask_hit(&idx, &[true, true]), Expr::bool_const(true));
        assert_eq!(ShadowMemExprs::mask_hit(&idx, &[false, false]), Expr::bool_const(false));
    }
}
