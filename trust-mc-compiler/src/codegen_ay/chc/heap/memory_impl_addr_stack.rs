// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Constant split-pointer extraction and stack-address provenance.

use ay_bindings::{Expr, ExprValue};
use tracing::debug;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Tries to extract a constant obj_id from a 64-bit address expression.
    ///
    /// Addresses are encoded as `(obj_id : bv32).concat(offset : bv32)` per the
    /// split-pointer model. This method attempts to extract the obj_id if it's
    /// a compile-time constant, enabling region array lookup.
    pub(in crate::codegen_ay::chc) fn try_extract_obj_id(addr: &Expr) -> Option<u32> {
        Self::try_extract_constant_addr(addr).map(|(obj_id, _)| obj_id)
    }

    /// Extract an allocation base, never an interior pointer's object alone.
    ///
    /// `known_alloc_ids` and whole-owner ref targets imply offset zero when
    /// read back as an address. Region/bounds queries must keep using
    /// `try_extract_obj_id`, which intentionally accepts interior addresses.
    pub(in crate::codegen_ay::chc) fn try_extract_base_obj_id(addr: &Expr) -> Option<u32> {
        Self::try_extract_constant_addr(addr)
            .filter(|(_, offset)| *offset == 0)
            .map(|(obj_id, _)| obj_id)
    }

    /// The concrete stack address recorded for `local_idx`, when that record
    /// holds on every path.
    ///
    /// The table is keyed by local, not by path. A local that more than one
    /// statement or call assigns (`let r = if b { &m } else { &n };`) keeps
    /// whichever producer was translated LAST, and that address is wrong on
    /// every path through another producer. Read through it, `*r` was `n` on
    /// the path where `r = &m`, and `--ay-chc` proved `assert!(*r == 2)` there
    /// (tools/soundness-duals/negative/joined_pointer_last_producer.rs). Such a
    /// local answers `None`, so its readers fall back to the local's own
    /// path-sensitive state.
    pub(in crate::codegen_ay::chc) fn known_stack_addr_expr(
        &self,
        local_idx: usize,
    ) -> Option<Expr> {
        // `known_stack_addr_exprs` is keyed by local and written in block encoding
        // order. For a local with more than one whole-local producer it names the
        // producer encoded LAST, not the address on the current path: after
        // `let p = if c { &mut b } else { &mut a }` the store `*p = 1` went to one
        // arm's constant object on both paths, and the modifies-frame check compared
        // that one address (negative/modifies_frame_residual.rs::merge_*). Refuse it;
        // every caller then takes its path-precise state-variable lane.
        if self.local_has_multiple_whole_definitions(local_idx) {
            debug!(
                local_idx,
                "CHC: stack address provenance ignored: the local has several producers"
            );
            return None;
        }
        self.known_stack_addr_exprs.get(&local_idx).cloned()
    }

    pub(in crate::codegen_ay::chc) fn record_known_stack_addr_expr(
        &mut self,
        local_idx: usize,
        addr: Expr,
        source: &'static str,
    ) -> bool {
        let Some((obj_id, offset)) = Self::try_extract_constant_addr(&addr) else {
            self.known_stack_addr_exprs.remove(&local_idx);
            return false;
        };
        if self.heap_state.local_idx_for_obj_id(obj_id).is_none() {
            self.known_stack_addr_exprs.remove(&local_idx);
            return false;
        }
        let canonical_addr =
            Expr::bitvec_const(obj_id as i128, 32).concat(Expr::bitvec_const(offset as i128, 32));

        debug!(
            local_idx,
            obj_id, offset, source, "CHC: recorded concrete stack address provenance"
        );
        self.known_stack_addr_exprs.insert(local_idx, canonical_addr);
        true
    }

    /// Extracts both obj_id and offset from a constant split-pointer address.
    pub(in crate::codegen_ay::chc) fn try_extract_constant_addr(addr: &Expr) -> Option<(u32, u32)> {
        if addr.sort().bitvec_width() != Some(64) {
            return None;
        }
        if let ExprValue::BvConcat(high, low) = addr.value()
            && high.sort().bitvec_width() == Some(32)
            && low.sort().bitvec_width() == Some(32)
        {
            let obj_id = match high.value() {
                ExprValue::BitVecConst { value, width: 32 } => value
                    .to_u32_digits()
                    .1
                    .first()
                    .copied()
                    .or_else(|| (value.sign() == num_bigint::Sign::NoSign).then_some(0)),
                _ => None,
            }?;
            let offset = match low.value() {
                ExprValue::BitVecConst { value, width: 32 } => value
                    .to_u32_digits()
                    .1
                    .first()
                    .copied()
                    .or_else(|| (value.sign() == num_bigint::Sign::NoSign).then_some(0)),
                _ => None,
            }?;
            return Some((obj_id, offset));
        }
        if let ExprValue::BitVecConst { value, width: 64 } = addr.value() {
            return Some(Self::split_u64_addr(
                value.to_u64_digits().1.first().copied().unwrap_or(0),
            ));
        }
        if let Some(folded) = trust_mc_core::chc_const_prop::eval::try_eval_to_const(addr)
            && let ExprValue::BitVecConst { value, width: 64 } = folded.value()
        {
            return Some(Self::split_u64_addr(
                value.to_u64_digits().1.first().copied().unwrap_or(0),
            ));
        }
        None
    }

    fn split_u64_addr(full: u64) -> (u32, u32) {
        ((full >> 32) as u32, full as u32)
    }
}
