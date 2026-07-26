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

    pub(in crate::codegen_ay::chc) fn known_stack_addr_expr(
        &self,
        local_idx: usize,
    ) -> Option<Expr> {
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
