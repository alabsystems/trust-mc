// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Initialization evidence crosses a CFG edge; values cross through memory
//! SSA. No expression naming the write block's inputs is reused in another
//! block, and later stores cannot retroactively rewrite an earlier read.

use super::codegen_types::CodegenTypes;
use super::{ChcCtx, native_init_custody::scalar};
use crate::codegen_ay::chc::codegen_ctx::ExactVar;
use ay_bindings::{Expr, Sort};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use std::collections::HashSet;

impl ChcCtx<'_, '_> {
    pub(super) fn native_init_event_dominates(&self, event: usize, target: usize) -> bool {
        if event == target {
            return true;
        }
        let mut pending = vec![0];
        let mut seen = HashSet::new();
        let mut hit_event = false;
        let mut budget = 16_384usize;
        while let Some(site) = pending.pop() {
            let Some(left) = budget.checked_sub(1) else {
                return false;
            };
            budget = left;
            if site == event {
                hit_event = true;
                continue;
            }
            if site == target {
                return false;
            }
            if seen.insert(site) {
                let Some(block) = self.body.blocks.get(site) else {
                    return false;
                };
                pending.extend(block.terminator.successors());
            }
        }
        hit_event
    }
    pub(super) fn native_initialized_array_data(
        &mut self,
        payload: Ty,
        address: &Expr,
    ) -> Option<Expr> {
        let TyKind::RigidTy(RigidTy::Array(element, n)) = payload.kind() else {
            return None;
        };
        let n = n.eval_target_usize().ok()?;
        if n == 0 || n > 64 || !scalar(element) {
            return None;
        }
        let width = u64::try_from(self.get_type_size(element)?).ok()?;
        let sort = Self::translate_ty(element)?;
        if width == 0 || self.elem_sort_for_memory_array(element) != sort {
            return None;
        }
        let key = self.type_key_for_body_ty(element).into_owned();
        // Only 0..len are initialized/observable here. Do not guess the other
        // cells: later safe growth must write them before increasing len.
        let mut data = ExactVar::unobserved(
            crate::codegen_ay::chc::chc_fresh_name("__native_init_vec_tail"),
            Sort::array(Sort::bitvec(64), sort.clone()),
        );
        for i in 0..n {
            let offset = i.checked_mul(width)?;
            let addr = if offset == 0 {
                address.clone()
            } else {
                address.clone().bvadd(Expr::bitvec_const(offset, 64))
            };
            let value = self.load_from_type_array(addr, &key, sort.clone(), Some(&sort))?;
            if super::native_drop_memory::has_output_or_binder(&value) {
                return None;
            }
            data = data.store(Expr::bitvec_const(i, 64), value);
        }
        Some(data)
    }
}
