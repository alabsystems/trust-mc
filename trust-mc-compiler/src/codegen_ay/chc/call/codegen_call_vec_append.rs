// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Vec append transfers the current source elements and clears its length.

use super::{ChcCtx, call_accumulator::CallAccumulator};
use crate::codegen_ay::shared::vec_capacity::VecGrowth;
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::Expr;
use rustc_public::mir::Operand;
use std::collections::HashSet;

impl ChcCtx<'_, '_> {
    pub(in crate::codegen_ay::chc) fn vec_op_append(
        &mut self,
        args: &[Operand],
        modified: &HashSet<usize>,
        receiver: Option<usize>,
        acc: &mut CallAccumulator<'_>,
    ) -> Option<Expr> {
        let Some(dst) = receiver else {
            self.record_sound_fallback_reason("vec_append_no_self_local");
            return None;
        };
        if !self.resolve_collection_field_projections(args).is_empty()
            || args.first().is_some_and(|arg| match arg {
                Operand::Copy(place) | Operand::Move(place) => !place.projection.is_empty(),
                _ => true,
            })
        {
            self.record_sound_fallback_reason("vec_append_projected_receiver_unmodelled");
            self.havoc_unresolved_append_fields(&[dst], acc);
            return None;
        }
        let src = args.get(1).and_then(|arg| {
            let (Operand::Copy(place) | Operand::Move(place)) = arg else { return None };
            if !place.projection.is_empty() {
                return None;
            }
            let target = self.ref_resolution.ref_targets.get(&place.local);
            match target {
                Some(target) if target.projections.is_empty() => Some(target.local),
                Some(_) => None,
                None => Some(place.local),
            }
        });
        let Some(src) = src.filter(|src| *src != dst) else {
            self.record_sound_fallback_reason("vec_append_source_unresolved");
            self.havoc_unresolved_append_fields(&[dst], acc);
            return None;
        };
        // Read both complete pre-states before writing either post-state. The
        // source may have changed since construction; literal caches are not
        // evidence for the values append moves.
        let fields = self.read_vec_fields(dst, modified).zip(self.read_vec_fields(src, modified));
        let Some(((ptr, len, cap, data), (_, src_len, _, src_data))) = fields else {
            self.record_sound_fallback_reason("vec_append_fields_unresolved");
            self.havoc_unresolved_append_fields(&[dst, src], acc);
            return None;
        };
        let new_len = len.clone().bvadd(src_len);
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        let Ok(data) =
            data.try_array_range_copy(src_data, len.clone(), new_len.clone(), zero.clone())
        else {
            self.record_sound_fallback_reason("vec_append_data_sort_unresolved");
            self.havoc_unresolved_append_fields(&[dst, src], acc);
            return None;
        };
        let new_cap = self.vec_reserved_cap(
            Some(self.body.locals()[dst].ty),
            &cap,
            &new_len,
            VecGrowth::Amortized,
            acc.constraints,
        );
        let Some(elem_size) = self.vec_capacity_elem_size(self.body.locals()[dst].ty) else {
            self.record_sound_fallback_reason("vec_append_element_layout_unresolved");
            self.havoc_unresolved_append_fields(&[dst, src], acc);
            return None;
        };
        // Capacity overflow is a checked panic, never an assumed precondition.
        let mut no_panic = new_len.clone().bvuge(len);
        if elem_size != 0 {
            no_panic = no_panic.and(
                new_cap
                    .clone()
                    .bvule(Expr::bitvec_const((i64::MAX as u64) / elem_size, POINTER_WIDTH)),
            );
        }
        acc.constraints.push(no_panic.clone());
        let ptr = self.allocate_vec_backing_on_zero_cap_growth(
            ptr,
            &cap,
            &new_cap,
            Some(self.body.locals()[dst].ty),
            acc.constraints,
        );
        if !self.write_vec_fields(
            dst,
            modified,
            |_, _, _, _| (ptr, new_len.clone(), new_cap.clone(), data),
            acc,
        ) || !self.write_vec_fields(
            src,
            modified,
            |ptr, _, cap, data| (ptr, zero.clone(), cap, data),
            acc,
        ) {
            self.record_sound_fallback_reason("vec_append_fields_unwritten");
        }
        if let Some(name) = self.collections.len_state.get_len_var(dst).cloned() {
            self.collection_len_set(&name, new_len, acc);
        }
        if let Some(name) = self.collections.len_state.get_cap_var(dst).cloned() {
            self.collection_cap_set(&name, new_cap, acc);
        }
        if let Some(name) = self.collections.len_state.get_len_var(src).cloned() {
            self.collection_len_set(&name, zero, acc);
        }
        Some(no_panic)
    }

    fn havoc_unresolved_append_fields(&mut self, locals: &[usize], acc: &mut CallAccumulator<'_>) {
        for &local in locals {
            acc.dests.push(local);
            if let Some(name) = self.collections.len_state.get_len_var(local).cloned() {
                self.mark_collection_len_modified(&name);
            }
            if let Some(name) = self.collections.len_state.get_cap_var(local).cloned() {
                self.mark_collection_cap_modified(&name);
            }
        }
    }
}
