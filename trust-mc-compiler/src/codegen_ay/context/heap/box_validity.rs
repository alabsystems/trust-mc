// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native allocation facts for checked BMC Box casts. Node identity preserves
//! pointer production: an unrelated integer with identical bits is not a root.

use super::super::AYCtx;
use ay_bindings::{Expr, ExprValue};

#[derive(Clone, Debug)]
pub(in crate::codegen_ay) struct BoxAllocation {
    pub(in crate::codegen_ay) pointer: Expr,
    pub(in crate::codegen_ay) size: u64,
    pub(in crate::codegen_ay) align: u64,
    pub(in crate::codegen_ay) alive: Option<Expr>,
}

#[derive(Clone, Copy, Debug)]
pub(in crate::codegen_ay) enum BoxPointerOrigin {
    Allocation(usize),
    Numeric,
}

fn node(expression: &Expr) -> usize {
    std::ptr::from_ref(expression.value()) as usize
}

impl AYCtx<'_, '_> {
    pub(super) fn guard_native_box_numeric_invalidation(&mut self, pointer: &Expr) {
        if self.heap_state.box_allocations.is_empty() {
            return;
        }
        let object = |value: &Expr| match value.value() {
            ExprValue::BitVecConst { value, width: 64 } => {
                let (sign, digits) = value.to_u64_digits();
                (sign != num_bigint::Sign::Minus && digits.len() <= 1)
                    .then(|| digits.first().copied().unwrap_or(0) / super::HEAP_STRIDE)
            }
            _ => None,
        };
        let candidate = object(pointer);
        if candidate.is_none()
            || self.heap_state.box_allocations.iter().any(|allocation| {
                object(&allocation.pointer).is_none_or(|known| Some(known) == candidate)
            })
        {
            self.unsupported_with_fallback("BoxNumericProvenanceInvalidation",
                "numeric pointer invalidation could alias synthetic native allocation IDs; it is not an actual free");
        }
    }
    /// A positive custody fact, not an assumption that unobserved ownership
    /// changes are UB. Ambiguous/path-conditional transfers withdraw it.
    pub(in crate::codegen_ay) fn release_native_box(
        &mut self,
        pointer: &Expr,
        guard: Option<Expr>,
    ) {
        if guard.as_ref().is_some_and(|g| !matches!(g.value(), ExprValue::BoolConst(true))) {
            self.heap_state.released_box_allocations.clear();
        } else if let Some(BoxPointerOrigin::Allocation(index)) = self.box_pointer_origin(pointer) {
            self.heap_state.released_box_allocations.insert(index);
        }
    }
    pub(in crate::codegen_ay) fn claim_released_native_box(
        &mut self,
        index: usize,
        guard: Option<Expr>,
    ) -> bool {
        if guard.as_ref().is_some_and(|g| !matches!(g.value(), ExprValue::BoolConst(true))) {
            self.heap_state.released_box_allocations.clear();
            return false;
        }
        self.heap_state.released_box_allocations.remove(&index)
    }
    pub(in crate::codegen_ay) fn has_native_box_allocations(&self) -> bool {
        !self.heap_state.box_allocations.is_empty()
    }
    pub(in crate::codegen_ay) fn record_native_box_allocation(
        &mut self,
        pointer: Expr,
        size: u64,
        align: u64,
        guard: Option<Expr>,
    ) {
        self.heap_state.box_allocations.push(BoxAllocation {
            pointer,
            size,
            align,
            alive: Some(guard.unwrap_or_else(|| Expr::bool_const(true))),
        });
    }

    pub(in crate::codegen_ay) fn record_box_numeric_address(&mut self, pointer: Expr) {
        self.heap_state.box_numeric_addresses.push(pointer);
    }

    pub(in crate::codegen_ay) fn record_erased_box_address(&mut self, value: Expr) {
        self.heap_state.box_erased_addresses.push(value);
    }

    pub(in crate::codegen_ay) fn is_erased_box_address(&self, value: &Expr) -> bool {
        self.heap_state.box_erased_addresses.iter().any(|known| {
            node(known) == node(value)
                || matches!((known.value(), value.value()),
                (ExprValue::Var { name: a }, ExprValue::Var { name: b }) if a == b)
        })
    }

    pub(in crate::codegen_ay) fn box_pointer_origin(
        &self,
        pointer: &Expr,
    ) -> Option<BoxPointerOrigin> {
        let id = node(pointer);
        if let Some(index) = self
            .heap_state
            .box_allocations
            .iter()
            .position(|allocation| node(&allocation.pointer) == id)
        {
            return Some(BoxPointerOrigin::Allocation(index));
        }
        self.heap_state
            .box_numeric_addresses
            .iter()
            .any(|known| node(known) == id)
            .then_some(BoxPointerOrigin::Numeric)
    }

    pub(in crate::codegen_ay) fn native_box_allocation(
        &self,
        index: usize,
    ) -> Option<&BoxAllocation> {
        self.heap_state.box_allocations.get(index)
    }

    /// The pointer has already been resolved through exact SSA definitions by
    /// the statement caller. Unknown provenance withdraws authority instead of
    /// manufacturing a definite use-after-free counterexample.
    pub(in crate::codegen_ay) fn native_box_deallocation_event(
        &mut self,
        pointer: &Expr,
        guard: Option<Expr>,
    ) {
        if self.heap_state.box_allocations.is_empty() {
            return;
        }
        // The native snapshot and the ordinary heap arrays use the same
        // execution guard. An off-path free changes neither metadata lane.
        let mut pending = vec![(pointer, Expr::bool_const(true), 0usize)];
        let mut events = Vec::new();
        let mut budget = 4096usize;
        while let Some((value, branch, depth)) = pending.pop() {
            let Some(left) = budget.checked_sub(1) else {
                events.clear();
                break;
            };
            budget = left;
            if depth > 64 {
                events.clear();
                break;
            }
            match self.box_pointer_origin(value) {
                Some(BoxPointerOrigin::Allocation(index)) => events.push((index, branch)),
                Some(BoxPointerOrigin::Numeric) => {
                    events.clear();
                    break;
                }
                None => match value.value() {
                    // Address arithmetic cannot identify which actual object
                    // a free affects. In particular A+(B-A) must not keep B
                    // live merely because the outer expression starts with A.
                    // Exact producer roots and their conditional selections are
                    // the only supported deallocation origins here.
                    ExprValue::Ite { cond: condition, then_expr, else_expr } => {
                        pending.push((then_expr, branch.clone().and(condition.clone()), depth + 1));
                        pending.push((else_expr, branch.and(condition.clone().not()), depth + 1));
                    }
                    _ => {
                        events.clear();
                        break;
                    }
                },
            }
        }
        if events.is_empty() {
            self.unsupported_with_fallback(
                "BoxDeallocationOrigin",
                "unknown deallocation provenance withdraws native allocation authority",
            );
            for allocation in &mut self.heap_state.box_allocations {
                allocation.alive = None;
            }
            return;
        }
        let guard = guard.unwrap_or_else(|| Expr::bool_const(true));
        for (index, branch) in events {
            let allocation = &mut self.heap_state.box_allocations[index];
            if matches!(guard.value(), ExprValue::BoolConst(true))
                && matches!(branch.value(), ExprValue::BoolConst(true))
                && node(pointer) == node(&allocation.pointer)
            {
                allocation.alive = Some(Expr::bool_const(false));
                continue;
            }
            if let Some(alive) = allocation.alive.take() {
                let freed =
                    guard.clone().and(branch).and(pointer.clone().eq(allocation.pointer.clone()));
                allocation.alive = Some(alive.and(freed.not()));
            }
        }
    }
}
