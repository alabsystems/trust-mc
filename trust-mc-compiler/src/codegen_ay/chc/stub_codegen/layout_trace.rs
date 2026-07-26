// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Layout tracing helpers: extract concrete (size, align) from MIR operands.
// Extracted from stubs_alloc_heap_ops.rs per #3254 (500 LOC decomposition).
use super::ChcCtx;
use rustc_public::mir::Operand;
use std::collections::HashSet;
use tracing::debug;
impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Trace a call argument through MIR assignments to find a Layout source local,
    /// returning the full `(size, align)` pair from `known_layout_sizes`.
    ///
    /// Part of #3273, #3641: After MIR inlining, `alloc_zeroed(layout)` becomes
    /// `__rust_alloc_zeroed(layout.size(), layout.align())`. The size argument is
    /// a local assigned from a field projection of the Layout local (e.g.,
    /// `_8 = (_5).0` where `_5` is the Layout). The Layout local IS in
    /// `known_layout_sizes` but the size local is not. This method scans MIR
    /// statements to trace the argument back to its Layout source.
    pub(in crate::codegen_ay::chc) fn trace_arg_to_layout_pair(
        &self,
        arg: &Operand,
    ) -> Option<(u64, u64)> {
        use rustc_public::mir::{Rvalue, StatementKind};

        let mut current_local = match arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                // Direct lookup: the operand's local itself may be in the cache.
                if let Some(&pair) = self.known_layout_sizes.get(&place.local) {
                    return Some(pair);
                }
                // Layout method calls take `&Layout`; MIR commonly materializes
                // `_ref = &_layout` immediately before calling `Layout::size` or
                // `padding_needed_for`. Follow ref_targets so the concrete
                // LayoutNew/LayoutForValueRaw cache on the pointee is still used.
                if let Some(ref_target) = self.ref_resolution.ref_targets.get(&place.local)
                    && ref_target.projections.is_empty()
                    && let Some(&pair) = self.known_layout_sizes.get(&ref_target.local)
                {
                    debug!(
                        ref_local = place.local,
                        layout_local = ref_target.local,
                        size = pair.0,
                        align = pair.1,
                        "trace_arg_to_layout_pair: resolved layout through reference target"
                    );
                    return Some(pair);
                }
                place.local
            }
            Operand::Copy(place) | Operand::Move(place) => {
                // Check if the base local is in the cache even though there's a projection
                if let Some(&pair) = self.known_layout_sizes.get(&place.local) {
                    return Some(pair);
                }
                return None;
            }
            _ => return None,
        };

        let mut visited = HashSet::from([current_local]);
        for _ in 0..12 {
            let mut next_local = None;
            'search: for bb_data in &self.body.blocks {
                for stmt in &bb_data.statements {
                    if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                        && lhs.local == current_local
                    {
                        match rhs {
                            Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) => {
                                if let Some(&pair) = self.known_layout_sizes.get(&src.local) {
                                    return Some(pair);
                                }
                                // Part of #3841: Follow through variant projections.
                                // Pattern: _L = Move((_R as variant#0).0: Layout)
                                // When the source has a Downcast+Field projection into
                                // a Result<Layout, LayoutError>, trace to the Result
                                // local and look for its Aggregate construction.
                                if !src.projection.is_empty() {
                                    if let Some(pair) =
                                        self.extract_layout_from_result_local(src.local)
                                    {
                                        return Some(pair);
                                    }
                                    if !visited.contains(&src.local) {
                                        next_local = Some(src.local);
                                        break 'search;
                                    }
                                } else {
                                    next_local = Some(src.local);
                                    break 'search;
                                }
                            }
                            // Part of #3841: Constant assignment — extract layout from
                            // MIR constant allocation bytes.
                            Rvalue::Use(Operand::Constant(c)) => {
                                if let Some(pair) = Self::extract_layout_from_mir_const(&c.const_) {
                                    return Some(pair);
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            let next_local = next_local?;
            if !visited.insert(next_local) {
                return None;
            }
            current_local = next_local;
        }
        None
    }

    /// Part of #3841: Extract a concrete `(size, align)` from a Result<Layout, LayoutError>
    /// local by scanning the MIR for Aggregate constructions of the Ok variant.
    ///
    /// When `Layout::from_size_align(CONST, CONST)` is inlined by rustc, the MIR
    /// contains:
    /// ```text
    /// _R = Aggregate(Result::Ok, layout_val)   // in the Ok branch
    /// _L = Move((_R as variant#0).0)           // unwrap
    /// ```
    /// The LayoutFromSizeAlign stub never fires (because the call is inlined),
    /// so `known_layout_sizes` stays empty. This method scans the MIR for the
    /// Aggregate that defines the Result local's Ok variant and extracts the
    /// concrete Layout payload by translating its operands.
    fn extract_layout_from_result_local(&self, result_local: usize) -> Option<(u64, u64)> {
        use rustc_public::mir::{Rvalue, StatementKind};
        let best_layout: Option<(u64, u64)> = None;
        for (bb_idx, bb_data) in self.body.blocks.iter().enumerate() {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                    && lhs.local == result_local
                    && lhs.projection.is_empty()
                {
                    match rhs {
                        // Aggregate construction: Result::Ok(layout) or similar
                        Rvalue::Aggregate(_, operands) => {
                            for op in operands {
                                if let Some(pair) = self.try_extract_layout_pair_from_operand(op) {
                                    debug!(
                                        size = pair.0,
                                        align = pair.1,
                                        bb_idx,
                                        result_local,
                                        "extract_layout_from_result_local: found layout in Aggregate"
                                    );
                                    // Return the FIRST Layout-sized pair found
                                    // (Result::Ok branch, not Err).
                                    return Some(pair);
                                }
                            }
                        }
                        // Copy/Move chain — follow to the source
                        Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                            if src.projection.is_empty() =>
                        {
                            if let Some(pair) = self.extract_layout_from_result_local(src.local) {
                                return Some(pair);
                            }
                        }
                        // Part of #3841: Also follow through projected sources.
                        // Pattern: _R = Move((_S as variant#0).0)
                        Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                            if !src.projection.is_empty() =>
                        {
                            if let Some(pair) = self.extract_layout_from_result_local(src.local) {
                                return Some(pair);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        best_layout
    }

    /// Part of #3841: Try to extract a concrete `(size, align)` from a MIR operand
    /// that represents a `Layout` value. Handles:
    /// - Constant operands with 16-byte allocations (packed BV128)
    /// - Move/Copy of a local that has a known layout in the cache
    /// - Move/Copy of a local whose defining assignment is a BV128 concat
    fn try_extract_layout_pair_from_operand(&self, op: &Operand) -> Option<(u64, u64)> {
        use rustc_public::mir::{Rvalue, StatementKind};
        match op {
            Operand::Constant(c) => Self::extract_layout_from_mir_const(&c.const_),
            Operand::Copy(place) | Operand::Move(place) => {
                // Check cache first
                if let Some(&pair) = self.known_layout_sizes.get(&place.local) {
                    return Some(pair);
                }
                // Scan MIR for the defining assignment of this local
                let target = place.local;
                for bb_data in &self.body.blocks {
                    for stmt in &bb_data.statements {
                        if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                            && lhs.local == target
                            && lhs.projection.is_empty()
                        {
                            match rhs {
                                Rvalue::Use(Operand::Constant(c)) => {
                                    if let Some(pair) =
                                        Self::extract_layout_from_mir_const(&c.const_)
                                    {
                                        return Some(pair);
                                    }
                                }
                                // Aggregate(Layout, [size_op, align_op]) — the Layout
                                // struct constructor itself
                                Rvalue::Aggregate(_, fields) if fields.len() >= 2 => {
                                    let size = self.try_extract_usize_from_operand(&fields[0]);
                                    let align = self.try_extract_usize_from_operand(&fields[1]);
                                    if let (Some(s), Some(a)) = (size, align) {
                                        return Some((s, a));
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                }
                None
            }
        }
    }

    /// Part of #3841: Extract a usize constant from a MIR operand.
    /// Follows through single-field Aggregate constructions (e.g.,
    /// `Alignment(NonZeroUsize(usize))`) to find the inner constant.
    fn try_extract_usize_from_operand(&self, op: &Operand) -> Option<u64> {
        use rustc_public::mir::{Rvalue, StatementKind};
        match op {
            Operand::Constant(c) => Self::extract_usize_from_mir_const(&c.const_),
            Operand::Copy(place) | Operand::Move(place) => {
                let target = place.local;
                for bb_data in &self.body.blocks {
                    for stmt in &bb_data.statements {
                        if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                            && lhs.local == target
                            && lhs.projection.is_empty()
                        {
                            match rhs {
                                Rvalue::Use(Operand::Constant(c)) => {
                                    if let Some(v) = Self::extract_usize_from_mir_const(&c.const_) {
                                        return Some(v);
                                    }
                                }
                                // Follow single-field Aggregate wrappers:
                                // Alignment(NonZeroUsize(val)) or NonZeroUsize(val)
                                Rvalue::Aggregate(_, fields) if fields.len() == 1 => {
                                    if let Some(v) = self.try_extract_usize_from_operand(&fields[0])
                                    {
                                        return Some(v);
                                    }
                                }
                                // Follow Move/Copy chains
                                Rvalue::Use(inner_op @ (Operand::Copy(_) | Operand::Move(_))) => {
                                    if let Some(v) = self.try_extract_usize_from_operand(inner_op) {
                                        return Some(v);
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                }
                None
            }
        }
    }

    /// Part of #3841: Extract a `(size, align)` pair from a 16-byte MIR constant
    /// allocation representing a packed BV128 Layout value.
    fn extract_layout_from_mir_const(c: &rustc_public::ty::MirConst) -> Option<(u64, u64)> {
        use rustc_public::ty::ConstantKind;
        let alloc = match c.kind() {
            ConstantKind::Allocated(alloc) => alloc,
            _ => return None,
        };
        let bytes = &alloc.bytes;
        if bytes.len() == 16 {
            // Layout is packed as (size: u64, align: u64) in little-endian
            let size_bytes: [u8; 8] =
                bytes[0..8].iter().map(|b| b.unwrap_or(0)).collect::<Vec<u8>>().try_into().ok()?;
            let align_bytes: [u8; 8] =
                bytes[8..16].iter().map(|b| b.unwrap_or(0)).collect::<Vec<u8>>().try_into().ok()?;
            let size = u64::from_le_bytes(size_bytes);
            let align = u64::from_le_bytes(align_bytes);
            if align > 0 && align.is_power_of_two() && size > 0 {
                return Some((size, align));
            }
        }
        None
    }

    /// Part of #3841: Extract a usize value from a MIR constant.
    fn extract_usize_from_mir_const(c: &rustc_public::ty::MirConst) -> Option<u64> {
        // Fast path: eval_target_usize handles both Allocated and Ty const kinds
        c.eval_target_usize().ok()
    }

    /// Trace a call argument to a Layout source and return just the size component.
    /// Delegates to `trace_arg_to_layout_pair`.
    pub(crate) fn trace_arg_to_layout_size(&self, arg: &Operand) -> Option<usize> {
        self.trace_arg_to_layout_pair(arg).map(|(size, _)| size as usize)
    }

    /// Trace a pointer argument through MIR assignments to find a known alloc ID.
    ///
    /// Part of #3273: When `realloc` receives a pointer that was returned by a
    /// previous `alloc` call, the CHC encoding cannot extract a concrete obj_id
    /// from the symbolic pointer variable. This method traces the pointer operand
    /// back through MIR Copy/Move/Cast assignments (up to 5 hops) to find the
    /// original alloc result local in `known_alloc_ids`.
    pub(crate) fn trace_arg_to_alloc_id(&self, arg: &Operand) -> Option<u32> {
        use rustc_public::mir::{Rvalue, StatementKind};

        let mut current_local = match arg {
            Operand::Copy(place) | Operand::Move(place) => place.local,
            _ => return None,
        };

        // Check direct match first.
        if let Some(&obj_id) = self.known_alloc_ids.get(&current_local) {
            return Some(obj_id);
        }

        // Trace through up to 5 Copy/Move/Cast hops.
        for _ in 0..5 {
            let mut found_source = None;
            'scan: for bb_data in &self.body.blocks {
                for stmt in &bb_data.statements {
                    if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                        && lhs.local == current_local
                    {
                        match rhs {
                            Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                            | Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _) => {
                                found_source = Some(src.local);
                                break 'scan;
                            }
                            _ => {}
                        }
                    }
                }
            }
            let Some(src_local) = found_source else { break };
            if let Some(&obj_id) = self.known_alloc_ids.get(&src_local) {
                return Some(obj_id);
            }
            current_local = src_local;
        }
        None
    }
}
