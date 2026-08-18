// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Mem-level deref store handler: `*ptr = value` or `(*ptr).field = value`.
//!
//! Part of #905, #1100: handles Deref stores at Mem tracking level.
//! Also updates local array state when the ref points to an array element (#1957).
//!
//! Mirror-store helpers (scalar, datatype, flattened) are in `deref_mem_mirror.rs`.

use ay_bindings::Expr;
use rustc_public::mir::{Place, ProjectionElem};
use tracing::{debug, warn};

use crate::args::ChcTrackLevel;
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::rustc_public_bridge::IndexedVal;

use super::super::ChcCtx;
use super::super::codegen_ctx::CollectionProjectionKind;
use super::super::codegen_ctx::diagnostics::CellCounter;
use super::super::codegen_stmt_store_ref::StmtStoreRef;
use super::super::stmt_accumulator::StmtAccumulator;

/// A ref_target projection field type that represents a heap-pointer indirection
/// (`Box`/`Rc`/`Arc` inner `Unique`/`NonNull`, or a raw pointer). When a
/// ref_target drills through one of these, the pointee lives on the heap behind
/// the pointer — the Reg-level ref_target handler (which only updates a stack
/// local's state var) cannot store to it and drops the write. Such stores must
/// stay on the Mem-level path, which writes the heap object via the pointer.
fn projection_ty_is_heap_pointer(ty: rustc_public::ty::Ty) -> bool {
    use rustc_public::CrateDef;
    use rustc_public::ty::{RigidTy, TyKind};
    match ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(..)) => true,
        TyKind::RigidTy(RigidTy::Adt(def, _)) => {
            matches!(def.trimmed_name().as_str(), "NonNull" | "Unique")
        }
        _ => false,
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Recover a concrete alloc_id by tracing backward through MIR assignments
    /// and identity-like call results.
    ///
    /// Follows statement-only wrappers (ShallowInitBox, tuple/ADT wraps,
    /// Copy/Move/Cast, plain refs) and pointer-identity call results
    /// (NonNull::from, Box::into_raw_with_allocator, etc.) where the output
    /// pointer is the same allocation as the first argument.
    ///
    /// Part of #3589: extended to cross call boundaries for identity calls
    /// so that Rc::new chains (exchange_malloc → Box::into_raw → NonNull::from
    /// → from_inner_in) preserve alloc_id even when blocks are processed out
    /// of execution order.
    pub(in crate::codegen_ay::chc) fn trace_deref_store_alloc_id(
        &self,
        local_idx: usize,
    ) -> Option<u32> {
        let mut current_local = local_idx;
        let mut seen = std::collections::HashSet::from([current_local]);

        for _ in 0..12 {
            if let Some(&obj_id) = self.known_alloc_ids.get(&current_local) {
                return Some(obj_id);
            }

            if let Some(ref_target) = self.ref_resolution.ref_targets.get(&current_local)
                && (ref_target.projections.is_empty()
                    || matches!(ref_target.projections.first(), Some(ProjectionElem::Deref)))
                && seen.insert(ref_target.local)
            {
                current_local = ref_target.local;
                continue;
            }

            // Try statement-level assignment chain first.
            if let Some(next_local) = self.scan_mir_for_alloc_source(current_local) {
                if seen.insert(next_local) {
                    current_local = next_local;
                    continue;
                }
                break;
            }

            // Part of #3589: If no statement assigns this local, check call
            // terminators. For pointer-identity calls (NonNull::from,
            // Box::into_raw, Unique::new_unchecked, etc.), the output
            // allocation is the same as the first argument's. Follow through
            // the first arg to continue the backward chain.
            if let Some(arg_local) = self.scan_identity_call_arg(current_local) {
                if seen.insert(arg_local) {
                    current_local = arg_local;
                    continue;
                }
            }

            break;
        }

        None
    }

    /// Resolve a pointer local to its target stack local, if the pointer
    /// is a reference to a plain local (no projections).
    ///
    /// Returns `Some(local_idx)` when the pointer ultimately targets a stack
    /// local via `ref_targets` or MIR assignment chain. Returns `None` for
    /// heap-allocated targets (Box, Vec backing store, etc.) or projected
    /// references (`&mut x.field`).
    ///
    /// Part of #3932: used by ptr::write local writeback to synchronize
    /// the state variable with the heap after a pointer write.
    pub(in crate::codegen_ay::chc) fn resolve_ptr_write_target_local(
        &self,
        ptr_local: usize,
    ) -> Option<usize> {
        // Follow ref_targets for the immediate case: _ptr = &mut _local
        if let Some(ref_target) = self.ref_resolution.ref_targets.get(&ptr_local) {
            if ref_target.projections.is_empty() {
                let target = ref_target.local;
                // Verify the target is a real local (has a state variable)
                if self.try_state_idx_for_local(target).is_some() {
                    return Some(target);
                }
            }
            return None;
        }
        // Follow MIR assignment chain for Cast/Use wrappers: _ptr2 = _ptr1 as *mut T
        if let Some(src_local) = self.scan_mir_for_alloc_source(ptr_local) {
            return self.resolve_ptr_write_target_local(src_local);
        }
        None
    }

    /// If `target_local` is the destination of an identity-like call, return
    /// the first argument's local (the allocation source).
    fn scan_identity_call_arg(&self, target_local: usize) -> Option<usize> {
        use rustc_public::mir::{Operand, TerminatorKind};

        for bb_data in &self.body.blocks {
            if let TerminatorKind::Call { destination, func, args, .. } = &bb_data.terminator.kind {
                if destination.local != target_local {
                    continue;
                }
                let callee = self.resolve_callee_path(func)?;
                if !Self::is_alloc_identity_callee(&callee) {
                    continue;
                }
                // Return the first argument's local.
                return args.first().and_then(|arg| match arg {
                    Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
                    _ => None,
                });
            }
        }
        None
    }

    /// Check whether a callee path represents a pointer-identity operation
    /// where the output allocation is the same as the first argument.
    fn is_alloc_identity_callee(path: &str) -> bool {
        // NonNull::from (From trait impl)
        (path.contains("NonNull") && path.contains("From") && path.contains("from"))
        // Box/Rc/Arc into_raw family.
        || path.contains("into_raw_with_allocator")
        || (path.ends_with("::into_raw")
            && (path.contains("boxed::Box")
                || path.contains("rc::Rc")
                || path.contains("sync::Arc")))
        // ptr::with_metadata_of preserves the data pointer allocation while
        // replacing metadata for dyn/slice raw pointers.
        || path.contains("with_metadata_of")
        // Raw pointer add/sub preserves allocation identity while changing the
        // in-object offset. Rc::from_raw uses `sub` to recover RcInner.
        || ((path.ends_with("::add") || path.ends_with("::sub"))
            && (path.contains("const_ptr") || path.contains("mut_ptr")))
        // Unique::new_unchecked
        || path.contains("Unique") && path.contains("new_unchecked")
        // NonNull::new / new_unchecked (inherent methods)
        || path.contains("NonNull") && (path.ends_with("new_unchecked") || path.ends_with("::new"))
    }

    /// Structural test for the ADDRESS-used-as-VALUE defect: would a deref
    /// load through `ptr_local` inherit the alloc_id of its own referent slot?
    ///
    /// A load `_d = copy (*_p)` reads the CONTENTS of the object `_p` points
    /// at. When `_p` provably holds `&_L` — the address of stack local `_L`'s
    /// own slot, with no projections — and the alloc_id recorded for `_p` is
    /// exactly that slot's obj_id, then `_d` holds the VALUE stored in `_L`,
    /// not an address into `_L`'s allocation. Propagating `_p`'s alloc_id to
    /// `_d` makes every later deref of `_d` resolve back to `_L`'s own slot,
    /// so the encoding reads a memory cell no rule ever writes at that type —
    /// a free variable, which makes the surrounding assertion refutable
    /// (`&[1,2,3][..]`: `head == &slice[0]` reported as a Genuine CTREX).
    ///
    /// Returns `Some(_L)` for exactly that shape; `None` for every other deref
    /// load — through a cast, through a projected reference (`&(*_p).field`),
    /// through a pointer carrying a heap alloc_id, or through a
    /// multiply-assigned local — which keeps the existing inheritance
    /// behaviour that Box/Rc/NonNull deref chains depend on. Callers use `_L`'s
    /// own recorded alloc_id — the allocation `_L`'s VALUE points into — in
    /// place of `_L`'s slot id.
    pub(in crate::codegen_ay::chc) fn deref_load_referent_local(
        &self,
        ptr_local: usize,
    ) -> Option<usize> {
        let &obj_id = self.known_alloc_ids.get(&ptr_local)?;
        let slot_local = self.heap_state.local_idx_for_obj_id(obj_id)?;
        if !self.ptr_provably_addresses_local(ptr_local, slot_local) {
            return None;
        }
        debug!(
            ptr_local,
            obj_id,
            slot_local,
            "GUARD4262_FIRED: deref load through a pointer to its own referent slot"
        );
        Some(slot_local)
    }

    /// Bounded backward walk answering "does `ptr_local` provably hold
    /// `&_target` with no projections?".
    ///
    /// Follows only unprojected `Use(Copy|Move)` wrappers, so it never crosses
    /// a load, a cast, an offset, or a field projection, and it requires every
    /// local on the chain to be written exactly once so the answer is
    /// path-independent. Any other shape answers `false`.
    fn ptr_provably_addresses_local(&self, ptr_local: usize, target: usize) -> bool {
        use rustc_public::mir::{Operand, Rvalue, StatementKind};

        let mut current = ptr_local;
        for _ in 0..8 {
            let mut def: Option<&Rvalue> = None;
            let mut assign_count = 0usize;
            for bb_data in &self.body.blocks {
                for stmt in &bb_data.statements {
                    if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                        && lhs.local == current
                    {
                        assign_count += 1;
                        if lhs.projection.is_empty() {
                            def = Some(rhs);
                        }
                    }
                }
            }
            // More than one writer (branch merge, reassignment, or a projected
            // write into the same local) makes the provenance path-dependent.
            if assign_count != 1 {
                return false;
            }
            match def {
                Some(Rvalue::Use(Operand::Copy(p) | Operand::Move(p)))
                    if p.projection.is_empty() =>
                {
                    current = p.local;
                }
                Some(Rvalue::Ref(_, _, p) | Rvalue::AddressOf(_, p)) => {
                    return p.projection.is_empty() && p.local == target;
                }
                _ => return false,
            }
        }
        false
    }

    /// Scan all MIR blocks for the assignment that defines `target_local`,
    /// returning the source local that may carry an alloc_id.
    fn scan_mir_for_alloc_source(&self, target_local: usize) -> Option<usize> {
        use rustc_public::mir::{BinOp, Operand, Rvalue, StatementKind};

        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                    && lhs.local == target_local
                {
                    let result = match rhs {
                        // Same ADDRESS-used-as-VALUE shape that
                        // `propagate_alloc_ids_for_assign` refuses to inherit:
                        // when the pointer names the referent's own slot, the
                        // backward hop must land on the referent `_L`, whose
                        // recorded alloc_id describes the loaded VALUE. Hopping
                        // to the pointer local instead picks the slot's own
                        // obj_id straight back up.
                        Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                            if matches!(src.projection.first(), Some(ProjectionElem::Deref)) =>
                        {
                            Some(self.deref_load_referent_local(src.local).unwrap_or(src.local))
                        }
                        Rvalue::ShallowInitBox(Operand::Copy(src) | Operand::Move(src), _)
                        | Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                        | Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _) => {
                            Some(src.local)
                        }
                        Rvalue::CopyForDeref(src) => Some(src.local),
                        Rvalue::BinaryOp(
                            BinOp::Offset,
                            Operand::Copy(src) | Operand::Move(src),
                            _,
                        )
                        | Rvalue::CheckedBinaryOp(
                            BinOp::Offset,
                            Operand::Copy(src) | Operand::Move(src),
                            _,
                        ) => Some(src.local),
                        Rvalue::Aggregate(_, operands) => self.pick_alloc_operand(operands),
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)
                            if place.projection.is_empty()
                                || matches!(
                                    place.projection.first(),
                                    Some(ProjectionElem::Deref)
                                ) =>
                        {
                            Some(place.local)
                        }
                        _ => None,
                    };
                    if result.is_some() {
                        return result;
                    }
                }
            }
        }
        None
    }

    /// Pick the best operand from an Aggregate that may carry an alloc_id.
    /// Prefers operands with known alloc_ids or ref_targets; falls back to
    /// the first operand with no projection.
    fn pick_alloc_operand(&self, operands: &[rustc_public::mir::Operand]) -> Option<usize> {
        use rustc_public::mir::Operand;
        operands
            .iter()
            .find_map(|op| match op {
                Operand::Copy(src) | Operand::Move(src)
                    if self.known_alloc_ids.contains_key(&src.local)
                        || self.ref_resolution.ref_targets.contains_key(&src.local) =>
                {
                    Some(src.local)
                }
                _ => None,
            })
            .or_else(|| {
                operands.iter().find_map(|op| match op {
                    Operand::Copy(src) | Operand::Move(src) if src.projection.is_empty() => {
                        Some(src.local)
                    }
                    _ => None,
                })
            })
    }

    /// Handles Deref store at Mem level: `*ptr = value` or `(*ptr).field = value`.
    ///
    /// Also updates local array state when the ref points to an array element (#1957).
    ///
    /// Returns `true` if the store was handled (caller should `continue`).
    pub(in crate::codegen_ay::chc) fn handle_deref_store_mem_level(
        &mut self,
        lhs: &Place,
        rhs_expr: &Expr,
        local_idx: usize,
        bb_idx: usize,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        // Only applies at Mem level with Deref as first projection
        if self.track_level < ChcTrackLevel::Mem
            || lhs.projection.is_empty()
            || !matches!(lhs.projection[0], ProjectionElem::Deref)
        {
            return false;
        }
        // Part of #428: Defer to Reg-level handler for known static pointers.
        // Static mut state variables are modeled as CHC state vars, not as
        // memory addresses. The Reg-level handler (handle_deref_store_via_ref_targets)
        // uses static_ref_to_state_idx to constrain the output state variable directly.
        if self.ref_resolution.static_ref_to_state_idx.contains_key(&local_idx) {
            return false;
        }

        // Part of #3348: Handle deref store through IndexMut-returned &mut T BEFORE
        // the generic memory store. At Mem level, this handler runs first and would
        // write to the typed memory array (e.g., mem_bool), but Vec reads come from
        // the abstract fld_data array. Without this check, fld_data is never updated,
        // causing Genuine CTREX on write-then-read patterns like `v[idx] = true;
        // assert!(v[idx])`. Delegate to handle_collection_mut_ref_store which
        // emits `data' = store(data, idx, val)` on the Vec's backing array.
        if lhs.projection.len() == 1 {
            if let Some(cmr) = self.ref_resolution.collection_mut_refs.get(&local_idx).cloned() {
                return self.handle_collection_mut_ref_store(rhs_expr.clone(), &cmr, acc);
            }
        }

        // Defer to Reg-level handler when ref_targets maps this local to a
        // known state variable. The Mem handler would write to the typed heap
        // array at the pointer's address, but the Reg handler writes directly
        // to the target local's state variable. For MIR-inlined FnMut closure
        // captures (e.g., *_28 = value where _28 = &mut sum), the Reg handler
        // correctly resolves through the closure env to the captured variable.
        //
        // Exception: offset pointers from ptr.add (subslice_offset is set) must
        // NOT defer to Reg-level. The Reg handler ignores the byte offset and
        // writes to the target local's state variable as a whole, while the Mem
        // handler uses the computed address (base + offset * sizeof(T)) to write
        // to the correct position in the type-indexed memory array. Without this
        // guard, `*vec.as_mut_ptr().add(5) = 0x42` writes to the Vec's state
        // variable instead of mem_u8[addr+5], and a subsequent Mem-level read
        // `*vec.as_ptr().add(5)` returns an unconstrained value because mem_u8
        // was never written. This mirrors the read-side guard in
        // try_resolve_deref_via_ref_targets (codegen_expr_deref_field.rs).
        if let Some(ref_target) = self.ref_resolution.ref_targets.get(&local_idx) {
            let has_state = self.try_state_idx_for_local(ref_target.local).is_some();
            let proj_1 = lhs.projection.len() == 1;
            let has_offset = self.ref_resolution.subslice_offset.contains_key(&local_idx);
            // Do NOT defer to the Reg-level handler when the ref_target drills
            // through a heap-pointer wrapper (e.g. `Box::as_mut` registers
            // `_r -> box.[Field(Unique), Field(NonNull)]`). The stored value lives
            // on the heap behind that NonNull; the Reg-level handler can only
            // update the Box's stack state var, so it mis-applies the store to the
            // pointer field and DROPS it — a fail-open over-approximation that
            // turns `*Box::as_mut(b) = v` into a spurious memory-safety CTREX
            // (the contract-modifies FP cluster). Keep it on the Mem-level store
            // path below, which writes the heap object via the pointer value.
            let drills_heap_pointer = ref_target.projections.iter().any(
                |p| matches!(p, ProjectionElem::Field(_, ty) if projection_ty_is_heap_pointer(*ty)),
            );
            if has_state && proj_1 && !has_offset && !drills_heap_pointer {
                return false; // defer to handle_deref_store_via_ref_targets
            }
        }

        // Get pointer type and pointee type
        let local_ty = self.body.locals()[local_idx].ty;
        let pointee_ty = if let Some(pointee_ty) = ChcCtx::deref_pointee_ty(local_ty) {
            pointee_ty
        } else {
            warn!(?lhs, "CHC: dropped Deref store — non-pointer type (Part of #2236)");
            self.diagnostics.store_dropped_transition.inc();
            return true; // handled (skip)
        };
        let projected_store_ty =
            lhs.projection[1..].iter().fold(pointee_ty, |current, proj| match proj {
                ProjectionElem::Field(_, field_ty) => *field_ty,
                _ => current,
            });

        // Get pointer expression (address) using expr env or OUTPUT for modified locals
        // Fix #2055: Check local_expr_env first
        // Fix #2238: Use local_to_state_idx mapping for correct vector index
        let Some(ptr_vec_idx) = self.try_state_idx_for_local(local_idx) else {
            warn!(
                ?local_idx,
                "CHC: dropped Deref store — missing local_to_state_idx mapping (Part of #2236)"
            );
            self.diagnostics.store_dropped_transition.inc();
            self.overapproximate_memory_store_target(projected_store_ty, None);
            return true;
        };
        let ptr_expr = if acc.modified.contains(&local_idx) {
            if let Some(env_expr) = self.encode.local_expr_env.get(&local_idx) {
                env_expr.clone()
            } else {
                let Some((out_name, out_sort)) =
                    self.state_var_mgr.output_state_vars.get(ptr_vec_idx)
                else {
                    warn!(
                        ?local_idx,
                        "CHC: dropped Deref store — missing output state var (Part of #2236)"
                    );
                    self.diagnostics.store_dropped_transition.inc();
                    self.overapproximate_memory_store_target(projected_store_ty, None);
                    return true;
                };
                Expr::var(&**out_name, out_sort.clone())
            }
        } else {
            let Some((in_name, in_sort)) = self.state_var_mgr.state_vars.get(ptr_vec_idx) else {
                warn!(
                    ?local_idx,
                    "CHC: dropped Deref store — missing input state var (Part of #2236)"
                );
                self.diagnostics.store_dropped_transition.inc();
                self.overapproximate_memory_store_target(projected_store_ty, None);
                return true;
            };
            Expr::var(&**in_name, in_sort.clone())
        };

        // Part of #3589: Resolve known allocation address for store-to-load symmetry.
        // When the pointer local has a known_alloc_ids entry, replace the symbolic
        // state variable with the constant allocation address. This mirrors the load
        // side (translate_place_with_deref line ~208) which uses alloc_ids to resolve
        // Deref loads to constant addresses. Without this, inlined Rc::new stores
        // through a reference at a symbolic address that doesn't match the constant
        // load address, breaking store-to-load forwarding.
        let trace_result = self.trace_deref_store_alloc_id(local_idx);
        let ptr_expr = if let Some(obj_id) = trace_result {
            Expr::bitvec_const(obj_id as i128, 32).concat(Expr::bitvec_const(0, 32))
        } else {
            ptr_expr
        };

        // Compute address with field offset if there are projections after Deref
        // Part of #1100: (*ptr).field = value stores at ptr + field_offset
        // Also track the final field type for the memory store (not the struct type)
        let (addr_expr, store_ty) = if lhs.projection.len() > 1 {
            let mut total_offset: u64 = 0;
            let mut current_ty = pointee_ty;
            let mut drop_store_ty = projected_store_ty;
            let mut all_fields = true;
            // Part of #3041: Track active variant for Downcast→Field projection chains.
            // When Downcast sets the variant, the next Field projection uses
            // variant-specific offsets from VariantsShape::Multiple.
            let mut active_variant: Option<usize> = None;

            for proj in &lhs.projection[1..] {
                match proj {
                    ProjectionElem::Field(field_idx, field_ty) => {
                        drop_store_ty = *field_ty;
                        // Part of #3041: Use variant-specific field offsets when
                        // a Downcast preceded this Field projection.
                        let offset = if let Some(vi) = active_variant.take() {
                            self.get_variant_field_offset(current_ty, vi, *field_idx)
                        } else {
                            self.get_field_offset(current_ty, *field_idx)
                        };
                        if let Some(offset) = offset {
                            total_offset += offset;
                            current_ty = *field_ty;
                        } else {
                            debug!("CHC: cannot compute field offset for field {}", *field_idx);
                            all_fields = false;
                            break;
                        }
                    }
                    ProjectionElem::Downcast(variant_idx) => {
                        // Downcast selects enum variant — address doesn't change
                        // but subsequent Field offsets must use variant-specific layout.
                        // Part of #3041: Category B fix.
                        active_variant = Some(variant_idx.to_index());
                        debug!(
                            "CHC: Downcast to variant {} for deref store",
                            variant_idx.to_index()
                        );
                    }
                    ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => {
                        // Part of #3041: Defer to Reg-level handler.
                        debug!(
                            ?proj,
                            "CHC: deferring Deref+Index store to Reg-level handler (#3041)"
                        );
                        return false;
                    }
                    _ => {
                        // external enum: ProjectionElem
                        debug!("CHC: unsupported projection after Deref: {:?}", proj);
                        all_fields = false;
                        break;
                    }
                }
            }

            if !all_fields {
                // Cannot compute complete offset — store dropped.
                // Sound (over-approximation): value becomes unconstrained.
                warn!(
                    ?lhs,
                    "CHC: dropped Deref+field store — cannot compute field offset (Part of #2236)"
                );
                self.diagnostics.store_dropped_transition.inc();
                self.overapproximate_memory_store_target(drop_store_ty, None);
                return true;
            }

            // Part of #2875: Coerce Int-lifted pointers to BV before arithmetic.
            let ptr_expr =
                if ptr_expr.sort().is_int() { ptr_expr.int2bv(POINTER_WIDTH) } else { ptr_expr };
            // Part of #2007: Guard against non-bitvec pointer sorts.
            // BigInt locals have Int sort and should not reach pointer
            // arithmetic, but if they do, skip the store (sound).
            if !ptr_expr.sort().is_bitvec() {
                warn!(
                    ?lhs,
                    "CHC: dropped Deref+field store — ptr_expr is not bitvec (Part of #2236)"
                );
                self.diagnostics.store_dropped_transition.inc();
                self.overapproximate_memory_store_target(drop_store_ty, None);
                return true;
            }
            let addr = if total_offset > 0 {
                ptr_expr.bvadd(Expr::bitvec_const(total_offset as i64, POINTER_WIDTH))
            } else {
                ptr_expr
            };
            // Use the final field type, not the original pointee struct type
            (addr, current_ty)
        } else {
            (ptr_expr, pointee_ty)
        };

        // Part of #2876: If the RHS is a reconstructed Datatype from a flattened
        // local, ensure the sort is declared before decomposition or store uses it.
        if rhs_expr.sort().is_datatype() {
            self.declare_datatype_sort_if_needed(rhs_expr.sort());
        }

        // OI2 (#2876): Detect stores to unmodeled VecIntoIter internal fields
        // and skip Mem-level memory store + heap-safety checks. The mirror handler
        // (OI1) emits deterministic out==in constraints for these paths instead.
        let skip_memory_store = self.is_unmodeled_into_iter_field_store(lhs, local_idx);

        // Offset-deref stack-provenance keystone: strict access bound for a
        // walk-resolved stack pointer (mirrors the read-side emission in
        // `codegen_expr_deref_projection`). `heap_access_checks` inside
        // `build_memory_store` fail-opens when the address's obj_id lane is an
        // opaque SSA variable; this closes the OOB-write hole for
        // offset-derived stack pointers (`*arr.as_mut_ptr().add(len) = v`).
        if !skip_memory_store {
            let checks = self.provenance_deref_bound_checks(&addr_expr, store_ty, local_idx);
            self.heap_state.pending_checks.extend(checks);
        }

        if !skip_memory_store {
            // Bug 3a (#1739): Try per-field decomposition first for struct stores.
            // The Datatype guard in build_memory_store replaces struct values with
            // lossy bitvec fallback. Decomposing into per-field stores at base+offset
            // bypasses the guard because each field has a primitive sort.
            let decomposed =
                self.try_decompose_struct_store(&addr_expr, rhs_expr, store_ty, acc.constraints);
            if !decomposed {
                // Not a decomposable struct — use standard memory store path
                if let Some(store_constraint) =
                    self.build_memory_store_untyped(addr_expr.clone(), rhs_expr.clone(), store_ty)
                {
                    acc.constraints.push(store_constraint);
                    if lhs.projection.len() > 1 {
                        debug!(?local_idx, "CHC: emitted Deref+field store constraint at offset");
                    } else {
                        debug!(?local_idx, "CHC: emitted Deref store constraint for *ptr = value");
                    }
                }

                // Part of #3095: Mirror array elements to flat element-type memory.
                // When `*ptr = [T; N]`, the whole-array store writes to `mem_arr_T`
                // (2D array keyed by array type), but element-wise reads (e.g., in
                // `vec![]` → `into_vec` → Vec iterator) load from `mem_T` (1D array
                // keyed by element type). Without this bridge, those reads return
                // unconstrained values, causing spurious CTREX in Vec iterator tests.
                self.mirror_array_elements_to_flat_memory(
                    &rhs_expr,
                    store_ty,
                    &addr_expr,
                    acc.constraints,
                );
            }
        }

        // Part of #1957: Also update the local array when writing through a ref.
        // When ref points to arr[idx], we must update both:
        // 1. Memory (done above via build_memory_store)
        // 2. Local array state (so reads of arr[idx] see the new value)
        //
        // Exception: offset pointers from ptr.add (subslice_offset is set) must
        // skip the register mirror and array update. The offset pointer writes to
        // a specific byte position within the allocation, not the whole target
        // local. Mirroring would overwrite the target local's state variable
        // (e.g., Vec's fld_ptr) with the stored value (e.g., 0x42), corrupting
        // the Vec's pointer field. The memory store above already placed the
        // value at the correct address in the type-indexed array.
        let has_offset = self.ref_resolution.subslice_offset.contains_key(&local_idx);
        if !has_offset {
            if let Some(ref_target) = self.ref_resolution.ref_targets.get(&local_idx).cloned() {
                let has_array_index = ref_target.projections.iter().any(|p| {
                    matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. })
                });

                // Part of #2278: Mem-level *ref stores must mirror into register state for
                // scalar/field ref targets so subsequent deref reads via ref_targets don't
                // observe stale __in values.
                if !has_array_index {
                    self.mirror_scalar_ref_store(
                        &ref_target,
                        lhs,
                        rhs_expr,
                        local_idx,
                        store_ty,
                        acc,
                    );
                }

                self.emit_ref_target_array_update(&ref_target, rhs_expr, local_idx, bb_idx, acc);
            }
        }
        if self.ref_resolution.ref_arg_pointee_idx.contains_key(&local_idx) {
            let _ = self.handle_deref_store_via_ref_targets(lhs, rhs_expr.clone(), local_idx, acc);
        }
        true
    }

    /// OI2 (#2876): Detect whether a deref store targets an unmodeled VecIntoIter
    /// internal field (e.g. `end: *const T`, field_idx >= modeled field count).
    ///
    /// When true, the caller should skip `build_memory_store` and its associated
    /// heap-safety checks. The mirror handler (OI1) emits deterministic `out == in`
    /// constraints for the projected slots instead.
    fn is_unmodeled_into_iter_field_store(&self, lhs: &Place, local_idx: usize) -> bool {
        // Resolve the ref target for this pointer local.
        let ref_target = match self.ref_resolution.ref_targets.get(&local_idx) {
            Some(rt) => rt,
            None => return false,
        };
        let target_local = ref_target.local;

        // Check if the target is a VecIntoIter projected local.
        if self.collections.projection_locals.get(&target_local).copied()
            != Some(CollectionProjectionKind::VecIntoIter)
        {
            return false;
        }

        // Check if the target is flattened.
        if !self.flatten.flattened_tuple_locals.contains(&target_local) {
            return false;
        }
        let field_count = self.flattened_field_count(target_local);

        // Collect the final field index from the combined projection chain:
        // ref_target projections + lhs projections after Deref.
        let lhs_field_idx = lhs.projection[1..].iter().rev().find_map(|p| match p {
            ProjectionElem::Field(idx, _) => Some(*idx),
            _ => None, // external enum: ProjectionElem
        });
        let ref_field_idx = ref_target.projections.iter().rev().find_map(|p| match p {
            ProjectionElem::Field(idx, _) => Some(*idx),
            _ => None, // external enum: ProjectionElem
        });

        // The final field index is the deepest (last) field projection in the chain.
        let final_field_idx = lhs_field_idx.or(ref_field_idx);
        match final_field_idx {
            Some(idx) if idx >= field_count => {
                debug!(
                    target_local,
                    ref_local = local_idx,
                    field_idx = idx,
                    field_count,
                    "CHC: OI2 — skipping Mem-level store for unmodeled VecIntoIter field"
                );
                true
            }
            _ => false, // non-enum: Option<FieldIdx> with guard
        }
    }
}

#[cfg(test)]
mod tests {
    use super::ChcCtx;

    #[test]
    fn alloc_identity_callee_recognizes_box_into_raw_family() {
        assert!(ChcCtx::<'_, '_>::is_alloc_identity_callee("alloc::boxed::Box::<u32>::into_raw",));
        assert!(ChcCtx::<'_, '_>::is_alloc_identity_callee("alloc::rc::Rc::<u32>::into_raw",));
        assert!(ChcCtx::<'_, '_>::is_alloc_identity_callee("alloc::sync::Arc::<u32>::into_raw",));
        assert!(ChcCtx::<'_, '_>::is_alloc_identity_callee(
            "alloc::boxed::Box::<u32>::into_raw_with_allocator",
        ));
    }
}
