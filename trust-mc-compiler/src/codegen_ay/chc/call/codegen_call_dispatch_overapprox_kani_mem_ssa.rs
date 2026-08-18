// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SSA-level resolution helpers for `kani::mem` validity predicates.
//!
//! Part of #3930: Resolves pointer arguments to their MIR-level source locals,
//! then extracts field values from SSA state variables (flattened or datatype)
//! for validity predicate evaluation. This bypasses symbolic pointer
//! decomposition which fails on state variables that carry `addr_of!` results.
//!
//! Extracted from `codegen_call_dispatch_overapprox_kani_mem.rs` for file-size limit.

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::{Operand, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Part of #3930: Resolve pointer address to the stack-local index it targets.
    ///
    /// When the address is `concat(obj_id, 0)` where obj_id maps to a known
    /// stack local, return the local index. Returns None for non-stack or
    /// non-zero-offset pointers (e.g. symbolic state variables).
    pub(in crate::codegen_ay::chc) fn try_resolve_addr_to_local(
        &self,
        addr: &Expr,
    ) -> Option<usize> {
        let (obj_id, offset) = self.split_pointer(addr)?;
        let const_obj_id = Self::const_obj_id_u32(&obj_id)?;
        let local_idx = self.heap_state.local_idx_for_obj_id(const_obj_id)?;
        let const_offset = Self::const_obj_id_u32(&offset)?;
        if const_offset != 0 {
            return None;
        }
        debug!(local_idx, "kani_mem: resolved addr to stack local (#3930)");
        Some(local_idx)
    }

    /// Part of #3930: Resolve a kani_mem pointer argument to its MIR-level
    /// source local by tracing `AddressOf`/`Ref` assignments.
    ///
    /// When the pointer arg is `Copy(_N)` or `Move(_N)` and the MIR has
    /// `_N = &raw const _M` (with no projection), returns `Some(M)`.
    /// This works even when `_N`'s runtime value is a symbolic state variable
    /// that `split_pointer` cannot decompose.
    pub(in crate::codegen_ay::chc) fn try_resolve_mir_ptr_to_local(
        &self,
        args: &[rustc_public::mir::Operand],
    ) -> Option<usize> {
        let ptr_arg = args.first()?;
        let ptr_local = match ptr_arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => return None,
        };
        // Part of #3958: Collect ALL matching source locals for the pointer
        // local. Return Some only when the candidate set is uniquely one local.
        // Multiple different source locals → ambiguous → fall back to None.
        let mut candidate: Option<usize> = None;
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                    && lhs.projection.is_empty()
                    && lhs.local == ptr_local
                {
                    match rhs {
                        Rvalue::AddressOf(_, place) | Rvalue::Ref(_, _, place)
                            if place.projection.is_empty() =>
                        {
                            match candidate {
                                None => candidate = Some(place.local),
                                Some(prev) if prev != place.local => {
                                    debug!(
                                        ptr_local,
                                        prev,
                                        conflicting = place.local,
                                        "kani_mem: ambiguous ptr — multiple source locals (#3958)"
                                    );
                                    return None;
                                }
                                Some(_) => {} // same local, deduplicated
                            }
                        }
                        _ => {
                            // Non-AddressOf/Ref assignment to the pointer local
                            // (e.g. `_p = move _tmp`, `_p = fn_call()`). We
                            // cannot trace through these, so the source is
                            // ambiguous.
                            debug!(
                                ptr_local,
                                "kani_mem: non-addressof assignment to ptr local, \
                                 cannot resolve (#3958)"
                            );
                            return None;
                        }
                    }
                }
            }
        }
        if let Some(target) = candidate {
            debug!(
                ptr_local,
                target_local = target,
                "kani_mem: MIR ptr traces to unique local (#3930)"
            );
        }
        candidate
    }

    /// Part of #3930: Get a field's SSA expression from a stack-local.
    ///
    /// Handles both datatype locals (single state var with field accessors)
    /// and flattened locals (one state var per field). When the local was
    /// modified in the current block, uses OUTPUT state vars to capture the
    /// assigned value (INPUT vars carry the prior block's unconstrained value).
    pub(in crate::codegen_ay::chc) fn try_resolve_ssa_field(
        &self,
        local_idx: usize,
        field_idx: usize,
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<Expr> {
        let vec_idx = self.try_state_idx_for_local(local_idx)?;
        let use_output = modified_locals.contains(&local_idx);

        // Case 1: flattened local — each field is a separate state var
        if self.flatten.flattened_tuple_locals.contains(&local_idx) {
            let field_count =
                self.flatten.flattened_local_field_count.get(&local_idx).copied().unwrap_or(0);
            if field_idx >= field_count {
                return None;
            }
            let slot = vec_idx + field_idx;
            let (var_name, var_sort) = if use_output {
                self.state_var_mgr.output_state_vars.get(slot)?
            } else {
                self.state_var_mgr.state_vars.get(slot)?
            };
            debug!(
                local_idx,
                field_idx,
                slot,
                use_output,
                "kani_mem validity: resolved flattened SSA field (Part of #3930)"
            );
            return Some(Expr::var(&**var_name, var_sort.clone()));
        }

        // Case 2: datatype local — single state var with field accessors
        let (var_name, var_sort) = if use_output {
            self.state_var_mgr.output_state_vars.get(vec_idx)?
        } else {
            self.state_var_mgr.state_vars.get(vec_idx)?
        };
        if !var_sort.is_datatype() {
            return None;
        }
        // A CHC state variable IS the local's current contents, so it is a value
        // (it is the local's datum even when that datum is a pointer bit-pattern;
        // the local's *address* would be a `Loc`, and is not what is wanted here).
        let root_expr =
            crate::codegen_ay::provenance::Val::of_value(Expr::var(&**var_name, var_sort.clone()));
        Self::datatype_field_select(&root_expr, field_idx, None)
            .map(crate::codegen_ay::provenance::Val::into_expr)
    }

    /// Part of #3930: Compute validity predicate for a field extracted from SSA.
    ///
    /// Unlike the memory-based path, the field value is already an SSA expression
    /// connected to kani::any() constraints. Apply the appropriate validity
    /// predicate directly.
    pub(in crate::codegen_ay::chc) fn compute_ssa_field_validity(
        &self,
        field_expr: Expr,
        field_ty: rustc_public::ty::Ty,
    ) -> (Expr, bool) {
        match field_ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => match Self::bool_validity_predicate(field_expr) {
                Some(p) => (p, false),
                None => (Expr::bool_const(true), true),
            },
            TyKind::RigidTy(RigidTy::Char) => match Self::char_validity_predicate(field_expr) {
                Some(p) => (p, false),
                None => (Expr::bool_const(true), true),
            },
            // VALVALID_ARRAY_NONZERO_KANIMEM: a NonZero<T> field is valid iff its
            // loaded value is non-zero. Without this the arm below would treat
            // the field as an unconditionally-valid scalar, silently admitting
            // the zero bit-pattern.
            TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "NonZero" => {
                match Self::nonzero_validity_predicate(field_expr) {
                    Some(p) => (p, false),
                    None => (Expr::bool_const(true), true),
                }
            }
            // All other scalar types are unconditionally valid
            _ => (Expr::bool_const(true), false),
        }
    }
}
