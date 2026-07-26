// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Precise `kani::mem` predicate helpers for CHC overapprox dispatch.
//!
//! Keeps the main dispatch module under the file-size guard while localizing the
//! packed-value validity encoding added for Part of #3470.

use ay_bindings::{Expr, ExprValue};

use super::{ChcCtx, dyn_coercion};
use crate::args::ChcTrackLevel;
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};
use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use tracing::{debug, warn};

/// VALVALID_ARRAY_NONZERO_KANIMEM: upper bound on the number of array elements
/// whose per-element validity predicate is unrolled into a conjunction for
/// `can_dereference`/`can_write` on `*const [T; N]`. Arrays larger than this
/// over-approximate soundly (return `true` with the overapprox flag set) rather
/// than emitting an intractably large formula.
const KANI_MEM_ARRAY_VALIDITY_MAX: u64 = 256;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Returns the precise pointer-alignment predicate when the pointee type and
    /// pointer operand are translatable. Falls back to `true` with overapprox
    /// metadata when layout/translation support is missing.
    pub(in crate::codegen_ay::chc) fn compute_ptr_alignment_check(
        &mut self,
        func: &rustc_public::mir::Operand,
        args: &[rustc_public::mir::Operand],
        modified_locals: &std::collections::HashSet<usize>,
    ) -> (Expr, bool) {
        let Some((ptr_expr, pointee_ty)) =
            self.translate_kani_mem_ptr_arg(func, args, modified_locals)
        else {
            debug!("kani_mem alignment: cannot translate ptr arg, falling back to true");
            return (Expr::bool_const(true), true);
        };
        // Part of #4014: When the pointer operand is from a local that was
        // never assigned in the function body, the kani_mem check produces
        // spurious CTREX because the solver picks non-aligned values for the
        // unconstrained state variable. This occurs with Rc/Arc internals
        // where the inline walker bails on intermediate pointer locals.
        if self.is_unassigned_ptr_operand(args) {
            debug!("kani_mem alignment: unassigned pointer local, over-approximating");
            return (Expr::bool_const(true), true);
        }
        // Part of #4172: call-only assigned pointer with non-constant obj_id.
        // Part of #4249: exempt pointers from known allocation stubs — those
        // have concrete obj_ids assigned by allocation codegen.
        if self.is_call_only_assigned_ptr_operand(args)
            && !self.is_call_assigned_by_known_alloc_only(args)
        {
            if let Some((obj_id, _)) = self.split_pointer(&ptr_expr) {
                if Self::const_obj_id_u32(&obj_id).is_none() {
                    debug!("kani_mem alignment: call-only untraceable pointer, over-approximating");
                    return (Expr::bool_const(true), true);
                }
            }
        }
        let Some(alignment_expr) = self.compute_alignment_predicate(ptr_expr, pointee_ty) else {
            debug!(?pointee_ty, "kani_mem alignment: no layout info, falling back to true");
            return (Expr::bool_const(true), true);
        };
        (alignment_expr, false)
    }

    pub(in crate::codegen_ay::chc) fn compute_kani_mem_predicate(
        &mut self,
        func: &rustc_public::mir::Operand,
        args: &[rustc_public::mir::Operand],
        modified_locals: &std::collections::HashSet<usize>,
        require_alignment: bool,
    ) -> (Expr, bool) {
        let Some((ptr_expr, pointee_ty)) =
            self.translate_kani_mem_ptr_arg(func, args, modified_locals)
        else {
            debug!("kani_mem predicate: cannot translate ptr arg, falling back to true");
            return (Expr::bool_const(true), true);
        };

        // Part of #4014: When the pointer operand is from a local that was
        // never assigned in the function body, the kani_mem predicate produces
        // spurious CTREX. Over-approximate to true.
        if self.is_unassigned_ptr_operand(args) {
            debug!("kani_mem predicate: unassigned pointer local, over-approximating");
            return (Expr::bool_const(true), true);
        }

        // Part of #4172: When the pointer operand is assigned only by Call
        // terminators (not by Assign statements like &raw const or Ref), and
        // its obj_id is non-constant after split_pointer, the pointer is
        // untraceable — likely from an inline walker bail-out on Rc/Arc
        // internals. Over-approximate to avoid spurious CTREX from alignment
        // and bounds checks on unconstrained solver-chosen addresses.
        //
        // Pointers from Assign statements (field projections, addr_of) are
        // constrained even when obj_id is non-constant, because the base
        // address is a constrained state variable.
        //
        // Part of #4249: exempt pointers from known allocation stubs — those
        // have concrete obj_ids assigned by allocation codegen.
        if self.is_call_only_assigned_ptr_operand(args)
            && !self.is_call_assigned_by_known_alloc_only(args)
        {
            if let Some((obj_id, _)) = self.split_pointer(&ptr_expr) {
                if Self::const_obj_id_u32(&obj_id).is_none() {
                    debug!(
                        "kani_mem predicate: call-only assigned local with non-constant obj_id, \
                         untraceable pointer, over-approximating"
                    );
                    return (Expr::bool_const(true), true);
                }
            }
        }

        // Part of #3930: Resolve the MIR-level pointer source before it becomes
        // a symbolic state variable. When the pointer arg is `Copy(_N)` and
        // `_N = &raw const _M`, the target local `_M` is known statically.
        let mir_target_local = self.try_resolve_mir_ptr_to_local(args);

        let (access_predicate, access_overapprox) =
            self.compute_kani_mem_access_predicate(ptr_expr.clone(), pointee_ty, require_alignment);
        let (validity_predicate, validity_overapprox) = self
            .compute_kani_mem_valid_value_predicate_with_hint(
                ptr_expr,
                pointee_ty,
                modified_locals,
                mir_target_local,
            );

        (access_predicate.and(validity_predicate), access_overapprox || validity_overapprox)
    }

    fn translate_kani_mem_ptr_arg(
        &mut self,
        func: &rustc_public::mir::Operand,
        args: &[rustc_public::mir::Operand],
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<(Expr, rustc_public::ty::Ty)> {
        let ptr_arg = args.first()?;
        let operand_pointee_ty = match ptr_arg.ty(self.body.locals()).ok()?.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _))
            | TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => pointee,
            other => {
                debug!(?other, "kani_mem pointer arg is not a pointer/reference");
                return None;
            }
        };
        let pointee_ty = self.extract_kani_mem_pointee_ty(func).unwrap_or(operand_pointee_ty);

        let ptr_expr = self.translate_operand_with_modified(ptr_arg, modified_locals)?;
        let ptr_expr = Self::normalize_kani_mem_pointer_expr(ptr_expr)?;
        Some((ptr_expr, pointee_ty))
    }

    fn normalize_kani_mem_pointer_expr(expr: Expr) -> Option<Expr> {
        let ptr_expr = dyn_coercion::extract_pointer_expr(&expr).unwrap_or(expr);
        let ptr_expr =
            if ptr_expr.sort().is_int() { ptr_expr.int2bv(POINTER_WIDTH) } else { ptr_expr };
        let ptr_expr = coerce_bitvec_width_safe(ptr_expr, POINTER_WIDTH, SignExtension::ZeroExtend);
        (ptr_expr.sort().bitvec_width() == Some(POINTER_WIDTH)).then_some(ptr_expr)
    }

    fn extract_kani_mem_pointee_ty(
        &self,
        func: &rustc_public::mir::Operand,
    ) -> Option<rustc_public::ty::Ty> {
        let func_ty = func.ty(self.body.locals()).ok()?;
        let fn_args = match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(_, fn_args)) => fn_args,
            other => {
                debug!(?other, "kani_mem callee is not an FnDef");
                return None;
            }
        };
        fn_args.0.iter().find_map(|arg| match arg {
            GenericArgKind::Type(ty) => Some(*ty),
            _ => None,
        })
    }

    fn compute_kani_mem_access_predicate(
        &mut self,
        ptr_expr: Expr,
        pointee_ty: rustc_public::ty::Ty,
        require_alignment: bool,
    ) -> (Expr, bool) {
        let mut overapproximated = false;
        let mut predicate = Expr::bool_const(true);

        if require_alignment {
            match self.compute_alignment_predicate(ptr_expr.clone(), pointee_ty) {
                Some(alignment_expr) => predicate = predicate.and(alignment_expr),
                None => overapproximated = true,
            }
        }

        let Some(access_size) = self.get_type_size(pointee_ty) else {
            debug!(?pointee_ty, "kani_mem access: unknown pointee size");
            return (predicate, true);
        };

        if access_size == 0 {
            return (predicate, overapproximated);
        }

        let Some(access_size_bv32) = u32::try_from(access_size).ok() else {
            debug!(access_size, ?pointee_ty, "kani_mem access: pointee too large for bv32 bounds");
            return (predicate, true);
        };

        let Some((obj_id, offset)) = self.split_pointer(&ptr_expr) else {
            debug!(?pointee_ty, "kani_mem access: cannot split pointer, falling back");
            return (predicate, true);
        };

        // Part of #3930: When the obj_id resolves to a known stack local,
        // skip the obj_valid[obj_id] check. Stack locals are always valid
        // (constrained by the entry rule), but the obj_valid array may not
        // be correctly threaded through all CHC state variables for functions
        // that don't otherwise use heap operations. Using concrete sizes
        // instead of array lookups avoids solver failures on packed structs.
        let const_obj_id = Self::const_obj_id_u32(&obj_id);
        let local_idx = const_obj_id.and_then(|id| self.heap_state.local_idx_for_obj_id(id));
        let local_ty_size = local_idx
            .and_then(|li| self.body.locals().get(li))
            .and_then(|local_decl| self.get_type_size(local_decl.ty))
            .and_then(|size| u32::try_from(size).ok());

        if local_ty_size.is_none() {
            // Non-stack pointer: need obj_valid check from heap metadata.
            self.mark_heap_metadata_read();
            predicate = predicate.and(self.current_obj_valid_array().select(obj_id.clone()));

            // Part of #4249: Null pointer check. obj_id=0 is reserved for null
            // (alloc IDs start at 2 — see collect_null_obj_size_constraint).
            // Without this, null pointers pass bounds checks because
            // obj_size[0]=0 triggers the zero-size exemption. The null check
            // is only needed for non-stack pointers (stack locals always have
            // concrete non-zero obj_ids assigned at entry).
            let null_id = Expr::bitvec_const(0u64, 32);
            predicate = predicate.and(obj_id.clone().eq(null_id).not());
        }

        let access_size_expr = Expr::bitvec_const(access_size_bv32 as u64, 32);
        let end_offset = offset.clone().bvadd(access_size_expr);
        predicate = predicate.and(end_offset.clone().bvuge(offset));

        let alloc_size = if let Some(size) = local_ty_size {
            Some(Expr::bitvec_const(size as u64, 32))
        } else {
            // Field pointers like `addr_of!(packed.c)` often appear as
            // `bvadd(base_addr, const_offset)`. After `split_pointer`, the
            // extracted obj_id is no longer syntactically constant even though
            // selecting obj_size[obj_id] remains sound and precise.
            self.mark_heap_metadata_read();
            Some(self.current_obj_size_array().select(obj_id))
        };

        if let Some(alloc_size) = alloc_size {
            let zero = Expr::bitvec_const(0u64, 32);
            predicate = predicate.and(alloc_size.clone().eq(zero).or(end_offset.bvule(alloc_size)));
        }

        (predicate, overapproximated)
    }

    fn compute_kani_mem_valid_value_predicate_with_hint(
        &mut self,
        addr: Expr,
        ty: rustc_public::ty::Ty,
        modified_locals: &std::collections::HashSet<usize>,
        mir_target_local: Option<usize>,
    ) -> (Expr, bool) {
        if self.get_type_size(ty).is_some_and(|size| size == 0) {
            return (Expr::bool_const(true), false);
        }

        match ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => {
                self.compute_scalar_memory_validity(addr, ty, Self::bool_validity_predicate)
            }
            TyKind::RigidTy(RigidTy::Char) => {
                self.compute_scalar_memory_validity(addr, ty, Self::char_validity_predicate)
            }
            TyKind::RigidTy(
                RigidTy::Int(_)
                | RigidTy::Uint(_)
                | RigidTy::Float(_)
                | RigidTy::RawPtr(..)
                | RigidTy::FnPtr(..),
            ) => (Expr::bool_const(true), false),
            TyKind::RigidTy(RigidTy::Tuple(elems)) => {
                let mut predicate = Expr::bool_const(true);
                let mut overapproximated = false;
                for (field_idx, elem_ty) in elems.iter().enumerate() {
                    let Some(field_offset) = self.get_field_offset(ty, field_idx) else {
                        overapproximated = true;
                        continue;
                    };
                    let (field_predicate, field_overapprox) = self
                        .compute_kani_mem_valid_value_predicate_with_hint(
                            self.pointer_with_offset(addr.clone(), field_offset),
                            *elem_ty,
                            modified_locals,
                            None, // MIR hint only applies at top-level ADT
                        );
                    predicate = predicate.and(field_predicate);
                    overapproximated |= field_overapprox;
                }
                (predicate, overapproximated)
            }
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                // VALVALID_ARRAY_NONZERO_KANIMEM: NonZero<T> validity is the
                // inner primitive != 0. NonZero is repr(transparent) over T, so
                // the value at `addr` loads as T; its lone field is an opaque
                // `NonZeroInner` that the generic single-variant field recursion
                // below would treat as an unconstrained (always-valid) integer,
                // silently dropping the zero bit-pattern check. Handle it here.
                // Prefer the SSA field value (constrained to kani::any()); fall
                // back to a direct memory load. Sound: a T we cannot resolve
                // over-approximates to true+overapprox, never a false "valid".
                if def.trimmed_name() == "NonZero" {
                    let Some(GenericArgKind::Type(inner_ty)) = args.0.first().cloned() else {
                        return (Expr::bool_const(true), true);
                    };
                    let ssa_local = self.try_resolve_addr_to_local(&addr).or(mir_target_local);
                    if let Some(local_idx) = ssa_local
                        && let Some(field_expr) =
                            self.try_resolve_ssa_field(local_idx, 0, modified_locals)
                    {
                        return match Self::nonzero_validity_predicate(field_expr) {
                            Some(p) => (p, false),
                            None => (Expr::bool_const(true), true),
                        };
                    }
                    return self.compute_scalar_memory_validity(
                        addr,
                        inner_ty,
                        Self::nonzero_validity_predicate,
                    );
                }
                let variants = def.variants();
                if variants.len() != 1 {
                    debug!(ty = ?ty, "kani_mem validity: multi-variant ADT unsupported");
                    return (Expr::bool_const(true), true);
                }
                // Part of #3930: When the base address resolves to a known stack
                // local, extract field values via SSA state variables. Aggregate
                // assignments store struct values in SSA variables (either as a
                // single datatype or flattened into per-field state vars) without
                // populating per-field memory entries, so load_from_memory at
                // field offsets returns unconstrained values disconnected from
                // kani::any() constraints.
                //
                // Try symbolic pointer decomposition first, then fall back to
                // MIR-level hint from addr_of!/Ref resolution (#3930).
                let ssa_local = self.try_resolve_addr_to_local(&addr).or(mir_target_local);
                let mut predicate = Expr::bool_const(true);
                let mut overapproximated = false;
                for (field_idx, field) in variants[0].fields().iter().enumerate() {
                    let field_ty = field.ty_with_args(&args);
                    // Try SSA extraction for scalar validity-bearing fields
                    if let Some(local_idx) = ssa_local {
                        if let Some(field_expr) =
                            self.try_resolve_ssa_field(local_idx, field_idx, modified_locals)
                        {
                            let (field_pred, field_oa) =
                                self.compute_ssa_field_validity(field_expr, field_ty);
                            predicate = predicate.and(field_pred);
                            overapproximated |= field_oa;
                            continue;
                        }
                    }
                    // Fall back to memory-based path
                    let Some(field_offset) = self.get_field_offset(ty, field_idx) else {
                        overapproximated = true;
                        continue;
                    };
                    let (field_predicate, field_overapprox) = self
                        .compute_kani_mem_valid_value_predicate_with_hint(
                            self.pointer_with_offset(addr.clone(), field_offset),
                            field_ty,
                            modified_locals,
                            None, // MIR hint only applies at top-level ADT
                        );
                    predicate = predicate.and(field_predicate);
                    overapproximated |= field_overapprox;
                }
                (predicate, overapproximated)
            }
            // VALVALID_ARRAY_NONZERO_KANIMEM: [T; N] validity is the conjunction
            // of element validity across all N elements. Element i lives at
            // addr + i*size_of::<T>() (array stride == element size in Rust).
            // The unrolled conjunction is bounded (KANI_MEM_ARRAY_VALIDITY_MAX);
            // non-const-length or over-sized arrays over-approximate soundly.
            TyKind::RigidTy(RigidTy::Array(elem_ty, len)) => {
                let Some(n) = len.eval_target_usize().ok() else {
                    debug!(ty = ?ty, "kani_mem validity: array length not const, over-approx");
                    return (Expr::bool_const(true), true);
                };
                let Some(elem_size) = self.get_type_size(elem_ty) else {
                    debug!(?elem_ty, "kani_mem validity: array elem size unknown, over-approx");
                    return (Expr::bool_const(true), true);
                };
                if n > KANI_MEM_ARRAY_VALIDITY_MAX {
                    debug!(
                        n,
                        "VALVALID_ARRAY_NONZERO_KANIMEM: array too large to unroll, over-approx"
                    );
                    return (Expr::bool_const(true), true);
                }
                let mut predicate = Expr::bool_const(true);
                let mut overapproximated = false;
                for i in 0..n {
                    let elem_addr = self.pointer_with_offset(addr.clone(), i * elem_size as u64);
                    let (elem_predicate, elem_overapprox) = self
                        .compute_kani_mem_valid_value_predicate_with_hint(
                            elem_addr,
                            elem_ty,
                            modified_locals,
                            None,
                        );
                    predicate = predicate.and(elem_predicate);
                    overapproximated |= elem_overapprox;
                }
                (predicate, overapproximated)
            }
            TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::Dynamic(..))
            | TyKind::RigidTy(RigidTy::Slice(..) | RigidTy::Str) => {
                debug!(ty = ?ty, "kani_mem validity: unsupported pointee validity");
                (Expr::bool_const(true), true)
            }
            _ => (Expr::bool_const(true), false),
        }
    }

    fn compute_scalar_memory_validity(
        &mut self,
        addr: Expr,
        ty: rustc_public::ty::Ty,
        predicate_builder: fn(Expr) -> Option<Expr>,
    ) -> (Expr, bool) {
        let pending_checks_len = self.heap_state.pending_checks.len();
        let loaded = self.load_from_memory(addr, ty);
        self.heap_state.pending_checks.truncate(pending_checks_len);

        let Some(loaded) = loaded else {
            debug!(?ty, "kani_mem validity: load_from_memory failed");
            return (Expr::bool_const(true), true);
        };
        match predicate_builder(loaded) {
            Some(predicate) => (predicate, false),
            None => {
                debug!(?ty, "kani_mem validity: loaded value has unsupported sort");
                (Expr::bool_const(true), true)
            }
        }
    }

    fn compute_alignment_predicate(
        &self,
        ptr_expr: Expr,
        pointee_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        let align = self.get_type_align(pointee_ty)?;
        if align <= 1 {
            return Some(Expr::bool_const(true));
        }

        // Part of #4014: Use split-pointer model for alignment checks.
        // All allocation bases are (obj_id << 32), aligned to 2^32, so alignment
        // depends only on the offset part. For known obj_id (constant), check
        // offset alignment precisely on BV32 offset. For computed pointers
        // (field projections, bvadd expressions), use the full 64-bit check.
        if let Some((obj_id, offset)) = self.split_pointer(&ptr_expr) {
            if Self::const_obj_id_u32(&obj_id).is_some() {
                let align_bv = Expr::bitvec_const(align, 32);
                let zero_bv = Expr::bitvec_const(0u64, 32);
                return Some(offset.bvurem(align_bv).eq(zero_bv));
            }
        }

        // Fallback: non-constant obj_id (field projections via bvadd that
        // const_bv_value couldn't fully evaluate, or symbolic offsets).
        // Use full 64-bit alignment check. D1 guard in compute_kani_mem_access_predicate
        // prevents this path from being reached for untraceable pointers.
        let align_bv = Expr::bitvec_const(align, POINTER_WIDTH);
        let zero_bv = Expr::bitvec_const(0u64, POINTER_WIDTH);
        Some(ptr_expr.bvurem(align_bv).eq(zero_bv))
    }

    /// Part of #4014: Checks if the kani_mem pointer operand comes from a local
    /// that was never assigned in the entire function body. Such locals arise when
    /// the inline walker bails on intermediate Rc/Arc internal pointer locals —
    /// their state variables are unconstrained, and the solver picks non-aligned
    /// values to produce spurious CTREX.
    ///
    /// Scans all basic blocks for direct assignments and call destinations.
    /// Function parameters (args) are considered "assigned" (they have entry
    /// constraints). Only non-parameter, non-return locals without any assignment
    /// trigger the over-approximation.
    fn is_unassigned_ptr_operand(&self, args: &[rustc_public::mir::Operand]) -> bool {
        use rustc_public::mir::{Operand, StatementKind, TerminatorKind};

        let ptr_arg = match args.first() {
            Some(arg) => arg,
            None => return false,
        };
        let local_idx = match ptr_arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => return false, // Not a simple local — has projections or is a constant
        };

        // Function parameters and return place are "assigned" by the calling convention
        let arg_count = self.body.arg_locals().len();
        if local_idx == 0 || local_idx <= arg_count {
            return false;
        }

        // Scan all blocks for any assignment to this local
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(lhs, _) = &stmt.kind
                    && lhs.local == local_idx
                    && lhs.projection.is_empty()
                {
                    return false; // Found a direct assignment
                }
            }
            if let TerminatorKind::Call { destination, .. } = &bb_data.terminator.kind
                && destination.local == local_idx
                && destination.projection.is_empty()
            {
                return false; // Found a call destination assignment
            }
        }

        debug!(local_idx, "kani_mem: pointer local has no assignment in function body");
        true
    }

    /// Part of #4172: Returns true when the pointer operand's local is assigned
    /// only by Call terminators (not by Assign statements). Such locals arise
    /// from `Rc::as_ptr`, `Box::into_raw`, etc. where the inline walker may
    /// bail, leaving the state variable unconstrained. Locals assigned by
    /// Assign statements (Ref, AddressOf, field projections) are constrained
    /// by the CHC encoding even when obj_id is non-constant.
    fn is_call_only_assigned_ptr_operand(&self, args: &[rustc_public::mir::Operand]) -> bool {
        use rustc_public::mir::{Operand, StatementKind, TerminatorKind};

        let ptr_arg = match args.first() {
            Some(arg) => arg,
            None => return false,
        };
        let local_idx = match ptr_arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => return false,
        };

        let arg_count = self.body.arg_locals().len();
        if local_idx == 0 || local_idx <= arg_count {
            return false; // Parameters are constrained by entry rule
        }

        let mut has_call_assignment = false;
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(lhs, _) = &stmt.kind
                    && lhs.local == local_idx
                    && lhs.projection.is_empty()
                {
                    return false; // Has an Assign statement — pointer is constrained
                }
            }
            if let TerminatorKind::Call { destination, .. } = &bb_data.terminator.kind
                && destination.local == local_idx
                && destination.projection.is_empty()
            {
                has_call_assignment = true;
            }
        }

        has_call_assignment
    }

    /// Part of #4249 (Phase 2c): Returns true when all Call terminators
    /// assigning to the pointer local are known allocation stubs (RustAlloc,
    /// RustAllocZeroed, BoxNew, etc.). These stubs produce pointers with
    /// concrete obj_ids assigned by the allocation codegen, so the resulting
    /// pointer IS constrained even though `split_pointer` may not evaluate
    /// to a constant obj_id at the kani_mem call site.
    ///
    /// This allows the untraceable-pointer guard to skip the overapprox
    /// fallback for allocation-returned pointers, reducing false positives.
    fn is_call_assigned_by_known_alloc_only(&self, args: &[rustc_public::mir::Operand]) -> bool {
        use rustc_public::mir::{Operand, TerminatorKind};

        let ptr_arg = match args.first() {
            Some(arg) => arg,
            None => return false,
        };
        let local_idx = match ptr_arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => return false,
        };

        let mut has_alloc_call = false;
        for bb_data in &self.body.blocks {
            if let TerminatorKind::Call { func, destination, .. } = &bb_data.terminator.kind
                && destination.local == local_idx
                && destination.projection.is_empty()
            {
                match self.detect_stub(func) {
                    Some(stub) if stub.is_known_alloc_producer() => {
                        has_alloc_call = true;
                    }
                    _ => return false, // Non-alloc call assigns to this local
                }
            }
        }

        has_alloc_call
    }

    fn pointer_with_offset(&self, addr: Expr, offset: u64) -> Expr {
        if offset == 0 { addr } else { addr.bvadd(Expr::bitvec_const(offset, POINTER_WIDTH)) }
    }

    pub(in crate::codegen_ay::chc) fn bool_validity_predicate(value: Expr) -> Option<Expr> {
        if value.sort().is_bool() {
            return Some(Expr::bool_const(true));
        }
        if let Some(width) = value.sort().bitvec_width() {
            let zero = Expr::bitvec_const(0u64, width);
            let one = Expr::bitvec_const(1u64, width);
            return Some(value.clone().eq(zero).or(value.eq(one)));
        }
        if value.sort().is_int() {
            let zero = Expr::int_const(0);
            let one = Expr::int_const(1);
            return Some(value.clone().eq(zero).or(value.eq(one)));
        }
        None
    }

    pub(in crate::codegen_ay::chc) fn char_validity_predicate(value: Expr) -> Option<Expr> {
        if let Some(width) = value.sort().bitvec_width() {
            let low_range = value.clone().bvule(Expr::bitvec_const(0xD7FFu64, width));
            let high_lower = value.clone().bvuge(Expr::bitvec_const(0xE000u64, width));
            let high_upper = value.bvule(Expr::bitvec_const(0x10FFFFu64, width));
            return Some(low_range.or(high_lower.and(high_upper)));
        }
        if value.sort().is_int() {
            let low_range = value.clone().int_le(Expr::int_const(0xD7FFi64));
            let high_lower = value.clone().int_ge(Expr::int_const(0xE000i64));
            let high_upper = value.int_le(Expr::int_const(0x10FFFFi64));
            return Some(low_range.or(high_lower.and(high_upper)));
        }
        None
    }

    /// VALVALID_ARRAY_NONZERO_KANIMEM: validity predicate for `NonZero<T>` — the
    /// loaded primitive value must be non-zero. Returns `None` for value sorts
    /// that cannot carry an integer zero (caller over-approximates).
    pub(in crate::codegen_ay::chc) fn nonzero_validity_predicate(value: Expr) -> Option<Expr> {
        if let Some(width) = value.sort().bitvec_width() {
            let zero = Expr::bitvec_const(0u64, width);
            return Some(value.eq(zero).not());
        }
        if value.sort().is_int() {
            let zero = Expr::int_const(0);
            return Some(value.eq(zero).not());
        }
        None
    }

    /// Part of #4249 Phase 3: Direct `same_allocation(p1, p2)` encoding.
    ///
    /// Instead of letting `same_allocation` decompose through separate
    /// `pointer_object` hook calls (which produce independent symbolic results
    /// that the solver cannot unify for distinct pointers), this stub directly
    /// compares the obj_id portions (upper 32 bits) of both pointer arguments
    /// in a single AY expression.
    ///
    /// Encoding at Ptr+ level:
    ///   `obj_id(p1) == obj_id(p2) && live_allocation(obj_id(p1))`
    ///
    /// `live_allocation` uses exact stack-local provenance when the object id
    /// resolves to a stack allocation. For symbolic object ids, stack ids are
    /// handled explicitly so a dead stack object cannot be admitted through the
    /// heap metadata array's default value.
    ///
    /// Falls back to `true` (sound over-approximation) when:
    /// - Track level is below Ptr
    /// - Either pointer argument cannot be translated or split
    /// Returns `(result_expr, overapproximated)` consistent with the other
    /// `compute_kani_mem_*` methods.
    pub(in crate::codegen_ay::chc) fn compute_same_allocation(
        &mut self,
        args: &[rustc_public::mir::Operand],
        modified_locals: &std::collections::HashSet<usize>,
    ) -> (Expr, bool) {
        if self.track_level < ChcTrackLevel::Ptr {
            debug!("same_allocation: below Ptr track level, over-approximating as true");
            self.record_sound_fallback_reason("same_allocation_below_ptr_level");
            return (Expr::bool_const(true), true);
        }

        let obj_id1 = args
            .first()
            .and_then(|op| self.same_allocation_obj_id_for_operand(op, modified_locals));
        let obj_id2 =
            args.get(1).and_then(|op| self.same_allocation_obj_id_for_operand(op, modified_locals));

        let (Some(obj_id1), Some(obj_id2)) = (obj_id1, obj_id2) else {
            warn!(
                "same_allocation: pointer arg obj_id extraction failed, \
                 falling back to true (sound over-approximation)"
            );
            self.record_sound_fallback_reason("same_allocation_obj_id_extraction_failed");
            return (Expr::bool_const(true), true);
        };

        if let (Some(id1), Some(id2)) =
            (Self::const_obj_id_u32(&obj_id1), Self::const_obj_id_u32(&obj_id2))
        {
            if id1 != id2 || id1 == 0 {
                return (Expr::bool_const(false), false);
            }
            if let Some(local_idx) = self.heap_state.local_idx_for_obj_id(id1) {
                return match self.same_allocation_stack_local_live(local_idx) {
                    Some(true) => {
                        // Part of #72: the kani_core model (models.rs:73-78)
                        // is same object AND in bounds of that object. Equal
                        // obj ids alone false-prove wrapped pointers: the
                        // wrapping step propagates the alloc-id METADATA to
                        // the result while its offset lane underflows, so a
                        // `wrapping_add(usize::MAX/64)` pointer still reported
                        // "same allocation" (offset-wraps-around
                        // original_harness). Conjoin the in-bounds component
                        // when both offset lanes and the allocation size
                        // resolve; demote (sound over-approx) otherwise.
                        match self.same_allocation_in_bounds_expr(args, modified_locals, local_idx)
                        {
                            Some(in_bounds) => (in_bounds, false),
                            None => {
                                self.record_sound_fallback_reason(
                                    "same_allocation_offset_unresolvable",
                                );
                                (Expr::bool_const(true), true)
                            }
                        }
                    }
                    Some(false) => (Expr::bool_const(false), false),
                    None => {
                        self.record_sound_fallback_reason("same_allocation_stack_liveness_unknown");
                        (Expr::bool_const(true), true)
                    }
                };
            }
        }

        let ids_equal = obj_id1.clone().eq(obj_id2);
        let (is_valid, overapproximated) = self.same_allocation_live_obj_predicate(obj_id1);
        (ids_equal.and(is_valid), overapproximated)
    }

    /// Part of #72: the in-bounds half of the same-allocation model — both
    /// pointers' offset lanes must lie within the allocation (one-past-end
    /// allowed). Returns `None` (caller demotes) when the offsets or the
    /// allocation size cannot be resolved.
    fn same_allocation_in_bounds_expr(
        &mut self,
        args: &[rustc_public::mir::Operand],
        modified_locals: &std::collections::HashSet<usize>,
        local_idx: usize,
    ) -> Option<Expr> {
        let size = self.get_type_size(self.body.locals().get(local_idx)?.ty)? as u128;
        let mut conds: Vec<Expr> = Vec::with_capacity(2);
        for op in args.iter().take(2) {
            let ptr_expr = self.translate_operand_with_modified(op, modified_locals)?;
            let ptr_expr = Self::normalize_kani_mem_pointer_expr(ptr_expr)?;
            let (_, offset) = self.split_pointer(&ptr_expr)?;
            conds.push(offset.bvule(Expr::bitvec_const(size, 32)));
        }
        conds.into_iter().reduce(Expr::and)
    }

    fn same_allocation_obj_id_for_operand(
        &mut self,
        op: &Operand,
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<Expr> {
        if let Some(local_idx) = Self::simple_operand_local(op)
            && let Some(&obj_id) = self.known_alloc_ids.get(&local_idx)
        {
            return Some(Expr::bitvec_const(obj_id as u64, 32));
        }

        let ptr_expr = self.translate_operand_with_modified(op, modified_locals)?;
        let ptr_expr = Self::normalize_kani_mem_pointer_expr(ptr_expr)?;
        let (obj_id, _) = self.split_pointer(&ptr_expr)?;
        Some(Self::simplify_same_allocation_obj_id_expr(obj_id))
    }

    pub(in crate::codegen_ay::chc) fn simplify_same_allocation_obj_id_expr(obj_id: Expr) -> Expr {
        if let ExprValue::BvExtract { expr, high, low } = obj_id.value()
            && *high == 63
            && *low == 32
            && let ExprValue::BvConcat(high_expr, low_expr) = expr.value()
            && high_expr.sort().bitvec_width() == Some(32)
            && low_expr.sort().bitvec_width() == Some(32)
        {
            return Self::simplify_same_allocation_obj_id_expr(high_expr.clone());
        }
        obj_id
    }

    pub(in crate::codegen_ay::chc) fn same_allocation_live_obj_predicate(
        &mut self,
        obj_id: Expr,
    ) -> (Expr, bool) {
        let obj_id = Self::simplify_same_allocation_obj_id_expr(obj_id);
        if let Some(id) = Self::const_obj_id_u32(&obj_id) {
            if id == 0 {
                return (Expr::bool_const(false), false);
            }
            if let Some(local_idx) = self.heap_state.local_idx_for_obj_id(id) {
                return match self.same_allocation_stack_local_live(local_idx) {
                    Some(live) => (Expr::bool_const(live), false),
                    None => {
                        self.record_sound_fallback_reason("same_allocation_stack_liveness_unknown");
                        (Expr::bool_const(true), true)
                    }
                };
            }
        }

        self.mark_heap_metadata_read();
        let metadata_valid = self.current_obj_valid_array().select(obj_id.clone());
        let non_null = obj_id.clone().eq(Expr::bitvec_const(0u64, 32)).not();
        let mut stack_obj_ids = self.heap_state.stack_local_obj_ids();
        stack_obj_ids.sort_unstable();
        let mut non_stack_obj_id = Expr::bool_const(true);
        let mut stack_valid = Expr::bool_const(false);
        for stack_id in stack_obj_ids {
            let Some(local_idx) = self.heap_state.local_idx_for_obj_id(stack_id) else {
                continue;
            };
            let is_stack_obj_id = obj_id.clone().eq(Expr::bitvec_const(stack_id as u64, 32));
            non_stack_obj_id = non_stack_obj_id.and(is_stack_obj_id.clone().not());
            let Some(live) = self.same_allocation_stack_local_live(local_idx) else {
                self.record_sound_fallback_reason("same_allocation_stack_liveness_unknown");
                return (Expr::bool_const(true), true);
            };
            if live {
                stack_valid = stack_valid.or(is_stack_obj_id);
            }
        }
        let heap_metadata_valid = non_stack_obj_id.and(metadata_valid);
        (non_null.and(stack_valid.or(heap_metadata_valid)), false)
    }

    fn same_allocation_stack_local_live(&self, local_idx: usize) -> Option<bool> {
        if self.current_encode_bb >= self.liveness.dead_locals_at_entry.len() {
            return None;
        }
        Some(!self.liveness.dead_locals.contains(&local_idx))
    }

    fn simple_operand_local(op: &Operand) -> Option<usize> {
        match op {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        }
    }
}
