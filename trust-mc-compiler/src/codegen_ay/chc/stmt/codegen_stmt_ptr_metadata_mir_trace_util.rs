// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! PtrMetadata MIR trace utility helpers.
//!
//! Pure utility functions for tracing MIR locals through moves/copies,
//! extracting constant values from operands/allocations, and resolving
//! field projections through aggregate constructions.
//!
//! Extracted from `codegen_stmt_ptr_metadata_mir_trace.rs` per #4130.

use std::collections::HashSet;

use rustc_public::CrateDef;
use rustc_public::mir::{AggregateKind, Operand, ProjectionElem, Rvalue, StatementKind};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::shared::IntoOption;
use crate::codegen_ay::types::POINTER_WIDTH;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Trace a Use operand with field projections (`_x.field` or `(*_x).field`)
    /// back to a source local via Aggregate construction. Part of #3655.
    pub(in crate::codegen_ay::chc) fn trace_use_field_projection(
        &self,
        operand: &Operand,
    ) -> Option<usize> {
        let place = match operand {
            Operand::Copy(p) | Operand::Move(p) => p,
            _ => return None,
        };
        let field_idx = match place.projection.as_slice() {
            [ProjectionElem::Field(idx, _)] => *idx,
            [ProjectionElem::Deref, ProjectionElem::Field(idx, _)] => *idx,
            _ => return None,
        };
        self.trace_field_through_aggregate(place.local, field_idx).or(Some(place.local))
    }

    /// Part of #3497: When PtrMetadata traces through `_local = Copy(_y.uints)`,
    /// this finds the Aggregate that constructed `_y` and returns the source local
    /// for field `field_idx`, enabling the trace to continue through the struct.
    ///
    /// Part of #4017: When the field projection is through a Deref (`(*_ref).field`),
    /// the `struct_local` is a reference/pointer, not the struct itself. Follow
    /// Ref/AddressOf/Cast chains to find the underlying struct local before
    /// searching for Aggregate constructions.
    fn trace_field_through_aggregate(
        &self,
        struct_local: usize,
        field_idx: usize,
    ) -> Option<usize> {
        // Direct Aggregate lookup on struct_local.
        if let Some(result) = self.find_aggregate_field(struct_local, field_idx) {
            return Some(result);
        }
        // Part of #4017: struct_local may be a reference/pointer (e.g., `_25 = Ref(_struct)`
        // or `_25 = Cast(Unsize, _struct_ref, _dyn_ref)`). Trace through Ref/AddressOf/Cast/
        // Copy chains to find the underlying struct, then retry Aggregate lookup.
        let mut current = struct_local;
        let mut visited = HashSet::new();
        while visited.len() < 6 && visited.insert(current) {
            let mut next = None;
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    if let StatementKind::Assign(lhs, rvalue) = &stmt.kind
                        && lhs.local == current
                        && lhs.projection.is_empty()
                    {
                        match rvalue {
                            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                                next = Some(place.local);
                            }
                            Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _) => {
                                next = Some(p.local);
                            }
                            Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                                if p.projection.is_empty() =>
                            {
                                next = Some(p.local);
                            }
                            Rvalue::CopyForDeref(p) if p.projection.is_empty() => {
                                next = Some(p.local);
                            }
                            _ => {}
                        }
                    }
                }
            }
            match next {
                Some(n) => {
                    if let Some(result) = self.find_aggregate_field(n, field_idx) {
                        return Some(result);
                    }
                    current = n;
                }
                None => break,
            }
        }
        None
    }

    /// Search for an Aggregate assignment on `local` and return the source local
    /// for `field_idx`. Helper for `trace_field_through_aggregate`.
    fn find_aggregate_field(&self, local: usize, field_idx: usize) -> Option<usize> {
        for block in &self.body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(lhs, rvalue) = &stmt.kind
                    && lhs.local == local
                    && let Rvalue::Aggregate(_, operands) = rvalue
                {
                    if let Some(operand) = operands.get(field_idx) {
                        return Self::operand_bare_local(operand);
                    }
                }
            }
        }
        None
    }

    /// Check if a Call func operand is an Index::index method.
    /// Guards the Range MIR scan against false matches on non-index calls.
    pub(in crate::codegen_ay::chc) fn is_index_call(
        func: &Operand,
        locals: &[rustc_public::mir::LocalDecl],
    ) -> bool {
        let Ok(func_ty) = func.ty(locals) else { return false };
        match func_ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, _)) => {
                let name = def.trimmed_name();
                name == "index" || name.ends_with("::index")
            }
            _ => false,
        }
    }

    /// Extract the local index from an operand, if it is a simple Copy/Move.
    pub(in crate::codegen_ay::chc) fn operand_bare_local(op: &Operand) -> Option<usize> {
        match op {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        }
    }

    /// Trace a local through Use/Move chains in MIR to find a Range Aggregate
    /// definition, then extract its constant start/end fields.
    pub(in crate::codegen_ay::chc) fn extract_constant_range_fields(
        &self,
        start_local: usize,
    ) -> Option<(u64, u64)> {
        let traced = self.trace_through_moves(start_local);
        self.find_range_aggregate_const_fields(traced)
    }

    /// Follow Use(Move(_X)) / Use(Copy(_X)) chains to find the originating local.
    fn trace_through_moves(&self, mut local_idx: usize) -> usize {
        for _ in 0..5 {
            let mut followed = false;
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    if let StatementKind::Assign(lhs, rvalue) = &stmt.kind
                        && lhs.local == local_idx
                        && let Rvalue::Use(operand) = rvalue
                        && let Some(next) = Self::operand_bare_local(operand)
                    {
                        local_idx = next;
                        followed = true;
                        break;
                    }
                }
                if followed {
                    break;
                }
            }
            if !followed {
                break;
            }
        }
        local_idx
    }

    /// Find a Range Aggregate definition for the given local and extract
    /// constant start/end fields as (start, end).
    fn find_range_aggregate_const_fields(&self, local_idx: usize) -> Option<(u64, u64)> {
        for block in &self.body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(lhs, rvalue) = &stmt.kind
                    && lhs.local == local_idx
                    && let Rvalue::Aggregate(AggregateKind::Adt(..), operands) = rvalue
                    && operands.len() == 2
                {
                    let start = Self::extract_operand_const_usize(&operands[0])?;
                    let end = Self::extract_operand_const_usize(&operands[1])?;
                    return Some((start, end));
                }
            }
        }
        None
    }

    /// Extract a constant usize value from an Operand::Constant.
    pub(in crate::codegen_ay::chc) fn extract_operand_const_usize(
        operand: &Operand,
    ) -> Option<u64> {
        if let Operand::Constant(const_op) = operand {
            const_op.const_.eval_target_usize().ok()
        } else {
            None
        }
    }

    /// Extract str byte length from a constant `&str` operand by reading the
    /// length word from the fat pointer allocation. Part of #3497.
    pub(in crate::codegen_ay::chc) fn extract_str_len_from_const_operand(
        operand: &Operand,
    ) -> Option<u64> {
        use rustc_public::ty::ConstantKind;

        let Operand::Constant(const_op) = operand else { return None };
        let ty = const_op.ty();

        // Only handle &str references.
        let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) = ty.kind() else { return None };
        if !matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Str)) {
            return None;
        }

        // Extract the allocation from the constant.
        let alloc = match const_op.const_.kind() {
            ConstantKind::Allocated(alloc) => alloc,
            ConstantKind::Ty(ty_const) => {
                use rustc_public::ty::TyConstKind;
                match ty_const.kind() {
                    TyConstKind::Value(_ty, alloc) => alloc,
                    _ => return None, // external enum: TyConstKind
                }
            }
            _ => return None, // external enum: ConstantKind
        };

        // &str fat pointer layout: [data_ptr, length] — each POINTER_WIDTH/8 bytes.
        // alloc.bytes is Vec<Option<u8>> — None indicates uninitialized bytes.
        // The length field (second word) should be fully initialized.
        let ptr_bytes = (POINTER_WIDTH / 8) as usize;
        if alloc.bytes.len() >= ptr_bytes * 2 {
            let mut len_arr = [0u8; 8];
            for (i, opt_byte) in alloc.bytes[ptr_bytes..ptr_bytes * 2].iter().enumerate() {
                len_arr[i] = (*opt_byte)?;
            }
            let len = u64::from_le_bytes(len_arr);
            debug!(len, "PtrMetadata: resolved str len from constant allocation");
            Some(len)
        } else {
            None
        }
    }

    /// Extract the array length N from a reference/pointer to `[T; N]` or a struct
    /// with an array tail (e.g., `&Pair<u32, [u16; 3]>` → 3). Part of #3445.
    pub(in crate::codegen_ay::chc) fn extract_array_len_from_ref(
        ty: rustc_public::ty::Ty,
    ) -> Option<u64> {
        let pointee = match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => pointee,
            TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => pointee,
            _ => return None, // external enum: TyKind
        };
        Self::extract_tail_array_len(pointee)
    }

    /// Recursively extract the array length from a type's tail field.
    /// Handles `[T; N]` directly, or ADTs/tuples whose last field is `[T; N]`.
    fn extract_tail_array_len(ty: rustc_public::ty::Ty) -> Option<u64> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Array(_, len)) => len.eval_target_usize().into_option(),
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                let fields = def.variants_iter().next()?.fields();
                let layout = ty.layout().ok()?.shape();
                let fields_sorted = layout.fields.fields_by_offset_order();
                let last_idx = *fields_sorted.last()?;
                let last_ty = fields.get(last_idx)?.ty_with_args(&args);
                Self::extract_tail_array_len(last_ty)
            }
            TyKind::RigidTy(RigidTy::Tuple(tys)) => {
                let layout = ty.layout().ok()?.shape();
                let fields_sorted = layout.fields.fields_by_offset_order();
                let last_idx = *fields_sorted.last()?;
                Self::extract_tail_array_len(*tys.get(last_idx)?)
            }
            _ => None, // external enum: TyKind
        }
    }
}
