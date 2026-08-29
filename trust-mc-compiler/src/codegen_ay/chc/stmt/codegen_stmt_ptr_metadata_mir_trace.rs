// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! PtrMetadata MIR/type trace helpers.
//!
//! Pure MIR-analysis functions that resolve slice metadata (length) by tracing
//! backwards through MIR assignments, casts, and call terminators. These helpers
//! produce `Option<u64>` (concrete lengths), not AY `Expr` values.
//!
//! Extracted from `codegen_stmt_arithmetic_ops.rs` per #3619 Phase 1.
//! The Expr-producing PtrMetadata resolution stack remains in
//! `codegen_stmt_arithmetic_ops.rs` for now (Phase 2).
//!
//! Utility helpers (operand_bare_local, trace_through_moves,
//! extract_constant_range_fields, extract_str_len_from_const_operand,
//! extract_array_len_from_ref, trace_use_field_projection,
//! trace_field_through_aggregate, find_aggregate_field) extracted to
//! `codegen_stmt_ptr_metadata_mir_trace_util.rs` per #4130.

use std::collections::HashSet;

use rustc_public::CrateDef;
use rustc_public::mir::{Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Resolve slice metadata (length) by tracing MIR assignments backwards
    /// through Cast/Move/Copy/Ref chains to the original `Cast(Unsize)` from a
    /// sized source (e.g., `&[T; N]`). Part of #3445.
    pub(in crate::codegen_ay::chc) fn resolve_slice_metadata_from_mir(
        &self,
        local_idx: usize,
    ) -> Option<u64> {
        // Transitive trace with depth limit to prevent infinite loops.
        let mut current = local_idx;
        let mut visited = HashSet::new();
        while visited.insert(current) {
            if self.local_has_multiple_whole_definitions(current) {
                return None;
            }
            let mut traced_local = None;
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    if let StatementKind::Assign(lhs, rvalue) = &stmt.kind
                        && lhs.local == current
                    {
                        match rvalue {
                            Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _) => {
                                // Check if the source type has an array tail we can extract.
                                if let Ok(src_ty) = place.ty(self.body.locals()) {
                                    let len = Self::extract_array_len_from_ref(src_ty);
                                    if let Some(len) = len {
                                        return Some(len);
                                    }
                                }
                                // Trace through projected pointer casts like
                                // `Copy(((_2.0).0))` used by Box<str> fat-pointer
                                // lowering; the owning local still carries the
                                // length-preserving call provenance.
                                traced_local = Some(place.local);
                            }
                            Rvalue::Use(operand) => {
                                // Part of #3497: &str constant → extract byte length.
                                if let Some(len) = Self::extract_str_len_from_const_operand(operand)
                                {
                                    return Some(len);
                                }
                                if let Some(src_local) = Self::operand_bare_local(operand) {
                                    traced_local = Some(src_local);
                                }
                                // Part of #3497, #3655: trace through field projections.
                                if traced_local.is_none() {
                                    traced_local = self.trace_use_field_projection(operand);
                                }
                            }
                            Rvalue::CopyForDeref(place) if place.projection.is_empty() => {
                                traced_local = Some(place.local);
                            }
                            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                                // Part of #3445: AddressOf handles &raw const (*fat_ptr).
                                traced_local = Some(place.local);
                            }
                            _ => {}
                        }
                    }
                }
            }
            if let Some(next) = traced_local {
                current = next;
            } else {
                break;
            }
        }

        // Check Call terminators for both original and traced locals. Part of #3327, #3495.
        self.resolve_metadata_from_calls(local_idx, current)
    }

    /// Check Call terminators for slice metadata (Index::index with Range/RangeFull).
    /// Checks both the original `local_idx` and the `traced` local (after Ref/Copy chains).
    fn resolve_metadata_from_calls(&self, local_idx: usize, traced: usize) -> Option<u64> {
        if let Some(len) = self.resolve_metadata_from_index_call(local_idx) {
            return Some(len);
        }
        if traced != local_idx {
            if let Some(len) = self.resolve_metadata_from_index_call(traced) {
                return Some(len);
            }
        }
        if let Some(len) = self.resolve_metadata_from_call_slice_arg(traced) {
            return Some(len);
        }
        // Part of #3582: String::as_str → String::from → const &str chain.
        self.resolve_metadata_from_str_producing_call(local_idx, traced)
    }

    /// Resolve slice metadata through String method call chains (as_str/deref →
    /// String::from(const &str)). Part of #3582.
    fn resolve_metadata_from_str_producing_call(
        &self,
        local_idx: usize,
        traced: usize,
    ) -> Option<u64> {
        // Try both original and traced locals.
        for target in [local_idx, traced] {
            if let Some(len) = self.resolve_str_producing_call_single(target) {
                return Some(len);
            }
        }
        None
    }

    /// Single-local helper for resolve_metadata_from_str_producing_call.
    fn resolve_str_producing_call_single(&self, local_idx: usize) -> Option<u64> {
        if self.local_has_multiple_whole_definitions(local_idx) {
            return None;
        }
        for block in &self.body.blocks {
            let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
            else {
                continue;
            };
            if destination.local != local_idx || !destination.projection.is_empty() {
                continue;
            }
            let Ok(func_ty) = func.ty(self.body.locals()) else { continue };
            let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func_ty.kind() else { continue };
            let direct_def_id = rustc_internal::internal(self.tcx, def.def_id());
            if !matches!(
                self.tcx.crate_name(direct_def_id.krate).as_str(),
                "core" | "alloc" | "std"
            ) {
                continue;
            }
            let name = def.trimmed_name();
            let is_str_producing = name == "as_str"
                || name.ends_with("::as_str")
                || name == "deref"
                || name.ends_with("::deref");
            // Part of #3655: into_boxed_str preserves the String's length.
            let is_str_preserving = name == "into_boxed_str" || name.ends_with("::into_boxed_str");
            if !(is_str_producing || is_str_preserving) {
                continue;
            }
            let string_local = args.first().and_then(Self::operand_bare_local)?;
            if self.local_has_multiple_whole_definitions(string_local) {
                return None;
            }
            let string_local = self
                .ref_resolution
                .ref_targets
                .get(&string_local)
                .map_or(string_local, |rt| rt.local);
            if self.local_has_multiple_whole_definitions(string_local) {
                return None;
            }
            // Find the String::from call that produced this String local.
            if let Some(len) = self.resolve_string_from_source_len(string_local) {
                return Some(len);
            }
        }
        None
    }

    /// Find the const &str source length for a String local produced by String::from.
    fn resolve_string_from_source_len(&self, string_local: usize) -> Option<u64> {
        if self.local_has_multiple_whole_definitions(string_local) {
            return None;
        }
        for block in &self.body.blocks {
            let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
            else {
                continue;
            };
            if destination.local != string_local || !destination.projection.is_empty() {
                continue;
            }
            let Ok(func_ty) = func.ty(self.body.locals()) else { continue };
            let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func_ty.kind() else { continue };
            let direct_def_id = rustc_internal::internal(self.tcx, def.def_id());
            if !matches!(
                self.tcx.crate_name(direct_def_id.krate).as_str(),
                "core" | "alloc" | "std"
            ) {
                continue;
            }
            let name = def.trimmed_name();
            if !(name == "from" || name.ends_with("::from") || name.contains("From")) {
                continue;
            }
            // Check if args[0] is a const &str with extractable length.
            if let Some(arg) = args.first() {
                // Direct const arg.
                if let Some(len) = Self::extract_str_len_from_const_operand(arg) {
                    return Some(len);
                }
                // Trace through to find a const &str assignment.
                if let Some(arg_local) = Self::operand_bare_local(arg) {
                    if let Some(len) = self.resolve_const_str_from_local(arg_local) {
                        return Some(len);
                    }
                }
            }
        }
        None
    }

    /// Trace a local back through assignments to find a const &str source.
    fn resolve_const_str_from_local(&self, local_idx: usize) -> Option<u64> {
        let mut current = local_idx;
        let mut visited = HashSet::new();
        while visited.insert(current) {
            if self.local_has_multiple_whole_definitions(current) {
                return None;
            }
            let mut next_local = None;
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    if let StatementKind::Assign(lhs, rvalue) = &stmt.kind
                        && lhs.local == current
                    {
                        if let Rvalue::Use(operand) = rvalue {
                            if let Some(len) = Self::extract_str_len_from_const_operand(operand) {
                                return Some(len);
                            }
                            if let Some(src) = Self::operand_bare_local(operand) {
                                next_local = Some(src);
                            }
                        }
                        if let Rvalue::CopyForDeref(place) = rvalue {
                            next_local = Some(place.local);
                        }
                    }
                }
            }
            if let Some(next) = next_local {
                current = next;
            } else {
                break;
            }
        }
        None
    }

    /// Scan Call terminators for Index::index with a Range argument and extract
    /// constant subslice length. Part of #3327: MIR-level scan resolves constant
    /// Range bounds independently of block processing order.
    fn resolve_metadata_from_index_call(&self, local_idx: usize) -> Option<u64> {
        for block in &self.body.blocks {
            if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                && destination.local == local_idx
                && destination.projection.is_empty()
                && !self.local_has_multiple_whole_definitions(local_idx)
            {
                let Some((_, _, index)) = self.authenticated_core_slice_index_args(func, args)
                else {
                    continue;
                };
                if Self::is_range_type_operand(self.tcx, index, self.body.locals())
                    && !Self::is_range_inclusive_operand(self.tcx, index, self.body.locals())
                    && let Some(range_local) = Self::operand_bare_local(index)
                    && let Some((start, end)) = self.extract_constant_range_fields(range_local)
                {
                    debug!(
                        local_idx,
                        start, end, "PtrMetadata: resolved Range subslice len from MIR"
                    );
                    return Some(end.saturating_sub(start));
                }
            }
        }
        None
    }

    /// Resolve slice metadata from Index::index by tracing the slice argument's
    /// length (for RangeFull `&arr[..]` patterns). Part of #3495.
    fn resolve_metadata_from_call_slice_arg(&self, local_idx: usize) -> Option<u64> {
        for block in &self.body.blocks {
            if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                && destination.local == local_idx
                && destination.projection.is_empty()
                && !self.local_has_multiple_whole_definitions(local_idx)
            {
                let Some(source) = self.authenticated_core_range_full_source(func, args) else {
                    continue;
                };
                if let Some(arg_local) = Self::operand_bare_local(source)
                    && !self.local_has_multiple_whole_definitions(arg_local)
                    && let Some(len) = self.resolve_slice_metadata_from_mir(arg_local)
                {
                    debug!(
                        local_idx,
                        arg_local, len, "PtrMetadata: resolved slice len from Index call argument"
                    );
                    return Some(len);
                }
            }
        }
        None
    }
}
