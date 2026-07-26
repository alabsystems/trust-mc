// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! PtrMetadata resolution: slice/Vec length extraction for CHC encoding.
//!
//! Contains `translate_ptr_metadata` (the public entry point) and 8 private
//! helpers that resolve slice/Vec/subslice lengths into AY `Expr` values.
//!
//! Pure MIR/type trace helpers (returning `Option<u64>`) are in the sibling
//! `codegen_stmt_ptr_metadata_mir_trace.rs` module.
//!
//! Extracted from `codegen_stmt_arithmetic_ops.rs` per #3619 Phase 2.

use std::collections::HashSet;

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::names::vec_layout;
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};
use crate::kani_middle::abi::LayoutOf;

use super::codegen_decl_flatten::collect_leaf_sorts;
use super::codegen_types::CodegenTypes;
use super::{
    ChcCtx, UnknownProjectionPolicy, chc_fresh_name, collect_field_projections, declare_pending_var,
};
use crate::codegen_ay::chc::codegen_ctx::diagnostics::CellCounter;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn translate_ptr_metadata(
        &self,
        operand: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let ty = operand.ty(self.body.locals()).ok()?;

        // Check if this is a wide pointer (slice, str, dyn Trait, or ADT with unsized tail).
        // Thin pointers have no metadata → return 0.
        let is_wide = match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
            | TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => {
                if matches!(
                    pointee.kind(),
                    TyKind::RigidTy(RigidTy::Slice(_))
                        | TyKind::RigidTy(RigidTy::Str)
                        | TyKind::RigidTy(RigidTy::Dynamic(..))
                ) {
                    true
                } else {
                    // Part of #3445: ADTs with unsized tails (e.g., Pair<u32, [u16]>
                    // or Pair<u32, dyn Debug>) are also wide pointers.
                    pointee.layout().ok().is_some_and(|l| l.shape().is_unsized())
                }
            }
            _ => false, // external enum: TyKind
        };

        if !is_wide {
            return Some(Expr::bitvec_const(0, POINTER_WIDTH));
        }

        // Part of #3495: Check subslice_len from range-based slice indexing.
        // When `&source[start..end]` was encoded, the subslice length (end - start)
        // was stored in subslice_len[dest_local]. This resolves PtrMetadata for
        // subslice results without requiring compile-time-constant Range bounds.
        //
        // Phase ordering: subslice_len is set during rule generation (block-by-block)
        // but MIR Copy/Move chains may alias the dest_local to another local.
        // Trace through Copy/Move assignments to find the original subslice local.
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            // Direct lookup first.
            if let Some(len_expr) = self.ref_resolution.subslice_len.get(&place.local) {
                return Some(len_expr.clone());
            }

            // Trace through MIR Copy/Move chains to find a local with subslice_len.
            // This handles the pattern: _5 = Copy(_2) where _2 has subslice_len.
            if let Some(len_expr) =
                self.trace_subslice_len_through_copies(place.local, modified_locals)
            {
                return Some(len_expr);
            }
        }

        // Wide pointer: try to resolve metadata from MIR.
        // Trace back through the operand's definition to find the source type.
        // NOTE: This must run AFTER subslice_len chain tracing above, because
        // resolve_slice_metadata_from_mir may incorrectly return the static array
        // length N from Cast(Unsize, &[T;N], &[T]) even when the local is actually
        // a dynamic subslice with length (end - start).
        if let Operand::Copy(place) | Operand::Move(place) = operand
            && let Some(len) = self.resolve_slice_metadata_from_mir(place.local)
        {
            return Some(Expr::bitvec_const(len as i64, POINTER_WIDTH));
        }

        // Part of #3159: For dyn Trait fat pointers, resolve vtable metadata
        // from dyn_vtable_ids or vtable state variables. This produces the
        // concrete vtable discriminant instead of an unconstrained symbolic,
        // enabling downstream vtable_size/vtable_align ITE chains to match.
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            let local_idx = place.local;
            // Part of #3445: Also match ADTs with dyn trait tails
            // (e.g., Pair<u32, dyn Debug>) — not just bare dyn Trait.
            let is_dyn = match ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
                | TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => {
                    matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Dynamic(..)))
                        || LayoutOf::new(pointee).has_trait_tail()
                }
                _ => false, // external enum: TyKind
            };
            if is_dyn {
                // Try compile-time vtable ID (single-block case).
                if let Some(vtable_expr) = self.dyn_vtable_ids.get(&local_idx) {
                    debug!(local_idx, "PtrMetadata: resolved dyn vtable from dyn_vtable_ids");
                    return Some(vtable_expr.clone());
                }
                // Try path-sensitive vtable state variable (multi-block case).
                if let Some((in_name, _out_name)) = self.vtable_state_vars.get(&local_idx) {
                    debug!(local_idx, "PtrMetadata: resolved dyn vtable from state var");
                    return Some(Expr::var(&**in_name, Sort::bitvec(POINTER_WIDTH)));
                }
            }
        }

        // Part of #3582: Check collections.len_state for tracked length.
        // When StringAsStr or VecAsSlice copy tracked length to a dest local,
        // PtrMetadata for that local should resolve to the tracked length.
        // Part of #3655: Also trace through AddressOf/Ref/CopyForDeref/Use chains
        // to find the source local's len_var (e.g., Box<str> deref to *const str).
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            if let Some(len_expr) = self.resolve_len_state_through_mir_trace(place.local) {
                return Some(len_expr);
            }
        }

        // Part of #3348: Resolve PtrMetadata for Vec-backed slices.
        // When VecAsSlice creates a slice from a Vec (or struct-embedded Vec),
        // it records slice_to_vec_local[slice_dest] = vec_or_struct_local.
        // The vec/struct local inherits a len_var through alias propagation
        // (propagate_collection_aliases during Aggregate/Copy/Move).
        // Trace back through slice_to_vec_local to get the Vec's tracked len.
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            if let Some(len_expr) = self.resolve_ptr_metadata_from_vec_backed_slice(place.local) {
                return Some(len_expr);
            }
        }

        // Part of #4163: Flattened fat pointer fld1 extraction.
        // When the local is a flattened 2-field wide pointer (e.g., `&mut str`,
        // `&[T]`), the metadata (length) lives in state_vars[base_idx + 1] (fld1).
        // State vars are BV64 each, not a single BV128, so BV128 extraction cannot
        // work. Read fld1 directly as the metadata.
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            let local_idx = place.local;
            if self.flatten.flattened_tuple_locals.contains(&local_idx) {
                let field_count =
                    self.flatten.flattened_local_field_count.get(&local_idx).copied().unwrap_or(2);
                if field_count == 2 {
                    if let Some(base_idx) = self.try_state_idx_for_local(local_idx) {
                        let metadata_slot = base_idx + 1;
                        let vars = if modified_locals.contains(&local_idx) {
                            &self.state_var_mgr.output_state_vars
                        } else {
                            &self.state_var_mgr.state_vars
                        };
                        if let Some((name, sort)) = vars.get(metadata_slot) {
                            debug!(
                                local_idx,
                                metadata_slot, "PtrMetadata: resolved from flattened fld1"
                            );
                            return Some(Expr::var(&**name, sort.clone()));
                        }
                    }
                }
            }
        }

        // Part of #4163: BV128 fat pointer high-bits extraction.
        // Some fat pointer locals are declared as BV128 (not flattened). The
        // metadata (length) occupies bits 127..64. This covers non-flattened
        // fat pointers (e.g., results of inlined calls or casts).
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            if let Some(ptr_expr) = self.translate_place_with_modified(place, modified_locals) {
                if ptr_expr.sort().bitvec_width() == Some(128) {
                    // Only trust the high half when it can actually carry metadata.
                    // A thin BV64 address WIDENED into the 128-bit slot has a high
                    // half that is pure padding, and extracting it fabricates a
                    // metadata word the program never computed — reliably `0` for a
                    // zero-extension. That is not merely imprecise: a length of 0
                    // makes size/bounds obligations trivially satisfiable, so it can
                    // manufacture a PROOF. Fall through to the unconstrained fallback
                    // instead, which is a `SOUND_APPROXIMATION` category the driver
                    // force-demotes.
                    if is_fabricated_fat_ptr_metadata(&ptr_expr) {
                        debug!(
                            place.local,
                            "PtrMetadata: refusing fabricated BV128 high bits (widened thin pointer)"
                        );
                    } else {
                        debug!(place.local, "PtrMetadata: resolved from BV128 high bits");
                        return Some(ptr_expr.extract(127, 64));
                    }
                }
            }
        }

        // Fallback: return a fresh symbolic variable. This is sound
        // (over-approximation) but may cause false counterexamples.
        // Part of #3447: track PtrMetadata unconstrained fallbacks.
        //
        // AUDIT (task #65): the fresh var replaces the program-computed DST
        // metadata (slice/str length). Havoc direction: WIDENING ONLY — the
        // fresh var is universally quantified in the Horn rule body, so the
        // real metadata value is one admitted instantiation; every real
        // execution stays representable and a PROOF over the widened system is
        // valid. The residual risk is precision, not proof soundness: checks
        // guarded by the same havoced length can be co-satisfied with values
        // the program never produces (spurious CTREX), and a Success that
        // leaned on the havoc proves the property for ALL lengths — stronger,
        // never weaker. The counter is now plumbed through generate_metadata
        // (codegen_units.rs) as a SOUND_APPROXIMATION category: the driver's
        // Step-C fail-closes a Success carrying it (OverApproximation), which
        // is the conservative read Step-C is designed to make.
        self.diagnostics.ptr_metadata_unconstrained.inc();
        let name = chc_fresh_name("ptr_metadata");
        debug!(?operand, ?ty, "CHC: PtrMetadata unresolved, using symbolic var {name}");
        Some(declare_pending_var(name, ptr_sort()))
    }

    /// Trace through MIR assignments (AddressOf, Ref, CopyForDeref, Use, Cast)
    /// to find a source local with a `collections.len_state` entry.
    ///
    /// Part of #3655: When `Box<str>` drop glue calls `size_of_val_raw(*const str)`,
    /// the `*const str` local is derived via `AddressOf(&raw const (*_box))`.
    /// `StringIntoBoxedStr` records the length on the Box<str> local, but the
    /// `*const str` local doesn't inherit it. This trace follows the MIR chain
    /// back to the Box local and resolves its tracked length.
    fn resolve_len_state_through_mir_trace(&self, start_local: usize) -> Option<Expr> {
        // Direct check first.
        if let Some(len_var) = self.collections.len_state.get_len_var(start_local).cloned() {
            let len_expr = self.collection_current_len(&len_var);
            debug!(start_local, "PtrMetadata: resolved from collections.len_state (direct)");
            return Some(len_expr);
        }

        // Trace through MIR assignment chains.
        let mut current = start_local;
        let mut visited = HashSet::new();
        while visited.len() < 8 && visited.insert(current) {
            let mut traced_local = None;
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    if let StatementKind::Assign(lhs, rvalue) = &stmt.kind
                        && lhs.local == current
                        && lhs.projection.is_empty()
                    {
                        match rvalue {
                            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                                traced_local = Some(place.local);
                            }
                            Rvalue::CopyForDeref(place) if place.projection.is_empty() => {
                                traced_local = Some(place.local);
                            }
                            Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                                if place.projection.is_empty() =>
                            {
                                traced_local = Some(place.local);
                            }
                            Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _) => {
                                // Box<str> fat-pointer metadata goes through a projected
                                // transmute chain like `Copy(((_2.0).0))`; follow the
                                // root local even when the cast source is projected.
                                traced_local = Some(place.local);
                            }
                            _ => {}
                        }
                    }
                }
            }
            match traced_local {
                Some(next) => {
                    if let Some(len_var) = self.collections.len_state.get_len_var(next).cloned() {
                        let len_expr = self.collection_current_len(&len_var);
                        debug!(
                            start_local,
                            next, "PtrMetadata: resolved from collections.len_state via MIR trace"
                        );
                        return Some(len_expr);
                    }
                    current = next;
                }
                None => break,
            }
        }
        None
    }

    /// Resolve PtrMetadata for slice locals that were created by VecAsSlice.
    ///
    /// VecAsSlice records `slice_to_vec_local[slice_dest] = vec_or_struct_local`.
    /// The vec/struct local may have a propagated `len_var` (from `vec![expr]` →
    /// Aggregate alias propagation). If found, return the tracked length expression.
    ///
    /// Also traces through MIR Copy/Move chains to handle intermediary copies:
    /// `_copy = Copy(_deref)` where `_deref` is the VecAsSlice destination.
    ///
    /// Part of #3348: fixes PtrMetadata on Vec-backed slices (e.g.,
    /// `clause.literals().len()` where `literals()` returns `&self.0` from a
    /// struct wrapping `Vec<T>`).
    fn resolve_ptr_metadata_from_vec_backed_slice(&self, start_local: usize) -> Option<Expr> {
        // Direct lookup: is this local directly a VecAsSlice destination?
        if let Some(&vec_local) = self.ref_resolution.slice_to_vec_local.get(&start_local) {
            if let Some(len_expr) = self.resolve_vec_len_from_slice_mapping(start_local, vec_local)
            {
                debug!(start_local, vec_local, "PtrMetadata: resolved from slice_to_vec_local");
                return Some(len_expr);
            }
        }

        // Trace through Copy/Move chains to find a local in slice_to_vec_local.
        let mut current = start_local;
        let mut visited = HashSet::new();
        while visited.len() < 8 && visited.insert(current) {
            let mut source_local = None;
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    if let StatementKind::Assign(lhs, rvalue) = &stmt.kind
                        && lhs.local == current
                        && lhs.projection.is_empty()
                    {
                        if let Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) = rvalue
                            && place.projection.is_empty()
                        {
                            source_local = Some(place.local);
                        }
                    }
                }
            }
            match source_local {
                Some(src) => {
                    if let Some(&vec_local) = self.ref_resolution.slice_to_vec_local.get(&src) {
                        if let Some(len_expr) =
                            self.resolve_vec_len_from_slice_mapping(src, vec_local)
                        {
                            debug!(
                                start_local,
                                src,
                                vec_local,
                                "PtrMetadata: resolved from slice_to_vec_local via chain"
                            );
                            return Some(len_expr);
                        }
                    }
                    current = src;
                }
                None => break,
            }
        }

        // Phase-ordering fallback: when PtrMetadata's block is processed before the
        // VecAsSlice block, `slice_to_vec_local` hasn't been populated yet.
        // Check both the original local and the chain-traced local (current),
        // since PtrMetadata may be on a Copy of the VecAsSlice destination.
        // Part of #3348: fixes CnfClause newtype VecAsSlice → PtrMetadata ordering.
        if let Some(expr) = self.resolve_vec_len_from_defining_call(start_local) {
            return Some(expr);
        }
        if current != start_local {
            return self.resolve_vec_len_from_defining_call(current);
        }
        None
    }

    /// Scan Call terminators to find the defining call for a slice local and
    /// resolve the collection local's len_var directly from the call arguments.
    ///
    /// This handles the phase-ordering case where PtrMetadata's block is encoded
    /// before the VecAsSlice block, so `slice_to_vec_local` hasn't been populated.
    /// Resolves arg[0] through ref_targets (same as `resolve_collection_local`).
    ///
    /// Part of #3348: fixes CnfClause newtype VecAsSlice → PtrMetadata ordering.
    fn resolve_vec_len_from_defining_call(&self, dest_local: usize) -> Option<Expr> {
        for block in &self.body.blocks {
            if let TerminatorKind::Call { args, destination, .. } = &block.terminator.kind
                && destination.local == dest_local
            {
                if let Some(Operand::Copy(place) | Operand::Move(place)) = args.first() {
                    let ref_local = place.local;
                    let coll_local = self
                        .ref_resolution
                        .ref_targets
                        .get(&ref_local)
                        .map_or(ref_local, |rt| rt.local);
                    if let Some(len_var) =
                        self.collections.len_state.get_len_var(coll_local).cloned()
                    {
                        debug!(
                            dest_local,
                            ref_local,
                            coll_local,
                            "PtrMetadata: resolved Vec len via Call terminator scan"
                        );
                        return Some(self.collection_current_len(&len_var));
                    }
                    if let Some(len_expr) =
                        self.resolve_struct_embedded_vec_len_from_ref_local(ref_local)
                    {
                        debug!(
                            dest_local,
                            ref_local,
                            coll_local,
                            "PtrMetadata: resolved Vec len via Call terminator struct fallback"
                        );
                        return Some(len_expr);
                    }
                }
                break;
            }
        }
        None
    }

    fn resolve_vec_len_from_slice_mapping(
        &self,
        slice_local: usize,
        owner_local: usize,
    ) -> Option<Expr> {
        if let Some(len_var) = self.collections.len_state.get_len_var(owner_local).cloned() {
            return Some(self.collection_current_len(&len_var));
        }
        let projections = self.ref_resolution.slice_to_vec_field_projections.get(&slice_local)?;
        self.resolve_struct_embedded_vec_len(owner_local, projections)
    }

    /// Resolve the entry-state `fld_len` for a struct-embedded Vec referenced by `ref_local`.
    ///
    /// This extends the Call-terminator phase-ordering fallback for PtrMetadata:
    /// wrapper methods like `fn literals(&self) -> &[T] { &self.0 }` often have no
    /// sidecar `len_var` on the wrapper parameter, but `ref_targets` still records
    /// the field projection path from the wrapper to the embedded Vec.
    fn resolve_struct_embedded_vec_len_from_ref_local(&self, ref_local: usize) -> Option<Expr> {
        let rt = self.ref_resolution.ref_targets.get(&ref_local)?;
        self.resolve_struct_embedded_vec_len(rt.local, &rt.projections)
    }

    fn resolve_struct_embedded_vec_len(
        &self,
        owner_local: usize,
        projections: &[ProjectionElem],
    ) -> Option<Expr> {
        let field_projs = collect_field_projections(projections, UnknownProjectionPolicy::Skip);
        if field_projs.is_empty() {
            return None;
        }

        let owner_ty = self.struct_embedded_owner_ty(owner_local)?;
        let struct_state_idx =
            self.ref_resolution
                .ref_arg_pointee_idx
                .get(&owner_local)
                .copied()
                .or_else(|| self.state_var_mgr.local_to_state_idx.get(&owner_local).copied())?;
        let (in_name, in_sort) = self.state_var_mgr.state_vars.get(struct_state_idx)?.clone();

        if in_sort.datatype_name().is_some() {
            let struct_in = Expr::var(&*in_name, in_sort);
            let vec_expr = Self::apply_field_selections(struct_in, &field_projs)?;
            let vec_sort = vec_expr.sort().clone();
            let dt_name = vec_sort.datatype_name()?;
            let len_sort = Self::get_dt_field_sort(&vec_expr, "fld_len")?;
            return Some(vec_expr.field_select(dt_name, "fld_len", len_sort));
        }

        if field_projs.len() != 1 {
            return None;
        }
        let target_field_idx = field_projs[0].field_idx;
        let struct_sort = Self::translate_ty(owner_ty)?;
        let dt = struct_sort.datatype_sort()?;
        if dt.constructors.len() != 1 || target_field_idx >= dt.constructors[0].fields.len() {
            return None;
        }
        let cons = &dt.constructors[0];

        let mut flat_base = 0;
        for f in &cons.fields[..target_field_idx] {
            flat_base += collect_leaf_sorts(&f.sort, 0).len();
        }

        let target_sort = &cons.fields[target_field_idx].sort;
        let target_leaves = collect_leaf_sorts(target_sort, 0);
        if target_leaves.len() != vec_layout::FIELD_COUNT
            || !target_leaves[vec_layout::IDX_DATA].is_array()
        {
            return None;
        }

        let len_slot = struct_state_idx + flat_base + vec_layout::IDX_LEN;
        self.state_var_mgr
            .state_vars
            .get(len_slot)
            .map(|(name, sort)| Expr::var(&**name, sort.clone()))
    }
}

/// Does this 128-bit expression's high half carry *fabricated* pointer metadata?
///
/// A genuine fat pointer packs `(metadata, address)` into the 128-bit slot, so
/// `extract(127, 64)` is the program's own slice length. But the same slot is
/// also reached by WIDENING a thin 64-bit address, and then the high half is
/// extension padding — extracting it invents a length the program never
/// computed. For a zero-extension that invented length is exactly `0`, which
/// makes `size_of_val`, `len()` and bounds obligations trivially satisfiable:
/// the fabrication can manufacture a PROOF, not merely a spurious failure.
///
/// Two shapes are refused, matching what actually reaches the encoder:
///
/// * an extension node over a `<= 64`-bit expression (`zero_extend`/`sign_extend`),
///   the un-folded form seen when the address is symbolic;
/// * a 128-bit constant whose high half is zero, the folded form — constant
///   folding erases the extension node, so matching on the node alone misses it.
///
/// The second shape also catches a genuinely-empty slice whose real metadata is
/// `0`. That loss is deliberate: the two are indistinguishable at this point, and
/// refusing costs precision (a havoced length, hence a possible spurious
/// counterexample) while trusting costs soundness (a fabricated proof).
fn is_fabricated_fat_ptr_metadata(ptr_expr: &Expr) -> bool {
    match ptr_expr.value() {
        // Widened thin pointer: the high half is extension padding, never metadata.
        ExprValue::BvZeroExtend { expr, .. } | ExprValue::BvSignExtend { expr, .. } => {
            expr.sort().bitvec_width().is_some_and(|w| w <= 64)
        }
        // Folded form of the same thing: `zero_extend` of a concrete address.
        ExprValue::BitVecConst { value, width } => {
            *width == 128 && (value >> 64u32) == num_bigint::BigInt::from(0)
        }
        _ => false,
    }
}
