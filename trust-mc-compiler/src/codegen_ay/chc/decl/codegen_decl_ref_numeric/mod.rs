// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Numeric reference-target collection for CHC encoding.
//! Part of #2306: include!() to proper module migration.

mod numeric_ref_propagation;
mod offset_call_metadata;
mod ptr_deref_arg_derivation;
mod slice_call_metadata;

use self::numeric_ref_propagation::NumericRefPropagationMode;
use ay_bindings::Expr;
use rustc_public::mir::{
    CastKind, Operand, PointerCoercion, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::ChcCtx;
use super::RefTarget;
use crate::codegen_ay::chc::stmt::codegen_stmt_slice_metadata::projected_subslice_len;
use crate::codegen_ay::types::POINTER_WIDTH;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Collects BigInt/BigRational reference targets from MIR statements.
    ///
    /// When we see `_ref = &_bigint` where `_bigint` is a BigInt local, we record
    /// the mapping `ref_local_idx -> bigint_local_idx`. This allows `get_bigint_arg`
    /// to resolve reference arguments to their Int values. Similarly for BigRational
    /// references which map to Real values. We also track all simple reference
    /// locals for HashMap key/self resolution.
    ///
    /// Part of #734, #911: BigInt/BigRational interception for CHC codegen.
    /// Enable `--ay-chc-debug` or CHC_DEBUG=1 for verbose tracing (#861).
    pub(super) fn collect_numeric_ref_targets(&mut self) {
        // Part of #1712: Two-pass collection to handle deref-through-ref patterns.
        // Pass 1: Collect simple _ref = &local patterns
        // Pass 2: Resolve _ref = &((*other_ref).field) using results from pass 1
        //
        // Note: Argument references (&T/&mut T) are NOT seeded in ref_targets here.
        // They are handled directly by handle_deref_store_via_ref_targets using
        // ref_arg_pointee_idx (Part of #2496). Seeding ref_targets with virtual
        // locals caused index-out-of-bounds panics in body.locals() access sites.

        // Pass 1: Simple references
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                    && let Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) = rhs
                {
                    // Part of #1712: Debug log ALL Ref/AddressOf patterns for diagnosis
                    debug!(
                        "Pass1 Ref/AddressOf: lhs={} place.local={} projections={:?}",
                        lhs.local, place.local, place.projection
                    );
                    let pointee_local: usize = place.local;
                    let pointee_ty = self.body.locals()[pointee_local].ty;
                    let ref_local: usize = lhs.local;

                    // Part of #1712, #1739: Use RefTarget for value-semantics deref resolution.
                    // Track non-Deref projections so we can resolve patterns like `&arr[idx]`.
                    // Defer Deref-based patterns (e.g., &(*ref).field) to pass 2.
                    if place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref)) {
                        continue;
                    }
                    self.ref_resolution.ref_targets.insert(
                        ref_local,
                        RefTarget::with_projections(pointee_local, place.projection.clone()),
                    );

                    // Only track references to BigInt/BigUint types
                    if place.projection.is_empty() && Self::type_name_contains_bigint(&pointee_ty) {
                        debug!(ref_local, pointee_local, "CHC: tracking BigInt reference");
                        self.ref_resolution.bigint_ref_targets.insert(ref_local, pointee_local);
                    }

                    // Track references to BigRational/Ratio types for value semantics
                    if place.projection.is_empty()
                        && Self::type_name_contains_bigrational(&pointee_ty)
                    {
                        debug!(ref_local, pointee_local, "CHC: tracking BigRational reference");
                        self.ref_resolution
                            .bigrational_ref_targets
                            .insert(ref_local, pointee_local);
                    }
                }
            }
        }

        // Part of #2283, #2919: Pre-scan aggregate construction (Tuple + ADT) for
        // field-access ref propagation. When `_11 = Aggregate(_, [_9, _10])`, record
        // that field 0 of local 11 came from local 9, field 1 from local 10.
        // This allows Pass 1.5 to resolve `_17 = Copy(_11.0)` → `_9`'s ref_target.
        // Extended to ADT aggregates for nested deref chain resolution (#2919).
        let field_sources = self.collect_aggregate_field_sources();

        // Part of #2286: source-indexed worklist for Pass 1.5.
        // Replaces full-body fixed-point rescans with dependency-driven updates.
        let (pass15_candidates, pass15_by_src) = self.build_numeric_ref_propagation_candidates(
            &field_sources,
            NumericRefPropagationMode::FullPass15,
        );
        self.propagate_numeric_ref_targets_worklist(
            &pass15_candidates,
            &pass15_by_src,
            &field_sources,
            "Pass1.5",
        );

        // Pass 2.5 runs HERE as well as after PostPass2 (below): Pass 1.5's
        // `DerefProjectedCopy` records `dest = Copy((*src).f)` as the PLACE
        // `src_target.f` — the "value-of" relation — while Pass 2 consumes
        // `ref_targets` as the "points-at" relation. When `f` is itself
        // reference-typed the two disagree, and Pass 2 composes further
        // projections onto a base that means "the slot" instead of "what the
        // slot points to". `resolve_adt_field_ref_targets` is exactly the
        // repair for that shape, but running it only at the end left every
        // target Pass 2 had already COMPOSED on the stale base uncorrected —
        // a contract `ensures` reading `im.x` through a closure capture
        // resolved to the closure environment's own storage instead of the
        // captured referent, so the post-state read landed on a memory cell
        // nothing ever writes (free BV -> refutable postcondition on a correct
        // program). Correct the base BEFORE composing on top of it.
        self.resolve_adt_field_ref_targets(&field_sources);

        // Part of #1712: Pass 2 - Resolve deref-through-ref patterns like _ref = &((*other_ref).field)
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind
                    && let Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) = rhs
                    && matches!(place.projection.first(), Some(ProjectionElem::Deref))
                {
                    let base_local: usize = place.local;
                    let ref_local: usize = lhs.local;

                    // Try ref_targets first; fall back to ref_arg_pointee_idx for
                    // &T/&mut T parameters (Part of #3348).
                    //
                    // Last resort: a pointer with no `_p = &_L` statement of its
                    // own may still PROVABLY hold `&_L` — a contract closure's
                    // `&result` arrives through the one-element capture tuple
                    // that closure inlining builds, so Pass 1 never sees it.
                    // `mir_provable_referent_local` is the same single-assignment
                    // MIR walk the address-provenance guard already trusts.
                    // Without this edge, `&((*result) as B).0` becomes a symbolic
                    // address and the later load is a free variable, so an
                    // `ensures(|r| matches!(*r, Foo::B(c) if …))` on a
                    // BV-flattened multi-variant enum is refutable.
                    let base_target = self.propagated_ref_target(base_local).or_else(|| {
                        let referent = self.mir_provable_referent_local(base_local)?;
                        let pointee_ty = Self::deref_pointee_ty(self.body.locals()[base_local].ty)?;
                        (self.body.locals()[referent].ty == pointee_ty)
                            .then(|| RefTarget::with_projections(referent, vec![]))
                    });

                    if let Some(target) = base_target {
                        // Extract projections after the Deref and append to the existing target.
                        let mut combined_projs = target.projections.clone();
                        let mut all_supported = true;
                        for proj in &place.projection[1..] {
                            match proj {
                                ProjectionElem::Field(_, _)
                                | ProjectionElem::Downcast(_)
                                | ProjectionElem::Index(_)
                                | ProjectionElem::ConstantIndex { .. }
                                | ProjectionElem::Subslice { .. } => {
                                    combined_projs.push(proj.clone());
                                }
                                _ => {
                                    // external enum: ProjectionElem
                                    // Non-value projection - can't handle in value semantics.
                                    all_supported = false;
                                    break;
                                }
                            }
                        }
                        if all_supported {
                            debug!(
                                ref_local,
                                target_local = target.local,
                                proj_count = combined_projs.len(),
                                "CHC: resolved deref-through-ref pattern"
                            );
                            self.ref_resolution.ref_targets.insert(
                                ref_local,
                                RefTarget::with_projections(target.local, combined_projs),
                            );
                        }
                    }
                }
            }
        }

        // Part of #2283: Post-Pass 2 propagation. Pass 2 adds deref-through-ref entries
        // (e.g., _15 = &((*_20).field)). Copy/Move consumers of those entries (e.g.,
        // _22 = Copy(_15)) were missed by Pass 1.5 which ran before Pass 2.
        // Re-run the Copy/Move + tuple field propagation to pick them up.
        let (postpass2_candidates, postpass2_by_src) = self
            .build_numeric_ref_propagation_candidates(
                &field_sources,
                NumericRefPropagationMode::CopyMoveOnly,
            );
        self.propagate_numeric_ref_targets_worklist(
            &postpass2_candidates,
            &postpass2_by_src,
            &field_sources,
            "PostPass2",
        );

        // Part of #2919: Pass 2.5 - Resolve ref_targets that point to reference-typed
        // ADT fields through aggregate field sources.
        //
        // Pattern: `_tmp = Copy((*_ref_to_struct).inner)` where `inner: &Inner`.
        // DerefProjectedCopy produces: `_tmp → { local: struct_local, projs: [Field(0, &Inner)] }`.
        // The resolved place `struct_local.field_0` has type `&Inner`, but the ref_target
        // says "I am struct_local + field projection" rather than "I point to what inner
        // points to". When `*_tmp` is later resolved, it constructs
        // `struct_local[Field, Deref, ...]` which requires memory-model loading.
        //
        // Fix: if `struct_local` was initialized from `Aggregate(Adt, [Move(_ref_local)])`
        // and `_ref_local` has its own ref_target, replace `_tmp`'s ref_target with
        // `_ref_local`'s ref_target. This makes `*_tmp` resolve directly to the referent
        // without going through memory.
        self.resolve_adt_field_ref_targets(&field_sources);

        debug!(
            count = self.ref_resolution.bigint_ref_targets.len(),
            "CHC: collected BigInt reference targets"
        );
        debug!(
            count = self.ref_resolution.bigrational_ref_targets.len(),
            "CHC: collected BigRational reference targets"
        );
        debug!(count = self.ref_resolution.ref_targets.len(), "CHC: collected reference targets");
        debug!(
            "collect_numeric_ref_targets bigint={} bigrational={} ref_targets={:?}",
            self.ref_resolution.bigint_ref_targets.len(),
            self.ref_resolution.bigrational_ref_targets.len(),
            self.ref_resolution.ref_targets
        );

        // Part of #1905: Pass 3 - Collect constant reference discriminants.
        // When we see `_N = const &Ordering::Equal` or `_N = Copy(_M)` where _M holds
        // such a constant, record the discriminant value for translate_discriminant.
        self.collect_const_ref_discriminants();

        // Part of #1919: Pass 4 - Collect constant reference scalar values.
        // When we see `_N = const &0u8`, follow provenance to extract the pointee
        // value as a AY expression. This enables translate_place_with_deref to
        // resolve `(*_N)` for promoted constant references.
        self.collect_const_ref_values();

        // Part of #3495: Pass 5 - Pre-collect subslice metadata.
        // When MIR has `_N = Cast(Unsize, &[T; N], &[T])`, record
        // subslice_len[_N] = N. Then propagate through Ref+Deref+Subslice chains.
        // This must run before block iteration because block processing order
        // is not guaranteed to follow source order.
        self.collect_subslice_metadata();

        // Part of #3596: Pass 6 - Build pointer-cast-from-arg-ref derivation map.
        // Traces AddressOf + Cast chains from argument reference locals to build
        // ptr_deref_to_arg_pointee. This enables referent resolution to follow
        // patterns like `as_array(&self)` where a raw pointer is created from
        // &raw const (*self), cast to a different pointer type, then dereferenced.
        self.build_ptr_deref_to_arg_pointee();
    }

    /// Part of #3495: Pre-populate `subslice_len` from Unsize coercions and
    /// propagate through Subslice projections.
    ///
    /// Pass 5a: Scan all blocks for `Cast(PointerCoercion::Unsize)` from `&[T; N]`
    /// to `&[T]`. Extract the static array length N and store in `subslice_len`.
    ///
    /// Pass 5b: Scan all blocks for `Ref(_s, [Deref, Subslice { from, to, .. }])`.
    /// If `subslice_len[_s]` exists, compute the exact polarity-sensitive
    /// `subslice_len[dest]` and `subslice_offset[dest] = from`.
    fn collect_subslice_metadata(&mut self) {
        // Order: 5a (Unsize) → 5c (RangeFull terminators) → 5b (Subslice projections)
        // → 5d (Use chains).
        // Pass 5c must run before 5b so that subslice_len propagated through
        // RangeFull call destinations is available when 5b processes Subslice
        // projections referencing those destinations.
        self.collect_subslice_unsize_lens();
        self.collect_subslice_range_full_terminators();
        self.collect_subslice_projection_propagation();
        self.collect_subslice_use_chain_propagation();
        self.collect_pointer_offset_call_metadata();
        self.collect_slice_as_ptr_call_metadata();
        self.collect_str_as_bytes_call_metadata();
    }

    /// Pass 5a: Scan for `Cast(PointerCoercion::Unsize)` from `&[T; N]` to `&[T]`.
    fn collect_subslice_unsize_lens(&mut self) {
        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                    continue;
                };
                if !place.projection.is_empty() {
                    continue;
                }
                let Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), operand, _) =
                    rvalue
                else {
                    continue;
                };
                let source_local = match operand {
                    Operand::Copy(source) | Operand::Move(source)
                        if source.projection.is_empty() =>
                    {
                        Some(source.local)
                    }
                    _ => None,
                };
                if self.local_has_multiple_whole_definitions(place.local)
                    || source_local
                        .is_some_and(|source| self.local_has_multiple_whole_definitions(source))
                {
                    self.ref_resolution.clear_path_insensitive_ref_metadata(place.local);
                    continue;
                }
                let Ok(src_ty) = operand.ty(self.body.locals()) else {
                    continue;
                };
                let inner = match src_ty.kind() {
                    TyKind::RigidTy(RigidTy::Ref(_, t, _))
                    | TyKind::RigidTy(RigidTy::RawPtr(t, _)) => t,
                    _ => continue,
                };
                let TyKind::RigidTy(RigidTy::Array(_, const_len)) = inner.kind() else {
                    continue;
                };
                let Ok(n) = const_len.eval_target_usize() else {
                    continue;
                };
                let len_expr = Expr::bitvec_const(n as u128, POINTER_WIDTH);
                self.ref_resolution.subslice_len.insert(place.local, len_expr);
                if let Operand::Copy(src_place) | Operand::Move(src_place) = operand
                    && src_place.projection.is_empty()
                {
                    if let Some(array_expr) =
                        self.ref_resolution.const_ref_values.get(&src_place.local).cloned()
                    {
                        self.ref_resolution.const_ref_values.insert(place.local, array_expr);
                    }
                    if let Some(offset_expr) =
                        self.ref_resolution.subslice_offset.get(&src_place.local).cloned()
                    {
                        self.ref_resolution.subslice_offset.insert(place.local, offset_expr);
                    }
                }
                debug!(dest_local = place.local, n, "collect_subslice_metadata: unsize slice");
            }
        }
    }

    /// Pass 5b: Propagate `subslice_len`/`subslice_offset` through
    /// `Ref/AddressOf` with `Deref+Subslice` projections.
    fn collect_subslice_projection_propagation(&mut self) {
        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                    continue;
                };
                if !place.projection.is_empty() {
                    continue;
                }
                let dest_local = place.local;
                let ref_place = match rvalue {
                    Rvalue::Ref(_, _, p) | Rvalue::AddressOf(_, p) => p,
                    _ => continue,
                };
                if ref_place.projection.len() < 2 {
                    continue;
                }
                if !ref_place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref)) {
                    continue;
                }
                let Some((from, to, from_end)) = ref_place.projection.iter().rev().find_map(|p| {
                    if let ProjectionElem::Subslice { from, to, from_end } = p {
                        Some((*from, *to, *from_end))
                    } else {
                        None
                    }
                }) else {
                    continue;
                };
                let source_local = ref_place.local;
                if !self.path_insensitive_metadata_copy_is_unique(source_local, dest_local) {
                    self.ref_resolution.clear_path_insensitive_ref_metadata(dest_local);
                    continue;
                }

                if let Some(val) = self.ref_resolution.const_ref_values.get(&source_local).cloned()
                {
                    self.ref_resolution.const_ref_values.insert(dest_local, val);
                }
                let existing_offset =
                    self.ref_resolution.subslice_offset.get(&source_local).cloned();
                if from > 0 || existing_offset.is_some() {
                    let new_offset = if from > 0 {
                        let from_bv = Expr::bitvec_const(from as i128, POINTER_WIDTH);
                        match existing_offset {
                            Some(prev) => prev.bvadd(from_bv),
                            None => from_bv,
                        }
                    } else {
                        existing_offset.expect("invariant: checked is_some in guard")
                    };
                    self.ref_resolution.subslice_offset.insert(dest_local, new_offset);
                }
                if let Some(src_len) = self.ref_resolution.subslice_len.get(&source_local).cloned()
                {
                    match projected_subslice_len(src_len, from, to, from_end) {
                        Some(new_len) => {
                            self.ref_resolution.subslice_len.insert(dest_local, new_len);
                            debug!(
                                source_local,
                                dest_local,
                                from,
                                to,
                                from_end,
                                "collect_subslice_metadata: Subslice propagation"
                            );
                        }
                        None => {
                            self.ref_resolution.const_ref_values.remove(&dest_local);
                            self.ref_resolution.const_ref_slice_views.remove(&dest_local);
                            self.ref_resolution.subslice_offset.remove(&dest_local);
                            self.ref_resolution.subslice_len.remove(&dest_local);
                            debug!(
                                source_local,
                                dest_local,
                                from,
                                to,
                                from_end,
                                "collect_subslice_metadata: invalid Subslice bounds; dropping length authority"
                            );
                        }
                    }
                }
            }
        }
    }

    /// Pass 5c: Propagate `const_ref_values` and `subslice_len` through
    /// `Index::index(slice, RangeFull)` call terminators.
    ///
    /// When MIR has `Call Index::index(src, RangeFull) → dest`, the result is
    /// identity (same slice). Propagate metadata from `src` to `dest` so that
    /// downstream passes (5b) see the length/values before block iteration.
    ///
    /// Part of #3495: block processing order means the call terminator in a
    /// high-numbered block may run AFTER downstream blocks that depend on the
    /// destination's metadata.
    fn collect_subslice_range_full_terminators(&mut self) {
        for bb in &self.body.blocks {
            let TerminatorKind::Call { func, args, destination, .. } = &bb.terminator.kind else {
                continue;
            };
            // The suffix-compatible stub registry and generic debug names are
            // not semantic authority. Only the exact core Index/SliceIndex
            // method over the exact core RangeFull type may propagate identity
            // metadata in this path-insensitive prepass.
            let Some(source) = self.authenticated_core_range_full_source(func, args) else {
                continue;
            };
            if !destination.projection.is_empty() {
                continue;
            }
            let dest_local: usize = destination.local;
            let Some(src_local) = (match source {
                Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
                _ => None,
            }) else {
                continue;
            };
            // All three maps are path-insensitive semantic metadata. If either
            // endpoint has several whole-local producers, whichever producer
            // this scan visits last is not authority for the joined value.
            if !self.path_insensitive_metadata_copy_is_unique(src_local, dest_local) {
                self.ref_resolution.clear_path_insensitive_ref_metadata(dest_local);
                continue;
            }
            // Propagate subslice_len from source to destination (identity).
            if let Some(len) = self.ref_resolution.subslice_len.get(&src_local).cloned() {
                self.ref_resolution.subslice_len.insert(dest_local, len);
                debug!(src_local, dest_local, "Pass5c: RangeFull terminator → subslice_len");
            }
            // Propagate const_ref_values.
            if let Some(val) = self.ref_resolution.const_ref_values.get(&src_local).cloned() {
                self.ref_resolution.const_ref_values.insert(dest_local, val);
                debug!(src_local, dest_local, "Pass5c: RangeFull terminator → const_ref_values");
            }
            // Propagate subslice_offset.
            if let Some(off) = self.ref_resolution.subslice_offset.get(&src_local).cloned() {
                self.ref_resolution.subslice_offset.insert(dest_local, off);
            }
        }
    }

    /// Pass 5d: Propagate `const_ref_values`, `subslice_len`, and
    /// `subslice_offset` through `Use(Copy/Move)` chains.
    ///
    /// When MIR has `_dest = Use(Copy(_src))` or `_dest = Use(Move(_src))`,
    /// the destination carries the same metadata as the source.
    fn collect_subslice_use_chain_propagation(&mut self) {
        // Multiple passes to handle transitive chains (e.g., _a = Move(_b), _c = Copy(_a)).
        for _pass in 0..3 {
            #[allow(clippy::type_complexity)]
            let mut new_entries: Vec<(
                usize,
                Option<Expr>,
                Option<Expr>,
                Option<Expr>,
            )> = Vec::new();
            for bb in &self.body.blocks {
                for stmt in &bb.statements {
                    let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                        continue;
                    };
                    if !place.projection.is_empty() {
                        continue;
                    }
                    let src_local: usize = match rvalue {
                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                            if p.projection.is_empty() =>
                        {
                            p.local
                        }
                        _ => continue,
                    };
                    let dest_local = place.local;
                    if !self.path_insensitive_metadata_copy_is_unique(src_local, dest_local) {
                        self.ref_resolution.clear_path_insensitive_ref_metadata(dest_local);
                        continue;
                    }
                    let crv = self.ref_resolution.const_ref_values.get(&src_local).cloned();
                    let sl = self.ref_resolution.subslice_len.get(&src_local).cloned();
                    let so = self.ref_resolution.subslice_offset.get(&src_local).cloned();
                    if crv.is_some() || sl.is_some() || so.is_some() {
                        new_entries.push((dest_local, crv, sl, so));
                    }
                }
            }
            if new_entries.is_empty() {
                break;
            }
            for (dest, crv, sl, so) in new_entries {
                if let Some(v) = crv {
                    self.ref_resolution.const_ref_values.entry(dest).or_insert(v);
                }
                if let Some(v) = sl {
                    self.ref_resolution.subslice_len.entry(dest).or_insert(v);
                }
                if let Some(v) = so {
                    self.ref_resolution.subslice_offset.entry(dest).or_insert(v);
                }
            }
        }
    }
}
