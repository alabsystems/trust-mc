// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Reference tracking and propagation (converted from include!() per #2595).
// Extracted from codegen_assign.rs (#2246): reference/pointee tracking,
// cast propagation, and constant reference handling.

use super::{IntoOption, StatementCodegen};
use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::{
    AggregateKind, BorrowKind, CastKind, Operand, Place, ProjectionElem, Rvalue,
};
use rustc_public::ty::{AdtKind, RigidTy, Ty, TyKind};
use rustc_public_bridge::IndexedVal;
use std::fmt::Write;
use std::sync::Arc;
use tracing::debug;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Track aggregate field ref_pointees for tuples, closures, and ADTs.
    pub(super) fn track_rvalue_aggregate_refs(
        &mut self,
        base_name: &str,
        lhs: &Place,
        rhs: &Rvalue,
    ) {
        match rhs {
            Rvalue::Aggregate(AggregateKind::Tuple, operands) => {
                self.track_aggregate_ref_pointees(base_name, operands);
            }
            // #1585: Track ref_pointees for closure captures containing references.
            Rvalue::Aggregate(AggregateKind::Closure(_def, _args), operands) => {
                debug!(
                    "track_aggregate_ref_pointees for closure: base={}, {} captures",
                    base_name,
                    operands.len()
                );
                self.track_aggregate_ref_pointees(base_name, operands);
            }
            Rvalue::Aggregate(
                AggregateKind::Adt(def, variant_idx, _args, _user_ty_annot, _active_field),
                operands,
            ) => {
                if def.kind() != AdtKind::Union {
                    let is_multi_variant_enum =
                        def.kind() == AdtKind::Enum && def.variants().len() > 1;
                    let lhs_has_downcast = lhs
                        .projection
                        .iter()
                        .any(|proj| matches!(proj, ProjectionElem::Downcast(_)));
                    // Part of #2267: pre-allocate with capacity instead of to_string().
                    let mut aggregate_base = String::with_capacity(base_name.len() + 12);
                    aggregate_base.push_str(base_name);
                    if is_multi_variant_enum && !lhs_has_downcast {
                        let _ = write!(aggregate_base, "_variant_{}", variant_idx.to_index());
                    }
                    self.track_aggregate_ref_pointees(&aggregate_base, operands);
                }
            }
            _ => {} // external enum: Rvalue
        }
    }

    /// Track cast-related propagation: wide pointer metadata, ref_pointees, heap_pointees.
    pub(super) fn recover_heap_value_from_base(&mut self, base: &str) -> Option<Expr> {
        if let Some(heap_value) = self.heap_pointees.get(base).cloned() {
            return Some(heap_value);
        }
        let env_value = self.env_lookup(base).cloned()?;
        let recovered = if env_value.sort().is_bitvec() {
            self.ctx.load_symbolic_memory_value(env_value)
        } else {
            Some(env_value)
        }?;
        self.heap_pointees.insert(Arc::from(base), recovered.clone());
        Some(recovered)
    }

    pub(super) fn track_cast_propagation(&mut self, lhs: &Place, lhs_name: &str, rhs: &Rvalue) {
        let Rvalue::Cast(cast_kind, operand, target_ty) = rhs else {
            return;
        };
        self.try_codegen_wide_ptr_metadata_from_cast(lhs_name, operand, *target_ty);

        // For casts that produce reference or raw pointer types, propagate ref_pointees tracking
        if matches!(
            target_ty.kind(),
            TyKind::RigidTy(RigidTy::Ref(..)) | TyKind::RigidTy(RigidTy::RawPtr(..))
        ) && let Operand::Copy(src) | Operand::Move(src) = operand
        {
            let src_base = self.ssa_base_name(src);
            if let Some(pointee) = self.ref_pointees.get(src_base.as_str()).cloned() {
                let dst_base: Arc<str> = self.ssa_base_name(lhs).into();
                debug!(
                    "codegen_assign Cast: propagating ref {} -> {} (pointee={})",
                    src_base, dst_base, pointee
                );
                self.ref_pointees.insert(dst_base, pointee);
            }
        }

        // #1210: For raw pointer casts from Box internals, propagate heap_pointees.
        if matches!(target_ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(..)))
            && let Operand::Copy(src) | Operand::Move(src) = operand
        {
            let src_immediate: Arc<str> = Arc::from(self.root_ssa_base_name(src));
            let dst_base: Arc<str> = Arc::from(self.root_ssa_base_name(lhs));

            // #3159: Follow ptr_source_map chain transitively to find
            // the ultimate root (e.g., the original Box local). Without
            // this, unsized coercions like Box<T> → Box<dyn Trait> create
            // multi-hop chains where intermediate pointers are not in
            // heap_pointees, causing pointee_synthesis_fallback.
            let mut src_root = Arc::clone(&src_immediate);
            for _ in 0..8 {
                if let Some(next) = self.ptr_source_map.get(src_root.as_ref()) {
                    src_root = Arc::clone(next);
                } else {
                    break;
                }
            }

            let indirect_root = self
                .heap_pointees
                .keys()
                .find(|key| {
                    self.ptr_source_map.get(key.as_ref()).is_some_and(|info| info == &src_root)
                })
                .cloned();
            let found_value = self.recover_heap_value_from_base(src_root.as_ref()).or_else(|| {
                indirect_root.and_then(|key| {
                    debug!(
                        "#1210: propagating heap_pointees {} -> {} (from {})",
                        key, dst_base, src_root
                    );
                    self.recover_heap_value_from_base(key.as_ref())
                })
            });
            if let Some(heap_value) = found_value {
                debug!(
                    "#1210: Cast heap propagation: [{}] -> [{}] (root: {})",
                    src_immediate, dst_base, src_root
                );
                self.heap_pointees.insert(Arc::clone(&dst_base), heap_value);
            }
            if matches!(cast_kind, CastKind::PointerWithExposedProvenance) {
                // #3350: Integer-to-pointer cast has no allocation provenance.
                // Invalidate obj_valid so dereference checks can detect the
                // never-allocated address.
                let lhs_base_name = self.ssa_base_name(lhs);
                if let Some(ptr_expr) = self.env_lookup(&lhs_base_name).cloned() {
                    self.ctx.heap_invalidate_no_provenance(ptr_expr);
                }
            }
            self.ptr_source_map.insert(dst_base, src_root);
        }

        // #3159: For Transmute casts from raw pointer to Box/ADT, propagate heap_pointees.
        // After MIR inlining, Box::new uses Transmute(*mut T → Box<T>) instead of
        // ShallowInitBox. Without this propagation, the heap_pointees chain breaks
        // and deref of Box<dyn Trait> creates unconstrained symbolic variables.
        if matches!(cast_kind, CastKind::Transmute)
            && let Operand::Copy(src) | Operand::Move(src) = operand
            && matches!(target_ty.kind(), TyKind::RigidTy(RigidTy::Adt(..)))
        {
            if let Some(src_ty) = src.ty(self.body.locals()).into_option()
                && matches!(src_ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(..)))
            {
                let src_base: Arc<str> = Arc::from(self.root_ssa_base_name(src));
                let dst_base: Arc<str> = Arc::from(self.root_ssa_base_name(lhs));
                // Follow ptr_source_map chain to find ultimate allocation root.
                let mut src_root = Arc::clone(&src_base);
                for _ in 0..8 {
                    if let Some(next) = self.ptr_source_map.get(src_root.as_ref()) {
                        src_root = Arc::clone(next);
                    } else {
                        break;
                    }
                }
                if let Some(heap_val) = self.recover_heap_value_from_base(src_root.as_ref()) {
                    debug!(
                        "#3159: Transmute raw ptr→ADT: heap_pointees [{}] -> [{}] (root: {})",
                        src_base, dst_base, src_root
                    );
                    self.heap_pointees.insert(Arc::clone(&dst_base), heap_val);
                }
                self.ptr_source_map.insert(dst_base, src_root);
            }
        }
    }

    /// The ssa base name a borrow of `place` must use when `place`'s LAST
    /// projection is a `Field` that reads through a SORT-ERASED wrapper
    /// (`ManuallyDrop`/`MaybeUninit`/`NonZero`/…).
    ///
    /// Such a wrapper has no separate representation from its payload — see
    /// [`StatementCodegen::erased_wrapper_field_sort`] — so `&mut (w.N)` and
    /// `&mut w` name the SAME storage, and the borrow must inherit the wrapper's
    /// base name rather than the syntactic `..._field_N` that `ssa_base_name`
    /// would build.
    ///
    /// Two shapes, both exact (no approximation):
    /// * `(_w.N)` — the wrapper is a local, so the name is that local's.
    /// * `((*_r).N)` — the wrapper is `*_r`, whose storage the deref ladder already
    ///   names `ref_pointees[_r]`; that is the name to inherit.
    ///
    /// Anything else returns `None` and keeps the existing syntactic name.
    fn erased_wrapper_pointee_alias(&mut self, place: &Place) -> Option<Arc<str>> {
        let last = place.projection.len().checked_sub(1)?;
        let ProjectionElem::Field(field_idx, field_ty) = &place.projection[last] else {
            return None;
        };
        let wrapper = Place { local: place.local, projection: place.projection[..last].to_vec() };
        let wrapper_ty = wrapper.ty(self.body.locals()).into_option()?;
        Self::erased_wrapper_field_sort(wrapper_ty, *field_idx, *field_ty)?;

        match wrapper.projection.last() {
            None => Some(Arc::from(self.ssa_base_name(&wrapper))),
            Some(ProjectionElem::Deref) => {
                let ref_base = self.ssa_base_name_for_prefix(place, last - 1);
                self.ref_pointees.get(ref_base.as_str()).cloned()
            }
            _ => None,
        }
    }

    /// The CANONICAL ssa base name for a borrow whose referent place starts with
    /// a `Deref` of a reference local the deref ladder already resolves.
    ///
    /// `ssa_base_name` names the referent SYNTACTICALLY, after the reference
    /// local it was reached through: `&mut (*_98).0` becomes
    /// `main::local_98_deref_field_0`. Two different reference locals that alias
    /// the SAME storage (`_98`, `_99`, `_100` are all copies of the same
    /// `&mut NoCopy<u32>` argument) therefore get three UNRELATED env slots, and a
    /// store through one is invisible to a load through another — the
    /// `history/clone_pass` ensures read `ptr.0` from `local_100_deref_field_0`
    /// while `ptr.0 += 1` had written `local_99_deref_field_0`, so the post-state
    /// was unconstrained and a TRUE contract was reported FAILED. The same split
    /// makes the `modifies` footprint (recorded under a third name,
    /// `local_98_deref_field_0`) uncertifiable against its own store.
    ///
    /// The read path ALREADY canonicalizes: `codegen_place_deref_first` looks the
    /// reference local up in `ref_pointees` and resolves the referent from THAT
    /// base. This makes the borrow side agree, by rebuilding the name from the
    /// resolved pointee plus the remaining projections:
    /// `(*_98).0` with `ref_pointees[_98] = main::local_2` → `main::local_2_field_0`.
    ///
    /// SOUNDNESS: this only RENAMES a slot, and renames it to the name the read
    /// path already uses for the same storage — it merges two aliases of one
    /// location instead of keeping them separate, which removes stale reads; it
    /// never merges distinct locations, because the suffix is exactly the
    /// projection chain and the prefix is the mapping the deref ladder itself
    /// trusts. Restricted to `Field`/`Downcast` suffixes (a static offset into the
    /// referent); `Index`/`Subslice`/`OpaqueCast` decline and keep the old
    /// syntactic name. Declines to `None` whenever `ref_pointees` has no entry, so
    /// the previous behaviour stands.
    fn deref_pointee_alias(&mut self, place: &Place) -> Option<Arc<str>> {
        if !matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
            return None;
        }
        let ref_base = self.ssa_base_name_for_prefix(place, 0);
        let resolved = self.ref_pointees.get(ref_base.as_str()).cloned()?;
        let mut base = String::with_capacity(resolved.len() + 16 * place.projection.len());
        base.push_str(resolved.as_ref());
        for proj in &place.projection[1..] {
            match proj {
                ProjectionElem::Field(field, _) => {
                    let _ = write!(base, "_field_{field}");
                }
                ProjectionElem::Downcast(variant_idx) => {
                    let _ = write!(base, "_variant_{}", variant_idx.to_index());
                }
                _ => return None,
            }
        }
        Some(Arc::from(base))
    }

    /// Track reference pointees for Ref/AddressOf rvalues.
    ///
    /// When we see `_ref = &_pointee`, store the mapping. Also evaluates
    /// complex pointee places (with projections) and stores them in the env.
    pub(super) fn track_ref_pointees(&mut self, lhs: &Place, rhs: &Rvalue) {
        let (Rvalue::Ref(_, _, pointee_place) | Rvalue::AddressOf(_, pointee_place)) = rhs else {
            return;
        };
        let ref_base: Arc<str> = self.ssa_base_name(lhs).into();
        // #g4-erased-wrapper-payload: `&mut (wrapper.N)` where `.N` reads through
        // a SORT-ERASED wrapper borrows the wrapper's own storage, so it must
        // carry the wrapper's own ssa base name. The read side makes that
        // projection the identity (`apply_projection_chain`); if only the read
        // side knew, `*r = v` would land under `.._field_N` while the read still
        // saw the wrapper's slot — a lost write, i.e. a stale read that can PROVE
        // a false claim.
        let pointee_base: Arc<str> = match self.erased_wrapper_pointee_alias(pointee_place) {
            Some(alias) => alias,
            // #alias-split-on-deref-borrow: name the referent after the storage the
            // deref ladder resolves, not after the reference local it was reached
            // through. See `deref_pointee_alias`.
            None => match self.deref_pointee_alias(pointee_place) {
                Some(alias) => alias,
                None => self.ssa_base_name(pointee_place).into(),
            },
        };

        // #3013: a referent's concrete value normally lives only in the volatile
        // `current_env`; once a later block / phi rebuild / inline boundary
        // supersedes that entry, the deref ladder loses it and mints a fresh
        // UNCONSTRAINED symbolic (`synthesize_pointee_expr` — the
        // `pointee_synthesis_fallback` EncodingGap), which for an enum field drops
        // the active variant and trips the #3017 variant-0 fail-close → INCONCLUSIVE.
        // Publish the real value DURABLY into `heap_pointees` — the same store
        // `ensure_derived_pointee_in_env` recovers from on the slice::get path — so
        // the true value (with its variant + fields) survives supersession.
        //
        // SOUNDNESS — two gates, both required (`publishable`):
        //  (1) SHARED (`&`, not `&mut`) borrow only. A `&mut`/raw referent may be
        //      mutated in place, so a durable copy could be recovered stale.
        //  (2) The referent type must be provably FREEZE (no `UnsafeCell` → no
        //      interior mutability). This is essential: through a shared `&Cell`/
        //      `&RefCell`/`&Atomic` the referent IS mutated while the borrow is
        //      live, so a durable snapshot could go stale and — once env drops the
        //      entry — be recovered as a concrete-but-wrong value, PROVING an
        //      assertion that should fail (a FALSE PROOF). `definitely_freeze` is
        //      conservative (any type it cannot fully inspect → not publishable),
        //      so at worst we lose an improvement, never soundness.
        // With both gates the referent is immutable for the borrow, so the snapshot
        // cannot go stale. Recovery tries `env_lookup` FIRST (a fresher value always
        // wins); `heap_pointees` fires only on total env miss and returns the
        // identical, already-asserted term — it strictly REMOVES an
        // over-approximation and never fabricates a value.
        let publishable = matches!(
            rhs,
            Rvalue::Ref(_, bk, _) if matches!(bk, BorrowKind::Shared | BorrowKind::Fake(_))
        ) && pointee_place
            .ty(self.body.locals())
            .into_option()
            .is_some_and(|ty| Self::definitely_freeze(ty, 0));

        // If the pointee has complex projections, evaluate it and store in the env
        if !pointee_place.projection.is_empty() {
            debug!(
                "codegen_assign Ref/AddressOf: pointee_place={:?}, pointee_base={}",
                pointee_place, pointee_base
            );
            if let Some(pointee_expr) = self.codegen_place(pointee_place) {
                debug!(
                    "codegen_assign Ref: storing pointee_expr (sort={:?}) in env under {}",
                    pointee_expr.sort(),
                    pointee_base
                );
                if publishable {
                    self.heap_pointees.insert(Arc::clone(&pointee_base), pointee_expr.clone());
                }
                self.env_update(Arc::clone(&pointee_base), pointee_expr);
            } else {
                debug!(
                    "codegen_assign Ref: codegen_place returned None for {:?}, trying fallback",
                    pointee_place
                );
                if let Some(pointee_expr) =
                    self.ensure_derived_pointee_in_env(pointee_base.as_ref())
                {
                    debug!(
                        "codegen_assign Ref: fallback resolved {} (sort={:?})",
                        pointee_base,
                        pointee_expr.sort()
                    );
                } else {
                    debug!("codegen_assign Ref: fallback also failed for {}", pointee_base);
                }
            }
        } else if publishable {
            // Bare `&local` (no projections): the local's current concrete value —
            // e.g. an aggregate `DatatypeConstructor` for a locally-built struct
            // with a multi-variant enum field — also needs to survive env
            // supersession. Publish it durably under the same shared+freeze
            // soundness gates as the projection branch above.
            if let Some(pointee_expr) = self.env_lookup(pointee_base.as_ref()).cloned() {
                self.heap_pointees.insert(Arc::clone(&pointee_base), pointee_expr);
            }
        }

        debug!("codegen_assign Ref: ref_pointees insert {} -> {}", ref_base, pointee_base);
        self.ref_pointees.insert(ref_base, pointee_base);
    }

    /// Conservatively decide whether `ty` is definitely FREEZE — i.e. contains no
    /// `UnsafeCell` anywhere in its own representation, hence no interior
    /// mutability. Returns `true` ONLY when we are certain; any type we cannot
    /// fully inspect (unions, closures/coroutines, `dyn`, foreign, generic params,
    /// aliases) returns `false`.
    ///
    /// This is the soundness gate for the #3013 durable-recovery publish
    /// (`track_ref_pointees`): a stale snapshot of an interior-mutable referent
    /// (`&Cell`/`&RefCell`/`&Atomic`, mutated through the shared ref) could
    /// otherwise be recovered and produce a FALSE PROOF. Being conservative here
    /// can only cost an improvement (fall back to the sound `synthesize` path),
    /// never soundness. `UnsafeCell` is the sole primitive of interior mutability,
    /// so every interior-mutable type (`Cell`/`RefCell`/atomics/`Mutex`/`RwLock`)
    /// is rejected transitively via its `UnsafeCell` field. Pointers/references
    /// are Freeze: interior mutability *behind* a pointer lives in a different
    /// allocation, not in this value's bytes, so we stop the walk there.
    fn definitely_freeze(ty: Ty, depth: u32) -> bool {
        // Bound the walk (recursive types terminate at pointers, but guard anyway).
        if depth > 16 {
            return false;
        }
        let TyKind::RigidTy(rigid) = ty.kind() else {
            return false; // generic param / alias / bound: not certain
        };
        match rigid {
            RigidTy::Bool
            | RigidTy::Char
            | RigidTy::Int(_)
            | RigidTy::Uint(_)
            | RigidTy::Float(_)
            | RigidTy::Str
            | RigidTy::Never
            | RigidTy::FnDef(..)
            | RigidTy::FnPtr(_)
            // Pointer-like: the pointer's own bytes are Freeze; do not recurse
            // through it (the pointee is a separate allocation).
            | RigidTy::RawPtr(..)
            | RigidTy::Ref(..) => true,
            RigidTy::Array(elem, _) | RigidTy::Slice(elem) | RigidTy::Pat(elem, _) => {
                Self::definitely_freeze(elem, depth + 1)
            }
            RigidTy::Tuple(tys) => tys.into_iter().all(|t| Self::definitely_freeze(t, depth + 1)),
            RigidTy::Adt(def, args) => {
                // `UnsafeCell` is the root of all interior mutability.
                if def.trimmed_name() == "UnsafeCell" {
                    return false;
                }
                // Union fields overlap in memory and a union may hold an
                // interior-mutable member without it showing on the read path —
                // be conservative (also excludes e.g. `MaybeUninit`).
                if def.kind() == AdtKind::Union {
                    return false;
                }
                def.variants().into_iter().all(|v| {
                    v.fields()
                        .into_iter()
                        .all(|f| Self::definitely_freeze(f.ty_with_args(&args), depth + 1))
                })
            }
            // Foreign / Closure / Coroutine* / Dynamic / CoroutineWitness: opaque.
            _ => false,
        }
    }

    /// Positive dual of `definitely_freeze`: returns `true` iff an `UnsafeCell`
    /// is PROVABLY reachable in `ty`'s own representation — i.e. `ty` is
    /// interior-mutable. Any uncertainty (opaque / closure / coroutine / union /
    /// generic) returns `false`, so callers demote ONLY provably interior-mutable
    /// values (never over-demote). Pointers stop the walk: interior mutability
    /// *behind* a pointer is a separate allocation, not part of this value's
    /// bytes. `UnsafeCell` is the sole primitive of interior mutability, so
    /// `Cell`/`RefCell`/atomics/`Mutex`/`RwLock` are all detected via their
    /// `UnsafeCell` struct field. Guards failing-closed on an interior-mutable
    /// value merged across control flow (see `compute_phi_for_var`).
    pub(super) fn ty_contains_unsafe_cell(ty: Ty, depth: u32) -> bool {
        if depth > 16 {
            return false;
        }
        let TyKind::RigidTy(rigid) = ty.kind() else {
            return false; // generic param / alias / bound: not provably IM
        };
        match rigid {
            RigidTy::Adt(def, args) => {
                if def.trimmed_name() == "UnsafeCell" {
                    return true;
                }
                // A union may hold an interior-mutable member without it being
                // reachable on a given read path; do not CLAIM interior mutability
                // from a union (uncertain -> false; also avoids demoting the
                // common `MaybeUninit`, which would hurt unrelated merges).
                if def.kind() == AdtKind::Union {
                    return false;
                }
                def.variants().into_iter().any(|v| {
                    v.fields()
                        .into_iter()
                        .any(|f| Self::ty_contains_unsafe_cell(f.ty_with_args(&args), depth + 1))
                })
            }
            RigidTy::Array(elem, _) | RigidTy::Slice(elem) | RigidTy::Pat(elem, _) => {
                Self::ty_contains_unsafe_cell(elem, depth + 1)
            }
            RigidTy::Tuple(tys) => {
                tys.into_iter().any(|t| Self::ty_contains_unsafe_cell(t, depth + 1))
            }
            // Pointer-like stops the walk; scalars / opaque / generic: not IM.
            _ => false,
        }
    }

    /// Track Copy/Move of references and wrapper values that carry reference fields.
    ///
    /// Direct ref copies (`_new = move _old_ref`) propagate the pointee mapping.
    /// Composite wrapper copies (for example `Pin<&mut T>`) also copy nested
    /// `field_N -> pointee` metadata so later field extraction still resolves the
    /// inner reference target.
    ///
    /// `CopyForDeref(_ref)` is the same reference-value transfer in MIR; rustc
    /// uses it when building temporary refs for wrapper-peeling deref chains
    /// such as `Pin<&mut T>` resume paths.
    pub(super) fn track_copy_move_ref_pointees(&mut self, lhs: &Place, rhs: &Rvalue) {
        let src = match rhs {
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) | Rvalue::CopyForDeref(src) => src,
            _ => return,
        };
        let src_base = self.ssa_base_name(src);
        let dst_base: Arc<str> = self.ssa_base_name(lhs).into();

        self.propagate_nested_copy_move_ref_pointees(&dst_base, &src_base);

        if !self.ref_pointees.contains_key(src_base.as_str()) {
            self.ensure_ref_pointee_for_place(src);
        }
        if let Some(pointee) = self.ref_pointees.get(src_base.as_str()).cloned() {
            debug!(
                "codegen_assign Copy/Move/CopyForDeref: propagating ref {} -> {} (pointee={})",
                src_base, dst_base, pointee
            );
            self.ref_pointees.insert(Arc::clone(&dst_base), pointee);
        }
        // Propagate entry_map_bases and entry_keys for BTreeMap Entry operations
        if let (Some(map_base), Some(key)) = (
            self.entry_map_bases.get(src_base.as_str()).cloned(),
            self.entry_keys.get(src_base.as_str()).cloned(),
        ) {
            debug!(
                "codegen_assign Copy/Move/CopyForDeref: propagating entry {} -> {} (map_base={})",
                src_base, dst_base, map_base
            );
            self.entry_map_bases.insert(Arc::clone(&dst_base), map_base);
            self.entry_keys.insert(dst_base, key);
        }
        // Handle Copy/Move of dereferenced reference: `_new = copy *_ref` (#409)
        if let Some(ProjectionElem::Deref) = src.projection.first() {
            self.track_deref_copy_ref_pointees(lhs, src);
        }
    }

    pub(super) fn propagate_nested_copy_move_ref_pointees(
        &mut self,
        dst_base: &Arc<str>,
        src_base: &str,
    ) {
        let mut prefix = String::with_capacity(src_base.len() + 1);
        prefix.push_str(src_base);
        prefix.push('_');
        let range_start: Arc<str> = Arc::from(prefix.as_str());
        let nested_refs: Vec<_> = self
            .ref_pointees
            .range(range_start..)
            .take_while(|(key, _)| key.starts_with(prefix.as_str()))
            .map(|(key, pointee)| (Arc::clone(key), Arc::clone(pointee)))
            .collect();

        for (nested_key, nested_pointee) in nested_refs {
            let suffix = &nested_key[src_base.len()..];
            let mut dst_nested_key = String::with_capacity(dst_base.len() + suffix.len());
            dst_nested_key.push_str(dst_base);
            dst_nested_key.push_str(suffix);
            debug!(
                "codegen_assign Copy/Move/CopyForDeref: propagating nested ref {} -> {} (pointee={})",
                nested_key, dst_nested_key, nested_pointee
            );
            self.ref_pointees.insert(Arc::from(dst_nested_key), nested_pointee);
        }
    }

    /// Handle `_new = copy *_ref` — propagate ref-to-ref and closure field pointees.
    fn track_deref_copy_ref_pointees(&mut self, lhs: &Place, src: &Place) {
        let ref_base = crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), src.local);
        let Some(pointee_base) = self.ref_pointees.get(ref_base.as_str()).cloned() else {
            debug!("track_deref_copy: ref_pointees[{}] not found", ref_base);
            return;
        };

        // If the pointee is itself in ref_pointees, this is a ref-to-ref
        if let Some(pointee_pointee) = self.ref_pointees.get(pointee_base.as_ref()).cloned() {
            let dst_base = self.ssa_base_name(lhs);
            debug!(
                "codegen_assign Copy(*ref): {} -> {} (pointee_pointee={})",
                ref_base, dst_base, pointee_pointee
            );
            self.ref_pointees.insert(Arc::from(dst_base), pointee_pointee);
        }

        // #1582: Handle Copy/Move of dereferenced aggregate field
        if src.projection.len() > 1 {
            let mut resolved_pointee_path = String::from(pointee_base.as_ref());
            for proj in src.projection.iter().skip(1) {
                if let ProjectionElem::Field(field_idx, _) = proj {
                    let _ = write!(resolved_pointee_path, "_field_{}", field_idx);
                } else if let ProjectionElem::Downcast(variant_idx) = proj {
                    let _ = write!(resolved_pointee_path, "_variant_{}", variant_idx.to_index());
                }
            }
            if let Some(field_pointee) =
                self.ref_pointees.get(resolved_pointee_path.as_str()).cloned()
            {
                let dst_base = self.ssa_base_name(lhs);
                debug!(
                    "#1582: Copy(*ref).field resolved {} -> {} (pointee={})",
                    resolved_pointee_path, dst_base, field_pointee
                );
                self.ref_pointees.insert(Arc::from(dst_base), field_pointee);
            }
        }
    }

    /// Track constant references (#366): `_ref = const &0` needs synthetic pointee.
    pub(super) fn track_const_ref_pointees(&mut self, lhs: &Place, rhs: &Rvalue) {
        let Rvalue::Use(Operand::Constant(c)) = rhs else {
            return;
        };
        let const_ty = c.const_.ty();
        debug!("codegen_assign: constant type = {:?}", const_ty.kind());
        let TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, _)) = const_ty.kind() else {
            return;
        };
        debug!("codegen_assign: detected constant reference, pointee_ty = {:?}", pointee_ty.kind());
        let Some(pointee_expr) = self.try_codegen_const_ref_pointee(&c.const_, pointee_ty) else {
            debug!("codegen_assign: pointee_expr = None",);
            return;
        };
        debug!("codegen_assign: pointee_expr = {pointee_expr:?}");

        // Part of #2267: pre-allocate instead of format!().
        let pointee_base: Arc<str> = {
            use std::fmt::Write;
            let fn_name = self.ctx.current_fn_name();
            let mut s = String::with_capacity(fn_name.len() + 20);
            s.push_str(fn_name);
            s.push_str("::const_pointee_");
            let _ = write!(s, "{}", self.synthetic_pointee_counter);
            Arc::from(s)
        };
        self.synthetic_pointee_counter += 1;

        // Part of #2267: push_str instead of format!().
        let pointee_name = {
            let mut s = String::with_capacity(pointee_base.len() + 2);
            s.push_str(&pointee_base);
            s.push_str("_0");
            s
        };
        let pointee_sort = pointee_expr.sort().clone();
        let pointee_var = self.ctx.declare_var(&pointee_name, pointee_sort);
        self.assert_ssa_def(pointee_var.clone(), pointee_expr, &pointee_base);
        self.env_update(Arc::clone(&pointee_base), pointee_var);

        let ref_base = self.ssa_base_name(lhs);
        self.ref_pointees.insert(Arc::from(ref_base), pointee_base);
    }
}

// Ref-deref write propagation methods moved to codegen_assign_ref_deref.rs per #4206.
