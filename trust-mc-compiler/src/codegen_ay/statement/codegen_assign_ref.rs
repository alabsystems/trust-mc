// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Reference tracking and propagation (converted from include!() per #2595).
// Extracted from codegen_assign.rs (#2246): reference/pointee tracking,
// cast propagation, and constant reference handling.

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
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
            let dst_base: Arc<str> = self.ssa_base_name(lhs).into();
            if let Some(pointee) =
                self.ref_pointees.copy_entry(Arc::clone(&dst_base), src_base.as_str())
            {
                debug!(
                    "codegen_assign Cast: propagating ref {} -> {} (pointee={})",
                    src_base, dst_base, pointee
                );
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
                    let ptr_expr = self.box_pointer_value(&ptr_expr).unwrap_or(ptr_expr);
                    self.ctx.heap_invalidate_no_provenance(ptr_expr);
                    // FAIL-CLOSED, not exact: Rust gives this pointer the
                    // provenance of any previously EXPOSED allocation, and the
                    // model has no exposed set, so a legitimate
                    // expose-then-reconstruct round trip reads as a use after
                    // free. Such a failure is forced, never Genuine
                    // (transmute_provenance_repro.rs::
                    // provenance_roundtrip_CONTROL_failclosed). The invalidation
                    // only adds violations, so a proof stays clean.
                    self.ctx.bmc_sound_havoc("pointer_with_exposed_provenance");
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

    /// Does more than one statement or call assign the whole of `local`?
    ///
    /// `ref_pointees` and the aggregate-field entries derived from it are keyed
    /// by the ssa base name of a local, not by path. For a local that several
    /// producers assign (`let r = if b { &m } else { &n };`, or an aggregate
    /// built in both arms holding `&m` and `&n`), the map keeps whichever
    /// producer the encoder translated last, and every read through the local
    /// uses it on every path.
    pub(in crate::codegen_ay::statement) fn bmc_local_has_multiple_whole_definitions(
        &self,
        local: usize,
    ) -> bool {
        use rustc_public::mir::{StatementKind, TerminatorKind};
        let statements = self
            .body
            .blocks
            .iter()
            .flat_map(|block| &block.statements)
            .filter(|stmt| {
                matches!(
                    &stmt.kind,
                    StatementKind::Assign(lhs, _) if lhs.local == local && lhs.projection.is_empty()
                )
            })
            .take(2)
            .count();
        let calls = self
            .body
            .blocks
            .iter()
            .filter(|block| {
                matches!(
                    &block.terminator.kind,
                    TerminatorKind::Call { destination, .. }
                        if destination.local == local && destination.projection.is_empty()
                )
            })
            .take(2)
            .count();
        statements + calls > 1
    }

    /// Is every whole definition of `local` a borrow or address-of of one and
    /// the same place, which has no `Deref` projection? A call that assigns the
    /// local, any other rvalue, a second distinct place, or a place read through
    /// a pointer answers `false`.
    pub(in crate::codegen_ay::statement) fn bmc_local_whole_definitions_borrow_one_place(
        &self,
        local: usize,
    ) -> bool {
        use rustc_public::mir::{StatementKind, TerminatorKind};
        let assigned_by_call = self.body.blocks.iter().any(|block| {
            matches!(
                &block.terminator.kind,
                TerminatorKind::Call { destination, .. } if destination.local == local
            )
        });
        if assigned_by_call {
            return false;
        }
        let mut borrowed: Option<&Place> = None;
        for stmt in self.body.blocks.iter().flat_map(|block| &block.statements) {
            let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
            if lhs.local != local {
                continue;
            }
            if !lhs.projection.is_empty() {
                return false;
            }
            let (Rvalue::Ref(_, _, source) | Rvalue::AddressOf(_, source)) = rhs else {
                return false;
            };
            if source.projection.iter().any(|elem| matches!(elem, ProjectionElem::Deref)) {
                return false;
            }
            match borrowed {
                None => borrowed = Some(source),
                Some(first) if first == source => {}
                Some(_) => return false,
            }
        }
        borrowed.is_some()
    }

    /// May the pointer held by `ptr_local` address a stack local?
    ///
    /// Walks backward over EVERY producer of each local on the way: a borrow of
    /// a place that does not start with a deref answers `true`; copies, casts,
    /// reborrows through `*p`, aggregates and call arguments are followed;
    /// constants and arithmetic end a branch. Hitting the bound answers `true`.
    pub(in crate::codegen_ay::statement) fn bmc_pointer_may_address_stack_local(
        &self,
        ptr_local: usize,
    ) -> bool {
        use rustc_public::mir::{Operand, StatementKind, TerminatorKind};
        const MAX_VISITED: usize = 64;
        let operand_local = |op: &Operand| match op {
            Operand::Copy(p) | Operand::Move(p) => Some(p.local),
            _ => None,
        };
        let mut stack = vec![ptr_local];
        let mut seen = std::collections::HashSet::new();
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            if seen.len() > MAX_VISITED {
                return true;
            }
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                    if lhs.local != current || !lhs.projection.is_empty() {
                        continue;
                    }
                    match rhs {
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                            if matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
                                stack.push(place.local);
                            } else {
                                return true;
                            }
                        }
                        Rvalue::Use(op, ..) | Rvalue::Cast(_, op, _) => {
                            stack.extend(operand_local(op));
                        }
                        Rvalue::CopyForDeref(place) => stack.push(place.local),
                        Rvalue::Aggregate(_, operands) => {
                            stack.extend(operands.iter().filter_map(operand_local));
                        }
                        _ => {}
                    }
                }
                if let TerminatorKind::Call { destination, args, .. } = &block.terminator.kind
                    && destination.local == current
                {
                    stack.extend(args.iter().filter_map(operand_local));
                }
            }
        }
        false
    }

    /// The stack locals a pointer held by `ptr_local` may address, and whether
    /// the walk was complete (same walk as
    /// [`Self::bmc_pointer_may_address_stack_local`]).
    pub(in crate::codegen_ay::statement) fn bmc_stack_locals_pointer_may_address(
        &self,
        ptr_local: usize,
    ) -> (Vec<usize>, bool) {
        use rustc_public::mir::{Operand, StatementKind, TerminatorKind};
        const MAX_VISITED: usize = 64;
        let operand_local = |op: &Operand| match op {
            Operand::Copy(p) | Operand::Move(p) => Some(p.local),
            _ => None,
        };
        let mut candidates = Vec::new();
        let mut stack = vec![ptr_local];
        let mut seen = std::collections::HashSet::new();
        while let Some(current) = stack.pop() {
            if !seen.insert(current) {
                continue;
            }
            if seen.len() > MAX_VISITED {
                return (candidates, false);
            }
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                    if lhs.local != current || !lhs.projection.is_empty() {
                        continue;
                    }
                    match rhs {
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                            if matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
                                stack.push(place.local);
                            } else if !candidates.contains(&place.local) {
                                candidates.push(place.local);
                            }
                        }
                        Rvalue::Use(op, ..) | Rvalue::Cast(_, op, _) => {
                            stack.extend(operand_local(op));
                        }
                        Rvalue::CopyForDeref(place) => stack.push(place.local),
                        Rvalue::Aggregate(_, operands) => {
                            stack.extend(operands.iter().filter_map(operand_local));
                        }
                        _ => {}
                    }
                }
                if let TerminatorKind::Call { destination, args, .. } = &block.terminator.kind
                    && destination.local == current
                {
                    stack.extend(args.iter().filter_map(operand_local));
                }
            }
        }
        (candidates, true)
    }

    /// Does a value of `ty` own its bytes in place (no raw pointer, reference
    /// or pointer wrapper anywhere in it)? A byte copy into such a local changes
    /// the local itself; a copy through a pointer derived from a container that
    /// holds a pointer (a `Vec`, a `Box`) lands in the heap buffer instead.
    fn bmc_ty_owns_bytes_in_place(ty: Ty, depth: usize) -> bool {
        if depth == 0 {
            return false;
        }
        match ty.kind() {
            TyKind::RigidTy(
                RigidTy::Bool
                | RigidTy::Char
                | RigidTy::Int(_)
                | RigidTy::Uint(_)
                | RigidTy::Float(_),
            ) => true,
            TyKind::RigidTy(RigidTy::Array(elem, _)) => {
                Self::bmc_ty_owns_bytes_in_place(elem, depth - 1)
            }
            TyKind::RigidTy(RigidTy::Tuple(elems)) => {
                elems.iter().all(|elem| Self::bmc_ty_owns_bytes_in_place(*elem, depth - 1))
            }
            TyKind::RigidTy(RigidTy::Adt(def, args)) => match def.kind() {
                AdtKind::Union => false,
                AdtKind::Enum | AdtKind::Struct => def.variants_iter().all(|variant| {
                    variant.fields().iter().all(|field| {
                        mono_ty::field_ty(field, &args)
                            .is_some_and(|t| Self::bmc_ty_owns_bytes_in_place(t, depth - 1))
                    })
                }),
            },
            _ => false,
        }
    }

    /// A byte-level copy (`copy_nonoverlapping`, `copy`, `write_bytes`) into
    /// `dst` updates the memory image only; the ssa environment a read of a
    /// stack local consults keeps the old value. When `dst` may address a
    /// stack local that owns its bytes in place, the copy is kept and the
    /// harness is marked: `a.swap(0, 1)` on `[Option<u8>; 2]` left `a[0]` at
    /// its old value and the BMC lane proved `assert!(!(a[0] == None))`
    /// (tools/soundness-duals/negative/review_r25_intrinsic_write_fallbacks.rs).
    ///
    /// `writes_nothing` is set for a constant count of zero or a zero-sized
    /// element: the unroll then writes no byte, so the memory image and the
    /// ssa environment still agree and there is nothing to mark
    /// (dual_write_bytes_zero_count_noop.rs).
    pub(in crate::codegen_ay::statement) fn mark_byte_copy_into_stack_local(
        &mut self,
        dst: &Operand,
        writes_nothing: bool,
        intrinsic: &'static str,
    ) {
        if writes_nothing {
            return;
        }
        let (Operand::Copy(place) | Operand::Move(place)) = dst else {
            return;
        };
        if !place.projection.is_empty() {
            self.ctx.unsupported_with_fallback(intrinsic, "copy destination is a projected place");
            return;
        }
        // A pointer with a tracked pointee (`ptr::swap`'s parameters, bound by the
        // mini-inline to `&mut a[0]` and `&mut a[1]`) addresses storage the ssa
        // environment holds; the body-local walk below cannot see where a
        // parameter came from, and `a.swap(0, 1)` was not marked.
        let ptr_name =
            crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), place.local);
        let tracked_pointee = self.ref_pointees.contains_key(ptr_name.as_str());
        let (candidates, complete) = self.bmc_stack_locals_pointer_may_address(place.local);
        let in_place = candidates.iter().any(|&local| {
            self.body
                .locals()
                .get(local)
                .is_some_and(|decl| Self::bmc_ty_owns_bytes_in_place(decl.ty, 8))
        });
        if in_place || !complete || tracked_pointee {
            debug!(
                dst_local = place.local,
                ?candidates,
                complete,
                tracked_pointee,
                intrinsic,
                "byte copy may write a stack local (fail closed)"
            );
            self.ctx.unsupported_with_fallback(
                intrinsic,
                format!("copy through _{} may write a stack local in place", place.local),
            );
        }
    }

    /// A store through `*p` whose pointer has no tracked pointee writes a
    /// syntactic slot (or memory) that no read of the stack local it addresses
    /// consults, so that local keeps its old value. With the points-at facts
    /// of joined pointers withdrawn (`forget_joined_ref_pointees`), a write
    /// through `let r = if b { &mut m } else { &mut n };` is such a store:
    /// it is kept, and the harness is marked so it cannot come back clean.
    pub(in crate::codegen_ay::statement) fn mark_untracked_deref_store(&mut self, lhs: &Place) {
        if !matches!(lhs.projection.first(), Some(ProjectionElem::Deref)) {
            return;
        }
        let ref_base = crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), lhs.local);
        if self.ref_pointees.contains_key(ref_base.as_str()) {
            return;
        }
        if !self.bmc_pointer_may_address_stack_local(lhs.local) {
            return;
        }
        debug!(
            local = lhs.local,
            "deref store through a pointer with no tracked pointee (fail closed)"
        );
        self.ctx.unsupported_with_fallback(
            "deref_store_untracked_pointee",
            format!("store through _{} may address a stack local", lhs.local),
        );
    }

    /// After a whole-local write to `place`, drop the points-at entries rooted
    /// at its local when that local has several producers.
    ///
    /// The value of such a local is joined path-sensitively by the ssa env; the
    /// points-at map is not, so an entry would name one producer's referent on
    /// every path. Without the entry a read through the local takes the deref
    /// ladder over its own path-sensitive pointer value, or fails closed. The
    /// BMC lane proved `assert!(*h.r == Some(2))` for
    /// `let h = if b { H { r: &m } } else { H { r: &n } };` with `m = Some(1)`
    /// (tools/soundness-duals/negative/review_r17_aggregate_field_join.rs).
    pub(in crate::codegen_ay) fn forget_joined_ref_pointees(&mut self, place: &Place) {
        if !place.projection.is_empty()
            || !self.bmc_local_has_multiple_whole_definitions(place.local)
        {
            return;
        }
        // Several producers that all borrow the SAME deref-free place give the
        // local one address, hence one referent, on every path: the entry is
        // exact. Two `Pin::new(&mut coro).resume(())` calls reuse one temporary
        // for `&mut coro`; dropping its entry left every store into the
        // coroutine's fields untracked, and coroutine_dual_wrongfield.rs's safe
        // harnesses failed closed.
        if self.bmc_local_whole_definitions_borrow_one_place(place.local) {
            return;
        }
        let base = crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), place.local);
        // `RefPointees` has no `DerefMut`: withdrawal goes through the table's
        // own method, which keeps a withdrawn key's poison (downgraded to
        // unknown) so a join the table already refused cannot read clean.
        let removed = self.ref_pointees.forget_rooted_at(base.as_str());
        if removed != 0 {
            debug!(
                local = place.local,
                removed, "ref_pointees: dropped entries of a local with several producers"
            );
        }
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

        // The referent's ADDRESS, derived from the object it sits in, recorded
        // under the referent's own name.
        //
        // A REBORROW (`&raw const *r`, the shape `ptr::eq(&S3.a, &S3.b)` lowers
        // to) reaches `codegen_address_of` with the place `(*r)`, whose base name
        // is the referent `r` names — and `derived_place_address` could not place
        // that name inside any object, so `get_or_create_address_symbol` minted
        // an UNRELATED fresh symbol for it. Two fields of one `static` then
        // compared EQUAL and two borrows of ONE field compared UNEQUAL, both
        // `FAILED [AY:CTREX_CAT:Genuine]` on safe programs (fourth adversarial
        // review of m3/soundness-fixes-2, 2026-09-14, defect D8). Recording the
        // derived address here makes the reborrow find it. Never overwrites an
        // address already minted for the name.
        if !pointee_place.projection.is_empty()
            && !self.addr_symbols.contains_key(pointee_base.as_ref())
        {
            let pointee_ty = pointee_place.ty(self.body.locals()).into_option();
            if let Some(addr) = self.derived_place_address(pointee_place, pointee_ty) {
                debug!(
                    "codegen_assign Ref: recording the derived address of {} under its own name",
                    pointee_base
                );
                self.addr_symbols.insert(Arc::clone(&pointee_base), addr);
            }
        }

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
    pub(super) fn definitely_freeze(ty: Ty, depth: u32) -> bool {
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
                        .all(|f| {
                            mono_ty::field_ty(&f, &args)
                                .is_some_and(|t| Self::definitely_freeze(t, depth + 1))
                        })
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
                    v.fields().into_iter().any(|f| {
                        mono_ty::field_ty(&f, &args)
                            .is_none_or(|t| Self::ty_contains_unsafe_cell(t, depth + 1))
                    })
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

    /// Whether every `UnsafeCell` inside `ty` is reached through a chain of
    /// SINGLE-PAYLOAD ADTs — i.e. the interior-mutable payload has exactly ONE
    /// storage slot in this model, named after the outermost wrapper by
    /// `erased_wrapper_field_sort` on both the read and the write side.
    ///
    /// This is the precondition under which the interior-mutability read
    /// fail-close in `place_deref_first` may stand down. `Cell<T>` and
    /// `UnsafeCell<T>` qualify — and so does a user struct that wraps exactly one
    /// of them, which is the `InteriorMutability { x: Cell<u32> }` shape the
    /// contract corpus uses.
    ///
    /// `RefCell<T>` deliberately does NOT: it is `{ borrow: Cell<isize>, value:
    /// UnsafeCell<T> }`, two non-ZST fields, so the erased-wrapper identity
    /// refuses it and its payload keeps a separate `_field_1` name. MEASURED on
    /// `RefCell::new(7); c.replace_with(|&mut old| old + 2)`: the write escapes
    /// into `mem::replace::arg_pointee_1`, a SYNTHETIC slot minted by
    /// `init_reference_arguments` because the `&mut` reaches `mem::replace`
    /// through `RefMut`'s struct field and loses its `ref_pointees` link, while
    /// `as_ptr()` still reads `local_1_field_1`. `*c.as_ptr() == 7` is then
    /// unfalsifiable — the very stale read the havoc exists to stop. So
    /// multi-field interior-mutable wrappers keep failing closed, exactly as
    /// before, until that reference identity is repaired.
    ///
    /// FAIL-CLOSED: anything not positively recognised answers `false`, which only
    /// ever KEEPS the havoc.
    pub(super) fn unsafe_cell_is_single_payload(ty: Ty, depth: u32) -> bool {
        if depth > 16 {
            return false;
        }
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
            return false;
        };
        if def.trimmed_name() == "UnsafeCell" {
            return true;
        }
        if def.kind() != AdtKind::Struct {
            return false;
        }
        let variants = def.variants();
        let Some(variant) = variants.first() else {
            return false;
        };
        let mut payload = None;
        for f in variant.fields() {
            let Some(field_ty) = mono_ty::field_ty(&f, &args) else {
                return false;
            };
            if Self::layout_is_zst(field_ty) {
                continue;
            }
            if payload.is_some() {
                return false; // more than one non-ZST field: not single-payload
            }
            payload = Some(field_ty);
        }
        payload.is_some_and(|t| Self::unsafe_cell_is_single_payload(t, depth + 1))
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
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
            | Rvalue::CopyForDeref(src) => src,
            _ => return,
        };
        let src_base = self.ssa_base_name(src);
        let dst_base: Arc<str> = self.ssa_base_name(lhs).into();

        self.propagate_nested_copy_move_ref_pointees(&dst_base, &src_base);

        if !self.ref_pointees.has_entry(src_base.as_str()) {
            self.ensure_ref_pointee_for_place(src);
        }
        // A copy names the same storage on the same paths: carry the entry and
        // its poison, and read no pointee (`RefPointees::copy_entry`).
        if let Some(pointee) =
            self.ref_pointees.copy_entry(Arc::clone(&dst_base), src_base.as_str())
        {
            debug!(
                "codegen_assign Copy/Move/CopyForDeref: propagating ref {} -> {} (pointee={})",
                src_base, dst_base, pointee
            );
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
        for nested_key in self.ref_pointees.nested_keys(prefix.as_str()) {
            let suffix = &nested_key[src_base.len()..];
            let mut dst_nested_key = String::with_capacity(dst_base.len() + suffix.len());
            dst_nested_key.push_str(dst_base);
            dst_nested_key.push_str(suffix);
            if let Some(nested_pointee) = self
                .ref_pointees
                .copy_entry(Arc::from(dst_nested_key.as_str()), nested_key.as_ref())
            {
                debug!(
                    "codegen_assign Copy/Move/CopyForDeref: propagating nested ref {} -> {} (pointee={})",
                    nested_key, dst_nested_key, nested_pointee
                );
            }
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
        let Rvalue::Use(Operand::Constant(c), ..) = rhs else {
            return;
        };
        let const_ty = c.const_.ty();
        debug!("codegen_assign: constant type = {:?}", const_ty.kind());
        let TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, _)) = const_ty.kind() else {
            return;
        };
        debug!("codegen_assign: detected constant reference, pointee_ty = {:?}", pointee_ty.kind());
        self.premint_const_ref_targets(&c.const_);
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

        // The ADDRESS of a constant allocation is keyed on the ALLOCATION, not
        // on this borrow: two borrows of one static share it, two statics do
        // not. `derived_place_address` reads this to place `&S[i]` inside a
        // registered, disjoint object.
        if let Some(object) = Self::const_allocation_target(&c.const_) {
            self.const_pointee_objects.insert(Arc::clone(&pointee_base), object);
        }

        let ref_base = self.ssa_base_name(lhs);
        self.ref_pointees.insert(Arc::from(ref_base), pointee_base);
    }

    /// The pointer a reference constant holds: the relocation AT its byte 0
    /// (its target) and the byte offset its bytes carry, or `None` when no
    /// relocation starts there or the pointer bytes are not all initialized.
    ///
    /// The offset matters: `const R: &u32 = &S.1` points 4 bytes into `S`, and
    /// keying on the allocation alone placed `*R` at `S`'s base.
    fn const_allocation_target(
        mir_const: &rustc_public::ty::MirConst,
    ) -> Option<crate::codegen_ay::shared::const_pointer::ConstPtr> {
        use crate::codegen_ay::shared::const_pointer::{self, ConstRead};
        const_pointer::const_bytes(mir_const)?.stored_pointer(0)
    }
}

// Ref-deref write propagation methods moved to codegen_assign_ref_deref.rs per #4206.
