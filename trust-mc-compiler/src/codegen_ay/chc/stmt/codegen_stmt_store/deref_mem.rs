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
/// Not blessed: an element store through a pointer into an array that is a
/// union's field; the union's other views are not updated.
pub(in crate::codegen_ay::chc) const DEREF_ELEM_STORE_THROUGH_UNION: &str =
    "deref_elem_store_through_union";

/// Whether `ty` is a union.
fn ty_is_union(ty: rustc_public::ty::Ty) -> bool {
    use rustc_public::ty::{AdtKind, RigidTy, TyKind};
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Adt(def, _)) if def.kind() == AdtKind::Union)
}

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

/// Single-writer MIR summary of one local's defining rvalue.
///
/// The address-provenance walk needs the same handful of shapes over and over;
/// summarising them once per body keeps each hop O(1) instead of rescanning
/// every block (that rescan made a contract harness spend ~30s in codegen).
/// `None` in the table means "not written exactly once by an unprojected
/// assignment", which is the walk's existing bail condition.
#[derive(Clone, Debug)]
pub(in crate::codegen_ay::chc) enum ProvDef {
    /// `_x = copy _y`
    CopyLocal(usize),
    /// `_x = &_y` / `_x = &raw _y`, no projections
    RefLocal(usize),
    /// `_x = &(*_y)` / `_x = &raw (*_y)` — a bare reborrow. The borrow of a
    /// pointer's own pointee has the SAME address value as the pointer, so the
    /// question "which local does this address?" transfers to `_y` unchanged.
    RefDeref(usize),
    /// `_x = &_y.f` — the walk cannot follow a projected borrow
    RefProjected,
    /// `_x = copy (_y.i)`
    CopyField(usize, usize),
    /// `_x = copy (*_y)`
    CopyDeref(usize),
    /// `_x = copy ((*_y).i)`
    CopyDerefField(usize, usize),
    /// Any aggregate; `tuple1` marks the one-element tuple closure-call
    /// inlining builds. Operands are the unprojected copy/move source locals.
    Aggregate { tuple1: bool, operands: Vec<Option<usize>> },
    /// Anything else the walk refuses to cross.
    Unsupported,
}

fn summarize_provenance_rvalue(rhs: &rustc_public::mir::Rvalue) -> ProvDef {
    use rustc_public::mir::{AggregateKind, Operand, Rvalue};

    let operand_local = |op: &Operand| match op {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
        _ => None,
    };

    match rhs {
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..) => match p.projection.as_slice() {
            [] => ProvDef::CopyLocal(p.local),
            [ProjectionElem::Field(idx, _)] => ProvDef::CopyField(p.local, *idx),
            [ProjectionElem::Deref] => ProvDef::CopyDeref(p.local),
            [ProjectionElem::Deref, ProjectionElem::Field(idx, _)] => {
                ProvDef::CopyDerefField(p.local, *idx)
            }
            _ => ProvDef::Unsupported,
        },
        Rvalue::Ref(_, _, p) | Rvalue::AddressOf(_, p) => match p.projection.as_slice() {
            [] => ProvDef::RefLocal(p.local),
            [ProjectionElem::Deref] => ProvDef::RefDeref(p.local),
            _ => ProvDef::RefProjected,
        },
        Rvalue::Aggregate(kind, operands) => ProvDef::Aggregate {
            tuple1: matches!(kind, AggregateKind::Tuple) && operands.len() == 1,
            operands: operands.iter().map(operand_local).collect(),
        },
        _ => ProvDef::Unsupported,
    }
}

/// Build the per-local summary table for `body`.
pub(in crate::codegen_ay::chc) fn build_provenance_defs(
    body: &rustc_public::mir::Body,
) -> Vec<Option<ProvDef>> {
    use rustc_public::mir::StatementKind;

    let n = body.locals().len();
    let mut counts = vec![0usize; n];
    let mut defs: Vec<Option<ProvDef>> = vec![None; n];
    for bb_data in &body.blocks {
        for stmt in &bb_data.statements {
            let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                continue;
            };
            let local: usize = lhs.local;
            if local >= n {
                continue;
            }
            counts[local] += 1;
            if lhs.projection.is_empty() {
                defs[local] = Some(summarize_provenance_rvalue(rhs));
            }
        }
    }
    // More than one writer (branch merge, reassignment, or a projected write
    // into the same local) makes the provenance path-dependent.
    for (local, def) in defs.iter_mut().enumerate() {
        if counts[local] != 1 {
            *def = None;
        }
    }
    defs
}

/// The byte offset of field `idx` of variant `variant` in an enum's layout.
fn layout_variant_field_offset(
    ty: rustc_public::ty::Ty,
    variant: usize,
    idx: usize,
) -> Option<u64> {
    let layout = ty.layout().ok()?;
    let rustc_public::abi::VariantsShape::Multiple { variants, .. } = &layout.shape().variants
    else {
        return None;
    };
    match &variants.get(variant)?.fields {
        rustc_public::abi::FieldsShape::Arbitrary { offsets } => {
            offsets.get(idx).map(|offset| offset.bytes() as u64)
        }
        _ => None,
    }
}

/// Byte offset of field `idx` from the start of a `ty` value, from rustc's layout.
fn layout_field_offset(ty: rustc_public::ty::Ty, idx: usize) -> Option<u64> {
    let layout = ty.layout().ok()?;
    match layout.shape().fields {
        rustc_public::abi::FieldsShape::Arbitrary { offsets } => {
            offsets.get(idx).map(|offset| offset.bytes() as u64)
        }
        _ => None,
    }
}

/// Whether `tail`, applied under a dereference of a `ty`-typed pointer, adds
/// zero bytes: fields at offset 0 only, with no second dereference, index or
/// downcast.
pub(in crate::codegen_ay::chc) fn projection_tail_at_offset_zero(
    mut ty: rustc_public::ty::Ty,
    tail: &[ProjectionElem],
) -> bool {
    for elem in tail {
        let ProjectionElem::Field(idx, field_ty) = elem else {
            return false;
        };
        if layout_field_offset(ty, *idx) != Some(0) {
            return false;
        }
        ty = *field_ty;
    }
    true
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Whether `projections` (starting with `Deref`) address the first byte of the
    /// object `base_local` points to: every projection after the leading `Deref` is a
    /// struct field at byte offset 0. Anything else (a nonzero field offset, a
    /// downcast, an index, a second deref) names a different address inside or
    /// beyond that object, which an object id cannot carry.
    pub(in crate::codegen_ay::chc) fn projections_after_leading_deref_add_zero_bytes(
        &self,
        base_local: usize,
        projections: &[ProjectionElem],
    ) -> bool {
        let Some(mut current_ty) = self
            .body
            .locals()
            .get(base_local)
            .and_then(|decl| Self::deref_pointee_ty(self.resolve_body_ty(decl.ty)))
        else {
            return false;
        };
        for projection in projections.iter().skip(1) {
            match projection {
                ProjectionElem::Field(field_idx, field_ty) => {
                    if crate::kani_middle::abi::LayoutOf::new(current_ty).field_offset(*field_idx)
                        != Some(0)
                    {
                        return false;
                    }
                    current_ty = *field_ty;
                }
                _ => return false,
            }
        }
        true
    }

    /// Whether `obj_id` is a heap allocation: neither a local's own slot nor a
    /// global object (a static, a promoted constant).
    pub(in crate::codegen_ay::chc) fn obj_id_is_heap_allocation(&self, obj_id: u32) -> bool {
        self.heap_state.local_idx_for_obj_id(obj_id).is_none()
            && !self.ref_resolution.global_objects.values().any(|object| object.obj_id == obj_id)
    }

    /// Whether `local`'s recorded allocation is a STACK slot (a local's own object).
    pub(in crate::codegen_ay::chc) fn local_holds_stack_slot_address(&self, local: usize) -> bool {
        self.known_alloc_ids
            .get(&local)
            .is_some_and(|&obj_id| self.heap_state.local_idx_for_obj_id(obj_id).is_some())
    }

    /// Whether reading `projs` out of a `ty` value yields `ty`'s own bits: every
    /// field starts at byte 0 and is as large as its parent, so the parent carries
    /// nothing else at runtime (`Box` -> `Unique` -> `NonNull` -> `*const T`). A
    /// `(p, q)` pair fails the size test: its first field is not the whole pair.
    ///
    /// A `Downcast(v)` followed by `Field(i, F)` reads variant `v`'s field `i`,
    /// under the same test against `v`'s own field layout: an enum whose tag is
    /// a niche of that field (`Result<NonNull<[u8]>, AllocError>`'s `Ok` payload)
    /// carries nothing else, so the payload read is the enum's bits. MIR reads
    /// a variant's field only on the path where the value is that variant.
    pub(in crate::codegen_ay::chc) fn field_chain_is_transparent(
        mut ty: rustc_public::ty::Ty,
        projs: &[ProjectionElem],
    ) -> bool {
        let mut elems = projs.iter();
        while let Some(elem) = elems.next() {
            let (offset, field_ty) = match elem {
                ProjectionElem::Field(idx, field_ty) => (layout_field_offset(ty, *idx), *field_ty),
                ProjectionElem::Downcast(variant) => {
                    let Some(ProjectionElem::Field(idx, field_ty)) = elems.next() else {
                        return false;
                    };
                    (layout_variant_field_offset(ty, variant.to_index(), *idx), *field_ty)
                }
                _ => return false,
            };
            let (Ok(parent), Ok(field)) = (ty.layout(), field_ty.layout()) else {
                return false;
            };
            let parent_size = parent.shape().size.bytes();
            let field_size = field.shape().size.bytes();
            if offset != Some(0) || parent_size != field_size {
                return false;
            }
            ty = field_ty;
        }
        true
    }

    /// Recover the allocation whose BASE a pointer local's value addresses.
    ///
    /// Callers mint `obj_id ++ 0` from the answer (the deref store below,
    /// `ptr::write`/`ptr::read`, receiver memory) or record it in
    /// `known_alloc_ids`, whose entries carry an implicit offset of zero. So a
    /// hop may only cross an assignment that keeps the pointer VALUE unchanged:
    /// a copy or value-preserving cast of the whole local or of a transparent
    /// wrapper field (`Box` -> `Unique` -> `NonNull` -> `*const T`), a reborrow
    /// `&(*p)` narrowed at most to fields at byte offset 0, `ShallowInitBox`, a
    /// wrapper aggregate with one runtime operand, a load through a pointer that
    /// provably holds `&_L` (the loaded value is `_L`'s), and the identity calls
    /// that return their argument's base pointer. It never crosses a borrow of a
    /// local's own slot (`&x` addresses `x`, while `known_alloc_ids` for `x`
    /// names what `x` points to), a field at a nonzero offset, a second
    /// dereference, any other load, pointer arithmetic, a write through or into
    /// the local, or a local with several producers. Each of those answers
    /// `None`, and the caller keeps the pointer's own symbolic value, which is
    /// the exact encoding.
    ///
    /// Every one of those crossings produced a false proof: `&mut (*b).b`
    /// traced to the box and stored `*pb = 9` into field `a`
    /// (`negative/box_new_payload.rs::mut_scalar_through_ref_must_fail`
    /// SUCCESSFUL), `copy (pair.1)` inherited the tuple's first pointer, a
    /// pointer loaded out of a box inherited the box that held it, and
    /// `*r = q` with `r = &mut p` wrote `q` into the object `p` pointed to.
    ///
    /// Part of #3589: identity calls are crossed so that Rc::new chains
    /// (exchange_malloc → Box::into_raw → NonNull::from → from_inner_in)
    /// preserve alloc_id even when blocks are processed out of execution order.
    pub(in crate::codegen_ay::chc) fn trace_deref_store_alloc_id(
        &self,
        local_idx: usize,
    ) -> Option<u32> {
        let mut current_local = local_idx;
        let mut seen = std::collections::HashSet::from([current_local]);

        for _ in 0..12 {
            // An allocation id recorded for a local with several producers names
            // only the producer translated last (see `scan_mir_for_alloc_source`).
            if self.local_has_multiple_whole_definitions(current_local) {
                return None;
            }
            if let Some(&obj_id) = self.known_alloc_ids.get(&current_local) {
                return Some(obj_id);
            }
            // Every hop below reads the ONE producer of `current_local`; with
            // several producers a flow-insensitive walk names one path's object.
            if self.local_has_multiple_whole_definitions(current_local) {
                return None;
            }
            let next = self
                .base_preserving_ref_target_source(current_local)
                .or_else(|| self.scan_mir_for_alloc_source(current_local))
                .or_else(|| self.scan_identity_call_arg(current_local))?;
            if !seen.insert(next) {
                return None;
            }
            current_local = next;
        }

        None
    }

    /// `ref_targets[local] = (t, [Deref, tail..])` names the place `(*t).tail`:
    /// `local` holds `t`'s pointer value plus the tail's byte offset, so only a
    /// tail at offset 0 without a further dereference keeps the base address.
    /// `(t, [])` names `t`'s own slot, not the allocation `t` points to.
    fn base_preserving_ref_target_source(&self, local: usize) -> Option<usize> {
        let target = self.ref_resolution.ref_targets.get(&local)?;
        let [ProjectionElem::Deref, tail @ ..] = target.projections.as_slice() else {
            return None;
        };
        if tail.is_empty() {
            return Some(target.local);
        }
        let pointee = Self::deref_pointee_ty(self.body.locals().get(target.local)?.ty)?;
        // Both reviews' guards, conjoined: the branch's layout walk over the tail
        // and main's `projections_after_leading_deref_add_zero_bytes` over the
        // whole projection. Either refusing refuses the hop.
        (projection_tail_at_offset_zero(pointee, tail)
            && self.projections_after_leading_deref_add_zero_bytes(
                target.local,
                &target.projections,
            ))
        .then_some(target.local)
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
                if destination.local != target_local || !destination.projection.is_empty() {
                    continue;
                }
                let callee = self.resolve_callee_path(func)?;
                if !Self::is_alloc_identity_callee(&callee)
                    || !Self::identity_callee_returns_base_address(&callee)
                {
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
        // NonNull's data-pointer accessors: `as_ptr`, and `NonNull<[T]>`'s
        // `as_non_null_ptr` / `as_mut_ptr`, return the address the NonNull holds.
        || (path.contains("ptr::NonNull")
            && (path.ends_with("::as_ptr")
                || path.ends_with("::as_non_null_ptr")
                || path.ends_with("::as_mut_ptr")))
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

    /// SECOND WITNESS for the ADDRESS-used-as-VALUE defect that
    /// `deref_load_referent_local` describes, for the bodies whose reference
    /// flow the MIR walk cannot follow.
    ///
    /// `deref_load_referent_local` answers the question from MIR alone, so it
    /// goes silent the moment the pointer reaches this load through a cast or a
    /// multiply-assigned local. A `#[kani::ensures]` closure is exactly that
    /// shape: its captured `&mut Box<u32>` arrives as `_p = copy ((*_env).0)`
    /// after a `&Closure` cast, so the walk returns `None`, the generic
    /// `src_local_for_alloc` arm copies the POINTER's alloc_id onto the loaded
    /// VALUE, and the `Box -> Unique -> NonNull -> *const T` extraction then
    /// mints `bv32(slot)++bv32(0)` for the payload address — a memory cell no
    /// rule ever writes at that type, so `**ptr < 101` is refutable against a
    /// correct contract.
    ///
    /// The encoder already holds the missing fact under a different name.
    /// `ref_targets[ptr_local] == (_L, [])` is its own record that the place
    /// `*ptr_local` IS the place `_L` — the very fact `translate_place_with_deref`
    /// uses to translate THIS load into a read of `_L`'s register. So the
    /// loaded value is `_L`'s VALUE, and the allocation it points into is
    /// whatever `_L`'s value points into (`known_alloc_ids[_L]`) — never `_L`'s
    /// own slot. Deriving provenance from the same map that resolved the load
    /// adds no assumption: were `ref_targets` wrong here, the load would
    /// already be reading the wrong local.
    ///
    /// Three conditions keep this to the defect's exact shape:
    /// - `projection == [Deref]` — a BARE `*_p`. With a trailing field
    ///   (`(*_p).f`) the loaded value is `_L.f`, whose allocation is not
    ///   `known_alloc_ids[_L]`, so that shape must not reach this rule.
    /// - the recorded alloc_id for `ptr_local` is exactly `_L`'s own STACK SLOT
    ///   object. A pointer already carrying a heap alloc_id is a genuine
    ///   Box/Rc/NonNull chain and keeps its existing inheritance.
    /// - the answer is a referent LOCAL, not an address. The caller forwards
    ///   `known_alloc_ids[_L]` and FAILS CLOSED (drops the destination's
    ///   alloc_id) when the referent has none, rather than substituting the
    ///   slot id it happens to be holding.
    fn deref_load_ref_target_referent_local(
        &self,
        ptr_local: usize,
        projection: &[ProjectionElem],
    ) -> Option<usize> {
        if !matches!(projection, [ProjectionElem::Deref]) {
            return None;
        }
        let &obj_id = self.known_alloc_ids.get(&ptr_local)?;
        let slot_local = self.heap_state.local_idx_for_obj_id(obj_id)?;
        let target = self.ref_resolution.ref_targets.get(&ptr_local)?;
        if !target.projections.is_empty() || target.local != slot_local {
            return None;
        }
        debug!(
            ptr_local,
            obj_id,
            slot_local,
            "GUARD4262_REF_TARGET_FIRED: deref load through a pointer whose ref_target \
             is its own referent slot"
        );
        Some(slot_local)
    }

    /// The referent whose VALUE a deref load through `ptr_local` yields, from
    /// either witness.
    ///
    /// Both witnesses answer the same question — "is `*ptr_local` the place
    /// `_L`, so that the loaded value is `_L`'s value rather than an address
    /// into `_L`?" — one from MIR, one from the encoder's own `ref_targets`.
    /// Kept separate from `deref_load_referent_local` so the MIR-only witness,
    /// which also drives Deref PLACE resolution in `codegen_expr_deref_resolve`,
    /// keeps its exact current meaning there.
    pub(in crate::codegen_ay::chc) fn deref_load_value_referent_local(
        &self,
        ptr_local: usize,
        projection: &[ProjectionElem],
    ) -> Option<usize> {
        self.deref_load_referent_local(ptr_local)
            .or_else(|| self.deref_load_ref_target_referent_local(ptr_local, projection))
    }

    /// Bounded backward walk answering "does `ptr_local` provably hold
    /// `&_target` with no projections?".
    fn ptr_provably_addresses_local(&self, ptr_local: usize, target: usize) -> bool {
        self.mir_provable_referent_local(ptr_local) == Some(target)
    }

    /// Bounded backward walk answering "which local's slot does `ptr_local`
    /// provably hold the address of?".
    ///
    /// Follows only unprojected `Use(Copy|Move)` wrappers and the
    /// single-element argument tuple that closure-call inlining introduces, so
    /// it never crosses a load, a cast, an offset, or a field projection, and
    /// it requires every local on the chain to be written exactly once so the
    /// answer is path-independent. Any other shape answers `None`.
    ///
    /// This is a pure MIR fact — no encoding state is consulted — so the
    /// declaration pass may use it to seed `ref_targets` for a pointer that
    /// never appears as `_p = &_L` in this body (a `&result` reaching a
    /// contract closure arrives through a capture tuple instead).
    pub(in crate::codegen_ay::chc) fn mir_provable_referent_local(
        &self,
        ptr_local: usize,
    ) -> Option<usize> {
        self.mir_provable_referent_local_at(ptr_local, 0)
    }

    fn mir_provable_referent_local_at(&self, ptr_local: usize, depth: usize) -> Option<usize> {
        // Two of the hops below re-enter this walk on a different pointer.
        if depth > 3 {
            return None;
        }
        if let Some(memo) = self.provenance_walk_memo.borrow().get(&(ptr_local, depth)) {
            return *memo;
        }
        let answer = self.mir_provable_referent_local_uncached(ptr_local, depth);
        self.provenance_walk_memo.borrow_mut().insert((ptr_local, depth), answer);
        answer
    }

    fn mir_provable_referent_local_uncached(
        &self,
        ptr_local: usize,
        depth: usize,
    ) -> Option<usize> {
        let defs = self.provenance_defs.get_or_init(|| build_provenance_defs(self.body));
        let mut current = ptr_local;
        for _ in 0..8 {
            match defs.get(current)?.as_ref()? {
                ProvDef::CopyLocal(src) => current = *src,
                ProvDef::RefLocal(target) => return Some(*target),
                // `_x = &(*_y)` is a reborrow: `_x` and `_y` hold the SAME
                // address, so the walk continues on `_y` with the question
                // unchanged. `#[kani::ensures]` capture lowering builds exactly
                // this shape (`_cap = &(*_arg)`), and without the hop the walk
                // stops at `RefProjected`, the deref-load through the capture
                // keeps the referent SLOT's alloc_id, and `**ptr` in the
                // post-state reads the `Box` local's own stack cell — a column
                // no rule ever writes.
                ProvDef::RefDeref(src) => current = *src,
                // Closure-call inlining packs the callee's arguments into a
                // one-element tuple and then binds the callee's parameter to
                // the tuple local itself (`_p = move (_arg,)`, later read as
                // `*_p`). The tuple has exactly one field, so `_p`'s value IS
                // that field's value — the same identification the alloc_id
                // `Aggregate` arm in `propagate_alloc_ids_for_assign` already
                // makes when it hands `_p` this obj_id in the first place.
                // Without the hop the walk stops here and a `&Enum`/`&*const T`
                // ensures-closure parameter keeps the referent SLOT's obj_id,
                // so `*result` reads the slot's own object instead of the
                // pointer value stored in it (one deref level short).
                ProvDef::Aggregate { tuple1: true, operands } => {
                    current = (*operands.first()?)?;
                }
                // A contract closure reads its captured reference back out of
                // the capture aggregate: `_p = copy (_clo.0)`. The field's
                // value IS the operand the aggregate was built from, so hop to
                // that operand — the same (local, field) -> source
                // identification `collect_aggregate_field_sources` makes for
                // `ref_targets`. Without the hop the walk stops at a projected
                // copy and `_d = copy (*_p)` inherits the CAPTURE's alloc_id,
                // so `**ptr` in a `requires` reads the `Box`'s own stack slot
                // as a `u32` (a cell no rule writes) instead of the heap value.
                ProvDef::CopyField(base, field_idx) => {
                    current = self.aggregate_field_source_local(*base, *field_idx)?;
                }
                // `_p = copy (*_q)` copies the VALUE held by whatever `_q`
                // addresses. When `_q` provably addresses `_L`, `_p` and `_L`
                // hold the SAME value, so the question "what does this pointer
                // address?" transfers to `_L` unchanged.
                ProvDef::CopyDeref(base) => {
                    current = self.mir_provable_referent_local_at(*base, depth + 1)?;
                }
                // Same as the two hops above, composed: `_p = copy ((*_q).i)`
                // reads field `i` out of the local `_q` addresses. The
                // `ensures` closure reaches its captured `&mut Box` this way.
                ProvDef::CopyDerefField(base, field_idx) => {
                    let owner = self.mir_provable_referent_local_at(*base, depth + 1)?;
                    current = self.aggregate_field_source_local(owner, *field_idx)?;
                }
                ProvDef::RefProjected
                | ProvDef::Aggregate { tuple1: false, .. }
                | ProvDef::Unsupported => return None,
            }
        }
        None
    }

    /// Which local's value was placed in field `field_idx` of the aggregate
    /// that defines `local`?
    ///
    /// Follows unprojected `Use(Copy|Move)` wrappers to the single aggregate
    /// construction, then reads that field's operand. Every local on the path
    /// must be written exactly once, so the answer is path-independent — the
    /// same gate the surrounding walk uses.
    fn aggregate_field_source_local(&self, local: usize, field_idx: usize) -> Option<usize> {
        self.aggregate_field_source_chain(local, field_idx).map(|(_, source)| source)
    }

    /// [`Self::aggregate_field_source_local`], with the owners the walk passed
    /// through: `local` first, then each local a `CopyLocal` hop reached, the
    /// last one being the aggregate itself.
    fn aggregate_field_source_chain(
        &self,
        local: usize,
        field_idx: usize,
    ) -> Option<(Vec<usize>, usize)> {
        let defs = self.provenance_defs.get_or_init(|| build_provenance_defs(self.body));
        let mut current = local;
        let mut owners = Vec::new();
        for _ in 0..8 {
            owners.push(current);
            match defs.get(current)?.as_ref()? {
                ProvDef::CopyLocal(src) => current = *src,
                ProvDef::Aggregate { operands, .. } => {
                    return Some((owners, (*operands.get(field_idx)?)?));
                }
                _ => return None,
            }
        }
        None
    }

    /// May the pointer held by `ptr_local` address a local that has its own
    /// state (a state variable or flattened field slots)?
    ///
    /// Walks backward over EVERY producer of each local on the way, statements
    /// and call destinations alike, so the answer covers every path: a borrow of
    /// such a local (`&mut L`, `&raw mut L`, `&L.f`) answers `true`; copies,
    /// casts, reborrows through `*p`, aggregates and call arguments are followed;
    /// constants and arithmetic end a branch. Hitting the bound answers `true`.
    pub(in crate::codegen_ay::chc) fn pointer_may_address_stack_local(
        &self,
        ptr_local: usize,
    ) -> bool {
        let (candidates, complete) = self.stack_locals_pointer_may_address(ptr_local);
        !candidates.is_empty() || !complete
    }

    /// The locals with their own state (a state variable or flattened field
    /// slots) that the pointer held by `ptr_local` may address, and whether the
    /// walk was complete.
    ///
    /// Same backward walk as [`Self::pointer_may_address_stack_local`], over
    /// EVERY producer of each local on the way: a borrow of such a local
    /// (`&mut L`, `&raw mut L`, `&L.f`) contributes `L`; copies, casts,
    /// reborrows through `*p`, aggregates and call arguments are followed;
    /// constants and arithmetic end a branch. `complete` is false when the
    /// visit bound was hit, in which case the list may be missing candidates.
    pub(in crate::codegen_ay::chc) fn stack_locals_pointer_may_address(
        &self,
        ptr_local: usize,
    ) -> (Vec<usize>, bool) {
        use rustc_public::mir::{Operand, Rvalue, StatementKind, TerminatorKind};

        const MAX_VISITED: usize = 64;
        let has_state = |local: usize| {
            self.try_state_idx_for_local(local).is_some()
                || self.flatten.flattened_tuple_locals.contains(&local)
        };
        let operand_local = |op: &Operand| match op {
            Operand::Copy(p) | Operand::Move(p) => Some(p.local),
            _ => None,
        };
        let mut candidates: Vec<usize> = Vec::new();
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
                            } else if has_state(place.local) && !candidates.contains(&place.local)
                            {
                                candidates.push(place.local);
                            }
                        }
                        // A pointer loaded out of a field of the aggregate the
                        // base pointer provably addresses holds the operand the
                        // aggregate took there, not an address of the aggregate:
                        // follow that operand.
                        Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..)
                        | Rvalue::CopyForDeref(place)
                            if self.loaded_pointer_field_source(place).is_some() =>
                        {
                            stack.extend(self.loaded_pointer_field_source(place));
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

    /// The identity callees whose result is the argument's pointer VALUE, not
    /// merely a pointer into the same allocation: `add`/`sub` move the offset,
    /// and `Rc`/`Arc::into_raw` return the payload, which sits after the
    /// reference counts.
    fn identity_callee_returns_base_address(path: &str) -> bool {
        let moves_offset = path.ends_with("::add") || path.ends_with("::sub");
        let returns_payload =
            ["alloc::rc::Rc", "std::rc::Rc", "alloc::sync::Arc", "std::sync::Arc"]
                .iter()
                .any(|prefix| path.starts_with(prefix));
        !moves_offset && !returns_payload
    }

    /// The local whose pointer value the one producer of `target_local` copies
    /// bit-for-bit (see `trace_deref_store_alloc_id` for the hops it crosses).
    fn scan_mir_for_alloc_source(&self, target_local: usize) -> Option<usize> {
        use rustc_public::mir::{CastKind, Operand, Rvalue, StatementKind};

        // The scan returns the FIRST assignment in block order. For a local that
        // several statements or calls assign (`let r = if b { &mut m } else
        // { &mut n };`) that is one producer, and the allocation it names is
        // wrong on every path through another: a write through a copy of `r`
        // landed in `m`'s cell on the path that took `&mut n`.
        if self.local_has_multiple_whole_definitions(target_local) {
            return None;
        }
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                    continue;
                };
                // `(*_p) = v` stores THROUGH `_p` and `_p.f = v` into it; neither
                // produces `_p`'s pointer value.
                if lhs.local != target_local || !lhs.projection.is_empty() {
                    continue;
                }
                return match rhs {
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
                    | Rvalue::CopyForDeref(src) => self.value_preserving_read_source(src),
                    Rvalue::Cast(
                        CastKind::PtrToPtr
                        | CastKind::Transmute
                        | CastKind::PointerCoercion(_)
                        | CastKind::PointerExposeAddress
                        | CastKind::PointerWithExposedProvenance
                        | CastKind::Subtype,
                        Operand::Copy(src) | Operand::Move(src),
                        _,
                    ) => self.value_preserving_read_source(src),
                    #[cfg(not(trust_toolchain))]
                    Rvalue::ShallowInitBox(Operand::Copy(src) | Operand::Move(src), _)
                        if src.projection.is_empty() =>
                    {
                        Some(src.local)
                    }
                    Rvalue::Aggregate(kind, operands) => {
                        self.pick_alloc_operand(target_local, kind, operands)
                    }
                    Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                        let [ProjectionElem::Deref, tail @ ..] = place.projection.as_slice() else {
                            return None;
                        };
                        if tail.is_empty() {
                            return Some(place.local);
                        }
                        let pointee =
                            Self::deref_pointee_ty(self.body.locals().get(place.local)?.ty)?;
                        // Both sides' guards again (see
                        // `base_preserving_ref_target_source`).
                        (projection_tail_at_offset_zero(pointee, tail)
                            && self.projections_after_leading_deref_add_zero_bytes(
                                place.local,
                                &place.projection,
                            ))
                        .then_some(place.local)
                    }
                    _ => None,
                };
            }
        }
        None
    }

    /// The local holding the same pointer value a read of `src` yields: `src`'s
    /// own local for a whole-local or transparent-wrapper read, or the referent
    /// `_L` for a load through a pointer that provably holds `&_L`. Any other
    /// load yields a pointer stored in memory, which is not the pointer that
    /// addressed it.
    fn value_preserving_read_source(&self, src: &Place) -> Option<usize> {
        match src.projection.as_slice() {
            [] => Some(src.local),
            [ProjectionElem::Deref, rest @ ..] => {
                // Main's rule (`local_holds_stack_slot_address`) said: when the
                // pointer names a STACK slot the loaded value is that slot's
                // CONTENT, never a pointer into the slot's own object, so the hop
                // must stop. This walk is stricter and stops on EVERY load whose
                // referent it cannot name, stack slot or not.
                let referent = self.deref_load_referent_local(src.local)?;
                if rest.is_empty() {
                    return Some(referent);
                }
                let referent_ty = self.body.locals().get(referent)?.ty;
                if Self::field_chain_is_transparent(referent_ty, rest) {
                    return Some(referent);
                }
                // One field of the aggregate the referent was built as: the
                // field holds the operand the aggregate took there
                // (`HM { n, p: &mut *bx }`, then `copy (*_r).p`).
                self.pointer_field_value_source(referent, rest)
            }
            fields => {
                let base_ty = self.body.locals().get(src.local)?.ty;
                Self::field_chain_is_transparent(base_ty, fields).then_some(src.local)
            }
        }
    }

    /// The local whose value a pointer-typed field of `owner` holds: `rest` is
    /// one `Field(i, T)` with `T` a reference or raw pointer, and `owner` is
    /// written once, by an aggregate whose operand `i` is a whole local
    /// (`aggregate_field_source_local`). A pointer stored into the field
    /// later (`h.p = &mut y`, `*q = H { .. }`) fails closed where it is
    /// stored (`pointer_stored_into_aggregate_rebinds_target`,
    /// `pointer_stored_through_deref_rebinds_target`); a write of the field's
    /// bytes that is not a pointer store (`*(addr_of_mut!(h.p) as *mut usize)
    /// = ..`, a byte copy over `h`) is refused here
    /// (`pointer_field_bytes_may_be_rewritten`). So the operand is the field's
    /// value whenever a proof or certified counterexample can rest on it.
    ///
    /// The check covers every owner on the copy chain, not only the final
    /// one: `let h2 = h;` copies the bytes `h` holds at that point, so an
    /// untyped rewrite of `h.p` before the copy changes `h2.p` as well. And
    /// it covers the operand local itself: `a` rewritten before
    /// `HR { p: a, .. }` is built (a `usize` store through
    /// `addr_of_mut!(a)`, `mem::swap(&mut a, ..)`, a byte copy) no longer
    /// holds the value its single definition gave it. Checking only the final
    /// owner placed `*h2.p = 7` on the old referent, and four safe programs
    /// were certified Genuine (review of fix/chc-lost-writes round 6,
    /// 2026-09-27).
    fn pointer_field_value_source(&self, owner: usize, rest: &[ProjectionElem]) -> Option<usize> {
        use rustc_public::ty::{RigidTy, TyKind};
        let [ProjectionElem::Field(field_idx, field_ty)] = rest else { return None };
        if !matches!(field_ty.kind(), TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))) {
            return None;
        }
        let (owners, source) = self.aggregate_field_source_chain(owner, *field_idx)?;
        for &hop in &owners {
            if self.local_has_multiple_whole_definitions(hop)
                || self.pointer_field_bytes_may_be_rewritten(hop, *field_idx)
            {
                return None;
            }
        }
        // The operand is usually a temporary copied from the local the
        // program named (`_9 = copy _5; HR { p: move _9, .. }`): every local
        // on that copy chain carries the operand's value.
        let defs = self.provenance_defs.get_or_init(|| build_provenance_defs(self.body));
        let mut carrier = source;
        for _ in 0..8 {
            if self.local_has_multiple_whole_definitions(carrier)
                || self.local_bytes_may_be_rewritten(carrier)
            {
                return None;
            }
            match defs.get(carrier).and_then(Option::as_ref) {
                Some(ProvDef::CopyLocal(from)) => carrier = *from,
                _ => break,
            }
        }
        Some(source)
    }

    /// For a read `copy (*q).f` of a pointer-typed field of the aggregate `q`
    /// provably addresses, the local that field was built from
    /// (`pointer_field_value_source`).
    fn loaded_pointer_field_source(&self, place: &Place) -> Option<usize> {
        let [ProjectionElem::Deref, rest @ ..] = place.projection.as_slice() else {
            return None;
        };
        let owner = self.deref_load_referent_local(place.local)?;
        self.pointer_field_value_source(owner, rest)
    }

    /// The operand whose value IS the aggregate's pointer value: the data
    /// pointer of a raw-pointer aggregate, or the one runtime operand of an
    /// aggregate no larger than that operand (a pointer wrapper). A `(p, q)`
    /// pair has no single base address, whichever operand carries an alloc_id.
    fn pick_alloc_operand(
        &self,
        aggregate_local: usize,
        kind: &rustc_public::mir::AggregateKind,
        operands: &[rustc_public::mir::Operand],
    ) -> Option<usize> {
        use rustc_public::mir::{AggregateKind, Operand};

        let unprojected_local = |op: &Operand| match op {
            Operand::Copy(src) | Operand::Move(src) if src.projection.is_empty() => Some(src.local),
            _ => None,
        };
        if matches!(kind, AggregateKind::RawPtr(..)) {
            return operands.first().and_then(unprojected_local);
        }
        let locals = self.body.locals();
        let size_of =
            |ty: rustc_public::ty::Ty| ty.layout().ok().map(|layout| layout.shape().size.bytes());
        let mut runtime =
            operands.iter().filter(|op| op.ty(locals).ok().and_then(size_of) != Some(0));
        let only = runtime.next()?;
        if runtime.next().is_some() {
            return None;
        }
        let aggregate_size = size_of(locals.get(aggregate_local)?.ty)?;
        let operand_size = only.ty(locals).ok().and_then(size_of)?;
        if aggregate_size != operand_size {
            return None;
        }
        unprojected_local(only)
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
            // A ref_target that names an ELEMENT (`let p = &mut a[1]`) with
            // FIELDS after the dereference (`p.x = 9`) belongs to the Reg-level
            // handler too: it selects the element, applies the field update and
            // stores it back, while the Mem store here lands in typed memory
            // that no read of `a[1].x` consults — the write was lost and
            // `assert!(a[1].x == 0)` verified SUCCESSFUL.
            let target_is_element = ref_target.projections.iter().any(|p| {
                matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. })
            });
            let tail_is_fields_only = lhs.projection.len() > 1
                && lhs.projection[1..]
                    .iter()
                    .all(|p| matches!(p, ProjectionElem::Field(..) | ProjectionElem::Downcast(_)));
            // Nor when the ref_target names a heap OWNER (a `Vec`, `String`, ...)
            // and the pointer points to something else: `Vec::as_mut_ptr`'s
            // pointer takes the Vec local as its ref_target, but its stores
            // land in the buffer, where the Mem-level read below takes them
            // back. The Reg-level handler took `*v.as_mut_ptr() = 5` as a
            // narrower store into the Vec handle and havocked the handle, so
            // a later `*p` read the old buffer cell: `let y = *p; assert!(y ==
            // 1)` after a copy of 5 into `p` was proved where Kani fails it
            // (third review of round 10 of fix/chc-false-certificates,
            // `a04_bug_moved_copy_dst_then_read`).
            let foreign_heap_owner = self.ref_target_is_foreign_heap_owner(local_idx);
            if has_state
                && !has_offset
                && !drills_heap_pointer
                && !foreign_heap_owner
                && (proj_1 || (target_is_element && tail_is_fields_only))
            {
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
            let booked = self.diagnostics.book_store_dropped();
            self.overapproximate_memory_store_target(booked, projected_store_ty, None);
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
                    let booked = self.diagnostics.book_store_dropped();
                    self.overapproximate_memory_store_target(booked, projected_store_ty, None);
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
                let booked = self.diagnostics.book_store_dropped();
                self.overapproximate_memory_store_target(booked, projected_store_ty, None);
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

        // A store reaches a borrowed local's STATE only through a single-producer
        // points-at edge (`ref_targets`, mirrored below) or the argument-pointee
        // lane. With neither, it lands in typed memory alone, and a local the
        // pointer may address keeps its old value: after `r.take()` through
        // `let r = if b { &mut m } else { &mut n };`, `n.is_some()` still read
        // `true` and --ay-chc proved it. No precise per-path update is available
        // here, so such a store fails closed: the harness cannot come back clean.
        //
        // A pointer the single-producer trace above resolved to a HEAP object
        // addresses that object on every path: the store is placed there
        // (`ptr_expr`), and no local's state mirrors heap memory. The
        // may-address walk follows a load `copy (*_p).f` as `_p` itself, so a
        // box's data pointer read through `&mut b` (`Box::as_mut`,
        // `&mut **b`) looked like `b`'s own address. That shape used to pass
        // only because a value-of edge onto the box's `NonNull` field stood
        // in for a points-at edge (`drop_pointer_field_value_of_edges`).
        let trace_names_heap_object =
            trace_result.is_some_and(|obj_id| self.obj_id_is_heap_allocation(obj_id));
        if !self.ref_resolution.ref_targets.contains_key(&local_idx)
            && !self.ref_resolution.ref_arg_pointee_idx.contains_key(&local_idx)
            && !trace_names_heap_object
            && self.pointer_may_address_stack_local(local_idx)
        {
            debug!(
                local_idx,
                "CHC: deref store through a pointer that may address a borrowed local, \
                 with no resolved target (fail closed)"
            );
            self.record_sound_fallback_reason("deref_store_stack_target_unresolved");
        }

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
            // Whether a Field step selected a field of a union: an array reached
            // that way shares its bytes with the union's other fields.
            let mut through_union = false;

            let tail_len = lhs.projection.len() - 1;
            for (tail_pos, proj) in lhs.projection[1..].iter().enumerate() {
                match proj {
                    ProjectionElem::Field(field_idx, field_ty) => {
                        drop_store_ty = *field_ty;
                        if ty_is_union(self.resolve_body_ty(current_ty)) {
                            through_union = true;
                        }
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
                    ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }
                        if tail_pos + 1 == tail_len
                            && active_variant.is_none()
                            && !self.ref_resolution.ref_targets.contains_key(&local_idx)
                            && !self
                                .ref_resolution
                                .ref_arg_pointee_idx
                                .contains_key(&local_idx)
                            && !self
                                .ref_resolution
                                .collection_mut_refs
                                .contains_key(&local_idx) =>
                    {
                        // The element of an array no register lane holds (a
                        // `Box`'s payload, memory behind a raw pointer): the
                        // Reg-level handler answers only a pointer with a
                        // register referent, and the store used to reach the
                        // projection fallback, which havocked the pointer and
                        // lost the write (`deref_elem_store.rs`).
                        //
                        // An array that is a union's field (`(*b).h[i] = v` on a
                        // `Box<union { x: u32, h: [u16; 2] }>`) shares its bytes
                        // with the union's other fields, and the element store
                        // below writes only the element's views: a later read of
                        // the union, whole or through the same element, selects
                        // the union's own object view (its region array, decoded
                        // by field) and returned the value from before the store.
                        // `b.h[1] = 0xAAAA; assert!(b.h[1] == 0x0102)` was a clean
                        // proof where Kani fails it, and `b.x == 0x0102_AAAA`
                        // after `b.h[0] = 0xAAAA` a certified counterexample
                        // (review of fix/chc-false-certificates round 1,
                        // 2026-10-14: `rv_union3.rs`, the same on main). The store
                        // fails closed.
                        if through_union {
                            debug!(
                                ?lhs,
                                "CHC: element store through a pointer into a union's array field (fail closed)"
                            );
                            let booked =
                                self.record_sound_fallback_reason(DEREF_ELEM_STORE_THROUGH_UNION);
                            self.overapproximate_memory_store_target(booked, current_ty, None);
                            return true;
                        }
                        let ptr_expr = if ptr_expr.sort().is_int() {
                            ptr_expr.int2bv(POINTER_WIDTH)
                        } else {
                            ptr_expr
                        };
                        let array_addr = if total_offset > 0 {
                            ptr_expr.bvadd(Expr::bitvec_const(total_offset as i64, POINTER_WIDTH))
                        } else {
                            ptr_expr
                        };
                        if self.try_store_array_element_through_pointer(
                            lhs, array_addr, current_ty, proj, rhs_expr, acc,
                        ) {
                            return true;
                        }
                        debug!(
                            ?proj,
                            "CHC: deferring Deref+Index store to Reg-level handler (#3041)"
                        );
                        return false;
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
                let booked = self.diagnostics.book_store_dropped();
                self.overapproximate_memory_store_target(booked, drop_store_ty, None);
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
                let booked = self.diagnostics.book_store_dropped();
                self.overapproximate_memory_store_target(booked, drop_store_ty, None);
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
            // A whole-pointee store `*p = v` starts at the pointer; a field
            // store's displacement is not carried here.
            let displacement = (lhs.projection.len() == 1).then_some(0);
            let mut checks =
                self.provenance_deref_bound_checks(&addr_expr, store_ty, local_idx, displacement);
            // A pointer a wrapping step may have moved out of a heap allocation
            // (heap/stack_address.rs).
            if checks.is_empty() {
                checks = self.wrapping_deref_checks(&addr_expr, store_ty, local_idx, acc.modified);
            }
            self.push_pending_checks_dedup(checks);
        }

        // The memory store and the static route below are ONE routed store:
        // the route updates or havocs the state of a static the store lands
        // in (`decl::static_path::StaticImageWrites`).
        self.begin_static_store_routing();
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

        // D7(b): a store whose address const-folds into a static the harness
        // keeps a state variable for writes that state variable too, along the
        // static place path (`decl::static_path`), so a read of the static
        // through its state variable sees it.
        let routed_static =
            !skip_memory_store && self.route_exact_static_store_stmt(&addr_expr, store_ty, rhs_expr, acc);
        self.end_static_store_routing();

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
        } else if let Some(ref_target) =
            self.ref_resolution.ref_targets.get(&local_idx).cloned()
            && let Some(offset) = self.ref_resolution.subslice_offset.get(&local_idx).cloned()
        {
            // OFFSET case, narrowed. The guard above exists because MIRRORING a
            // store through an offset pointer would overwrite the target
            // local's state variable — corrupting e.g. a Vec's fld_ptr with the
            // stored value. That hazard belongs to `mirror_scalar_ref_store`,
            // which is still skipped here.
            //
            // The ARRAY-LANE write is a different operation: it stores into one
            // element of an array-sorted state variable and cannot touch a
            // pointer field. Skipping it too meant `a.as_mut_ptr().add(2)`
            // wrote only into the address-indexed `mem` array, which nothing
            // reads — so the pruner deleted the store entirely and
            // `assert!(a[2] == 0)` was PROVED after writing 9.
            //
            // Gated on the target's state var actually being an ARRAY, so a Vec
            // or struct target still takes the old path untouched.
            let is_array_target = self
                .try_state_idx_for_local(ref_target.local)
                .and_then(|idx| self.state_var_mgr.state_vars.get(idx))
                .is_some_and(|(_, sort)| sort.is_array());
            // The index is `subslice_offset`, counted in the POINTER's pointee:
            // an element of the array only when that pointee is the element
            // type. `a.as_mut_ptr() as *mut u8` stepped by `add(3)` wrote a u8
            // into element 3 of a `[u16; 2]` (third review of
            // fix/chc-false-certificates, 2026-09-27: `u8_add_into_u16arr_safe`
            // FAILED certified Genuine and its `should_panic` twin passed, on
            // main and the branch).
            let element_typed = Place {
                local: ref_target.local,
                projection: ref_target.projections.clone(),
            }
            .ty(self.body.locals())
            .ok()
            .and_then(|referent| self.get_array_element_ty(self.resolve_body_ty(referent)))
            .is_some_and(|elem| self.resolve_body_ty(elem) == self.resolve_body_ty(store_ty));
            if is_array_target && !element_typed {
                // A narrower store whose byte offset the pointer's definition
                // chain establishes is the array's memory image with those
                // bytes spliced in (`ref_store_reinterpretation`); anything
                // else fails closed.
                let reinterpretation = self.ref_store_reinterpretation(
                    &ref_target,
                    lhs,
                    rhs_expr,
                    local_idx,
                    acc.modified,
                );
                use super::deref_mem_mirror::RefStoreReinterpretation;
                if matches!(reinterpretation, RefStoreReinterpretation::OutOfBounds) {
                    self.record_block_violation(
                        Expr::bool_const(true),
                        super::deref_mem_mirror::OUT_OF_BOUNDS_MESSAGE,
                    );
                    return true;
                }
                let spliced = matches!(
                    reinterpretation,
                    RefStoreReinterpretation::Converted(_)
                        | RefStoreReinterpretation::ConvertedLocal(_)
                );
                if spliced {
                    self.mirror_scalar_ref_store(
                        &ref_target,
                        lhs,
                        rhs_expr,
                        local_idx,
                        store_ty,
                        acc,
                    );
                } else {
                    debug!(
                        local_idx,
                        target = ref_target.local,
                        "CHC: offset deref store of another type than the array's element fails closed"
                    );
                    self.havoc_local_fail_closed(
                        ref_target.local,
                        "offset_store_not_element_typed",
                        acc,
                    );
                }
            } else if is_array_target
                && !self.element_offset_metadata_agrees(
                    local_idx,
                    &ref_target,
                    self.get_type_size(store_ty)
                        .and_then(|b| i128::try_from(b).ok())
                        .unwrap_or(-1),
                    Self::const_usize_from_expr(&offset).and_then(|o| i128::try_from(o).ok()),
                )
            {
                // The element index is the offset metadata, which counts
                // element steps from the target's start. A byte step (or a step
                // of a pointer to another type) before them makes it the wrong
                // index, and a chain the definition walk cannot follow leaves
                // it unchecked: `p.byte_add(2).add(1)` wrote element 1 of a
                // `[u16; 4]` (fourth review of fix/chc-false-certificates:
                // `eo_byte_add_then_add_bug`, a clean proof on main and the
                // branch). The target's register image is left free.
                debug!(
                    local_idx,
                    target = ref_target.local,
                    "CHC: offset deref store whose metadata its definition chain does not confirm fails closed"
                );
                self.havoc_local_fail_closed(
                    ref_target.local,
                    "offset_store_metadata_unconfirmed",
                    acc,
                );
            } else if is_array_target {
                debug!(
                    local_idx,
                    target = ref_target.local,
                    "CHC: offset deref store -> indexed array lane update"
                );
                self.emit_ref_target_array_update_indexed(
                    &ref_target,
                    rhs_expr,
                    local_idx,
                    bb_idx,
                    acc,
                    Some(offset),
                );
            } else {
                // The target's value lives in a register or a collection model
                // (a Vec's data array), which this store never reaches:
                // `*v.as_mut_ptr().add(3) = 5; assert!(v[3] == 0)` was PROVED from
                // the model's stale element. Nothing may rest on those reads.
                debug!(
                    local_idx,
                    target = ref_target.local,
                    "CHC: offset deref store into a non-array target fails closed"
                );
                self.record_sound_fallback_reason("offset_store_target_unsynced");
            }
        }
        if self.ref_resolution.ref_arg_pointee_idx.contains_key(&local_idx) {
            let _ = self.handle_deref_store_via_ref_targets(lhs, rhs_expr.clone(), local_idx, acc);
            return true;
        }

        // The store above reached TYPE-INDEXED MEMORY only. That is exact when the
        // referent lives in memory too — a traced allocation, a parameter's
        // pointee, a ref_target that the mirror block just updated. When the
        // pointer's referent is none of those, the model has no idea WHICH object
        // was written, and a read of the object through its register/state-var
        // representation still returns the old value: `let r: &mut [u8] = &mut a;
        // if let Some(x) = r.first_mut() { *x = 9; } assert!(a[0] == 1)` verified
        // SUCCESSFUL and its safe twin certified a Genuine counterexample
        // (negative/ref_index_ops.rs, main 31793ccc3) — the `&mut u8` came back
        // from a call, so nothing bound it to `a`'s element.
        //
        // Fail closed: the harness can still report a counterexample, but not a
        // certified one, and it can no longer report a clean proof.
        if self.ref_resolution.ref_targets.get(&local_idx).is_none()
            && trace_result.is_none()
            && !routed_static
            && !self.ref_resolution.collection_mut_refs.contains_key(&local_idx)
        {
            debug!(
                local_idx,
                ?lhs,
                "CHC: deref store through an unresolved referent — fail closed"
            );
            self.record_sound_fallback_reason("deref_store_referent_unresolved");
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

    /// `NonNull`'s data-pointer accessors return the address it holds; a
    /// method that merely shares a name elsewhere does not.
    #[test]
    fn alloc_identity_callee_recognizes_nonnull_data_pointer_accessors() {
        for path in [
            "core::ptr::NonNull::<u8>::as_ptr",
            "core::ptr::NonNull::<[u8]>::as_non_null_ptr",
            "core::ptr::NonNull::<[u8]>::as_mut_ptr",
        ] {
            assert!(ChcCtx::<'_, '_>::is_alloc_identity_callee(path), "{path}");
        }
        assert!(!ChcCtx::<'_, '_>::is_alloc_identity_callee("alloc::vec::Vec::<u8>::as_ptr"));
    }
}
