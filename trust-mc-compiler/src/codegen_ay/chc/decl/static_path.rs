// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The static place path (D6): which part of a static's STATE VARIABLE the
//! bytes `[k, k + size_of(P))` of the static are.
//!
//! `shared::const_pointer` states the rule: a constant pointer into a static
//! S at offset k with pointee P names S's bytes at k, and a live static's
//! pointee is the lane's LIVE state there. In the CHC lane a static's live
//! state is its state variable, a value of S's type, so the bytes at k are a
//! path of field selections and constant array indices into that value,
//! decided by rustc's layout (`LayoutOf::field_offset`, reordered layouts
//! included). A path exists only when the window is exactly one field or
//! element (nested to any depth); an enum, a union, padding, or a window that
//! straddles two fields has none, and the caller fails closed.
//!
//! Before this, a constant pointer into a static was the WHOLE static
//! whatever its offset, and a store through a pointer into a static never
//! reached its state variable: `*PP = 7; assert!(MP[1] == 2)` for
//! `static mut PP: *mut u32 = &raw mut MP[1]` PROVED.

use crate::codegen_ay::chc::codegen_ctx::ExactVar;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::Expr;
use rustc_public::ty::{RigidTy, Ty, TyKind};

use std::cell::OnceCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::codegen_ay::types::POINTER_WIDTH;
use crate::kani_middle::abi::LayoutOf;

use tracing::{debug, warn};

use super::ChcCtx;
use super::codegen_types::CodegenTypes;
use crate::codegen_ay::chc::FieldProjection;

/// One step of a static place path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) enum StaticPathElem {
    /// Field `i` of a single-variant struct or a tuple.
    Field(usize),
    /// Element `i` of an array.
    Index(u64),
}

/// Whether two types are the same up to regions: a constant `&&'erased [u32]`
/// names a `static SLS: &'static [u32]` WHOLE, although the two `Ty`s differ.
pub(in crate::codegen_ay::chc) fn same_ty_modulo_regions(a: Ty, b: Ty) -> bool {
    if a == b {
        return true;
    }
    rustc_middle::ty::tls::with(|tcx| {
        let a = rustc_public::rustc_internal::internal(tcx, a);
        let b = rustc_public::rustc_internal::internal(tcx, b);
        tcx.erase_and_anonymize_regions(a) == tcx.erase_and_anonymize_regions(b)
    })
}

/// The path from a CHC value of type `s_ty` to its part occupying bytes
/// `[k, k + size_of(p))`, read at type `p`, as the encoding's sorts nest: a
/// layer the encoding collapses onto its one field (`encoded_as_its_field`)
/// has no step. `None` when no such part exists.
pub(in crate::codegen_ay::chc) fn static_path(
    s_ty: Ty,
    k: u64,
    p: Ty,
) -> Option<Vec<StaticPathElem>> {
    let mut path = Vec::new();
    static_path_into(s_ty, k, p, &mut path, 16, true)?;
    Some(path)
}

/// [`static_path`] as the TYPES nest: every field step, a collapsed layer
/// included. Rule B's object path (`object_path_projections`) builds MIR
/// places and field types from it, and its consumers apply the collapse
/// themselves; with the collapsed steps dropped, `PM.m` (`ManuallyDrop<Q2>`)
/// stood for its `Q2` (`test_rule_b_object_path`).
pub(in crate::codegen_ay::chc) fn static_type_path(
    s_ty: Ty,
    k: u64,
    p: Ty,
) -> Option<Vec<StaticPathElem>> {
    let mut path = Vec::new();
    static_path_into(s_ty, k, p, &mut path, 16, false)?;
    Some(path)
}

fn static_path_into(
    ty: Ty,
    k: u64,
    p: Ty,
    path: &mut Vec<StaticPathElem>,
    depth: usize,
    collapse: bool,
) -> Option<()> {
    let depth = depth.checked_sub(1)?;
    if k == 0 && same_ty_modulo_regions(ty, p) {
        return Some(());
    }
    let p_size = LayoutOf::new(p).size_of()? as u64;
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Array(elem, len)) => {
            let len = len.eval_target_usize().ok()?;
            let size = LayoutOf::new(elem).size_of()? as u64;
            if size == 0 {
                return None;
            }
            let index = k / size;
            let rest = k % size;
            if index >= len || rest + p_size > size {
                return None;
            }
            path.push(StaticPathElem::Index(index));
            static_path_into(elem, rest, p, path, depth, collapse)
        }
        TyKind::RigidTy(RigidTy::Tuple(field_tys)) => {
            let layout = LayoutOf::new(ty);
            descend_fields(
                ty,
                &layout,
                field_tys.into_iter().enumerate(),
                k,
                p,
                p_size,
                path,
                depth,
                collapse,
            )
        }
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let variants = def.variants();
            let [variant] = &variants[..] else { return None };
            let internal_is_union = matches!(def.kind(), rustc_public::ty::AdtKind::Union);
            if internal_is_union {
                return None;
            }
            let layout = LayoutOf::new(ty);
            let fields: Vec<Ty> = variant
                .fields()
                .iter()
                .map(|f| crate::codegen_ay::shared::mono_ty::field_ty(f, &args))
                .collect::<Option<Vec<_>>>()?;
            descend_fields(
                ty,
                &layout,
                fields.into_iter().enumerate(),
                k,
                p,
                p_size,
                path,
                depth,
                collapse,
            )
        }
        _ => None,
    }
}

/// Descend into the ONE non-zero-sized field whose bytes contain the window.
#[allow(clippy::too_many_arguments)]
fn descend_fields(
    outer: Ty,
    layout: &LayoutOf,
    fields: impl Iterator<Item = (usize, Ty)>,
    k: u64,
    p: Ty,
    p_size: u64,
    path: &mut Vec<StaticPathElem>,
    depth: usize,
    collapse: bool,
) -> Option<()> {
    let mut found: Option<(usize, Ty, u64, u64)> = None;
    for (i, field_ty) in fields {
        let off = layout.field_offset(i)? as u64;
        let size = LayoutOf::new(field_ty).size_of()? as u64;
        if size == 0 {
            continue;
        }
        if off <= k && k + p_size <= off + size {
            if found.is_some() {
                return None;
            }
            found = Some((i, field_ty, k - off, off));
        }
    }
    let (i, field_ty, rest, off) = found?;
    if !(collapse && encoded_as_its_field(outer, field_ty, off)) {
        path.push(StaticPathElem::Field(i));
    }
    static_path_into(field_ty, rest, p, path, depth, collapse)
}

/// Whether the CHC value of `outer` IS the value of its field `field`: the
/// field starts at offset 0, fills the whole, and the two translate to the
/// same sort. The encoding collapses such a layer (`UnsafeCell<u32>` is
/// `u32`'s bitvector, so `AtomicU32` is `AtomicU32_mk (fld_v (_ BitVec 32))`
/// with no `UnsafeCell` level), and a field selection on it does not exist:
/// the path through `AtomicU32.v.value` was `[Field(0), Field(0)]`, the
/// second step failed on the bitvector, and every store through
/// `AtomicU32::as_ptr` into a static havocked it (`static_store_unrouted`).
/// A layer that is NOT collapsed is a datatype around the field's sort, so
/// the two sorts differ and the step is kept.
fn encoded_as_its_field(outer: Ty, field: Ty, field_offset: u64) -> bool {
    if field_offset != 0 || LayoutOf::new(outer).size_of() != LayoutOf::new(field).size_of() {
        return false;
    }
    match (ChcCtx::translate_ty(outer), ChcCtx::translate_ty(field)) {
        (Some(outer_sort), Some(field_sort)) => outer_sort == field_sort,
        _ => false,
    }
}

/// An integer static's value `current` with the `size_of(value_ty)` bytes at
/// byte `offset` replaced by `value`: a SUB-WORD store into a primitive
/// integer static, which no static place path names (a `u32` has no part
/// that is a `u8`). The state variable of an integer static is its value as
/// a bitvector, and its byte k is bits `[8k, 8k + 8)` (little-endian), so the
/// store keeps the bits outside the window and replaces the window.
///
/// Before, the scalar store lane coerced the stored byte to the static's
/// width: `*(addr_of_mut!(N) as *mut u8) = 9` set `N: u32 = 0x01020304` to
/// `9`, so `N == 9` PROVED where Kani reads `0x01020309`.
///
/// `None` unless both types are primitive integers whose layouts match the
/// sorts and the window lies strictly inside the static (the caller then
/// fails closed).
pub(in crate::codegen_ay::chc) fn splice_integer_bytes(
    static_ty: Ty,
    current: &Expr,
    offset: u64,
    value_ty: Ty,
    value: &Expr,
) -> Option<Expr> {
    let is_int = |ty: Ty| matches!(ty.kind(), TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_)));
    if !is_int(static_ty) || !is_int(value_ty) {
        return None;
    }
    let static_bits = current.sort().bitvec_width()?;
    let value_bits = value.sort().bitvec_width()?;
    if u64::from(static_bits) != LayoutOf::new(static_ty).size_of()? as u64 * 8
        || u64::from(value_bits) != LayoutOf::new(value_ty).size_of()? as u64 * 8
    {
        return None;
    }
    let lo = u32::try_from(offset.checked_mul(8)?).ok()?;
    let hi = lo.checked_add(value_bits)?;
    if value_bits >= static_bits || hi > static_bits {
        return None;
    }
    let mut spliced = value.clone();
    if lo > 0 {
        spliced = spliced.concat(current.clone().extract(lo - 1, 0));
    }
    if hi < static_bits {
        spliced = current.clone().extract(static_bits - 1, hi).concat(spliced);
    }
    Some(spliced)
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// The part of `root` (a static's value) the path names.
    pub(in crate::codegen_ay::chc) fn select_static_path(
        root: Expr,
        path: &[StaticPathElem],
    ) -> Option<Expr> {
        let mut current = root;
        for step in path {
            current = match step {
                StaticPathElem::Field(i) => Self::apply_field_selections(
                    current,
                    &[FieldProjection { field_idx: *i, cons_idx: None, field_ty: None }],
                )?,
                StaticPathElem::Index(i) => {
                    if !current.sort().is_array() {
                        return None;
                    }
                    current.select(Expr::bitvec_const(u128::from(*i), POINTER_WIDTH))
                }
            };
        }
        Some(current)
    }

    /// `root` with the part the path names replaced by `value`.
    pub(in crate::codegen_ay::chc) fn update_static_path(
        root: &Expr,
        path: &[StaticPathElem],
        value: Expr,
    ) -> Option<Expr> {
        let Some((first, rest)) = path.split_first() else {
            return (value.sort() == root.sort()).then_some(value);
        };
        match first {
            StaticPathElem::Field(i) => {
                let projection = FieldProjection { field_idx: *i, cons_idx: None, field_ty: None };
                let inner = Self::apply_field_selections(root.clone(), &[projection])?;
                let updated_inner = Self::update_static_path(&inner, rest, value)?;
                Self::apply_projection_update(root, &[projection], updated_inner)
            }
            StaticPathElem::Index(i) => {
                if !root.sort().is_array() {
                    return None;
                }
                let idx = Expr::bitvec_const(u128::from(*i), POINTER_WIDTH);
                let inner = root.clone().select(idx.clone());
                let updated_inner = Self::update_static_path(&inner, rest, value)?;
                Some(root.clone().store(idx, updated_inner))
            }
        }
    }

    /// [`Self::update_static_path`] for a call model that stores an atomic's
    /// SCALAR (`AtomicU32::store(7)` carries the `u32`, not the `AtomicU32`):
    /// when the part the path names is a chain of single-field datatypes
    /// around the value's sort, the store writes the innermost field, which
    /// determines every layer (each has one constructor with one field). A
    /// `bool` stored into a byte-encoded leaf (`AtomicBool`'s `fld_v` is a
    /// `(_ BitVec 8)`) is the byte 1 or 0. Anything else declines.
    pub(in crate::codegen_ay::chc) fn update_static_path_scalar(
        root: &Expr,
        path: &[StaticPathElem],
        value: Expr,
    ) -> Option<Expr> {
        if let Some(updated) = Self::update_static_path(root, path, value.clone()) {
            return Some(updated);
        }
        let mut part = Self::select_static_path(root.clone(), path)?;
        let mut full = path.to_vec();
        for _ in 0..8 {
            part = trust_mc_codegen_types::types::unwrap_single_field_datatype(&part)?;
            full.push(StaticPathElem::Field(0));
            if part.sort() == value.sort() {
                return Self::update_static_path(root, &full, value);
            }
            if value.sort().is_bool() && part.sort().bitvec_width() == Some(8) {
                let byte =
                    Expr::ite(value, Expr::bitvec_const(1i128, 8), Expr::bitvec_const(0i128, 8));
                return Self::update_static_path(root, &full, byte);
            }
        }
        None
    }
}

/// Sound-fallback reason: a store whose address const-folds into a static the
/// harness keeps a state variable for, but whose bytes no static place path
/// names (or whose value's sort is not the part's). The static's state
/// variable is havoced — a fresh, universally quantified value of which the
/// real one is an instance — so a proof over it is a proof, and a
/// counterexample that reads it is never certified.
pub(in crate::codegen_ay::chc) const STATIC_STORE_UNROUTED: &str = "static_store_unrouted";

/// Fail-closed reason: a store the inline walker made into a static whose
/// output the block had already bound (`local_expr_env`): the havoc the walker
/// can make (marking the output free) cannot drop that binding, so the state
/// may keep the value from before the store.
pub(in crate::codegen_ay::chc) const STATIC_STORE_INLINED_BOUND: &str =
    "static_store_inlined_bound";

/// Fail-closed reason: a store changed a static's state variable but its
/// memory image could not be rewritten to match (more than 256 array
/// elements, an unknown layout, an object claimed by two statics). A raw read
/// of the image may see the old value, so no verdict may rest on it.
pub(in crate::codegen_ay::chc) const STATIC_IMAGE_UNSYNCED: &str = "static_image_unsynced";

/// Fail-closed reason: a store wrote a static's memory image and nothing
/// updated or havocked the static's state variable with it (a lane with no
/// static route). The state variable may then be staler than the image, and
/// the image sync rewrites the image from it ([`StaticImageWrites`]): after
/// `write_volatile(A.as_ptr(), 9); A.fetch_add(1)`, `*A.as_ptr() == 6`
/// PROVED. Recorded once the body is translated, whatever the order of the
/// blocks.
pub(in crate::codegen_ay::chc) const STATIC_IMAGE_WRITTEN_UNROUTED: &str =
    "static_image_written_unrouted";

/// Fail-closed reason: a store wrote a static's memory image under a view the
/// image sync never rewrites (`*(A.as_ptr() as *mut u8) = 9` on an
/// `AtomicU32`, a `u16` inside a `u32` field), and another store wrote the
/// static too. That cell keeps the first store's value after the second
/// changed the bytes under it: `*(A.as_ptr() as *mut u8) = 9; A.store(0);
/// *(A.as_ptr() as *const u8) == 9` PROVED.
pub(in crate::codegen_ay::chc) const STATIC_IMAGE_VIEW_UNSYNCED: &str =
    "static_image_view_unsynced";

/// The type key a store through a static's STATE lane is noted under
/// (`handle_deref_store_via_ref_targets`): it names no image cell, so it never
/// equals a store's own key.
const STATE_LANE_KEY: &str = "<state lane>";

/// What one body's stores did to the memory images of its statics.
///
/// A static lives in its state variable and in its memory image, and the
/// image sync (`sync_static_image`) rewrites every view the image seeds from
/// the state after each store that changes the state. That is sound only when
/// (1) every store into the image updates or havocs the state, and (2) every
/// cell a store leaves in the image is one the sync rewrites, or no other
/// store changes the bytes under it. A routed store is made inside
/// [`ChcCtx::with_static_store_routing`] and notes its own (view, offset)
/// ([`ChcCtx::note_static_store`]); the memory writer notes every store it
/// makes at a static's address outside such a scope
/// ([`ChcCtx::note_type_array_store`]). Once the body is translated,
/// [`ChcCtx::fail_close_static_image_hazards`] fails closed where either
/// condition may not hold, whatever order the blocks were encoded in.
#[derive(Default)]
pub(in crate::codegen_ay::chc) struct StaticImageWrites {
    /// Routed stores in progress.
    routing: u32,
    /// Image writes in progress (`write_static_image`): not program stores.
    image_writer: u32,
    /// `Some` while the image's cells are listed instead of written.
    pub(in crate::codegen_ay::chc) dry_run: Option<Vec<(String, Expr)>>,
    /// Statics a store wrote outside any routed scope.
    unrouted: BTreeSet<usize>,
    /// Per static: the (type key, byte offset; `None` = symbolic) of each
    /// routed store into it.
    stores: BTreeMap<usize, BTreeSet<(String, Option<u64>)>>,
    /// Statics a routed store wrote under a cell the sync does not rewrite.
    uncovered: BTreeSet<usize>,
    /// Per static: the (type key, byte offset) cells the image sync writes.
    cells: HashMap<usize, Option<HashSet<(String, u64)>>>,
    /// The LIVE statics whose address some object's bytes, or a constant
    /// aggregate the body spells, hold.
    held_in_memory: OnceCell<BTreeSet<usize>>,
}

/// D7(b) for a store made at the end of a block by a call model (an atomic
/// store or RMW): the static it writes, the block's earlier bindings of that
/// static's output rewritten onto the pre-store value, and the pre-store value.
pub(in crate::codegen_ay::chc) struct StaticStoreRoute {
    pub(in crate::codegen_ay::chc) vec_idx: usize,
    /// The byte offset into the static; `None` when the address names the
    /// static's object but its offset is symbolic (`AS[i].store(7)`).
    pub(in crate::codegen_ay::chc) offset: Option<u64>,
    pub(in crate::codegen_ay::chc) address: Option<Expr>,
    /// Output-variable name → the value the block bound it to.
    pub(in crate::codegen_ay::chc) substitution: HashMap<String, Expr>,
    /// Indices of the block constraints that bound it (superseded).
    pub(in crate::codegen_ay::chc) superseded: Vec<usize>,
    /// The static's value just before the store.
    pub(in crate::codegen_ay::chc) current: Expr,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// The static state variable an address names, with the byte offset into
    /// it when the address const-folds. An address whose OBJECT word is a
    /// static's but whose offset is symbolic (`&AS[i]`: the static's base
    /// plus `i * 4`) answers `(static, None)`: the store writes that static
    /// somewhere, and the caller havocs it. Before, such a store reached typed
    /// memory only and the static's state variable kept its old value:
    /// `AS[i].store(7)` with `i == 1`, then `assert!(AS[1].load() == 2)`
    /// PROVED.
    fn static_state_at(&self, addr: &Expr) -> Option<(usize, Option<u64>)> {
        if let Some((obj_id, offset)) = Self::try_extract_constant_addr(addr) {
            let &vec_idx = self.ref_resolution.static_state_idx_by_obj.get(&obj_id)?;
            return Some((vec_idx, Some(u64::from(offset))));
        }
        self.static_state_of_symbolic_addr(addr, 4).map(|vec_idx| (vec_idx, None))
    }

    /// The static a call model's pointer operand addresses, from the MIR that
    /// made the pointer rather than from its translated address: a copy, a
    /// pointer-to-pointer cast, or `&(*b).f` / `&(*b)[c]` / `&raw` of such a
    /// place, back to a local that holds the static's own address
    /// (`static_ref_to_state_idx`, at offset 0). The offset is the projections'
    /// layout offsets; a symbolic index (or a downcast, or a subslice) gives
    /// the static with no offset, which havocs it. Each local must have one
    /// whole definition (`modifies_frame_net::unique_def`).
    ///
    /// The translated address does not always name the static: `&AS[1]` is
    /// `_3 + 4` with `_3` the relation variable holding `&AS`, so
    /// `AS[1].store(7)` and `CT.b.store(9)` never reached the static's state
    /// or its image, and `*(&AS as *const _ as *const u32).add(1) == 2` PROVED.
    pub(in crate::codegen_ay::chc) fn static_of_pointer_operand(
        &self,
        op: &rustc_public::mir::Operand,
    ) -> Option<(usize, Option<u64>)> {
        use rustc_public::mir::Operand;
        let (Operand::Copy(place) | Operand::Move(place)) = op else { return None };
        if !place.projection.is_empty() {
            return None;
        }
        self.static_of_pointer_local(place.local, 8)
    }

    fn static_of_pointer_local(&self, local: usize, depth: usize) -> Option<(usize, Option<u64>)> {
        use rustc_public::mir::{CastKind, Operand, ProjectionElem, Rvalue};
        let depth = depth.checked_sub(1)?;
        // Every local on the walk has ONE definition: a local assigned on two
        // paths (`r = if c { &AS[0] } else { &B }`) names neither alone.
        let rvalue = crate::codegen_ay::chc::modifies_frame_net::unique_def(self.body, local)?;
        if let Some(&vec_idx) = self.ref_resolution.static_ref_to_state_idx.get(&local) {
            // A constant pointer into a part of the static (a D6 path) carries
            // its offset in the path, which this walk does not re-derive.
            return (!self.ref_resolution.static_ref_paths.contains_key(&local))
                .then_some((vec_idx, Some(0)));
        }
        let whole_local = |op: &Operand| match op {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
            _ => None,
        };
        match rvalue {
            Rvalue::Use(op, ..) => self.static_of_pointer_local(whole_local(op)?, depth),
            Rvalue::Cast(CastKind::PtrToPtr, op, _) => {
                self.static_of_pointer_local(whole_local(op)?, depth)
            }
            Rvalue::Cast(
                CastKind::PointerCoercion(rustc_public::mir::PointerCoercion::Unsize),
                op,
                target,
            ) => {
                let (
                    TyKind::RigidTy(RigidTy::Ref(_, a, _)),
                    TyKind::RigidTy(RigidTy::Ref(_, b, _)),
                ) = (op.ty(self.body.locals()).ok()?.kind(), target.kind())
                else {
                    return None;
                };
                let (TyKind::RigidTy(RigidTy::Array(a, _)), TyKind::RigidTy(RigidTy::Slice(b))) =
                    (a.kind(), b.kind())
                else {
                    return None;
                };
                if !same_ty_modulo_regions(a, b) {
                    return None;
                }
                self.static_of_pointer_local(whole_local(op)?, depth)
            }
            Rvalue::Ref(_, _, borrowed) | Rvalue::AddressOf(_, borrowed) => {
                let [ProjectionElem::Deref, rest @ ..] = borrowed.projection.as_slice() else {
                    return None;
                };
                let (vec_idx, base) = self.static_of_pointer_local(borrowed.local, depth)?;
                let base_ty = self.body.locals().get(borrowed.local)?.ty;
                let mut ty = match base_ty.kind() {
                    TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _)) => {
                        pointee
                    }
                    _ => return None,
                };
                let mut offset = base;
                for elem in rest {
                    match elem {
                        ProjectionElem::Field(idx, field_ty) => {
                            let field_offset = LayoutOf::new(ty).field_offset(*idx);
                            offset = offset.zip(field_offset).map(|(o, f)| o + f as u64);
                            ty = *field_ty;
                        }
                        ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => {
                            let TyKind::RigidTy(RigidTy::Array(elem_ty, _)) = ty.kind() else {
                                return Some((vec_idx, None));
                            };
                            let index = match elem {
                                ProjectionElem::Index(index_local) => {
                                    self.constant_index_local(*index_local)
                                }
                                ProjectionElem::ConstantIndex {
                                    offset, from_end: false, ..
                                } => Some(*offset),
                                _ => None,
                            };
                            let size = LayoutOf::new(elem_ty).size_of().map(|s| s as u64);
                            offset = offset
                                .zip(index)
                                .zip(size)
                                .and_then(|((o, i), s)| o.checked_add(i.checked_mul(s)?));
                            ty = elem_ty;
                        }
                        // Somewhere inside the static, at an offset this walk
                        // does not compute.
                        _ => return Some((vec_idx, None)),
                    }
                }
                Some((vec_idx, offset))
            }
            _ => None,
        }
    }

    /// The value of an index local whose one definition is a constant.
    fn constant_index_local(&self, local: usize) -> Option<u64> {
        use rustc_public::mir::{Operand, Rvalue};
        match crate::codegen_ay::chc::modifies_frame_net::unique_def(self.body, local)? {
            Rvalue::Use(Operand::Constant(c), ..) => {
                crate::codegen_ay::shared::const_pointer::const_uint(&c.const_)
                    .and_then(|v| u64::try_from(v).ok())
            }
            _ => None,
        }
    }

    /// The static whose object word a symbolic address carries: `concat(obj,
    /// offset)`, or such an address moved by a number (`bvadd`/`bvsub`). The
    /// pointer model numbers the object in the high word, and an offset that
    /// carries into it leaves the object, which the access's own bounds check
    /// reports; naming the static then only havocs it once more.
    fn static_state_of_symbolic_addr(&self, addr: &Expr, depth: usize) -> Option<usize> {
        use ay_bindings::ExprValue;
        let depth = depth.checked_sub(1)?;
        let static_of =
            |obj_id: u32| self.ref_resolution.static_state_idx_by_obj.get(&obj_id).copied();
        match addr.value() {
            ExprValue::BvConcat(high, _) if high.sort().bitvec_width() == Some(32) => {
                match high.value() {
                    ExprValue::BitVecConst { value, .. } => {
                        static_of(u32::try_from(value.clone()).ok()?)
                    }
                    _ => None,
                }
            }
            ExprValue::BvAdd(a, b) => self
                .static_state_of_symbolic_addr(a, depth)
                .or_else(|| self.static_state_of_symbolic_addr(b, depth)),
            ExprValue::BvSub(a, _) => self.static_state_of_symbolic_addr(a, depth),
            _ => Self::try_extract_constant_addr(addr).and_then(|(obj_id, _)| static_of(obj_id)),
        }
    }

    /// The static's whole new value after writing `value` (of type
    /// `value_ty`) at `offset` into `current`, along the static place path.
    /// `scalar`: the value is an atomic's scalar (a call model), which may
    /// write the innermost field of a single-field chain
    /// ([`Self::update_static_path_scalar`]).
    fn static_whole_after_store(
        &self,
        vec_idx: usize,
        offset: Option<u64>,
        value_ty: Ty,
        current: &Expr,
        value: Expr,
        scalar: bool,
    ) -> Option<Expr> {
        let static_ty = *self.ref_resolution.static_state_ty.get(&vec_idx)?;
        let Some(path) = static_path(static_ty, offset?, value_ty) else {
            return splice_integer_bytes(static_ty, current, offset?, value_ty, &value);
        };
        if scalar {
            Self::update_static_path_scalar(current, &path, value)
        } else {
            Self::update_static_path(current, &path, value)
        }
    }

    /// After a store changed the static's state variable to `whole` (`Err`:
    /// havocked, with the token of the booking the havoc made), rewrite its
    /// memory image to match, or fail closed.
    pub(in crate::codegen_ay::chc) fn sync_static_image_or_fail_closed(
        &mut self,
        vec_idx: usize,
        whole: Result<Expr, crate::codegen_ay::chc::codegen_ctx::Booked>,
    ) {
        if !self.sync_static_image(vec_idx, whole) {
            self.record_sound_fallback_reason(STATIC_IMAGE_UNSYNCED);
        }
    }

    /// D7(b) in a STATEMENT store (`*p = v`): when `p`'s address const-folds
    /// into a static the harness keeps a state variable for, the store also
    /// writes that state variable along the static place path — through the
    /// statement accumulator, the same "last write wins" channel a direct
    /// `STATIC = v` uses, so the two can never bind the output twice.
    /// Without this a store through a pointer into a static reached typed
    /// memory only, and a read of the static through its state variable saw
    /// the old value. The static's memory image is rewritten from the new
    /// value too ([`Self::sync_static_image`]): the store itself wrote one
    /// typed view of the image, and every other view the entry rule seeded
    /// (`AtomicU32` beside its `u32`, a struct beside its fields) kept the
    /// initializer. Returns whether the store addressed such a static at a
    /// known offset; a symbolic offset havocs the static and answers `false`.
    pub(in crate::codegen_ay::chc) fn route_exact_static_store_stmt(
        &mut self,
        addr: &Expr,
        value_ty: Ty,
        value: &Expr,
        acc: &mut crate::codegen_ay::chc::stmt::stmt_accumulator::StmtAccumulator<'_>,
    ) -> bool {
        let Some((vec_idx, offset)) = self.static_state_at(addr) else { return false };
        let track_key = usize::MAX - vec_idx;
        let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
        else {
            self.static_image_writes.unrouted.insert(vec_idx);
            return false;
        };
        self.note_static_store(vec_idx, offset, value_ty);
        let updated = self.static_state_current(vec_idx, acc.modified).and_then(|current| {
            self.static_whole_after_store(vec_idx, offset, value_ty, &current, value.clone(), false)
        });
        let out_var = Expr::var(&*out_name, out_sort.clone());
        let image = match updated.filter(|u| u.sort() == &out_sort) {
            Some(updated) => {
                acc.replace_constraint(track_key, out_var.eq(updated.clone()));
                self.encode.local_expr_env.insert(track_key, updated.clone());
                Ok(updated)
            }
            None => {
                // Havoc: drop the block's earlier binding of the output.
                acc.replace_constraint(track_key, Expr::bool_const(true));
                self.encode.local_expr_env.remove(&track_key);
                Err(self.record_sound_fallback_reason(STATIC_STORE_UNROUTED))
            }
        };
        self.mark_state_var_modified(vec_idx);
        acc.modified.insert(track_key);
        let havocked = image.is_err();
        self.sync_static_image_or_fail_closed(vec_idx, image);
        if havocked {
            // The havoc rewrote the image with free values, the cell this
            // store wrote among them: its bytes are known, so their views are
            // written back exactly, as a call-model store's are.
            let _ = self.write_static_value_image(value_ty, value, addr);
        }
        offset.is_some()
    }

    /// D7(b) for a CALL-MODEL store at `addr` through the pointer operand
    /// `receiver`: the rebinding of the static it writes (the Cell lane's
    /// discipline, `cell_register_block_bindings`). The static is the one the
    /// address names, or else the one the receiver's MIR definition points
    /// into ([`Self::static_of_pointer_operand`]).
    ///
    /// A receiver neither names may still point into a LIVE static (one of
    /// two element references joined on two paths, an iterator's item): every
    /// such static whose address reaches the receiver or escapes the body's
    /// address-flow scan ([`Self::statics_an_untraced_store_may_write`]) gets
    /// a route with no offset, which havocs it. Before, `r.store(7)` with
    /// `r = if c { &AS[0] } else { &AS[1] }`, and a store through `AS.iter()`,
    /// reached typed memory only, and `AS[1].load() == 2` PROVED.
    pub(in crate::codegen_ay::chc) fn plan_static_store_route(
        &self,
        addr: &Expr,
        receiver: &rustc_public::mir::Operand,
        modified_locals: &HashSet<usize>,
        stmt_constraints: &[Expr],
    ) -> Vec<StaticStoreRoute> {
        // Keep the established constant-path lane (including scalar views
        // nested in an Atomic) before trying the bounded address route.
        if let Some((idx, Some(offset))) =
            self.static_state_at(addr).or_else(|| self.static_of_pointer_operand(receiver))
        {
            return self
                .plan_static_store_route_at(idx, Some(offset), modified_locals, stmt_constraints)
                .into_iter()
                .collect();
        }
        if let Some(origins) = self.static_array_address_origins(receiver) {
            return origins
                .into_iter()
                .filter_map(|idx| {
                    let mut route = self.plan_static_store_route_at(
                        idx,
                        None,
                        modified_locals,
                        stmt_constraints,
                    )?;
                    route.address = Some(crate::codegen_ay::chc::call::substitute_vars(
                        addr,
                        &route.substitution,
                    ));
                    Some(route)
                })
                .collect();
        }
        if let Some((vec_idx, offset)) =
            self.static_state_at(addr).or_else(|| self.static_of_pointer_operand(receiver))
        {
            return self
                .plan_static_store_route_at(vec_idx, offset, modified_locals, stmt_constraints)
                .into_iter()
                .collect();
        }
        self.statics_an_untraced_store_may_write(receiver, addr)
            .into_iter()
            .filter_map(|vec_idx| {
                self.plan_static_store_route_at(vec_idx, None, modified_locals, stmt_constraints)
            })
            .collect()
    }

    /// The LIVE statics a store through `receiver` at `addr` may write when
    /// neither names one: none when the address const-folds (it names its
    /// object exactly), else each LIVE static whose address, followed from
    /// the locals holding it (`static_ref_to_state_idx`) through copies,
    /// casts, reborrows and canonical accessors, reaches the receiver or
    /// escapes (`held_address_reach`).
    pub(in crate::codegen_ay::chc) fn statics_an_untraced_store_may_write(
        &self,
        receiver: &rustc_public::mir::Operand,
        addr: &Expr,
    ) -> Vec<usize> {
        use rustc_public::mir::Operand;
        if Self::try_extract_constant_addr(addr).is_some() {
            return Vec::new();
        }
        let receiver_local = match receiver {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        };
        self.live_static_address_holders()
            .into_iter()
            .filter(|(vec_idx, seeds)| {
                self.statics_held_in_memory().contains(vec_idx)
                    || self.held_address_reach(seeds, receiver_local).0
            })
            .map(|(vec_idx, _)| vec_idx)
            .collect()
    }

    /// Each LIVE static with the locals that hold its address, in state order;
    /// a static whose address only memory holds ([`Self::statics_held_in_memory`])
    /// comes with none.
    fn live_static_address_holders(&self) -> Vec<(usize, HashSet<usize>)> {
        let mut by_static: BTreeMap<usize, HashSet<usize>> = BTreeMap::new();
        for (&local, &vec_idx) in &self.ref_resolution.static_ref_to_state_idx {
            if self.ref_resolution.mutable_static_state_idxs.contains(&vec_idx) {
                by_static.entry(vec_idx).or_default().insert(local);
            }
        }
        for &vec_idx in self.statics_held_in_memory() {
            by_static.entry(vec_idx).or_default();
        }
        by_static.into_iter().collect()
    }

    /// A store the inline walker's atomic model made at `addr`, of `value` at
    /// the atomic's own type `value_ty` (`codegen_call_virtual_inline/
    /// atomic_inline.rs`), which writes typed memory and nothing else. When
    /// the address names a static (or may: a symbolic address while a LIVE
    /// static's address escapes the body), the static is havocked, its state
    /// variable and its whole memory image, and the stored value is written
    /// back at its own place in the image with every view below its type, so
    /// the atomic's views are exact and every other view is free. Before, only
    /// the atomic's own typed cell took the value: `bump(&COUNTER)` through a
    /// trait method left the `u32` view at 10, and `*COUNTER.as_ptr() == 10`
    /// PROVED. The walker has no channel to bind the state exactly, and a
    /// binding the block already made cannot be dropped from here
    /// ([`STATIC_STORE_INLINED_BOUND`], fail closed).
    pub(in crate::codegen_ay::chc) fn static_store_from_inlined_body(
        &mut self,
        addr: &Expr,
        value_ty: Ty,
        value: &Expr,
    ) {
        let statics: Vec<(usize, Option<u64>)> = match self.static_state_at(addr) {
            Some(found) => vec![found],
            None if Self::try_extract_constant_addr(addr).is_some() => return,
            None => self
                .live_static_address_holders()
                .into_iter()
                .filter(|(vec_idx, seeds)| {
                    self.statics_held_in_memory().contains(vec_idx)
                        || self.held_address_reach(seeds, None).1
                })
                .map(|(vec_idx, _)| (vec_idx, None))
                .collect(),
        };
        if statics.is_empty() {
            return;
        }
        for (vec_idx, offset) in statics {
            self.note_static_store(vec_idx, offset, value_ty);
            let track_key = usize::MAX - vec_idx;
            if self.encode.local_expr_env.remove(&track_key).is_some() {
                self.record_sound_fallback_reason(STATIC_STORE_INLINED_BOUND);
            }
            self.mark_state_var_modified(vec_idx);
            let booked = self.record_sound_fallback_reason(STATIC_STORE_UNROUTED);
            self.sync_static_image_or_fail_closed(vec_idx, Err(booked));
        }
        let _ = self.write_static_value_image(value_ty, value, addr);
    }

    /// The constraints `routes` add for a call-model store of `value` (of
    /// type `value_ty`) at `addr`, pushed onto `extra`. When a route havocs
    /// its static, the havoc rewrote the image with free values: the bytes
    /// this store wrote are known, so their views are written back exactly.
    pub(in crate::codegen_ay::chc) fn constrain_static_store_routes(
        &mut self,
        routes: &[StaticStoreRoute],
        value_ty: Ty,
        value: &Expr,
        addr: &Expr,
        extra: &mut Vec<Expr>,
    ) {
        let mut havocked = false;
        for route in routes {
            match self.static_store_route_constraint(route, value_ty, value.clone()) {
                Some(constraint) => extra.push(constraint),
                None => havocked = true,
            }
        }
        if havocked {
            let _ = self.write_static_value_image(value_ty, value, addr);
        }
    }

    /// The rebinding of the static `vec_idx` a call-model store at `offset`
    /// (`None`: unknown) makes.
    fn plan_static_store_route_at(
        &self,
        vec_idx: usize,
        offset: Option<u64>,
        modified_locals: &HashSet<usize>,
        stmt_constraints: &[Expr],
    ) -> Option<StaticStoreRoute> {
        let track_key = usize::MAX - vec_idx;
        let (out_name, out_sort) = self.state_var_mgr.output_state_vars.get(vec_idx).cloned()?;
        let (in_name, in_sort) = self.state_var_mgr.state_vars.get(vec_idx).cloned()?;
        let mut substitution = HashMap::new();
        let mut superseded = Vec::new();
        if modified_locals.contains(&track_key)
            || self.encode.modified_state_indices.contains(&vec_idx)
        {
            match self.cell_register_block_bindings(vec_idx, 1, stmt_constraints) {
                Ok(bindings) => {
                    for (name, idx, rhs) in bindings {
                        substitution.insert(name, rhs);
                        superseded.push(idx);
                    }
                }
                Err(_) => {
                    let fresh = ExactVar::defined(
                        crate::codegen_ay::chc::chc_fresh_name("__static_pre"),
                        out_sort.clone(),
                    );
                    substitution.insert(out_name.to_string(), fresh);
                }
            }
        }
        let current =
            substitution.get(&*out_name).cloned().unwrap_or_else(|| Expr::var(&*in_name, in_sort));
        Some(StaticStoreRoute { vec_idx, offset, address: None, substitution, superseded, current })
    }

    /// The constraint a call-model store adds for its routed static (`None`:
    /// no path — havoc and record), marking the static's output live. The
    /// value is the atomic's scalar ([`Self::update_static_path_scalar`]).
    /// The static's memory image is rewritten from the new value, or havocked
    /// with it ([`Self::sync_static_image`]): the call model's own store wrote
    /// the receiver's type only, so `A.store(7)` left the `u32` view the entry
    /// rule seeded at 5, and `*A.as_ptr() == 5` PROVED.
    pub(in crate::codegen_ay::chc) fn static_store_route_constraint(
        &mut self,
        route: &StaticStoreRoute,
        value_ty: Ty,
        value: Expr,
    ) -> Option<Expr> {
        self.note_static_store(route.vec_idx, route.offset, value_ty);
        self.mark_state_var_modified(route.vec_idx);
        let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(route.vec_idx).cloned()
        else {
            let booked = self.record_sound_fallback_reason(STATIC_STORE_UNROUTED);
            self.sync_static_image_or_fail_closed(route.vec_idx, Err(booked));
            return None;
        };
        let updated = if let Some(addr) = &route.address {
            self.static_array_after_address_store(
                route.vec_idx,
                addr,
                value_ty,
                &route.current,
                value,
            )
        } else {
            self.static_whole_after_store(
                route.vec_idx,
                route.offset,
                value_ty,
                &route.current,
                value,
                true,
            )
        }
        .filter(|u| u.sort() == &out_sort);
        match updated {
            Some(updated) => {
                self.sync_static_image_or_fail_closed(route.vec_idx, Ok(updated.clone()));
                Some(Expr::var(&*out_name, out_sort).eq(updated))
            }
            None => {
                let booked = self.record_sound_fallback_reason(STATIC_STORE_UNROUTED);
                self.sync_static_image_or_fail_closed(route.vec_idx, Err(booked));
                None
            }
        }
    }
}

/// Most aligned offsets a symbolic store's coverage check walks.
const MAX_COVERAGE_OFFSETS: u64 = 1024;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Run `f` as a ROUTED static store: every memory write it makes at a
    /// static's address goes with a route that updates or havocs that
    /// static's state variable, and notes itself ([`Self::note_static_store`]).
    pub(in crate::codegen_ay::chc) fn with_static_store_routing<R>(
        &mut self,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        self.static_image_writes.routing += 1;
        let out = f(self);
        self.static_image_writes.routing -= 1;
        out
    }

    /// [`Self::with_static_store_routing`] for a store whose code cannot be
    /// one closure: pair with [`Self::end_static_store_routing`].
    pub(in crate::codegen_ay::chc) fn begin_static_store_routing(&mut self) {
        self.static_image_writes.routing += 1;
    }

    /// Close [`Self::begin_static_store_routing`].
    pub(in crate::codegen_ay::chc) fn end_static_store_routing(&mut self) {
        self.static_image_writes.routing -= 1;
    }

    /// [`Self::with_static_image_writer`] for code that cannot be one closure:
    /// pair with [`Self::end_static_image_writer`].
    pub(in crate::codegen_ay::chc) fn begin_static_image_writer(&mut self) {
        self.static_image_writes.image_writer += 1;
    }

    /// Close [`Self::begin_static_image_writer`].
    pub(in crate::codegen_ay::chc) fn end_static_image_writer(&mut self) {
        self.static_image_writes.image_writer -= 1;
    }

    /// Run `f` as a write of the image itself (the sync, a write-back after a
    /// havoc): its memory writes are no program store.
    pub(in crate::codegen_ay::chc) fn with_static_image_writer<R>(
        &mut self,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        self.static_image_writes.image_writer += 1;
        let out = f(self);
        self.static_image_writes.image_writer -= 1;
        out
    }

    /// The memory writer's note of a store at `addr` (`store_to_type_array`):
    /// one at a static's address outside a routed scope reached the image
    /// only ([`STATIC_IMAGE_WRITTEN_UNROUTED`]).
    pub(in crate::codegen_ay::chc) fn note_type_array_store(
        &mut self,
        addr: &Expr,
        type_key: &str,
    ) {
        let writes = &self.static_image_writes;
        if writes.routing > 0
            || writes.image_writer > 0
            || writes.dry_run.is_some()
            || self.ref_resolution.static_state_idx_by_obj.is_empty()
        {
            return;
        }
        if let Some((vec_idx, _)) = self.static_state_at(addr) {
            debug!(
                vec_idx,
                type_key, "CHC: a store wrote a static's memory image with no static route"
            );
            self.static_image_writes.unrouted.insert(vec_idx);
        }
    }

    /// Note a routed store of type `value_ty` at byte `offset` (`None`:
    /// symbolic) into the static `vec_idx`, and whether the cell it leaves is
    /// one the image sync rewrites.
    pub(in crate::codegen_ay::chc) fn note_static_store(
        &mut self,
        vec_idx: usize,
        offset: Option<u64>,
        value_ty: Ty,
    ) {
        let key = self.type_key_for_body_ty(value_ty).into_owned();
        if !self.static_store_covered(vec_idx, offset, value_ty, &key) {
            debug!(
                vec_idx,
                ?offset,
                key,
                "CHC: a store into a static leaves a cell its image sync does not rewrite"
            );
            self.static_image_writes.uncovered.insert(vec_idx);
        }
        self.static_image_writes.stores.entry(vec_idx).or_default().insert((key, offset));
    }

    /// Note a store through the static's STATE lane, which writes its state
    /// and syncs its image with no memory store of its own.
    pub(in crate::codegen_ay::chc) fn note_static_state_lane_store(&mut self, vec_idx: usize) {
        if self.static_image_writes.routing > 0 {
            return;
        }
        self.static_image_writes
            .stores
            .entry(vec_idx)
            .or_default()
            .insert((STATE_LANE_KEY.to_string(), None));
    }

    /// Whether a store of `value_ty` (type key `key`) at `offset` leaves its
    /// value in a cell the image sync of static `vec_idx` rewrites: the cell
    /// `(key, offset)`, or, for a symbolic offset, the cell at EVERY offset in
    /// the static the store's alignment admits.
    fn static_store_covered(
        &mut self,
        vec_idx: usize,
        offset: Option<u64>,
        value_ty: Ty,
        key: &str,
    ) -> bool {
        let Some(cells) = self.static_image_cells(vec_idx) else { return false };
        if let Some(offset) = offset {
            return cells.contains(&(key.to_string(), offset));
        }
        let Some(static_ty) = self.ref_resolution.static_state_ty.get(&vec_idx).copied() else {
            return false;
        };
        let (Some(size), Some(align), Some(total)) = (
            self.get_type_size(value_ty).map(|s| s as u64),
            self.get_type_align(value_ty),
            self.get_type_size(static_ty).map(|s| s as u64),
        ) else {
            return false;
        };
        if size == 0 || align == 0 || size > total || total / align > MAX_COVERAGE_OFFSETS {
            return false;
        }
        (0..=(total - size) / align).all(|i| cells.contains(&(key.to_string(), i * align)))
    }

    /// The (type key, byte offset) cells the image sync of static `vec_idx`
    /// writes, listed by running the writer on a symbolic value without
    /// writing (`StaticImageWrites::dry_run`). `None`: it writes no image, or
    /// its writer declines.
    fn static_image_cells(&mut self, vec_idx: usize) -> Option<HashSet<(String, u64)>> {
        if let Some(cells) = self.static_image_writes.cells.get(&vec_idx) {
            return cells.clone();
        }
        let static_ty = self.ref_resolution.static_state_ty.get(&vec_idx).copied();
        let sort = self.state_var_mgr.output_state_vars.get(vec_idx).map(|(_, sort)| sort.clone());
        let cells = static_ty.zip(sort).and_then(|(static_ty, sort)| {
            let probe = Expr::var("__static_image_cells_probe", sort);
            self.static_image_writes.dry_run = Some(Vec::new());
            let written = self.store_static_image(vec_idx, static_ty, &probe);
            let listed = self.static_image_writes.dry_run.take().unwrap_or_default();
            written.then(|| {
                listed
                    .into_iter()
                    .filter_map(|(key, addr)| {
                        let (_, offset) = Self::try_extract_constant_addr(&addr)?;
                        Some((key, u64::from(offset)))
                    })
                    .collect()
            })
        });
        self.static_image_writes.cells.insert(vec_idx, cells.clone());
        cells
    }

    /// The LIVE statics whose address is held in memory the body can load a
    /// pointer from without a local that holds the static's address: in some
    /// object's bytes (`static RS: [&AtomicU32; 2] = [&AS[0], &AS[1]]`, a
    /// `static RSL: &[AtomicU32] = &AS`), or in a constant aggregate the body
    /// spells. A store through an untraced pointer may write such a static
    /// ([`Self::statics_an_untraced_store_may_write`]).
    fn statics_held_in_memory(&self) -> &BTreeSet<usize> {
        use crate::codegen_ay::shared::const_pointer::{self, ConstRead};
        self.static_image_writes.held_in_memory.get_or_init(|| {
            let static_of_key = |key: &const_pointer::TargetKey| {
                let obj = self.ref_resolution.global_objects.get(key)?;
                let vec_idx = *self.ref_resolution.static_state_idx_by_obj.get(&obj.obj_id)?;
                self.ref_resolution.mutable_static_state_idxs.contains(&vec_idx).then_some(vec_idx)
            };
            let mut held = BTreeSet::new();
            for key in self.ref_resolution.global_objects.keys() {
                let Some((window, _)) = const_pointer::target_bytes(self.tcx, key) else {
                    continue;
                };
                for (_, target) in window.relocation_keys() {
                    held.extend(target.as_ref().and_then(static_of_key));
                }
            }
            let keep = vec![true; self.body.blocks.len()];
            for (window, ty) in const_pointer::body_constants_read(self.body, &keep, &|_| false) {
                if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))) {
                    continue;
                }
                for (_, target) in window.relocation_keys() {
                    held.extend(target.as_ref().and_then(static_of_key));
                }
            }
            if !held.is_empty() {
                debug!(?held, "CHC: LIVE statics whose address memory holds");
            }
            held
        })
    }

    /// Once the body is translated: fail closed where a static's image sync
    /// may have rewritten a view from a state staler than the image
    /// ([`STATIC_IMAGE_WRITTEN_UNROUTED`]) or left a cell another store made
    /// stale ([`STATIC_IMAGE_VIEW_UNSYNCED`]).
    pub(in crate::codegen_ay::chc) fn fail_close_static_image_hazards(&mut self) {
        let writes = &self.static_image_writes;
        let unrouted: Vec<usize> = writes.unrouted.iter().copied().collect();
        let unsynced: Vec<usize> = writes
            .uncovered
            .iter()
            .copied()
            .filter(|vec_idx| writes.stores.get(vec_idx).is_some_and(|s| s.len() >= 2))
            .collect();
        for vec_idx in unrouted {
            warn!(fn_name = %self.fn_name, vec_idx, "CHC: a static's memory image was written with no static route — fail closed");
            self.record_sound_fallback_reason(STATIC_IMAGE_WRITTEN_UNROUTED);
        }
        for vec_idx in unsynced {
            warn!(fn_name = %self.fn_name, vec_idx, "CHC: a static's memory image keeps a view its sync does not rewrite under another store — fail closed");
            self.record_sound_fallback_reason(STATIC_IMAGE_VIEW_UNSYNCED);
        }
    }
}
