// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Register-mirror coherence for the `Cell`/`RefCell` store lane.
//!
//! The store lane (`codegen_call_cell.rs`) writes a `set`/`replace`/`take`/
//! `replace_with` ONLY to the referent's memory-mirror address. The referent
//! local keeps a second copy of its value, its state variable (the register
//! mirror), and several encoder lanes read that register after the store:
//!
//! - every whole-local borrow `&c` / `&raw c` re-mirrors the local's state
//!   variable into its address (`codegen_stmt_assign_simple`, the
//!   `Ref/AddressOf value mirroring` block);
//! - a store through a mutable reference into the local refreshes the whole
//!   local's memory image from its register (`refresh_ref_target_memory_image`),
//!   and so does a volatile store;
//! - a by-value move or copy of the local (or of a place holding the cell)
//!   copies the register into the destination.
//!
//! With the register left stale, the next `&c` (the `Cell::get` receiver)
//! overwrote the stored value with the pre-store one before any read could see
//! it: `let c = Cell::new(0u32); c.set(5); assert!(c.get() == 0)` verified
//! SUCCESSFUL `[AY:PROOF_QUALIFIERS:clean]` and its `== 5` twin FAILED
//! `[AY:CTREX_CAT:Genuine]` (design 3 review finding R5,
//! docs/chc-hole-fix-designs-2026-09-24.md;
//! tools/soundness-duals/cell_set_lost_write_dual.rs).
//!
//! The repair keeps the two copies equal: a store whose referent place is
//! known also binds the referent local's OUTPUT state to the post-store value
//! (whole local, a field of a datatype local, or a slot of a flattened local).
//! When that update cannot be built exactly, the register of every local the
//! store can have written is HAVOCED: its output slots reach the rule head
//! with no binding, so every later reader of the register sees an arbitrary
//! value, never the stale one. There is no "nobody reads it" shortcut: a
//! by-value move is a reader too, and a havoc nobody reads costs nothing.
//!
//! A referent the block already assigned before the call has its output slots
//! bound by the block's own statement constraints. Every term built earlier in
//! the block that names those slots meant the local's value BEFORE the call,
//! so the call rewrites them onto the pre-call value (the binding's right-hand
//! side, or a fresh variable standing for it) before it rebinds or havocs the
//! slots; a second binding of the same output would contradict the first and
//! make every path through the call vacuous, and leaving the first in place
//! would pin the "havoced" register to its stale value.
//!
//! Accounting. A havoc of an EXACT store's referent is complete (the store's
//! address names one known object, or a known set of objects, and every
//! register mirroring them is havoced), so it is a certified fresh havoc
//! (`cell_store_register_havoc`, `FallbackSoundness::SoundHavoc`, with the
//! havoced slots recorded as freed variables): a proof over it stays a proof,
//! and a counterexample that reads a havoced register is never certified. A
//! RefCell store is not exact (its register is a (flag, value) pair and the
//! lane addresses the payload at the object base, which the `&r` mirror does
//! not), and a store whose referent is unidentified havocs a candidate set,
//! so both stay fail-closed (`cell_store_register_refcell`,
//! `cell_store_referent_unidentified`).

use crate::codegen_ay::chc::codegen_ctx::{ExactVar, Havoc};
use std::collections::{HashMap, HashSet};

use ay_bindings::{Expr, ExprValue, rebuild_with_children};
use rustc_public::CrateDef;
use rustc_public::mir::{
    BinOp, BorrowKind, CastKind, Operand, Place, ProjectionElem, Rvalue, StatementKind,
    TerminatorKind,
};
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};
use tracing::debug;

use crate::codegen_ay::provenance::{MaybeLoc, Val};
use crate::rustc_public_bridge::IndexedVal;

use super::codegen_ctx::globals::chc_fresh_name;
use super::codegen_types::CodegenTypes;
use super::{ChcCtx, FieldProjection};

/// Complete, certified havoc of an exact store's referent register
/// (`FallbackSoundness::SoundHavoc`, see the module header).
pub(in crate::codegen_ay::chc) const CELL_REGISTER_HAVOC: &str = "cell_store_register_havoc";
/// A RefCell store's register is havoced; the RefCell lane itself is not exact.
pub(in crate::codegen_ay::chc) const CELL_REGISTER_REFCELL: &str = "cell_store_register_refcell";
/// A store whose referent is unidentified havocs every candidate register.
pub(in crate::codegen_ay::chc) const CELL_REGISTER_UNIDENTIFIED: &str =
    "cell_store_referent_unidentified";

/// Which objects an intercepted Cell store can land in, as far as register
/// mirrors go.
#[derive(Clone, Debug)]
pub(in crate::codegen_ay::chc) enum CellReferent {
    /// The referent place the store's address was taken from (route 1,
    /// `ref_targets` of an unprojected receiver).
    Place(Place),
    /// A stack local whose object the (constant) address names, at an offset
    /// or type this module does not map to a place.
    Local(usize),
    /// The address is an if-then-else of constant addresses: the store lands
    /// in one of these stack locals, or in heap storage (a pointer phi,
    /// `if b { &c1 } else { &c2 }`).
    Locals(Vec<usize>),
    /// Every object the constant address can name is heap storage (an `Rc`,
    /// `Box` or `Vec` allocation): no register mirrors it.
    Heap,
    /// Nothing identifies the referent: the store may land in any of these
    /// stack locals (those whose address can reach the receiver and whose
    /// register a lane reads, see `cell_store_unknown_candidates`).
    Unknown { candidates: Vec<usize>, complete: bool },
}

/// The referent of an intercepted Cell store and whether it is a RefCell.
#[derive(Clone, Debug)]
pub(in crate::codegen_ay::chc) struct CellStoreTarget {
    pub(in crate::codegen_ay::chc) referent: CellReferent,
    /// A `RefCell` receiver: its register is a (flag, value) pair the lane
    /// does not model, so it is never synced exactly.
    pub(in crate::codegen_ay::chc) refcell: bool,
}

/// What a Cell store does to the register mirrors.
#[derive(Debug)]
pub(in crate::codegen_ay::chc) enum CellRegisterSync {
    /// No register can mirror the written storage.
    NotNeeded,
    /// Constraints binding `local`'s output state to the post-store value,
    /// already expressed over the pre-call values.
    Synced { local: usize, constraints: Vec<Expr> },
    /// The registers of `locals` are havoced (their output slots reach the
    /// rule head unbound). `reason` is recorded; `cause` names why the exact
    /// update was not built (measurement only).
    Havoc { locals: Vec<usize>, reason: &'static str, cause: &'static str },
}

/// A store's register plan: the sync outcome plus the rewrite that keeps the
/// block's earlier terms meaning the pre-call values of every rebound slot.
#[derive(Debug)]
pub(in crate::codegen_ay::chc) struct CellRegisterPlan {
    pub(in crate::codegen_ay::chc) sync: CellRegisterSync,
    /// Output slot name -> the slot's value just before the call, for every
    /// rebound (synced or havoced) local the block assigned before the call.
    /// Every term built before the call is rewritten through it.
    pub(in crate::codegen_ay::chc) substitution: HashMap<String, Expr>,
    /// Statement constraints `slot_out == rhs` the rewrite made redundant
    /// (the caller drops them).
    pub(in crate::codegen_ay::chc) superseded: Vec<usize>,
}

impl CellRegisterPlan {
    fn not_needed() -> Self {
        Self { sync: CellRegisterSync::NotNeeded, substitution: HashMap::new(), superseded: vec![] }
    }
}

/// The payload type behind canonical `Cell`/`UnsafeCell` wrappers, or `None`
/// when `ty` is not one. `Cell<T>` and `UnsafeCell<T>` translate to `T`'s own
/// sort (`codegen_types_adt`, transparent wrappers), so their register IS the
/// payload.
fn cell_wrapper_payload(ty: Ty) -> Option<Ty> {
    let mut current = ty;
    let mut peeled = false;
    for _ in 0..8 {
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = current.kind() else { break };
        let name = def.name();
        let canonical =
            name.strip_prefix("core::cell::").or_else(|| name.strip_prefix("std::cell::"));
        if !matches!(canonical, Some("Cell" | "UnsafeCell")) {
            break;
        }
        let Some(GenericArgKind::Type(inner)) = args.0.first() else { break };
        current = *inner;
        peeled = true;
    }
    peeled.then_some(current)
}

/// Whether `ty` is a reference or raw pointer to a canonical `RefCell`.
pub(in crate::codegen_ay::chc) fn is_refcell_receiver_ty(ty: Ty) -> bool {
    let TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _)) = ty.kind()
    else {
        return false;
    };
    let TyKind::RigidTy(RigidTy::Adt(def, _)) = pointee.kind() else { return false };
    let name = def.name();
    matches!(
        name.strip_prefix("core::cell::").or_else(|| name.strip_prefix("std::cell::")),
        Some("RefCell")
    )
}

/// The constant `(obj_id, offset)` leaves of a split-pointer address that is
/// a constant or an if-then-else of constants; `None` when any leaf is not a
/// constant.
fn constant_address_leaves(addr: &Expr, out: &mut Vec<(u32, u32)>, depth: u8) -> bool {
    if depth == 0 {
        return false;
    }
    if let Some(leaf) = ChcCtx::try_extract_constant_addr(addr) {
        out.push(leaf);
        return true;
    }
    match addr.value() {
        ExprValue::Ite { then_expr, else_expr, .. } => {
            constant_address_leaves(then_expr, out, depth - 1)
                && constant_address_leaves(else_expr, out, depth - 1)
        }
        _ => false,
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// The referent an intercepted Cell store writes, for register purposes.
    pub(in crate::codegen_ay::chc) fn cell_store_target(
        &self,
        self_arg: &Operand,
        addr: &MaybeLoc,
        value_ty: Ty,
    ) -> CellStoreTarget {
        let refcell = self_arg
            .ty(self.body.locals())
            .map(|ty| is_refcell_receiver_ty(self.resolve_body_ty(ty)))
            .unwrap_or(false);
        let referent = self.cell_store_referent(self_arg, addr).unwrap_or_else(|| {
            let (candidates, complete) = self.cell_store_unknown_candidates(self_arg, value_ty);
            CellReferent::Unknown { candidates, complete }
        });
        CellStoreTarget { referent, refcell }
    }

    /// The referent the address itself identifies, or `None` when it does not.
    fn cell_store_referent(&self, self_arg: &Operand, addr: &MaybeLoc) -> Option<CellReferent> {
        // Route 1's address-of lane: the address IS `&referent`. A target
        // whose projections dereference a pointer stored in the target local
        // (a static reached through its constant reference, `(*_2).0`) names
        // the POINTEE's storage, not the local's, so it is not a place of the
        // local: the address decides below.
        if matches!(addr, MaybeLoc::Known(_))
            && let Operand::Copy(place) | Operand::Move(place) = self_arg
            && place.projection.is_empty()
            && let Some(rt) = self.ref_resolution.ref_targets.get(&place.local)
            && !rt.projections.iter().any(|p| matches!(p, ProjectionElem::Deref))
        {
            return Some(CellReferent::Place(Place {
                local: rt.local,
                projection: rt.projections.clone(),
            }));
        }
        // A constant split pointer, or a choice between constants.
        let mut leaves = Vec::new();
        if !constant_address_leaves(addr.as_addr_expr(), &mut leaves, 8) || leaves.is_empty() {
            debug!(addr = %addr.as_addr_expr(), "cell register: store address names no known object");
            return None;
        }
        let mut locals: Vec<usize> = Vec::new();
        for &(obj_id, _) in &leaves {
            if let Some(local) = self.heap_state.local_idx_for_obj_id(obj_id) {
                if !locals.contains(&local) {
                    locals.push(local);
                }
            } else if self.obj_id_is_static(obj_id) {
                // A static's state variable may mirror it: not identified here.
                return None;
            }
            // Otherwise heap storage (an allocation site's object), which no
            // register mirrors.
        }
        Some(match (leaves.as_slice(), locals.as_slice()) {
            (_, []) => CellReferent::Heap,
            ([(_, 0)], [local]) => CellReferent::Place(Place { local: *local, projection: vec![] }),
            ([_], [local]) => CellReferent::Local(*local),
            _ => CellReferent::Locals(locals),
        })
    }

    /// Stack locals an unidentified Cell store can land in, and whose register
    /// some lane reads afterwards (`cell_register_remirror_exposed`), and
    /// whether that set is COMPLETE.
    ///
    /// Each tracked local's address is followed through the body
    /// (`cell_register_address_reach`). When no local's address escapes the
    /// scan and the body touches no static, the receiver can only point into
    /// a local whose address reaches it (or into heap storage, which no
    /// register mirrors), so those locals are the complete set, whatever
    /// their type. Otherwise the set is the reaching and escaping locals that
    /// a Cell view can legally write (interior-mutable, or the stored type
    /// itself seen through `Cell::from_mut`), and it is not complete.
    fn cell_store_unknown_candidates(
        &self,
        self_arg: &Operand,
        value_ty: Ty,
    ) -> (Vec<usize>, bool) {
        let value_ty = self.resolve_body_ty(value_ty);
        let receiver = match self_arg {
            Operand::Copy(place) | Operand::Move(place) => Some(place.local),
            _ => None,
        };
        // Only a local whose address is taken somewhere can be reached.
        let addressed: HashSet<usize> = self
            .body
            .blocks
            .iter()
            .flat_map(|block| &block.statements)
            .filter_map(|stmt| match &stmt.kind {
                StatementKind::Assign(
                    _,
                    Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place),
                ) => Some(place.local),
                _ => None,
            })
            .collect();
        let mut reaching: Vec<usize> = Vec::new();
        let mut escaping: Vec<usize> = Vec::new();
        for local in 0..self.body.locals().len() {
            if !addressed.contains(&local) || self.try_state_idx_for_local(local).is_none() {
                continue;
            }
            match self.cell_register_address_reach(local, receiver) {
                AddressReach::Contained => {}
                AddressReach::Reaches => reaching.push(local),
                AddressReach::Escapes => escaping.push(local),
            }
        }
        let no_statics =
            !self.ref_resolution.global_objects.keys().any(|key| key.static_def().is_some())
                && self.ref_resolution.static_ref_to_state_idx.is_empty();
        let complete = receiver.is_some() && escaping.is_empty() && no_statics;
        let candidates: Vec<usize> = reaching
            .into_iter()
            .chain(escaping)
            .filter(|&local| {
                let ty = self.resolve_body_ty(self.body.locals()[local].ty);
                (complete || self.ty_has_interior_mut(ty) || ty_holds_by_value(ty, value_ty))
                    && self.cell_register_remirror_exposed(local)
            })
            .collect();
        debug!(?candidates, complete, "cell register: unidentified referent candidates");
        (candidates, complete)
    }

    /// Whether the address of `root` (or of a place inside it) flows into the
    /// store receiver `receiver` through copies, casts, reborrows and pointer
    /// offsets, or escapes somewhere this flow-insensitive scan does not
    /// follow (stored into a place, an aggregate or memory, passed to a call
    /// other than a canonical cell/atomic accessor that does not retain it,
    /// exposed as an integer, or its holder's own address taken). An unknown
    /// receiver counts as an escape.
    fn cell_register_address_reach(&self, root: usize, receiver: Option<usize>) -> AddressReach {
        let Some(receiver) = receiver else { return AddressReach::Escapes };
        let mut holders: HashSet<usize> = HashSet::new();
        loop {
            let before = holders.len();
            match self.cell_register_address_flow_step(root, &mut holders) {
                AddressFlow::Escaped => return AddressReach::Escapes,
                AddressFlow::Contained => {}
            }
            if holders.contains(&receiver) {
                return AddressReach::Reaches;
            }
            if holders.len() == before {
                return AddressReach::Contained;
            }
        }
    }

    /// Where an address held BY VALUE in the locals `seeds` goes (a static's
    /// address, which the locals of `static_ref_to_state_idx` hold): whether
    /// it reaches the store receiver `receiver` (`None`: an operand that is
    /// not a whole local, which it may), and whether it escapes where the
    /// scan cannot follow it. The scan is `cell_register_address_flow_step`'s,
    /// with no local whose own address is the root.
    pub(in crate::codegen_ay::chc) fn held_address_reach(
        &self,
        seeds: &HashSet<usize>,
        receiver: Option<usize>,
    ) -> (bool, bool) {
        let mut holders = seeds.clone();
        loop {
            let before = holders.len();
            if let AddressFlow::Escaped =
                self.cell_register_address_flow_step(usize::MAX, &mut holders)
            {
                return (true, true);
            }
            if holders.len() == before {
                return (receiver.is_none_or(|r| holders.contains(&r)), false);
            }
        }
    }

    /// One pass of `cell_register_address_reaches` over the body.
    fn cell_register_address_flow_step(
        &self,
        root: usize,
        holders: &mut HashSet<usize>,
    ) -> AddressFlow {
        // An operand that carries the address itself (not a value read
        // through it).
        let carries = |holders: &HashSet<usize>, op: &Operand| match op {
            Operand::Copy(place) | Operand::Move(place) => {
                holders.contains(&place.local)
                    && !matches!(place.projection.first(), Some(ProjectionElem::Deref))
            }
            _ => false,
        };
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(lhs, rvalue) = &stmt.kind else {
                    if let StatementKind::Intrinsic(_) = &stmt.kind
                        && !holders.is_empty()
                    {
                        // `copy_nonoverlapping` moves bytes, possibly a held
                        // address: not followed.
                        return AddressFlow::Escaped;
                    }
                    continue;
                };
                let produces = match rvalue {
                    Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                        let derefs = place
                            .projection
                            .iter()
                            .filter(|p| matches!(p, ProjectionElem::Deref))
                            .count();
                        let leading_deref =
                            matches!(place.projection.first(), Some(ProjectionElem::Deref));
                        if place.local == root {
                            // `&root`, `&root.f`, `&root[i]`: inside root. A
                            // place through a pointer stored in root is not.
                            derefs == 0
                        } else if holders.contains(&place.local) {
                            if derefs == 0 {
                                // The address of a holder: the held address is
                                // now reachable through memory.
                                return AddressFlow::Escaped;
                            }
                            // `&(*h).f` reborrows inside root; a second
                            // dereference follows a pointer read out of root,
                            // which is not root's own address.
                            leading_deref && derefs == 1
                        } else {
                            false
                        }
                    }
                    Rvalue::Use(op, ..) => carries(holders, op),
                    Rvalue::CopyForDeref(place) => {
                        holders.contains(&place.local)
                            && !matches!(place.projection.first(), Some(ProjectionElem::Deref))
                    }
                    Rvalue::Cast(kind, op, _) if carries(holders, op) => match kind {
                        CastKind::PtrToPtr
                        | CastKind::Transmute
                        | CastKind::PointerCoercion(_)
                        | CastKind::Subtype => true,
                        _ => return AddressFlow::Escaped,
                    },
                    Rvalue::BinaryOp(BinOp::Offset, op, _) => carries(holders, op),
                    Rvalue::Aggregate(_, operands)
                        if operands.iter().any(|o| carries(holders, o)) =>
                    {
                        return AddressFlow::Escaped;
                    }
                    Rvalue::Repeat(op, _) if carries(holders, op) => return AddressFlow::Escaped,
                    _ => false,
                };
                if produces {
                    if !lhs.projection.is_empty() {
                        return AddressFlow::Escaped;
                    }
                    holders.insert(lhs.local);
                }
            }
            match &block.terminator.kind {
                TerminatorKind::Call { func, args, destination, .. } => {
                    let held: Vec<usize> = args
                        .iter()
                        .enumerate()
                        .filter(|(_, op)| carries(holders, op))
                        .map(|(i, _)| i)
                        .collect();
                    if held.is_empty() {
                        continue;
                    }
                    let path = self.resolve_callee_path(func).unwrap_or_default();
                    match accessor_retains(&path) {
                        Some(retains) if held == [0] => {
                            if retains {
                                if !destination.projection.is_empty() {
                                    return AddressFlow::Escaped;
                                }
                                holders.insert(destination.local);
                            }
                        }
                        _ => return AddressFlow::Escaped,
                    }
                }
                TerminatorKind::InlineAsm { .. } if !holders.is_empty() => {
                    return AddressFlow::Escaped;
                }
                _ => {}
            }
        }
        AddressFlow::Contained
    }

    /// Whether `obj_id` is a static's object (`global_objects`).
    fn obj_id_is_static(&self, obj_id: u32) -> bool {
        self.ref_resolution
            .global_objects
            .iter()
            .any(|(key, object)| key.static_def().is_some() && object.obj_id == obj_id)
    }

    /// Plan how a Cell store that wrote `value` keeps the register mirrors
    /// coherent. See the module header.
    pub(in crate::codegen_ay::chc) fn plan_cell_register_mirror(
        &mut self,
        target: &CellStoreTarget,
        value: &Expr,
        value_ty: Ty,
        modified_locals: &HashSet<usize>,
        stmt_constraints: &[Expr],
    ) -> CellRegisterPlan {
        let tracked = |ctx: &Self, local: &usize| ctx.try_state_idx_for_local(*local).is_some();
        let (locals, cause) = match &target.referent {
            CellReferent::Heap => return CellRegisterPlan::not_needed(),
            CellReferent::Place(place) => {
                if !tracked(self, &place.local) {
                    return CellRegisterPlan::not_needed();
                }
                let local = place.local;
                let (substitution, superseded) =
                    self.cell_register_rebinding(&[local], modified_locals, stmt_constraints);
                if target.refcell {
                    return CellRegisterPlan {
                        sync: CellRegisterSync::Havoc {
                            locals: vec![local],
                            reason: CELL_REGISTER_REFCELL,
                            cause: "refcell_register_unmodelled",
                        },
                        substitution,
                        superseded,
                    };
                }
                // The stored value was translated before the rebinding: any
                // output slot it names meant the pre-call value.
                let value = substitute_vars(value, &substitution);
                let update = self.cell_register_current(local, &substitution).and_then(|current| {
                    self.cell_register_update(place, &value, value_ty, &current, modified_locals)
                });
                let sync = match update {
                    Ok(constraints) => CellRegisterSync::Synced { local, constraints },
                    Err(cause) => CellRegisterSync::Havoc {
                        locals: vec![local],
                        reason: CELL_REGISTER_HAVOC,
                        cause,
                    },
                };
                return CellRegisterPlan { sync, substitution, superseded };
            }
            CellReferent::Local(local) => (vec![*local], "path_unmapped"),
            CellReferent::Locals(locals) => (locals.clone(), "referent_one_of"),
            CellReferent::Unknown { candidates, complete } => {
                if candidates.is_empty() {
                    return CellRegisterPlan::not_needed();
                }
                let (substitution, superseded) =
                    self.cell_register_rebinding(candidates, modified_locals, stmt_constraints);
                // A complete candidate set is havoced like a known one.
                let reason = match (complete, target.refcell) {
                    (true, false) => CELL_REGISTER_HAVOC,
                    (true, true) => CELL_REGISTER_REFCELL,
                    (false, _) => CELL_REGISTER_UNIDENTIFIED,
                };
                return CellRegisterPlan {
                    sync: CellRegisterSync::Havoc {
                        locals: candidates.clone(),
                        reason,
                        cause: "referent_unidentified",
                    },
                    substitution,
                    superseded,
                };
            }
        };
        let locals: Vec<usize> = locals.into_iter().filter(|l| tracked(self, l)).collect();
        if locals.is_empty() {
            return CellRegisterPlan::not_needed();
        }
        let (substitution, superseded) =
            self.cell_register_rebinding(&locals, modified_locals, stmt_constraints);
        let reason = if target.refcell { CELL_REGISTER_REFCELL } else { CELL_REGISTER_HAVOC };
        CellRegisterPlan {
            sync: CellRegisterSync::Havoc { locals, reason, cause },
            substitution,
            superseded,
        }
    }

    /// Record a register havoc. A complete havoc of an exact store's referent
    /// (`CELL_REGISTER_HAVOC`) is a certified fresh havoc whose freed
    /// variables are the havoced output slots, so a counterexample that reads
    /// one is never certified and one independent of them can be; any other
    /// havoc is fail-closed.
    pub(in crate::codegen_ay::chc) fn record_cell_register_havoc(
        &mut self,
        reason: &'static str,
        cause: &'static str,
        locals: &[usize],
    ) {
        debug!(reason, cause, ?locals, "cell register: havoc recorded");
        if reason != CELL_REGISTER_HAVOC {
            self.record_sound_fallback_reason(reason);
            return;
        }
        let mut freed: Vec<String> = Vec::new();
        for &local in locals {
            let Some(vec_idx) = self.try_state_idx_for_local(local) else { continue };
            for i in 0..self.cell_register_slot_count(local) {
                if let Some((name, _)) = self.state_var_mgr.output_state_vars.get(vec_idx + i) {
                    freed.push(name.to_string());
                }
            }
        }
        self.record_sound_fallback_reason_identified(reason, freed.first().map(String::as_str));
        for name in freed.iter().skip(1) {
            self.vc.note_additional_freed_var(name);
        }
    }

    /// Whether an argument of `ty` lets a callee write interior-mutable state
    /// of the caller: a reference or raw pointer (possibly through further
    /// pointers, tuples, arrays or generic arguments) to a `!Freeze` pointee.
    pub(in crate::codegen_ay::chc) fn ty_points_to_interior_mut(&self, ty: Ty, depth: u8) -> bool {
        if depth == 0 {
            return true;
        }
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _)) => {
                let pointee = self.resolve_body_ty(pointee);
                self.ty_has_interior_mut(pointee)
                    || self.ty_points_to_interior_mut(pointee, depth - 1)
            }
            TyKind::RigidTy(RigidTy::Tuple(tys)) => {
                tys.iter().any(|t| self.ty_points_to_interior_mut(*t, depth - 1))
            }
            TyKind::RigidTy(RigidTy::Array(elem, _) | RigidTy::Slice(elem)) => {
                self.ty_points_to_interior_mut(elem, depth - 1)
            }
            // A shared-ownership pointer to interior-mutable data
            // (`Rc<Cell<u8>>`: a clone the caller keeps observes the write),
            // or a type argument that points at some (`Option<&Cell<u8>>`).
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                let name = def.name();
                let shared = ["::rc::Rc", "::rc::Weak", "::sync::Arc", "::sync::Weak"]
                    .iter()
                    .any(|suffix| name.ends_with(suffix));
                args.0.iter().any(|arg| match arg {
                    GenericArgKind::Type(t) => {
                        let t = self.resolve_body_ty(*t);
                        (shared && self.ty_has_interior_mut(t))
                            || self.ty_points_to_interior_mut(t, depth - 1)
                    }
                    _ => false,
                })
            }
            _ => false,
        }
    }

    /// Model a call the encoder cannot follow whose arguments reach
    /// interior-mutable caller state (`f(&c)` through a function pointer,
    /// where the inline walker receives the referent's VALUE and has no Cell
    /// store lane, so a `c.set(200)` in the callee was dropped with no
    /// record). The callee is not walked: every stack local such an argument
    /// names has its register havoced and its memory image re-mirrored from
    /// the havoced register, a heap pointee gets a fresh value at the pointer,
    /// and the destination is havoced. The reason is fail-closed: the callee's
    /// own checks are not encoded and a pointee this cannot name keeps its
    /// stale value.
    pub(in crate::codegen_ay::chc) fn emit_interior_mut_call_havoc(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: usize,
        from_app: &super::RelationApp,
        stmt_constraints: &[Expr],
        modified_locals: &HashSet<usize>,
        reason: &'static str,
    ) {
        use super::codegen_call_coerce::CallCoerce;
        use super::codegen_rules::CodegenRules;

        let dest_local = destination.local;
        let booked = self.record_sound_fallback_reason(reason);
        let mut referents: Vec<usize> = Vec::new();
        let mut heap_pointers: Vec<(Expr, Ty)> = Vec::new();
        for arg in args {
            let Ok(arg_ty) = arg.ty(self.body.locals()) else { continue };
            let arg_ty = self.resolve_body_ty(arg_ty);
            if !self.ty_points_to_interior_mut(arg_ty, 4) {
                continue;
            }
            // A target reached through a pointer stored in the target local
            // (`(*_2).0`, a static through its constant reference) is the
            // pointee's storage: it is havoced at the pointer value below.
            let resolved = match arg {
                Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => self
                    .ref_resolution
                    .ref_targets
                    .get(&place.local)
                    .filter(|rt| !rt.projections.iter().any(|p| matches!(p, ProjectionElem::Deref)))
                    .map(|rt| rt.local),
                _ => None,
            };
            match resolved {
                Some(local) if self.try_state_idx_for_local(local).is_some() => {
                    if !referents.contains(&local) {
                        referents.push(local);
                    }
                }
                Some(_) => {}
                None => {
                    let pointee = match arg_ty.kind() {
                        TyKind::RigidTy(RigidTy::Ref(_, p, _) | RigidTy::RawPtr(p, _)) => {
                            Some(self.resolve_body_ty(p))
                        }
                        _ => None,
                    };
                    let ptr = self.translate_operand_with_modified(arg, modified_locals);
                    match (pointee, ptr) {
                        (Some(pointee), Some(ptr))
                            if ptr.sort().bitvec_width()
                                == Some(crate::codegen_ay::types::POINTER_WIDTH) =>
                        {
                            heap_pointers.push((ptr, pointee));
                        }
                        _ => {
                            self.record_sound_fallback_reason("interior_mut_arg_unresolved");
                        }
                    }
                }
            }
        }
        let (substitution, superseded) =
            self.cell_register_rebinding(&referents, modified_locals, stmt_constraints);
        let kept: Vec<Expr> = stmt_constraints
            .iter()
            .enumerate()
            .filter(|(idx, _)| !superseded.contains(idx))
            .map(|(_, c)| substitute_vars(c, &substitution))
            .collect();
        if !substitution.is_empty() {
            self.heap_state.rewrite_pending_terms(|e| substitute_vars(e, &substitution));
        }
        let mut modified_after = modified_locals.clone();
        modified_after.extend(referents.iter().copied());
        modified_after.insert(dest_local);
        let mut extra: Vec<Expr> = Vec::new();
        // Every pointee gets a fresh value in memory (the register of a stack
        // referent is havoced separately, through the rule head): a read of
        // either copy sees an arbitrary value, and the next whole-local borrow
        // re-mirrors the havoced register.
        let mut targets: Vec<(Expr, Ty)> = Vec::new();
        for &local in &referents {
            self.encode.invalidate_local_cache(local);
            self.encode.local_expr_env.remove(&local);
            let place = Place { local, projection: Vec::new() };
            match self.translate_ref_to_address(&place, &modified_after) {
                Some(loc) => targets.push((loc.into_expr(), self.body.locals()[local].ty)),
                None => {
                    self.record_sound_fallback_reason("interior_mut_arg_unresolved");
                }
            }
        }
        targets.extend(heap_pointers);
        for (addr, pointee) in targets {
            let pointee = self.resolve_body_ty(pointee);
            let Some(sort) = Self::translate_ty(pointee) else {
                self.record_sound_fallback_reason("interior_mut_arg_unresolved");
                continue;
            };
            let fresh = Havoc::booked(booked, chc_fresh_name("__interior_mut_havoc"), sort);
            let prev = self.suppress_heap_store_checks;
            self.suppress_heap_store_checks = true;
            #[allow(deprecated)]
            if let Some(c) = self.build_memory_store_untyped(addr.clone(), fresh.clone(), pointee) {
                extra.push(c);
            }
            if fresh.sort().is_datatype() {
                self.try_decompose_struct_store(&addr, &fresh, pointee, &mut extra);
            }
            self.suppress_heap_store_checks = prev;
        }
        super::ptr_receiver_mem::drain_pending_updates(self, &mut extra);
        let mut out_locals = vec![dest_local];
        out_locals.extend(referents.iter().copied().filter(|l| *l != dest_local));
        let out = self.build_output_args(modified_locals, &out_locals);
        debug!(?referents, dest_local, reason, "interior-mutable call arguments havoced");
        self.emit_goto_rule_extra(from_app, target, &out, &kept, extra);
    }

    /// Whether some encoder lane can read `local`'s register after a store:
    /// a whole-local borrow (the `&c` value mirror), any mutable borrow or raw
    /// address (a store through it refreshes the whole local's image from the
    /// register), a by-value move or copy of a place of the local that holds
    /// interior-mutable data (it copies the register), or a drop of it.
    pub(in crate::codegen_ay::chc) fn cell_register_remirror_exposed(&self, local: usize) -> bool {
        let locals = self.body.locals();
        let reads_interior = |op: &Operand| match op {
            Operand::Copy(place) | Operand::Move(place) => {
                place.local == local
                    && place.ty(locals).map_or(true, |ty| self.ty_has_interior_mut(ty))
            }
            Operand::Constant(_) => false,
            #[allow(unreachable_patterns)]
            _ => false,
        };
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(_, rvalue) = &stmt.kind else { continue };
                match rvalue {
                    Rvalue::Ref(_, kind, place) if place.local == local => {
                        if place.projection.is_empty() || matches!(kind, BorrowKind::Mut { .. }) {
                            return true;
                        }
                    }
                    Rvalue::AddressOf(_, place) if place.local == local => return true,
                    Rvalue::Use(op, ..) | Rvalue::Repeat(op, _) | Rvalue::Cast(_, op, _)
                        if reads_interior(op) =>
                    {
                        return true;
                    }
                    #[cfg(not(trust_toolchain))]
                    Rvalue::ShallowInitBox(op, _) if reads_interior(op) => return true,
                    Rvalue::Aggregate(_, operands) if operands.iter().any(reads_interior) => {
                        return true;
                    }
                    _ => {}
                }
            }
            match &block.terminator.kind {
                TerminatorKind::Call { args, .. } if args.iter().any(reads_interior) => {
                    return true;
                }
                TerminatorKind::Drop { place, .. } if place.local == local => return true,
                _ => {}
            }
        }
        false
    }

    /// The rewrite for every local in `locals` the block assigned before the
    /// call: each output slot maps to its pre-call value. A slot bound by
    /// exactly one plain statement constraint `slot_out == rhs` (whose `rhs`
    /// names no output slot of the local) maps to `rhs`, and that constraint
    /// is superseded. Any other shape maps every slot of the local to a fresh
    /// variable, which the rewrite then puts in the slot's place in every
    /// earlier term (including the block's own binding): the block's meaning
    /// is unchanged and the output slots are free for the call to rebind or
    /// havoc.
    fn cell_register_rebinding(
        &self,
        locals: &[usize],
        modified_locals: &HashSet<usize>,
        stmt_constraints: &[Expr],
    ) -> (HashMap<String, Expr>, Vec<usize>) {
        let mut substitution = HashMap::new();
        let mut superseded = Vec::new();
        for &local in locals {
            if !modified_locals.contains(&local) {
                continue;
            }
            let Some(vec_idx) = self.try_state_idx_for_local(local) else { continue };
            let slots = self.cell_register_slot_count(local);
            match self.cell_register_block_bindings(vec_idx, slots, stmt_constraints) {
                Ok(bindings) => {
                    for (name, idx, rhs) in bindings {
                        substitution.insert(name, rhs);
                        superseded.push(idx);
                    }
                }
                Err(why) => {
                    debug!(local, why, "cell register: renaming the block's slot bindings");
                    for i in 0..slots {
                        let Some((name, sort)) =
                            self.state_var_mgr.output_state_vars.get(vec_idx + i).cloned()
                        else {
                            continue;
                        };
                        let fresh = ExactVar::defined(chc_fresh_name("__cell_pre"), sort);
                        substitution.insert(name.to_string(), fresh);
                    }
                }
            }
        }
        (substitution, superseded)
    }

    /// Number of state slots `local` occupies.
    fn cell_register_slot_count(&self, local: usize) -> usize {
        if self.flatten.flattened_tuple_locals.contains(&local) {
            self.flattened_field_count(local).max(1)
        } else {
            1
        }
    }

    /// The value each state slot of `local` holds just before the call: the
    /// rewrite's value for a slot the block bound, else the input state.
    fn cell_register_current(
        &self,
        local: usize,
        substitution: &HashMap<String, Expr>,
    ) -> Result<Vec<Expr>, &'static str> {
        let vec_idx =
            self.try_state_idx_for_local(local).ok_or("cell_store_register_state_missing")?;
        let slots = self.cell_register_slot_count(local);
        let mut current = Vec::with_capacity(slots);
        for i in 0..slots {
            let (out_name, _) = self
                .state_var_mgr
                .output_state_vars
                .get(vec_idx + i)
                .ok_or("cell_store_register_state_missing")?;
            if let Some(pre) = substitution.get(&**out_name) {
                current.push(pre.clone());
                continue;
            }
            let (name, sort) = self
                .state_var_mgr
                .state_vars
                .get(vec_idx + i)
                .cloned()
                .ok_or("cell_store_register_state_missing")?;
            current.push(Expr::var(&*name, sort));
        }
        Ok(current)
    }

    /// The block's own bindings of `local`'s output slots, when the block
    /// assigned the local before the call: for each slot `vec_idx + i`, its
    /// output variable name, the index of the one statement constraint
    /// `slot_out == rhs`, and `rhs` (the slot's value just before the call).
    /// `Err` unless every slot has exactly one such binding and no `rhs`
    /// names an output slot itself.
    pub(in crate::codegen_ay::chc) fn cell_register_block_bindings(
        &self,
        vec_idx: usize,
        slots: usize,
        stmt_constraints: &[Expr],
    ) -> Result<Vec<(String, usize, Expr)>, &'static str> {
        let mut names = Vec::with_capacity(slots);
        for i in 0..slots {
            let (name, _) = self
                .state_var_mgr
                .output_state_vars
                .get(vec_idx + i)
                .ok_or("cell_store_register_state_missing")?;
            names.push(name.to_string());
        }
        let mut bindings: Vec<Option<(usize, Expr)>> = vec![None; slots];
        for (idx, constraint) in stmt_constraints.iter().enumerate() {
            let ExprValue::Eq(lhs, rhs) = constraint.value() else { continue };
            let ExprValue::Var { name } = lhs.value() else { continue };
            let Some(slot) = names.iter().position(|n| n == name) else { continue };
            if bindings[slot].is_some() {
                return Err("cell_store_register_sync_conflict");
            }
            bindings[slot] = Some((idx, rhs.clone()));
        }
        let bindings: Vec<(usize, Expr)> = bindings
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .ok_or("cell_store_register_sync_unbound")?;
        if bindings.iter().any(|(_, rhs)| names.iter().any(|n| expr_mentions_var(rhs, n))) {
            return Err("cell_store_register_sync_conflict");
        }
        Ok(names.into_iter().zip(bindings).map(|(name, (idx, rhs))| (name, idx, rhs)).collect())
    }

    /// Constraints binding the output state of `place.local` so that `place`
    /// holds `value` and every other part of the local keeps its pre-call
    /// value (`current`, one entry per state slot).
    ///
    /// The place is field projections, at most one array element (`[i]` or a
    /// constant index) and field projections inside that element; the
    /// element is updated with a functional array store.
    fn cell_register_update(
        &mut self,
        place: &Place,
        value: &Expr,
        value_ty: Ty,
        current: &[Expr],
        modified_locals: &HashSet<usize>,
    ) -> Result<Vec<Expr>, &'static str> {
        let local = place.local;
        let local_ty = self.resolve_body_ty(self.body.locals()[local].ty);

        // Field path in the sort world. A field whose container translates to
        // the field's own sort (`Cell`/`UnsafeCell`, `(T,)`) is the identity.
        let mut ty = local_ty;
        let mut prefix: Vec<FieldProjection> = Vec::new();
        let mut index: Option<Expr> = None;
        let mut suffix: Vec<FieldProjection> = Vec::new();
        let mut pending_cons: Option<usize> = None;
        for elem in &place.projection {
            match elem {
                ProjectionElem::Field(idx, field_ty) => {
                    let field_ty = self.resolve_body_ty(*field_ty);
                    let container_sort = Self::translate_ty(ty);
                    if pending_cons.is_none()
                        && container_sort.is_some()
                        && container_sort == Self::translate_ty(field_ty)
                    {
                        ty = field_ty;
                        continue;
                    }
                    let fp = FieldProjection {
                        field_idx: *idx,
                        cons_idx: pending_cons.take(),
                        field_ty: Some(field_ty),
                    };
                    if index.is_some() {
                        suffix.push(fp)
                    } else {
                        prefix.push(fp)
                    }
                    ty = field_ty;
                }
                ProjectionElem::Downcast(variant) => pending_cons = Some(variant.to_index()),
                ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }
                    if index.is_none() && pending_cons.is_none() =>
                {
                    let TyKind::RigidTy(RigidTy::Array(elem_ty, _)) = ty.kind() else {
                        return Err("cell_store_register_path_unsyncable");
                    };
                    index = Some(match elem {
                        ProjectionElem::Index(idx_local) => self
                            .translate_operand_with_modified(
                                &Operand::Copy(Place { local: *idx_local, projection: vec![] }),
                                modified_locals,
                            )
                            .ok_or("cell_store_register_index_unresolved")?,
                        ProjectionElem::ConstantIndex { offset, from_end: false, .. } => {
                            Expr::bitvec_const(u128::from(*offset), 64)
                        }
                        _ => return Err("cell_store_register_path_unsyncable"),
                    });
                    ty = self.resolve_body_ty(elem_ty);
                }
                _ => return Err("cell_store_register_path_unsyncable"),
            }
        }
        if pending_cons.is_some() {
            return Err("cell_store_register_path_unsyncable");
        }

        // The referent's register must be exactly the stored payload: a
        // Cell/UnsafeCell of the stored type, or a local of the stored type
        // itself seen through a Cell view (`Cell::from_mut(&mut x)`).
        let value_ty = self.resolve_body_ty(value_ty);
        let payload_ty = cell_wrapper_payload(ty).map(|p| self.resolve_body_ty(p)).unwrap_or(ty);
        if payload_ty != value_ty {
            return Err("cell_store_register_referent_not_cell");
        }
        let value_sort = Self::translate_ty(value_ty).ok_or("cell_store_register_sort_unknown")?;
        if Self::translate_ty(ty).as_ref() != Some(&value_sort) || value.sort() != &value_sort {
            return Err("cell_store_register_sort_mismatch");
        }

        let flattened = self.flatten.flattened_tuple_locals.contains(&local);
        let vec_idx =
            self.try_state_idx_for_local(local).ok_or("cell_store_register_state_missing")?;
        let slots = self.cell_register_slot_count(local);
        if current.len() != slots {
            return Err("cell_store_register_state_missing");
        }
        let out_var = |ctx: &Self, i: usize| -> Result<Expr, &'static str> {
            let (name, sort) = ctx
                .state_var_mgr
                .output_state_vars
                .get(vec_idx + i)
                .cloned()
                .ok_or("cell_store_register_state_missing")?;
            Ok(Expr::var(&*name, sort))
        };
        // `container` with its element `idx` replaced by `value` placed at
        // `suffix` inside the element.
        let store_element = |container: &Expr, idx: &Expr| -> Result<Expr, &'static str> {
            let arr = container.sort().array_sort().ok_or("cell_store_register_index_sort")?;
            let width = arr.index_sort.bitvec_width().ok_or("cell_store_register_index_sort")?;
            let idx = crate::codegen_ay::types::coerce_bitvec_width_safe(
                idx.clone(),
                width,
                crate::codegen_ay::types::SignExtension::ZeroExtend,
            );
            if idx.sort() != &arr.index_sort {
                return Err("cell_store_register_index_sort");
            }
            let element = if suffix.is_empty() {
                value.clone()
            } else {
                Self::apply_projection_update(
                    &container.clone().select(idx.clone()),
                    &suffix,
                    value.clone(),
                )
                .ok_or("cell_store_register_field_update")?
            };
            if element.sort() != &arr.element_sort {
                return Err("cell_store_register_sort_mismatch");
            }
            Ok(container.clone().store(idx, element))
        };

        // The value the prefix place holds after the store.
        let place_new = |container: Option<&Expr>| -> Result<Expr, &'static str> {
            match (&index, container) {
                (None, _) => Ok(value.clone()),
                (Some(idx), Some(container)) => store_element(container, idx),
                (Some(_), None) => Err("cell_store_register_path_unsyncable"),
            }
        };

        if prefix.is_empty() {
            if flattened {
                if index.is_some() {
                    return Err("cell_store_register_flattened_undecomposed");
                }
                let fields = self
                    .build_flattened_destination_field_constraints(local, value.clone())
                    .ok_or("cell_store_register_flattened_undecomposed")?;
                if fields.len() != slots || fields.iter().enumerate().any(|(i, (f, _))| *f != i) {
                    return Err("cell_store_register_flattened_undecomposed");
                }
                return Ok(fields.into_iter().map(|(_, c)| c).collect());
            }
            let out = out_var(self, 0)?;
            let new_root = place_new(current.first())?;
            if out.sort() != new_root.sort() {
                return Err("cell_store_register_sort_mismatch");
            }
            return Ok(vec![out.eq(new_root)]);
        }

        if flattened {
            let slot = if let [fp] = prefix.as_slice()
                && let Some(cons_idx) = fp.cons_idx
            {
                // One variant payload field of a BV-flattened enum: slot 0 is
                // the discriminant and the payload slot comes from the layout
                // (the slot `encode_flattened_field_projection` writes for
                // `(e as A).0 = v`). The store runs only where the variant is
                // active, so writing its payload slot is exact.
                let layout = self
                    .flatten
                    .enum_bv_layouts
                    .get(&local)
                    .ok_or("cell_store_register_flattened_downcast")?;
                if cons_idx >= layout.ctor_field_slot.len()
                    || fp.field_idx >= layout.ctor_field_slot[cons_idx].len()
                {
                    return Err("cell_store_register_flattened_downcast");
                }
                1 + layout
                    .payload_slot(cons_idx, fp.field_idx)
                    .ok_or("cell_store_register_flattened_downcast")?
            } else {
                let slot = self
                    .faithful_nested_flat_slot(local, &prefix)
                    .map_err(cell_register_flattened_reason)?;
                match self.flat_span_for(local, &prefix) {
                    Ok((start, 1)) if start == slot => {}
                    _ => return Err("cell_store_register_flattened_span"),
                }
                slot
            };
            if slot >= slots {
                return Err("cell_store_register_flattened_span");
            }
            let slot_new = place_new(current.get(slot))?;
            let mut constraints = Vec::with_capacity(slots);
            for (i, slot_current) in current.iter().enumerate() {
                let out = out_var(self, i)?;
                let slot_value = if i == slot { slot_new.clone() } else { slot_current.clone() };
                if slot_value.sort() != out.sort() {
                    return Err("cell_store_register_sort_mismatch");
                }
                constraints.push(out.eq(slot_value));
            }
            return Ok(constraints);
        }

        let out = out_var(self, 0)?;
        let root = current.first().ok_or("cell_store_register_state_missing")?;
        let prefix_value = if index.is_some() {
            let mut at = Val::of_value(root.clone());
            for fp in &prefix {
                at = Self::datatype_field_select(&at, fp.field_idx, fp.cons_idx)
                    .ok_or("cell_store_register_field_update")?;
            }
            Some(at.into_expr())
        } else {
            None
        };
        let new_prefix = place_new(prefix_value.as_ref())?;
        let updated = Self::apply_projection_update(root, &prefix, new_prefix)
            .ok_or("cell_store_register_field_update")?;
        if updated.sort() != out.sort() {
            return Err("cell_store_register_sort_mismatch");
        }
        Ok(vec![out.eq(updated)])
    }
}

/// `faithful_nested_flat_slot`'s refusals under this lane's reason prefix, so
/// a havoc caused by one is attributable to the Cell register lane.
fn cell_register_flattened_reason(why: &'static str) -> &'static str {
    match why {
        "enum_downcast_in_path" => "cell_store_register_flattened_downcast",
        "slot_unresolved" => "cell_store_register_flattened_slot_unresolved",
        "root_sort_unavailable" => "cell_store_register_flattened_root_sort",
        "local_missing" => "cell_store_register_flattened_local_missing",
        _ => "cell_store_register_flattened_unfaithful",
    }
}

/// `expr` with every variable named in `substitution` replaced by its value.
pub(in crate::codegen_ay::chc) fn substitute_vars(
    expr: &Expr,
    substitution: &HashMap<String, Expr>,
) -> Expr {
    if substitution.is_empty() {
        return expr.clone();
    }
    if let ExprValue::Var { name } = expr.value() {
        return substitution.get(name).cloned().unwrap_or_else(|| expr.clone());
    }
    let children: Vec<&Expr> = expr.children().collect();
    if children.is_empty() {
        return expr.clone();
    }
    let rewritten: Vec<Expr> = children.iter().map(|c| substitute_vars(c, substitution)).collect();
    if rewritten.iter().zip(children.iter()).all(|(new, old)| new == *old) {
        return expr.clone();
    }
    rebuild_with_children(expr, rewritten)
}

/// Whether `expr` mentions the variable `name`.
fn expr_mentions_var(expr: &Expr, name: &str) -> bool {
    let mut stack = vec![expr.clone()];
    while let Some(node) = stack.pop() {
        if let ExprValue::Var { name: var } = node.value()
            && var == name
        {
            return true;
        }
        stack.extend(node.children().cloned());
    }
    false
}

/// Where a local's address goes, for `cell_register_address_reach`.
enum AddressReach {
    /// It never reaches the receiver.
    Contained,
    /// It flows into the receiver.
    Reaches,
    /// It escapes where the scan cannot follow it.
    Escapes,
}

/// Outcome of one address-flow pass.
enum AddressFlow {
    /// The address may be anywhere.
    Escaped,
    /// The address stays in the tracked holders (so far).
    Contained,
}

/// For a canonical interior-mutability accessor taking the held address as
/// its receiver: `Some(true)` when its result is derived from that address
/// (`as_ptr`, `UnsafeCell::get`, `Cell::from_mut`-like views), `Some(false)`
/// when it neither retains nor returns it, `None` for any other callee.
fn accessor_retains(path: &str) -> Option<bool> {
    const CELLS: [&str; 6] = [
        "core::cell::Cell",
        "std::cell::Cell",
        "core::cell::RefCell",
        "std::cell::RefCell",
        "core::cell::UnsafeCell",
        "std::cell::UnsafeCell",
    ];
    const ATOMICS: [&str; 2] = ["core::sync::atomic::Atomic", "std::sync::atomic::Atomic"];
    let canonical =
        CELLS.iter().chain(ATOMICS.iter()).find_map(|prefix| path.strip_prefix(prefix)).is_some();
    if !canonical {
        return None;
    }
    let method = path.rsplit("::").next().unwrap_or_default();
    match method {
        "as_ptr" | "get" if path.contains("UnsafeCell") => Some(true),
        "as_ptr" => Some(true),
        "get"
        | "set"
        | "replace"
        | "take"
        | "replace_with"
        | "swap"
        | "update"
        | "load"
        | "store"
        | "fetch_add"
        | "fetch_sub"
        | "fetch_and"
        | "fetch_or"
        | "fetch_xor"
        | "fetch_nand"
        | "fetch_max"
        | "fetch_min"
        | "compare_exchange"
        | "compare_exchange_weak"
        | "fetch_update" => Some(false),
        _ => None,
    }
}

/// Whether a value of `ty` holds a `payload` BY VALUE where a `Cell` view of
/// it can write one: `ty` is `payload` itself or an array of it
/// (`Cell::from_mut(&mut x)`, `Cell::from_mut(&mut arr).as_slice_of_cells()`).
fn ty_holds_by_value(ty: Ty, payload: Ty) -> bool {
    if ty == payload {
        return true;
    }
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Array(elem, _)) if elem == payload)
}
