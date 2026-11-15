// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A raw access through a `Vec`'s buffer pointer after the `Vec` may have
//! changed fails the harness closed.
//!
//! `Vec::as_ptr` / `as_mut_ptr` / `as_non_null` hand out the buffer's address,
//! and a dereference through that pointer reads typed memory at the buffer's
//! object. The `Vec` stubs keep the contents in the `Vec`'s own model and do
//! not write that memory: an `IndexMut` store after `as_ptr` was not seen by a
//! later `*p.add(1)`, a `push` or `shrink_to_fit` that reallocates and a drop
//! that frees the buffer left the old cells readable, so `assert!(x == 2)` after
//! `v[1] = 9` was a clean proof where Kani fails it and its `x == 9` twin a
//! certified counterexample where Kani proves it (second review of round 9 of
//! fix/chc-false-certificates, `r2_vec.rs` v02, v03, v09, v12, `r2_vec2.rs`
//! w02, w03, w09, w20-w22, w31; the same on main, and the heap checks do not
//! report the dangling read).
//!
//! The rule is a prescan over the body ([`ChcCtx::book_vec_buffer_access_after_mutation`]):
//! an access (a dereference place, a `CopyNonOverlapping` operand, or a call
//! argument of a callee that may dereference it) through a pointer whose
//! single-definition chain reaches a buffer accessor of a `Vec`, at a point
//! reachable from a possible change of that `Vec` which is itself reachable
//! from the accessor call, records a sound fallback reason. A change is a
//! mutable borrow or raw address of the `Vec` (or of a reference to it), a
//! write to a part of it, a move of it into a call or an aggregate, or a drop;
//! a whole move into another local carries the `Vec` along. A mutable borrow
//! handed only to `clear`, `truncate` or `set_len` of a `Vec` of plain scalars
//! changes no byte of the buffer and keeps it in place.
//!
//! Third review of round 10: the pointer may also be a reference made from the
//! buffer pointer (`&*p.add(1)`, `slice::from_raw_parts(p, n)`), a change may
//! go through a mutable handle of the `Vec` taken before the accessor (`vp =
//! &mut v; p = v.as_ptr(); (*vp)[1] = 9`), a `String`'s buffer (`as_mut_ptr`,
//! `str::as_mut_ptr` of `deref_mut`) is a buffer too, and the other direction
//! fails closed as well: a read of the `Vec`'s model (anything but its pointer
//! accessors, `len`, `capacity`, `is_empty` and the drop glue) reachable from a
//! write through its buffer pointer. An access whose dead-target violation
//! ([`ChcCtx::access_through_dead_ref_target`]) the encoder certifies on every
//! path needs no fail-close: it is a dangling access whatever it reads.
//!
//! The module also holds that dead-target test: `ref_targets` names a heap
//! owner's local for its accessor's pointer, and the test tells the owner's
//! own storage (or a dropped unique owner's freed buffer) from a moved `Vec`
//! buffer its new owner keeps alive.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use std::collections::{HashMap, HashSet};

use rustc_public::mir::{
    AggregateKind, BinOp, BorrowKind, Operand, Place, ProjectionElem, Rvalue, StatementKind,
    TerminatorKind,
};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use super::ChcCtx;

/// A statement (`index < statements.len()`) or the terminator
/// (`index == statements.len()`) of block `block`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Site {
    block: usize,
    index: usize,
}

/// Where a buffer pointer comes from: the accessor call's block, the `Vec`
/// place's base local, and the local the accessor takes its reference in.
struct BufferRoot {
    call_block: usize,
    vec_local: usize,
    accessor_arg: Option<usize>,
}

fn operand_place(op: &Operand) -> Option<&Place> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        _ => None,
    }
}

fn whole_local(op: &Operand) -> Option<usize> {
    operand_place(op).filter(|p| p.projection.is_empty()).map(|p| p.local)
}

/// Callee method names that take a raw pointer without reading or writing
/// through it.
const NON_DEREFERENCING_METHODS: &[&str] = &[
    "add",
    "sub",
    "offset",
    "byte_add",
    "byte_sub",
    "byte_offset",
    "wrapping_add",
    "wrapping_sub",
    "wrapping_offset",
    "wrapping_byte_add",
    "wrapping_byte_sub",
    "wrapping_byte_offset",
    "arith_offset",
    "cast",
    "cast_mut",
    "cast_const",
    "addr",
    "expose_provenance",
    "is_null",
    "is_aligned",
    "is_aligned_to",
    "align_offset",
    "with_addr",
    "map_addr",
    "offset_from",
    "byte_offset_from",
    "offset_from_unsigned",
    "precondition_check",
    "eq",
    "ne",
    "new_unchecked",
    "as_ptr",
    "as_mut_ptr",
];

/// Callee method names whose result is the first argument's address moved or
/// re-typed (a buffer pointer stays one).
const POINTER_STEP_METHODS: &[&str] = &[
    "add",
    "sub",
    "offset",
    "byte_add",
    "byte_sub",
    "byte_offset",
    "wrapping_add",
    "wrapping_sub",
    "wrapping_offset",
    "wrapping_byte_add",
    "wrapping_byte_sub",
    "wrapping_byte_offset",
    "arith_offset",
    "cast",
    "cast_mut",
    "cast_const",
    "with_addr",
    "map_addr",
    "as_ptr",
    "as_mut_ptr",
    "new_unchecked",
];

/// [`ChcCtx::dead_ref_target_kind`].
enum DeadRefTarget {
    /// The access dangles: the pointer addresses the dead local's own
    /// storage, or the allocation a unique owner in it freed when dropped.
    Dangling,
    /// The pointer addresses the buffer of a `Vec` moved out of the dead
    /// local, which its new owner keeps alive.
    MovedVecBuffer,
    /// A heap owner's pointer the walk cannot place: fail closed.
    Unresolved,
}

/// A heap-owning type a pointer accessor may take a pointer out of.
struct HeapOwner {
    /// One owner holds the allocation: dropping it frees it.
    unique: bool,
    /// A `Vec` (the buffer [`ChcCtx::buffer_root`] names).
    vec: bool,
}

/// The heap owner the ADT path `name` is, if it is one.
fn heap_owner_kind(name: &str) -> Option<HeapOwner> {
    let name = name.split('<').next().unwrap_or(name);
    let ends = |suffix: &str| name.ends_with(suffix);
    if ends("vec::Vec") {
        return Some(HeapOwner { unique: true, vec: true });
    }
    if ["string::String", "boxed::Box", "raw_vec::RawVec", "vec_deque::VecDeque", "c_str::CString", "os_str::OsString", "path::PathBuf", "binary_heap::BinaryHeap"]
        .iter()
        .any(|s| ends(s))
    {
        return Some(HeapOwner { unique: true, vec: false });
    }
    if ["rc::Rc", "rc::Weak", "sync::Arc", "sync::Weak", "linked_list::LinkedList", "hash_map::HashMap", "hash_set::HashSet", "btree_map::BTreeMap", "btree_set::BTreeSet"]
        .iter()
        .any(|s| ends(s))
    {
        return Some(HeapOwner { unique: false, vec: false });
    }
    None
}

/// The type part of a method path `std::vec::Vec::<T, A>::push`:
/// `std::vec::Vec`.
fn owner_type_prefix(path: &str) -> &str {
    let head = path.rsplit_once("::").map_or(path, |(head, _)| head);
    head.split("::<").next().unwrap_or(head)
}

/// Kani's uninitialized-memory instrumentation (`-Z uninit-checks`):
/// `kani::mem_init::is_ptr_initialized` / `set_ptr_initialized` read and write
/// the shadow memory at a pointer's address, never the bytes behind it.
fn is_shadow_memory_call(path: &str) -> bool {
    path.contains("mem_init::")
}

fn method_name(path: &str) -> &str {
    let method = path.rsplit("::").next().unwrap_or(path);
    method.split('<').next().unwrap_or(method)
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// See the module documentation.
    pub(in crate::codegen_ay::chc) fn book_vec_buffer_access_after_mutation(&self) {
        let body: &rustc_public::mir::Body = self.body;
        if !body.blocks.iter().any(|block| {
            matches!(&block.terminator.kind, TerminatorKind::Call { func, .. }
                if self.resolve_callee_path(func).or_else(|| self.resolve_fn_def_name(func))
                    .is_some_and(|path| matches!(method_name(&path), "as_ptr" | "as_mut_ptr" | "as_non_null")))
        }) {
            // No buffer accessor, and no slice or `str` view's pointer that
            // may be one (`v.as_slice().as_ptr()`).
            return;
        }
        let defs = self.whole_def_sites();
        let reach = self.blocks_reachable_from();
        let dead_at_entry = Self::compute_dead_locals_at_block_entry(self.body);
        let mut roots: HashMap<usize, Option<BufferRoot>> = HashMap::new();
        for (pointer, at, write, dead_checked) in self.raw_pointer_accesses() {
            let root = roots.entry(pointer).or_insert_with(|| self.buffer_root(&defs, pointer));
            let Some(root) = root.as_ref() else { continue };
            // An access the dead-target test fails on every path (the `Vec`'s
            // scope ended: it was dropped, then its storage died) is a certified
            // dangling access whatever value it reads; it needs no fail-close.
            if dead_checked && self.dead_ref_target_certified_at(pointer, at, &dead_at_entry) {
                continue;
            }
            if let Some(change) = self.vec_change_between(&reach, root, at) {
                debug!(
                    fn_name = %self.fn_name,
                    pointer,
                    vec_local = root.vec_local,
                    ?at,
                    ?change,
                    "CHC: an access through a Vec buffer pointer after the Vec may have changed (fail closed)"
                );
                self.record_sound_fallback_reason("vec_buffer_access_after_mutation");
                return;
            }
            // The other direction: the Vec stubs read the contents from the
            // Vec's own model, which a write through the buffer pointer does
            // not reach. `*p = 5; assert!(w[0] == 1)` for `p = v.as_mut_ptr()`
            // and `w = v` was proved where Kani fails it (third review of round
            // 10 of fix/chc-false-certificates, `a03_bug_moved_store_then_read`;
            // the same on main f5dfb8d48).
            if write && let Some(read) = self.vec_model_read_after(&reach, root, at) {
                debug!(
                    fn_name = %self.fn_name,
                    pointer,
                    vec_local = root.vec_local,
                    ?at,
                    ?read,
                    "CHC: the Vec's contents are read after a write through its buffer pointer (fail closed)"
                );
                self.record_sound_fallback_reason("vec_model_read_after_buffer_write");
                return;
            }
        }
    }

    /// Whether an access through the pointer or reference `ptr_local` is a
    /// dangling access because its `ref_targets` entry names a local whose
    /// storage is dead here (#762).
    ///
    /// `ref_targets` takes `Vec::as_ptr` / `as_mut_ptr` (and `String`'s, `Rc`'s
    /// pointer accessors) to the OWNER local, not to the allocation the pointer
    /// addresses. When the owner is moved to another local inside an inner
    /// scope, its storage dies while the buffer lives on in the new owner, and
    /// the dead-target test certified a dangling access where Kani proves the
    /// program: a read (`h01`), a one-element copy out of the buffer (`h02`,
    /// `k01`..`k05`, `n02`, `n05`) and, on the store side, a write (`h03`,
    /// `h04`, `h06`, `h08`) (third review of round 10 of
    /// fix/chc-false-certificates, `r3_dead3.rs`..`r3_dead5.rs`; the read is
    /// the same on main f5dfb8d48).
    ///
    /// The pointer addresses the dead local's own storage unless the target
    /// place is a heap owner and the pointer's pointee is not that owner:
    /// - a unique owner (`Vec`, `String`, `Box`, ...) that is never moved out
    ///   and whose buffer no borrow can hand to another owner was dropped
    ///   before its storage died, so its allocation is freed: dangling;
    /// - a `Vec` moved out whose buffer pointer's single-definition chain
    ///   reaches its accessor addresses the moved buffer, which the new owner
    ///   keeps alive: no violation here (a later drop or change of the new
    ///   owner is [`Self::book_vec_buffer_access_after_mutation`]'s);
    /// - anything else fails the harness closed: the access is still a
    ///   failing obligation, and no counterexample through it is certified.
    pub(in crate::codegen_ay::chc) fn access_through_dead_ref_target(&self, ptr_local: usize) -> bool {
        match self.dead_ref_target_kind(ptr_local, |local| self.liveness.dead_locals.contains(&local)) {
            None | Some(DeadRefTarget::MovedVecBuffer) => false,
            Some(DeadRefTarget::Dangling) => true,
            Some(DeadRefTarget::Unresolved) => {
                debug!(
                    fn_name = %self.fn_name,
                    ptr_local,
                    "CHC: access through a pointer whose dead ref target is a heap owner (fail closed)"
                );
                self.record_sound_fallback_reason("dead_heap_owner_target_unresolved");
                true
            }
        }
    }

    /// Whether the access at `at` through `pointer` is the certified
    /// dangling access of [`Self::access_through_dead_ref_target`] on every
    /// path: its ref target's storage is dead there by the must-analysis the
    /// encoder's liveness follows.
    fn dead_ref_target_certified_at(&self, pointer: usize, at: Site, dead_at_entry: &[HashSet<usize>]) -> bool {
        let Some(entry) = dead_at_entry.get(at.block) else { return false };
        let mut dead = entry.clone();
        for stmt in self.body.blocks[at.block].statements.iter().take(at.index) {
            match &stmt.kind {
                StatementKind::StorageLive(local) => {
                    dead.remove(local);
                }
                StatementKind::StorageDead(local) => {
                    dead.insert(*local);
                }
                _ => {}
            }
        }
        matches!(self.dead_ref_target_kind(pointer, |local| dead.contains(&local)), Some(DeadRefTarget::Dangling))
    }

    /// The classification behind [`Self::access_through_dead_ref_target`],
    /// with `dead` the storage-dead test at the access.
    fn dead_ref_target_kind(&self, ptr_local: usize, dead: impl Fn(usize) -> bool) -> Option<DeadRefTarget> {
        let target = self.ref_resolution.ref_targets.get(&ptr_local)?;
        if !dead(target.local) {
            return None;
        }
        // A constant pointer's pointee (`(*_2)` with `_2 = const &A`) is a
        // static or constant memory that no `StorageDead` ends, so the target
        // is not dead (main's LIVE-statics rule, `ref_target_through_constant`).
        // The read sites bound such an access through the global-object lane
        // or fail closed (`bound_access_through_constant_or_fail_close`), and a
        // store is bounded by `emit_const_object_deref_bound_check`. Classified
        // `Dangling`, a store or copy through `&A as *const _ as *mut u32`
        // after `_2` died would fail on a constant-false obligation.
        if self.ref_target_through_constant(target.local, &target.projections) {
            return None;
        }
        let Some(owner) = self.ref_target_heap_owner(ptr_local, target) else {
            return Some(DeadRefTarget::Dangling);
        };
        let moved_out = self.owner_place_moved_out(target.local, &target.projections);
        if !moved_out
            && owner.unique
            && !self.owner_buffer_may_change_owner(target.local, &target.projections)
        {
            return Some(DeadRefTarget::Dangling);
        }
        if moved_out && owner.vec && self.pointer_addresses_vec_buffer(ptr_local) {
            debug!(
                fn_name = %self.fn_name,
                ptr_local,
                target_local = target.local,
                "CHC: access through a Vec buffer pointer whose owner was moved out of its dead local: the buffer is live"
            );
            return Some(DeadRefTarget::MovedVecBuffer);
        }
        Some(DeadRefTarget::Unresolved)
    }

    /// Whether `ptr_local`'s `ref_targets` entry names a heap owner (a `Vec`,
    /// `String`, `Box`, `Rc`, ...) while the pointer points to something
    /// other than that owner: the pointer addresses the owner's heap
    /// allocation (`Vec::as_mut_ptr`), not the owner local's storage.
    pub(in crate::codegen_ay::chc) fn ref_target_is_foreign_heap_owner(&self, ptr_local: usize) -> bool {
        self.ref_resolution
            .ref_targets
            .get(&ptr_local)
            .is_some_and(|target| self.ref_target_heap_owner(ptr_local, target).is_some())
    }

    /// Whether the raw pointer (or reference) local `pointer` addresses a
    /// `Vec`'s heap buffer: its single-definition chain reaches a buffer
    /// accessor ([`Self::buffer_root`]).
    pub(in crate::codegen_ay::chc) fn pointer_addresses_vec_buffer(&self, pointer: usize) -> bool {
        let defs = self.whole_def_sites();
        self.buffer_root(&defs, pointer).is_some()
    }

    /// The heap owner `target`'s place is, when it is one and `ptr_local`
    /// points to something other than it.
    fn ref_target_heap_owner(
        &self,
        ptr_local: usize,
        target: &crate::codegen_ay::chc::codegen_ctx::RefTarget,
    ) -> Option<HeapOwner> {
        if target.projections.iter().any(|p| matches!(p, ProjectionElem::Deref)) {
            return None;
        }
        let decl = self.body.locals().get(ptr_local)?;
        let pointee = match self.resolve_body_ty(decl.ty).kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _) | RigidTy::Ref(_, inner, _)) => {
                self.resolve_body_ty(inner)
            }
            _ => return None,
        };
        let place = Place { local: target.local, projection: target.projections.clone() };
        let place_ty = self.resolve_body_ty(place.ty(self.body.locals()).ok()?);
        if place_ty == pointee {
            return None;
        }
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = place_ty.kind() else { return None };
        heap_owner_kind(&rustc_public::CrateDef::name(&def))
    }

    /// Whether a place that contains the owner place `local.projections`, or
    /// that place itself, is moved or copied out by value anywhere in the body
    /// (an assignment, a call argument, an aggregate operand). A heap owner is
    /// not `Copy`, so any by-value use of such a place hands its buffer on.
    fn owner_place_moved_out(&self, local: usize, projections: &[ProjectionElem]) -> bool {
        let contains_owner = |op: &Operand| {
            operand_place(op).is_some_and(|p| {
                p.local == local
                    && p.projection.len() <= projections.len()
                    && p.projection.iter().zip(projections).all(|(a, b)| a == b)
            })
        };
        self.body.blocks.iter().any(|block| {
            block.statements.iter().any(|stmt| {
                let StatementKind::Assign(_, rvalue) = &stmt.kind else { return false };
                match rvalue {
                    Rvalue::Use(op, ..) | Rvalue::Cast(_, op, _) | Rvalue::UnaryOp(_, op) => {
                        contains_owner(op)
                    }
                    Rvalue::BinaryOp(_, a, b) => contains_owner(a) || contains_owner(b),
                    Rvalue::Aggregate(_, ops) => ops.iter().any(contains_owner),
                    Rvalue::Repeat(op, _) => contains_owner(op),
                    _ => false,
                }
            }) || matches!(&block.terminator.kind,
                TerminatorKind::Call { args, .. } if args.iter().any(contains_owner))
        })
    }

    /// Whether a borrow of the owner place `local.projections` (or of a place
    /// that contains it or lies in it) may hand the owner's buffer to another
    /// owner (`mem::swap`, `mem::take`, a whole write through it): any
    /// mutable borrow or raw address whose derived references are used other
    /// than to read through, as the receiver of one of the owner type's own
    /// methods (which keep the buffer in the owner or free it), or by the drop
    /// glue.
    fn owner_buffer_may_change_owner(&self, local: usize, projections: &[ProjectionElem]) -> bool {
        let related = |place: &Place| {
            place.local == local
                && !place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
                && place.projection.iter().zip(projections).all(|(a, b)| a == b)
        };
        let mut handles: HashSet<usize> = HashSet::new();
        loop {
            let before = handles.len();
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    let StatementKind::Assign(lhs, rvalue) = &stmt.kind else { continue };
                    let derived = match rvalue {
                        Rvalue::Ref(_, kind, place) => {
                            (related(place) && !matches!(kind, BorrowKind::Shared | BorrowKind::Fake(_)))
                                || (handles.contains(&place.local)
                                    && matches!(place.projection.first(), Some(ProjectionElem::Deref)))
                        }
                        Rvalue::AddressOf(_, place) => {
                            related(place)
                                || (handles.contains(&place.local)
                                    && matches!(place.projection.first(), Some(ProjectionElem::Deref)))
                        }
                        Rvalue::Use(op, ..) | Rvalue::Cast(_, op, _) => {
                            whole_local(op).is_some_and(|l| handles.contains(&l))
                        }
                        _ => false,
                    };
                    if derived {
                        if !lhs.projection.is_empty() {
                            return true;
                        }
                        handles.insert(lhs.local);
                    }
                }
            }
            if handles.len() == before {
                break;
            }
        }
        if handles.is_empty() {
            return false;
        }
        let mentions = |op: &Operand| operand_place(op).is_some_and(|p| handles.contains(&p.local));
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(lhs, rvalue) = &stmt.kind else { continue };
                // A write through a handle, or a handle stored into a place.
                if handles.contains(&lhs.local) && matches!(lhs.projection.first(), Some(ProjectionElem::Deref)) {
                    return true;
                }
                let stored = match rvalue {
                    Rvalue::Aggregate(_, ops) => ops.iter().any(mentions),
                    Rvalue::Use(op, ..) | Rvalue::Cast(_, op, _) => {
                        mentions(op) && !(lhs.projection.is_empty() && whole_local(op).is_some())
                    }
                    _ => false,
                };
                if stored {
                    return true;
                }
            }
            if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind {
                if handles.contains(&destination.local)
                    && matches!(destination.projection.first(), Some(ProjectionElem::Deref))
                {
                    return true;
                }
                if !args.iter().any(mentions) {
                    continue;
                }
                let path = self.resolve_callee_path(func).or_else(|| self.resolve_fn_def_name(func));
                let Some(path) = path else { return true };
                if is_shadow_memory_call(&path) {
                    continue;
                }
                let drop_glue = path.contains("drop_in_place") || path.ends_with("as std::ops::Drop>::drop")
                    || path.ends_with("as core::ops::Drop>::drop") || path.ends_with("Drop>::drop");
                let receiver_only = args.iter().skip(1).all(|op| !mentions(op))
                    && args.first().is_some_and(&mentions);
                let own_method = heap_owner_kind(owner_type_prefix(&path)).is_some()
                    && !matches!(method_name(&path), "as_mut_vec" | "leak" | "into_raw" | "as_mut")
                    && !path.contains(" as ");
                if !(drop_glue || (receiver_only && own_method)) {
                    return true;
                }
            }
        }
        false
    }

    /// A `Vec`'s, or a `String`'s, buffer accessor. A `String` is a `Vec<u8>`
    /// whose buffer its drop frees as well: a read through `s.as_mut_ptr()`
    /// after `s`'s scope ended read the freed cells and was proved where Kani
    /// reports a dangling read (round 10 repair of the third review,
    /// `bug_string_dropped_read`; the same on main f5dfb8d48).
    fn is_vec_buffer_accessor(path: &str) -> bool {
        (path.contains("vec::Vec") || path.contains("string::String"))
            && matches!(method_name(path), "as_ptr" | "as_mut_ptr" | "as_non_null")
    }

    fn whole_def_sites(&self) -> HashMap<usize, Vec<Site>> {
        let mut defs: HashMap<usize, Vec<Site>> = HashMap::new();
        for (bb, block) in self.body.blocks.iter().enumerate() {
            for (si, stmt) in block.statements.iter().enumerate() {
                if let StatementKind::Assign(place, _) = &stmt.kind
                    && place.projection.is_empty()
                {
                    defs.entry(place.local).or_default().push(Site { block: bb, index: si });
                }
            }
            if let TerminatorKind::Call { destination, .. } = &block.terminator.kind
                && destination.projection.is_empty()
            {
                defs.entry(destination.local)
                    .or_default()
                    .push(Site { block: bb, index: block.statements.len() });
            }
        }
        defs
    }

    /// `reach[b]`: the blocks reachable from `b` along at least one edge.
    fn blocks_reachable_from(&self) -> Vec<HashSet<usize>> {
        let blocks = &self.body.blocks;
        (0..blocks.len())
            .map(|start| {
                let mut seen = HashSet::new();
                let mut stack: Vec<usize> = blocks[start].terminator.successors();
                while let Some(bb) = stack.pop() {
                    if bb < blocks.len() && seen.insert(bb) {
                        stack.extend(blocks[bb].terminator.successors());
                    }
                }
                seen
            })
            .collect()
    }

    fn local_is_raw_pointer(&self, local: usize) -> bool {
        self.body.locals().get(local).is_some_and(|decl| {
            matches!(self.resolve_body_ty(decl.ty).kind(), TyKind::RigidTy(RigidTy::RawPtr(..)))
        })
    }

    /// A raw pointer or a reference: a reference made from a buffer pointer
    /// (`&*p.add(1)`, `slice::from_raw_parts(p, n)`) reads the buffer as the
    /// pointer does (third review of round 10, `r3_vecbuf.rs` v05, v06).
    fn local_is_pointer_like(&self, local: usize) -> bool {
        self.body.locals().get(local).is_some_and(|decl| {
            matches!(
                self.resolve_body_ty(decl.ty).kind(),
                TyKind::RigidTy(RigidTy::RawPtr(..) | RigidTy::Ref(..))
            )
        })
    }

    /// Every access through a raw pointer or reference local:
    /// `(pointer, site, may_write, dead_checked)`, where `dead_checked` says
    /// the encoder's dead-target test runs at it (a dereference place of a
    /// statement, a whole operand of a `CopyNonOverlapping`).
    fn raw_pointer_accesses(&self) -> Vec<(usize, Site, bool, bool)> {
        let mut out = Vec::new();
        let deref_place = |place: &Place, at: Site, write: bool, checked: bool, out: &mut Vec<(usize, Site, bool, bool)>| {
            if matches!(place.projection.first(), Some(ProjectionElem::Deref))
                && self.local_is_pointer_like(place.local)
            {
                out.push((place.local, at, write, checked));
            }
        };
        for (bb, block) in self.body.blocks.iter().enumerate() {
            for (si, stmt) in block.statements.iter().enumerate() {
                let at = Site { block: bb, index: si };
                match &stmt.kind {
                    StatementKind::Assign(lhs, rvalue) => {
                        // The store side's dead-target test runs for a raw
                        // pointer base only.
                        deref_place(lhs, at, true, self.local_is_raw_pointer(lhs.local), &mut out);
                        let mut operands: Vec<&Operand> = Vec::new();
                        match rvalue {
                            Rvalue::Use(op, ..) | Rvalue::Cast(_, op, _) | Rvalue::UnaryOp(_, op) => {
                                operands.push(op)
                            }
                            Rvalue::BinaryOp(_, a, b) => {
                                operands.push(a);
                                operands.push(b);
                            }
                            Rvalue::Aggregate(_, ops) => operands.extend(ops.iter()),
                            Rvalue::Repeat(op, _) => operands.push(op),
                            Rvalue::Discriminant(place) | Rvalue::CopyForDeref(place) => {
                                deref_place(place, at, false, false, &mut out)
                            }
                            // `&mut (*p).f` / `&raw mut (*p)`: a reference that may
                            // write through `p` later (its own uses are accesses
                            // through it in turn).
                            Rvalue::Ref(_, BorrowKind::Mut { .. }, place)
                            | Rvalue::AddressOf(rustc_public::mir::RawPtrKind::Mut, place) => {
                                deref_place(place, at, true, false, &mut out)
                            }
                            _ => {}
                        }
                        for op in operands {
                            if let Some(place) = operand_place(op) {
                                deref_place(place, at, false, true, &mut out);
                            }
                        }
                    }
                    StatementKind::Intrinsic(
                        rustc_public::mir::NonDivergingIntrinsic::CopyNonOverlapping(copy),
                    ) => {
                        for (op, write) in [(&copy.src, false), (&copy.dst, true)] {
                            if let Some(local) = whole_local(op).filter(|&l| self.local_is_pointer_like(l)) {
                                out.push((local, at, write, true));
                            }
                            if let Some(place) = operand_place(op) {
                                deref_place(place, at, false, false, &mut out);
                            }
                        }
                    }
                    _ => {}
                }
            }
            let at = Site { block: bb, index: block.statements.len() };
            match &block.terminator.kind {
                TerminatorKind::Call { func, args, destination, .. } => {
                    deref_place(destination, at, true, false, &mut out);
                    let path =
                        self.resolve_callee_path(func).or_else(|| self.resolve_fn_def_name(func));
                    // `core::ub_checks` (`maybe_is_aligned_and_not_null`,
                    // `maybe_is_nonoverlapping`) inspects the address only.
                    let reads_through = !path.as_deref().is_some_and(|p| {
                        NON_DEREFERENCING_METHODS.contains(&method_name(p))
                            || p.contains("ub_checks::")
                            || is_shadow_memory_call(p)
                    });
                    // The intrinsics whose CHC handlers write a `Vec`'s model
                    // through its buffer pointer (`volatile_store(v.as_mut_ptr(),
                    // x)`, `write_bytes`) keep a later read of the model exact.
                    let writes_model = path.as_deref().is_some_and(|p| {
                        matches!(
                            method_name(p),
                            "volatile_store" | "volatile_set_memory" | "write_bytes" | "write_volatile"
                        )
                    });
                    for op in args {
                        if let Some(place) = operand_place(op) {
                            deref_place(place, at, false, false, &mut out);
                        }
                        if reads_through
                            && let Some(local) = whole_local(op).filter(|&l| self.local_is_pointer_like(l))
                        {
                            out.push((local, at, !writes_model, false));
                        }
                    }
                }
                TerminatorKind::SwitchInt { discr, .. } => {
                    if let Some(place) = operand_place(discr) {
                        deref_place(place, at, false, false, &mut out);
                    }
                }
                TerminatorKind::Assert { cond, .. } => {
                    if let Some(place) = operand_place(cond) {
                        deref_place(place, at, false, false, &mut out);
                    }
                }
                _ => {}
            }
        }
        out
    }

    /// The buffer accessor `pointer`'s single-definition chain reaches, if any:
    /// through whole copies and casts, `Offset`, reborrows of a pointee,
    /// thin pointer rebuilds, pointer steps and casts, and `<[T]>::as_ptr` of a
    /// `Vec`'s slice view.
    fn buffer_root(&self, defs: &HashMap<usize, Vec<Site>>, pointer: usize) -> Option<BufferRoot> {
        let mut cur = pointer;
        let mut seen = HashSet::new();
        while seen.insert(cur) && seen.len() <= 48 {
            let [site] = defs.get(&cur)?.as_slice() else { return None };
            let block = &self.body.blocks[site.block];
            if site.index < block.statements.len() {
                let StatementKind::Assign(_, rvalue) = &block.statements[site.index].kind else {
                    return None;
                };
                cur = match rvalue {
                    Rvalue::Use(op, ..) | Rvalue::Cast(_, op, _) => whole_local(op)?,
                    Rvalue::BinaryOp(BinOp::Offset, op, _) => whole_local(op)?,
                    Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)
                        if matches!(place.projection.first(), Some(ProjectionElem::Deref)) =>
                    {
                        place.local
                    }
                    Rvalue::Aggregate(AggregateKind::RawPtr(..), ops) => whole_local(ops.first()?)?,
                    _ => return None,
                };
                continue;
            }
            let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else {
                return None;
            };
            let path = self.resolve_callee_path(func).or_else(|| self.resolve_fn_def_name(func))?;
            let arg0 = args.first()?;
            if Self::is_vec_buffer_accessor(&path) {
                return self.vec_root_of_reference(defs, arg0, site.block);
            }
            let method = method_name(&path);
            if (path.contains("slice") || path.contains("<impl str>")) && matches!(method, "as_ptr" | "as_mut_ptr") {
                // `<[T]>::as_ptr(s)` of `s = Vec::deref(&v)` / `as_slice(&v)`,
                // and `str::as_mut_ptr(s)` of `s = String::deref_mut(&mut t)`.
                let slice = whole_local(arg0)?;
                let [slice_site] = defs.get(&slice)?.as_slice() else { return None };
                let slice_block = &self.body.blocks[slice_site.block];
                if slice_site.index < slice_block.statements.len() {
                    return None;
                }
                let TerminatorKind::Call { func: view, args: view_args, .. } =
                    &slice_block.terminator.kind
                else {
                    return None;
                };
                let view_path =
                    self.resolve_callee_path(view).or_else(|| self.resolve_fn_def_name(view))?;
                if !((view_path.contains("vec::Vec") || view_path.contains("string::String"))
                    && matches!(
                        method_name(&view_path),
                        "deref" | "deref_mut" | "as_slice" | "as_mut_slice" | "as_str" | "as_mut_str"
                    ))
                {
                    return None;
                }
                return self.vec_root_of_reference(defs, view_args.first()?, site.block);
            }
            // `slice::from_raw_parts(p, n)` / `ptr::slice_from_raw_parts(p, n)`:
            // a slice over the buffer from `p` (third review of round 10,
            // `r3_vecbuf.rs` v06).
            let slice_over = matches!(
                method,
                "from_raw_parts" | "from_raw_parts_mut" | "slice_from_raw_parts" | "slice_from_raw_parts_mut"
            ) && (path.contains("slice") || path.contains("ptr"));
            let stepping = slice_over
                || POINTER_STEP_METHODS.contains(&method)
                    && (path.contains("const_ptr")
                        || path.contains("mut_ptr")
                        || path.contains("ptr::NonNull")
                        || path.contains("ptr::non_null"))
                || path.contains("intrinsics::offset")
                || path.contains("intrinsics::arith_offset");
            if !stepping {
                return None;
            }
            cur = whole_local(arg0)?;
        }
        None
    }

    /// The `Vec` the reference operand `arg` of an accessor names: the base
    /// local of the borrowed place (`&v`, `&mut v`, `&s.v`), or, for a
    /// reborrow `&(*r)` of a reference `r`, `r` itself.
    fn vec_root_of_reference(
        &self,
        defs: &HashMap<usize, Vec<Site>>,
        arg: &Operand,
        call_block: usize,
    ) -> Option<BufferRoot> {
        let reference = whole_local(arg)?;
        let vec_local = match defs.get(&reference).map(Vec::as_slice) {
            Some([site]) if site.index < self.body.blocks[site.block].statements.len() => {
                match &self.body.blocks[site.block].statements[site.index].kind {
                    StatementKind::Assign(_, Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)) => {
                        place.local
                    }
                    StatementKind::Assign(_, Rvalue::Use(op, ..)) => whole_local(op)?,
                    _ => reference,
                }
            }
            _ => reference,
        };
        Some(BufferRoot { call_block, vec_local, accessor_arg: Some(reference) })
    }

    /// A possible change of `root`'s `Vec` reachable from its accessor call
    /// and from which `access` is reachable.
    fn vec_change_between(
        &self,
        reach: &[HashSet<usize>],
        root: &BufferRoot,
        access: Site,
    ) -> Option<Site> {
        let aliases = self.vec_aliases(root.vec_local);
        let after_call = |at: Site| reach.get(root.call_block).is_some_and(|r| r.contains(&at.block));
        let before_access = |at: Site| {
            (at.block == access.block && at.index < access.index)
                || reach.get(at.block).is_some_and(|r| r.contains(&access.block))
        };
        self.vec_change_sites(&aliases, root)
            .into_iter()
            .find(|&at| after_call(at) && before_access(at))
    }

    /// The `Vec` local and every local a whole copy or move of it reaches.
    fn vec_aliases(&self, vec_local: usize) -> HashSet<usize> {
        let mut aliases: HashSet<usize> = HashSet::from([vec_local]);
        loop {
            let before = aliases.len();
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    if let StatementKind::Assign(lhs, Rvalue::Use(op, ..)) = &stmt.kind
                        && lhs.projection.is_empty()
                        && whole_local(op).is_some_and(|l| aliases.contains(&l))
                    {
                        aliases.insert(lhs.local);
                    }
                }
            }
            if aliases.len() == before {
                return aliases;
            }
        }
    }

    /// The locals holding a mutable borrow or a raw address of the `Vec`
    /// (an alias of it, or a part of one), whenever it was taken, other than
    /// the accessor's own receiver, and every local a whole copy, cast or
    /// reborrow through a dereference of one reaches. A write through one
    /// taken BEFORE the accessor changes the `Vec` as a fresh borrow does:
    /// `vp = &mut v; p = v.as_ptr(); (*vp)[1] = 9; *p.add(1)` read the old
    /// byte (third review of round 10, `r3_vecbuf.rs` v10; the same on main).
    fn vec_mutable_handles(&self, aliases: &HashSet<usize>, root: &BufferRoot) -> HashSet<usize> {
        let mut handles: HashSet<usize> = HashSet::new();
        loop {
            let before = handles.len();
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    let StatementKind::Assign(lhs, rvalue) = &stmt.kind else { continue };
                    if !lhs.projection.is_empty() || Some(lhs.local) == root.accessor_arg {
                        continue;
                    }
                    let behind_handle = |place: &Place| {
                        handles.contains(&place.local)
                            && matches!(place.projection.first(), Some(ProjectionElem::Deref))
                    };
                    let derived = match rvalue {
                        Rvalue::Ref(_, kind, place) => {
                            (aliases.contains(&place.local)
                                && !place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
                                && !matches!(kind, BorrowKind::Shared | BorrowKind::Fake(_))
                                && !self.borrow_only_resizes_in_place(lhs.local, place.local))
                                || behind_handle(place)
                        }
                        Rvalue::AddressOf(_, place) => {
                            (aliases.contains(&place.local)
                                && !place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref)))
                                || behind_handle(place)
                        }
                        Rvalue::Use(op, ..) | Rvalue::Cast(_, op, _) => {
                            whole_local(op).is_some_and(|l| handles.contains(&l))
                        }
                        _ => false,
                    };
                    if derived {
                        handles.insert(lhs.local);
                    }
                }
            }
            if handles.len() == before {
                return handles;
            }
        }
    }

    fn vec_change_sites(&self, aliases: &HashSet<usize>, root: &BufferRoot) -> Vec<Site> {
        let rooted = |place: &Place| aliases.contains(&place.local);
        let handles = self.vec_mutable_handles(aliases, root);
        let through_handle = |place: &Place| handles.contains(&place.local);
        let handle_operand = |op: &Operand| operand_place(op).is_some_and(|p| handles.contains(&p.local));
        let mut out = Vec::new();
        for (bb, block) in self.body.blocks.iter().enumerate() {
            for (si, stmt) in block.statements.iter().enumerate() {
                let at = Site { block: bb, index: si };
                let StatementKind::Assign(lhs, rvalue) = &stmt.kind else { continue };
                // A use of a handle other than to copy it whole: a write
                // through it, a reborrow of what it points to, or the handle
                // stored into a place or an aggregate.
                let uses_handle = (through_handle(lhs) && !lhs.projection.is_empty())
                    || match rvalue {
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => through_handle(place),
                        Rvalue::Use(op, ..) | Rvalue::Cast(_, op, _) => {
                            handle_operand(op) && !(lhs.projection.is_empty() && whole_local(op).is_some())
                        }
                        Rvalue::Aggregate(_, ops) => ops.iter().any(handle_operand),
                        _ => false,
                    };
                if uses_handle {
                    out.push(at);
                }
            }
            if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                && (args.iter().any(handle_operand) || through_handle(destination))
                && !self
                    .resolve_callee_path(func)
                    .or_else(|| self.resolve_fn_def_name(func))
                    .is_some_and(|path| is_shadow_memory_call(&path))
            {
                out.push(Site { block: bb, index: block.statements.len() });
            }
            if let TerminatorKind::Drop { place, .. } = &block.terminator.kind
                && through_handle(place)
            {
                out.push(Site { block: bb, index: block.statements.len() });
            }
        }
        for (bb, block) in self.body.blocks.iter().enumerate() {
            for (si, stmt) in block.statements.iter().enumerate() {
                let at = Site { block: bb, index: si };
                let StatementKind::Assign(lhs, rvalue) = &stmt.kind else {
                    if let StatementKind::SetDiscriminant { place, .. } = &stmt.kind
                        && rooted(place)
                    {
                        out.push(at);
                    }
                    continue;
                };
                if rooted(lhs) && !lhs.projection.is_empty() {
                    out.push(at);
                    continue;
                }
                let changes = match rvalue {
                    Rvalue::Ref(_, kind, place) if rooted(place) => {
                        !matches!(kind, BorrowKind::Shared | BorrowKind::Fake(_))
                            && Some(lhs.local) != root.accessor_arg
                            && !(lhs.projection.is_empty() && self.borrow_only_resizes_in_place(lhs.local, place.local))
                    }
                    Rvalue::AddressOf(_, place) if rooted(place) => {
                        Some(lhs.local) != root.accessor_arg
                            && !(lhs.projection.is_empty() && self.borrow_used_only_by_shadow_memory(lhs.local))
                    }
                    Rvalue::Aggregate(_, ops) => ops.iter().any(|op| {
                        matches!(op, Operand::Move(p) if rooted(p))
                            || whole_local(op).is_some_and(|l| aliases.contains(&l) && self.local_is_mut_reference(l))
                    }),
                    _ => false,
                };
                if changes {
                    out.push(at);
                }
            }
            let at = Site { block: bb, index: block.statements.len() };
            match &block.terminator.kind {
                TerminatorKind::Drop { place, .. } if rooted(place) => out.push(at),
                TerminatorKind::Call { args, destination, .. } => {
                    let changes = rooted(destination)
                        || args.iter().any(|op| match op {
                            Operand::Move(p) if rooted(p) => true,
                            Operand::Copy(p) if rooted(p) => {
                                p.projection.is_empty() && self.local_is_mut_reference(p.local)
                            }
                            _ => false,
                        });
                    if changes {
                        out.push(at);
                    }
                }
                _ => {}
            }
        }
        out
    }

    /// A read of the `Vec`'s contents through its model reachable from the
    /// write `write` through its buffer pointer.
    fn vec_model_read_after(
        &self,
        reach: &[HashSet<usize>],
        root: &BufferRoot,
        write: Site,
    ) -> Option<Site> {
        let aliases = self.vec_aliases(root.vec_local);
        let after = |at: Site| {
            (at.block == write.block && at.index > write.index)
                || reach.get(write.block).is_some_and(|r| r.contains(&at.block))
        };
        self.vec_model_read_sites(&aliases).into_iter().find(|&at| after(at))
    }

    /// The sites that may read the contents of the `Vec` (`aliases`) through
    /// its model: a borrow of it used other than by its pointer accessors,
    /// `len` / `capacity` / `is_empty` and the drop glue, a read of a part of
    /// it, and a move of it into a call or an aggregate.
    fn vec_model_read_sites(&self, aliases: &HashSet<usize>) -> Vec<Site> {
        let rooted = |place: &Place| {
            aliases.contains(&place.local)
                && !place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
        };
        let mut out = Vec::new();
        for (bb, block) in self.body.blocks.iter().enumerate() {
            for (si, stmt) in block.statements.iter().enumerate() {
                let at = Site { block: bb, index: si };
                let StatementKind::Assign(lhs, rvalue) = &stmt.kind else { continue };
                let reads = match rvalue {
                    Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) if rooted(place) => {
                        !(lhs.projection.is_empty() && self.borrow_reads_no_contents(lhs.local))
                    }
                    Rvalue::Use(op, ..) | Rvalue::Cast(_, op, _) => {
                        operand_place(op).is_some_and(|p| rooted(p) && !p.projection.is_empty())
                    }
                    Rvalue::Aggregate(_, ops) => ops.iter().any(|op| operand_place(op).is_some_and(rooted)),
                    _ => false,
                };
                if reads {
                    out.push(at);
                }
            }
            if let TerminatorKind::Call { args, .. } = &block.terminator.kind
                && args.iter().any(|op| operand_place(op).is_some_and(rooted))
            {
                out.push(Site { block: bb, index: block.statements.len() });
            }
        }
        out
    }

    /// Whether the borrow `borrow` of a `Vec`, and every reference derived
    /// from it (whole copies, casts, reborrows through it), is only the
    /// receiver of a call that reads none of the contents: a pointer
    /// accessor, `len`, `capacity`, `is_empty`, or the drop glue.
    fn borrow_reads_no_contents(&self, borrow: usize) -> bool {
        let mut refs: HashSet<usize> = HashSet::from([borrow]);
        loop {
            let before = refs.len();
            for block in &self.body.blocks {
                for stmt in &block.statements {
                    let StatementKind::Assign(lhs, rvalue) = &stmt.kind else { continue };
                    let derived = match rvalue {
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                            refs.contains(&place.local)
                                && matches!(place.projection.first(), Some(ProjectionElem::Deref))
                        }
                        Rvalue::Use(op, ..) | Rvalue::Cast(_, op, _) => {
                            whole_local(op).is_some_and(|l| refs.contains(&l))
                        }
                        _ => false,
                    };
                    if derived {
                        if !lhs.projection.is_empty() {
                            return false;
                        }
                        refs.insert(lhs.local);
                    }
                }
            }
            if refs.len() == before {
                break;
            }
        }
        let mentions = |op: &Operand| operand_place(op).is_some_and(|p| refs.contains(&p.local));
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let StatementKind::Assign(lhs, rvalue) = &stmt.kind else { continue };
                if refs.contains(&lhs.local) && !lhs.projection.is_empty() {
                    return false;
                }
                let other_use = match rvalue {
                    Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                        refs.contains(&place.local)
                            && !(lhs.projection.is_empty()
                                && matches!(place.projection.first(), Some(ProjectionElem::Deref)))
                    }
                    Rvalue::Use(op, ..) | Rvalue::Cast(_, op, _) => {
                        mentions(op) && !(lhs.projection.is_empty() && whole_local(op).is_some())
                    }
                    Rvalue::Aggregate(_, ops) => ops.iter().any(mentions),
                    Rvalue::BinaryOp(_, a, b) => mentions(a) || mentions(b),
                    Rvalue::UnaryOp(_, op) | Rvalue::Repeat(op, _) => mentions(op),
                    Rvalue::Discriminant(place) | Rvalue::CopyForDeref(place) => refs.contains(&place.local),
                    _ => false,
                };
                if other_use {
                    return false;
                }
            }
            match &block.terminator.kind {
                TerminatorKind::Call { func, args, destination, .. } => {
                    if refs.contains(&destination.local) && !destination.projection.is_empty() {
                        return false;
                    }
                    if !args.iter().any(mentions) {
                        continue;
                    }
                    let Some(path) = self.resolve_callee_path(func).or_else(|| self.resolve_fn_def_name(func))
                    else {
                        return false;
                    };
                    if is_shadow_memory_call(&path) {
                        continue;
                    }
                    let drop_glue = path.contains("drop_in_place") || path.ends_with("Drop>::drop");
                    let no_contents = matches!(
                        method_name(&path),
                        "as_ptr" | "as_mut_ptr" | "as_non_null" | "len" | "capacity" | "is_empty"
                    ) && (path.contains("vec::Vec") || path.contains("string::String"));
                    let receiver_only =
                        args.first().is_some_and(&mentions) && !args.iter().skip(1).any(&mentions);
                    if !(receiver_only && (drop_glue || no_contents)) {
                        return false;
                    }
                }
                TerminatorKind::Drop { .. } => {}
                TerminatorKind::SwitchInt { discr, .. } if mentions(discr) => return false,
                TerminatorKind::Assert { cond, .. } if mentions(cond) => return false,
                _ => {}
            }
        }
        true
    }

    /// Whether the raw address `borrow` is only an argument of Kani's
    /// shadow-memory instrumentation ([`is_shadow_memory_call`]).
    fn borrow_used_only_by_shadow_memory(&self, borrow: usize) -> bool {
        let mentions = |op: &Operand| operand_place(op).is_some_and(|p| p.local == borrow);
        let mut used = false;
        for block in &self.body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(lhs, rvalue) = &stmt.kind {
                    let mention = lhs.local == borrow && !lhs.projection.is_empty()
                        || match rvalue {
                            Rvalue::Use(op, ..) | Rvalue::Cast(_, op, _) | Rvalue::UnaryOp(_, op) | Rvalue::Repeat(op, _) => {
                                mentions(op)
                            }
                            Rvalue::BinaryOp(_, a, b) => mentions(a) || mentions(b),
                            Rvalue::Aggregate(_, ops) => ops.iter().any(mentions),
                            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => place.local == borrow,
                            Rvalue::Discriminant(place) | Rvalue::CopyForDeref(place) => place.local == borrow,
                            _ => false,
                        };
                    if mention {
                        return false;
                    }
                }
            }
            match &block.terminator.kind {
                TerminatorKind::Call { func, args, destination, .. } => {
                    if destination.local == borrow {
                        return false;
                    }
                    if args.iter().any(mentions) {
                        let shadow = self
                            .resolve_callee_path(func)
                            .or_else(|| self.resolve_fn_def_name(func))
                            .is_some_and(|path| is_shadow_memory_call(&path));
                        if !shadow {
                            return false;
                        }
                        used = true;
                    }
                }
                TerminatorKind::SwitchInt { discr, .. } if mentions(discr) => return false,
                TerminatorKind::Assert { cond, .. } if mentions(cond) => return false,
                TerminatorKind::Drop { place, .. } if place.local == borrow => return false,
                _ => {}
            }
        }
        used
    }

    fn local_is_mut_reference(&self, local: usize) -> bool {
        self.body.locals().get(local).is_some_and(|decl| {
            matches!(
                self.resolve_body_ty(decl.ty).kind(),
                TyKind::RigidTy(RigidTy::Ref(_, _, rustc_public::mir::Mutability::Mut))
                    | TyKind::RigidTy(RigidTy::RawPtr(_, rustc_public::mir::Mutability::Mut))
            )
        })
    }

    /// Whether the mutable borrow `borrow` of the `Vec` local `vec` is only the
    /// receiver of `Vec::clear`, `truncate` or `set_len` of plain scalar
    /// elements: none writes a byte of the buffer or moves it.
    fn borrow_only_resizes_in_place(&self, borrow: usize, vec: usize) -> bool {
        let scalar_elements = self.body.locals().get(vec).is_some_and(|decl| {
            let TyKind::RigidTy(RigidTy::Adt(def, args)) = self.resolve_body_ty(decl.ty).kind() else {
                return false;
            };
            if !rustc_public::CrateDef::name(&def).contains("vec::Vec") {
                return false;
            }
            args.0.first().is_some_and(|arg| match arg {
                rustc_public::ty::GenericArgKind::Type(t) => matches!(
                    self.resolve_body_ty(*t).kind(),
                    TyKind::RigidTy(
                        RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_) | RigidTy::Bool | RigidTy::Char
                    )
                ),
                _ => false,
            })
        });
        if !scalar_elements {
            return false;
        }
        let mut uses = 0usize;
        let mut only_resize = true;
        for block in &self.body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(lhs, rvalue) = &stmt.kind {
                    let mentions = match rvalue {
                        Rvalue::Use(op, ..) | Rvalue::Cast(_, op, _) => {
                            operand_place(op).is_some_and(|p| p.local == borrow)
                        }
                        Rvalue::Ref(_, _, p) | Rvalue::AddressOf(_, p) => p.local == borrow,
                        Rvalue::Aggregate(_, ops) => {
                            ops.iter().any(|op| operand_place(op).is_some_and(|p| p.local == borrow))
                        }
                        _ => false,
                    } || (lhs.local == borrow && !lhs.projection.is_empty());
                    if mentions {
                        only_resize = false;
                    }
                }
            }
            if let TerminatorKind::Call { func, args, .. } = &block.terminator.kind
                && args.iter().any(|op| operand_place(op).is_some_and(|p| p.local == borrow))
            {
                uses += 1;
                let path = self.resolve_callee_path(func).or_else(|| self.resolve_fn_def_name(func));
                let resize = path.as_deref().is_some_and(|p| {
                    p.contains("vec::Vec") && matches!(method_name(p), "clear" | "truncate" | "set_len")
                });
                let receiver = args.first().and_then(whole_local) == Some(borrow);
                if !(resize && receiver) {
                    only_resize = false;
                }
            }
        }
        only_resize && uses == 1
    }
}
