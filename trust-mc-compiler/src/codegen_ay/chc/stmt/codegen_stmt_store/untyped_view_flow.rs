// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Where values travel inside one MIR body, for the two untyped-view nets
//! (`untyped_view_scan.rs`).
//!
//! Both nets follow a value of interest (a pointer cast to another view of
//! pointer-carrying bytes; a pointer into a static) from where it is made to
//! where it is used. Following only direct copies and casts lost it on every
//! carrier the review of fix/chc-lost-writes round 7 found (findings 1-3): a
//! reference to the pointer local read back as `copy (*r)`, a struct, tuple or
//! array field, an `Option` payload, a closure environment capturing the local
//! by reference, a helper taking `&q`, a `CheckedBinaryOp` or `UnaryOp` on an
//! address. This module follows every carrier instead, as a flow-insensitive
//! and field-insensitive over-approximation:
//!
//! - every local, and one cell standing for all memory outside the body's
//!   locals ([`Cell::Ext`]: the heap, statics, a caller's frame), has
//!   [`Contents`]: the tracked value it may carry anywhere inside it (joined in
//!   the net's lattice) and the cells whose address it may hold anywhere inside
//!   it;
//! - an assignment adds the right-hand side's contents to every cell the
//!   left-hand place may denote; a read through a pointer reads the contents of
//!   every cell the pointer may address;
//! - a call may store anything reachable from its arguments into any cell
//!   reachable from them, and may return any of it.
//!
//! The net-specific part (what a cast, a reborrow, arithmetic or a
//! pointer-returning callee makes of a tracked value) is [`FlowRules`]. The
//! nets' checks then ask the solved flow what a place, an operand or a call
//! may carry.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use std::collections::{BTreeSet, HashMap};

use rustc_public::mir::{
    BinOp, Body, CastKind, NonDivergingIntrinsic, Operand, Place, ProjectionElem, Rvalue,
    StatementKind, TerminatorKind,
};
use rustc_public::ty::{IntTy, RigidTy, Ty, TyKind, UintTy};

use super::untyped_view_scan::{may_hold_pointer, memory_of_constant};

/// Fixpoint rounds before the flow gives up; a body that has not converged by
/// then is answered with [`Flow::saturated`], and the nets flag every block.
const MAX_ROUNDS: usize = 200;

/// A place a value can live in.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub(super) enum Cell {
    /// A local of the body, as a whole (fields are not told apart).
    Local(usize),
    /// Memory outside the body's locals.
    Ext,
    /// Anonymous constant memory a constant operand points into (a promoted
    /// constant, a literal): immutable, so nothing is ever stored there. Kept
    /// apart from [`Cell::Ext`] so a constant handed to a call does not make
    /// every pointer loaded from unknown memory carry the constant's value.
    Const,
}

/// A net's tracked value: a join-semilattice of finite height.
pub(super) trait Tracked: Clone + PartialEq + std::fmt::Debug {
    fn join(&self, other: &Self) -> Self;
}

fn join_opt<V: Tracked>(a: &Option<V>, b: &Option<V>) -> Option<V> {
    match (a, b) {
        (Some(x), Some(y)) => Some(x.join(y)),
        (Some(x), None) | (None, Some(x)) => Some(x.clone()),
        (None, None) => None,
    }
}

/// What a value (or a cell) may carry anywhere inside it.
#[derive(Clone, Debug, PartialEq)]
pub(super) struct Contents<V> {
    pub(super) val: Option<V>,
    pub(super) pts: BTreeSet<Cell>,
}

impl<V: Tracked> Contents<V> {
    pub(super) fn empty() -> Self {
        Self { val: None, pts: BTreeSet::new() }
    }

    fn address_of(cell: Cell) -> Self {
        Self { val: None, pts: BTreeSet::from([cell]) }
    }

    /// Join `other` in; `true` when that changed `self`.
    pub(super) fn absorb(&mut self, other: &Contents<V>) -> bool {
        let val = join_opt(&self.val, &other.val);
        let mut changed = val != self.val;
        self.val = val;
        for cell in &other.pts {
            changed |= self.pts.insert(*cell);
        }
        changed
    }

    fn joined(mut self, other: &Contents<V>) -> Self {
        self.absorb(other);
        self
    }

    /// The cells a pointer with these contents may address: an unknown
    /// pointer addresses memory outside the locals.
    pub(super) fn targets(&self) -> BTreeSet<Cell> {
        if self.pts.is_empty() { BTreeSet::from([Cell::Ext]) } else { self.pts.clone() }
    }
}

/// The net-specific transfer of a tracked value.
pub(super) trait FlowRules {
    type V: Tracked;

    /// The value a constant operand of type `ty` carries by itself.
    fn constant(&self, op: &Operand, ty: Option<Ty>) -> Option<Self::V>;

    /// A cast of kind `kind` from `from` to `to` of the operand `op` carrying
    /// `v`.
    fn cast(
        &self,
        kind: &CastKind,
        op: &Operand,
        from: Option<Ty>,
        to: Ty,
        v: Option<Self::V>,
    ) -> Option<Self::V>;

    /// `v` stored into a place of type `holder` (the value now lives under
    /// that type: a pointer to another pointee, an integer, an aggregate);
    /// `None` when the holder no longer carries anything the net tracks.
    fn retype(&self, v: Self::V, holder: Option<Ty>) -> Option<Self::V>;

    /// `&(*p).rest` / `&raw (*p).rest` for a pointer `p` carrying `v` whose
    /// pointee is `pointee`.
    fn reborrow(&self, v: Self::V, pointee: Option<Ty>, rest: &[ProjectionElem])
    -> Option<Self::V>;

    /// Arithmetic `op` (`None`: a unary operator) on a value carrying `v`,
    /// giving a value of type `ty`.
    fn arith(&self, op: Option<&BinOp>, v: Self::V, ty: Option<Ty>) -> Option<Self::V>;

    /// What a read of a value of type `loaded` through a pointer carrying `v`
    /// yields besides the addressed cells' contents.
    fn load(&self, v: &Self::V, loaded: Option<Ty>) -> Option<Self::V>;

    /// A call of the pointer-returning, memory-neutral callee `leaf`: the
    /// destination's value from the arguments' types and values, or `None`
    /// when `leaf` is not such a callee (the call is then treated as opaque).
    fn pointer_call(
        &self,
        leaf: &str,
        callee_ty: Option<Ty>,
        ops: &[Operand],
        args: &[(Option<Ty>, Option<Self::V>)],
        dest: Option<Ty>,
    ) -> Option<Option<Self::V>>;

    /// Callees that neither write through nor keep their arguments.
    fn is_inert_callee(&self, leaf: &str) -> bool;

    /// `v` after it went through memory, a call, or a local with more than
    /// one definition: no longer the value of one direct chain of copies and
    /// borrows from where it was made.
    fn through_memory(&self, v: Self::V) -> Self::V;

    /// An opaque call may return an external pointer or rewrite reachable
    /// memory. This is distinct from copying the same value through memory.
    fn through_call(&self, v: Self::V) -> Self::V {
        self.through_memory(v)
    }

    /// A pointer operation accepted by `pointer_call`, before ambiguous
    /// destinations are handled by `through_memory`.
    fn through_pointer_call(&self, v: Self::V) -> Self::V {
        self.through_memory(v)
    }

    /// Borrowing a carrier local addresses its storage, not the pointee
    /// named by a pointer value held there.
    fn borrow_local(&self, _v: Option<Self::V>) -> Option<Self::V> {
        None
    }
}

/// Can a value of `ty` carry a pointer or an address, or a piece of one (a
/// pointer, an integer of any width, an aggregate that holds one)?
///
/// An integer narrower than a pointer carries a piece of an address: an
/// address split into `u32` halves or bytes and joined back reaches its
/// pointer carrying what it started with. Dropping the narrow pieces lost a
/// static's address on the way (`((hi as usize) << 32 | lo as usize) as *const
/// u8` read a `[u16; 2]` static's image under a byte view, certified Genuine;
/// review of fix/chc-lost-writes round 3, finding 1). A `bool`, `char` or float
/// does not: Kani drops provenance through a float's bits. A narrow integer
/// carries only what it is computed from in the body, not what it is loaded
/// from memory or returned by a call as ([`narrow_int`]): those are the
/// program's data, and memory outside the locals is one cell here, so every
/// `u32` read from it would carry whatever address any integer there ever held
/// (a `static mut PTR: u32` under Kani's contract havoc,
/// `function-contract/modifies/global_replace_fail.rs`).
pub(super) fn may_carry(ty: Option<Ty>) -> bool {
    let Some(ty) = ty else { return true };
    match ty.kind() {
        TyKind::RigidTy(
            RigidTy::Bool | RigidTy::Char | RigidTy::Float(_) | RigidTy::Never | RigidTy::Str,
        ) => false,
        TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_)) => true,
        TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty() => false,
        _ => true,
    }
}

/// An integer narrower than a pointer: a piece of an address when computed
/// from one, data when loaded from memory or returned by a call.
fn narrow_int(ty: Option<Ty>) -> bool {
    matches!(
        ty.map(|t| t.kind()),
        Some(TyKind::RigidTy(
            RigidTy::Int(IntTy::I8 | IntTy::I16 | IntTy::I32)
                | RigidTy::Uint(UintTy::U8 | UintTy::U16 | UintTy::U32)
        ))
    )
}

/// The solved flow of one body.
pub(super) struct Flow<'b, R: FlowRules> {
    body: &'b Body,
    rules: &'b R,
    /// The callee leaf name of each block's `Call` terminator.
    leaves: HashMap<usize, String>,
    cells: HashMap<Cell, Contents<R::V>>,
    /// Locals written more than once, or whose address is taken mutably.
    rewritten: std::collections::HashSet<usize>,
    /// The fixpoint did not converge: every answer is unknown.
    pub(super) saturated: bool,
}

/// Locals written more than once (a whole or partial assignment, a call
/// result, a discriminant write), or whose address is taken mutably.
fn rewritten_locals(body: &Body) -> std::collections::HashSet<usize> {
    use rustc_public::mir::{BorrowKind, RawPtrKind};
    let mut defs: HashMap<usize, usize> = HashMap::new();
    let mut out = std::collections::HashSet::new();
    let own = |place: &Place| !matches!(place.projection.first(), Some(ProjectionElem::Deref));
    for block in &body.blocks {
        for stmt in &block.statements {
            match &stmt.kind {
                StatementKind::Assign(lhs, rv) => {
                    if own(lhs) {
                        *defs.entry(lhs.local).or_default() += 1;
                    }
                    match rv {
                        Rvalue::Ref(_, BorrowKind::Mut { .. }, place)
                        | Rvalue::AddressOf(RawPtrKind::Mut, place)
                            if own(place) =>
                        {
                            out.insert(place.local);
                        }
                        _ => {}
                    }
                }
                StatementKind::SetDiscriminant { place, .. } if own(place) => {
                    *defs.entry(place.local).or_default() += 1;
                }
                _ => {}
            }
        }
        if let TerminatorKind::Call { destination, .. } = &block.terminator.kind
            && own(destination)
        {
            *defs.entry(destination.local).or_default() += 1;
        }
    }
    out.extend(defs.into_iter().filter(|(_, n)| *n > 1).map(|(l, _)| l));
    out
}

impl<'b, R: FlowRules> Flow<'b, R> {
    /// Solve the flow of `body`. `callee_args`: the body's arguments are
    /// pointers from a caller this scan cannot see (a body the call walker
    /// inlines), so they address memory outside the locals.
    pub(super) fn solve(
        body: &'b Body,
        rules: &'b R,
        leaves: HashMap<usize, String>,
        callee_args: bool,
    ) -> Self {
        let mut flow = Self {
            body,
            rules,
            leaves,
            cells: HashMap::new(),
            rewritten: rewritten_locals(body),
            saturated: false,
        };
        if callee_args {
            for arg in 1..=body.arg_locals().len() {
                flow.cells
                    .entry(Cell::Local(arg))
                    .or_insert_with(Contents::empty)
                    .absorb(&Contents::address_of(Cell::Ext));
            }
        }
        for _ in 0..MAX_ROUNDS {
            if !flow.round() {
                return flow;
            }
        }
        flow.saturated = true;
        flow
    }

    fn round(&mut self) -> bool {
        let mut changed = false;
        for (bb, block) in self.body.blocks.iter().enumerate() {
            for stmt in &block.statements {
                match &stmt.kind {
                    StatementKind::Assign(lhs, rv) => {
                        let holder = lhs.ty(self.body.locals()).ok();
                        let mut contents = self.retyped(self.rvalue(rv), holder);
                        let through_pointer =
                            lhs.projection.iter().any(|e| matches!(e, ProjectionElem::Deref));
                        if through_pointer || self.rewritten.contains(&lhs.local) {
                            contents = self.through_memory(contents);
                        }
                        for cell in self.write_targets(lhs) {
                            changed |= self.add(cell, &contents);
                        }
                    }
                    StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(copy)) => {
                        let src = self.operand(&copy.src);
                        let loaded =
                            self.load_through(&src, pointee(copy.src.ty(self.body.locals()).ok()));
                        let holder = pointee(copy.dst.ty(self.body.locals()).ok());
                        let loaded = self.through_memory(self.retyped(loaded, holder));
                        for cell in self.operand(&copy.dst).targets() {
                            changed |= self.add(cell, &loaded);
                        }
                    }
                    _ => {}
                }
            }
            changed |= self.terminator(bb);
        }
        changed
    }

    fn add(&mut self, cell: Cell, contents: &Contents<R::V>) -> bool {
        // Constant memory is immutable: a store "into" it writes nothing.
        if cell == Cell::Const || contents.val.is_none() && contents.pts.is_empty() {
            return false;
        }
        self.cells.entry(cell).or_insert_with(Contents::empty).absorb(contents)
    }

    fn terminator(&mut self, bb: usize) -> bool {
        let locals = self.body.locals();
        match &self.body.blocks[bb].terminator.kind {
            TerminatorKind::Call { func, args, destination, .. } => {
                let arg_contents: Vec<Contents<R::V>> =
                    args.iter().map(|a| self.operand(a)).collect();
                let dest_ty = destination.ty(locals).ok();
                let leaf = self.leaves.get(&bb).cloned().unwrap_or_default();
                let typed: Vec<(Option<Ty>, Option<R::V>)> = args
                    .iter()
                    .zip(&arg_contents)
                    .map(|(a, c)| (a.ty(locals).ok(), c.val.clone()))
                    .collect();
                if let Some(val) =
                    self.rules.pointer_call(&leaf, func.ty(locals).ok(), args, &typed, dest_ty)
                {
                    let mut out = Contents { val, pts: BTreeSet::new() };
                    for c in &arg_contents {
                        out.pts.extend(c.pts.iter().copied());
                    }
                    let mut out = self.retyped(out, dest_ty);
                    out.val = out.val.map(|v| self.rules.through_pointer_call(v));
                    if !destination.projection.is_empty()
                        || self.rewritten.contains(&destination.local)
                    {
                        out = self.through_memory(out);
                    }
                    let mut changed = false;
                    for cell in self.write_targets(destination) {
                        changed |= self.add(cell, &out);
                    }
                    return changed;
                }
                let inert = self.rules.is_inert_callee(&leaf);
                self.opaque_call(&arg_contents, Some(destination), dest_ty, !inert)
            }
            TerminatorKind::Drop { place, .. } => {
                let held = Contents::address_of(Cell::Local(place.local));
                self.opaque_call(&[held], None, None, true)
            }
            TerminatorKind::InlineAsm { operands, .. } => {
                let held: Vec<Contents<R::V>> = operands
                    .iter()
                    .filter_map(|o| o.in_value.as_ref())
                    .map(|op| self.operand(op))
                    .collect();
                let mut changed = self.opaque_call(&held, None, None, true);
                let (_, all) = self.reach_all(&held);
                let mut all = all.joined(&Contents::address_of(Cell::Ext));
                all.val = all.val.map(|v| self.rules.through_call(v));
                for place in operands.iter().filter_map(|o| o.out_place.as_ref()) {
                    let out = self.retyped(all.clone(), place.ty(locals).ok());
                    for cell in self.write_targets(place) {
                        changed |= self.add(cell, &out);
                    }
                }
                changed
            }
            _ => false,
        }
    }

    /// A call this flow does not model: it may store anything reachable from
    /// its arguments into every cell reachable from them (`writes`), and may
    /// return any of it, or a pointer to memory outside the locals.
    fn opaque_call(
        &mut self,
        args: &[Contents<R::V>],
        destination: Option<&Place>,
        dest_ty: Option<Ty>,
        writes: bool,
    ) -> bool {
        let (reach, all) = self.reach_all(args);
        let all = Contents { val: all.val.map(|v| self.rules.through_call(v)), pts: all.pts };
        let mut changed = false;
        if writes {
            let locals = self.body.locals();
            for cell in &reach {
                if let Cell::Local(l) = cell
                    && narrow_int(locals.get(*l).map(|d| d.ty))
                {
                    continue;
                }
                // A local keeps its own type: what lands in it lives under it.
                let stored = match cell {
                    Cell::Local(l) => self.retyped(all.clone(), locals.get(*l).map(|d| d.ty)),
                    Cell::Ext | Cell::Const => all.clone(),
                };
                changed |= self.add(*cell, &stored);
            }
        }
        if let Some(destination) = destination
            && !narrow_int(dest_ty)
        {
            let out = self.retyped(all.joined(&Contents::address_of(Cell::Ext)), dest_ty);
            for cell in self.write_targets(destination) {
                changed |= self.add(cell, &out);
            }
        }
        changed
    }

    /// The cells reachable from `args` (following held addresses), and
    /// everything the arguments and those cells carry, with what a read
    /// through a tracked pointer among them yields.
    pub(super) fn reach_all(&self, args: &[Contents<R::V>]) -> (BTreeSet<Cell>, Contents<R::V>) {
        let mut all = Contents::empty();
        for a in args {
            all.absorb(a);
        }
        let reach = self.reach(all.pts.iter().copied());
        for cell in &reach {
            if let Some(c) = self.cells.get(cell) {
                all.absorb(c);
            }
        }
        if let Some(v) = all.val.clone()
            && let Some(extra) = self.rules.load(&v, None)
        {
            all.val = join_opt(&all.val, &Some(extra));
        }
        (reach, all)
    }

    /// The cells reachable from `start` by following held addresses.
    pub(super) fn reach(&self, start: impl Iterator<Item = Cell>) -> BTreeSet<Cell> {
        let mut seen: BTreeSet<Cell> = BTreeSet::new();
        let mut work: Vec<Cell> = start.collect();
        while let Some(cell) = work.pop() {
            if !seen.insert(cell) {
                continue;
            }
            if let Some(c) = self.cells.get(&cell) {
                work.extend(c.pts.iter().copied().filter(|p| !seen.contains(p)));
            }
        }
        seen
    }

    /// The contents of `cell`.
    pub(super) fn cell(&self, cell: Cell) -> Contents<R::V> {
        self.cells.get(&cell).cloned().unwrap_or_else(Contents::empty)
    }

    fn cells_contents(&self, cells: &BTreeSet<Cell>) -> Contents<R::V> {
        let mut out = Contents::empty();
        for cell in cells {
            if let Some(c) = self.cells.get(cell) {
                out.absorb(c);
            }
        }
        out
    }

    fn through_memory(&self, mut contents: Contents<R::V>) -> Contents<R::V> {
        contents.val = contents.val.map(|v| self.rules.through_memory(v));
        contents
    }

    fn retyped(&self, mut contents: Contents<R::V>, holder: Option<Ty>) -> Contents<R::V> {
        if !may_carry(holder) {
            return Contents::empty();
        }
        contents.val = contents.val.and_then(|v| self.rules.retype(v, holder));
        contents
    }

    /// What a read of a value of type `loaded` through a pointer with
    /// `pointer` contents yields.
    fn load_through(&self, pointer: &Contents<R::V>, loaded: Option<Ty>) -> Contents<R::V> {
        if narrow_int(loaded) {
            return Contents::empty();
        }
        let mut out = self.through_memory(self.cells_contents(&pointer.targets()));
        if let Some(v) = &pointer.val
            && let Some(extra) = self.rules.load(v, loaded)
        {
            out.val = join_opt(&out.val, &Some(extra));
        }
        out
    }

    /// What the value read from `place` may carry.
    pub(super) fn place(&self, place: &Place) -> Contents<R::V> {
        let locals = self.body.locals();
        let mut current = self.cell(Cell::Local(place.local));
        for (k, elem) in place.projection.iter().enumerate() {
            if matches!(elem, ProjectionElem::Deref) {
                // The value read through this dereference: up to the next one.
                let end = place.projection[k + 1..]
                    .iter()
                    .position(|e| matches!(e, ProjectionElem::Deref))
                    .map_or(place.projection.len(), |p| k + 1 + p);
                let loaded =
                    Place { local: place.local, projection: place.projection[..end].to_vec() }
                        .ty(locals)
                        .ok();
                current = self.load_through(&current, loaded);
            }
        }
        current
    }

    /// The contents of the pointer the LAST dereference of `place` goes
    /// through, the pointee type there, and the projection after it; `None`
    /// when `place` has no dereference.
    pub(super) fn last_deref(
        &self,
        place: &Place,
    ) -> Option<(Contents<R::V>, Option<Ty>, Vec<ProjectionElem>)> {
        let d = place.projection.iter().rposition(|e| matches!(e, ProjectionElem::Deref))?;
        let prefix = Place { local: place.local, projection: place.projection[..d].to_vec() };
        let pointer = self.place(&prefix);
        let pointee = Place { local: place.local, projection: place.projection[..=d].to_vec() }
            .ty(self.body.locals())
            .ok();
        Some((pointer, pointee, place.projection[d + 1..].to_vec()))
    }

    /// Every dereference of `place`: the pointer's contents, the pointee type,
    /// and the projection up to the next dereference (the part read through
    /// that pointer).
    pub(super) fn derefs(
        &self,
        place: &Place,
    ) -> Vec<(Contents<R::V>, Option<Ty>, Vec<ProjectionElem>)> {
        let locals = self.body.locals();
        let mut out = Vec::new();
        for (k, elem) in place.projection.iter().enumerate() {
            if !matches!(elem, ProjectionElem::Deref) {
                continue;
            }
            let end = place.projection[k + 1..]
                .iter()
                .position(|e| matches!(e, ProjectionElem::Deref))
                .map_or(place.projection.len(), |p| k + 1 + p);
            let prefix = Place { local: place.local, projection: place.projection[..k].to_vec() };
            let pointee = Place { local: place.local, projection: place.projection[..=k].to_vec() }
                .ty(locals)
                .ok();
            out.push((self.place(&prefix), pointee, place.projection[k + 1..end].to_vec()));
        }
        out
    }

    /// The cells an assignment to `place` may write.
    pub(super) fn write_targets(&self, place: &Place) -> BTreeSet<Cell> {
        match self.last_deref(place) {
            None => BTreeSet::from([Cell::Local(place.local)]),
            Some((pointer, _, _)) => pointer.targets(),
        }
    }

    /// What the value of `op` may carry (nothing, when its type cannot carry
    /// a pointer or an address).
    pub(super) fn operand(&self, op: &Operand) -> Contents<R::V> {
        let ty = op.ty(self.body.locals()).ok();
        if !may_carry(ty) {
            return Contents::empty();
        }
        match op {
            Operand::Copy(place) | Operand::Move(place) => self.place(place),
            Operand::Constant(_) => {
                let pts = if memory_of_constant(op).is_some() {
                    BTreeSet::from([Cell::Const])
                } else if ty.is_some_and(|t| may_hold_pointer(t, 0)) {
                    BTreeSet::from([Cell::Ext])
                } else {
                    BTreeSet::new()
                };
                Contents { val: self.rules.constant(op, ty), pts }
            }
            _ => Contents::empty(),
        }
    }

    /// What the value of `rv` may carry.
    pub(super) fn rvalue(&self, rv: &Rvalue) -> Contents<R::V> {
        let locals = self.body.locals();
        match rv {
            Rvalue::Use(op, ..) | Rvalue::Repeat(op, _) => self.operand(op),
            Rvalue::CopyForDeref(place) => self.place(place),
            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                match self.last_deref(place) {
                    None => Contents {
                        val: self.rules.borrow_local(self.cell(Cell::Local(place.local)).val),
                        pts: BTreeSet::from([Cell::Local(place.local)]),
                    },
                    Some((pointer, pointee, rest)) => {
                        let val = pointer
                            .val
                            .clone()
                            .and_then(|v| self.rules.reborrow(v, pointee, &rest));
                        Contents { val, pts: pointer.targets() }
                    }
                }
            }
            Rvalue::Cast(kind, op, to) => {
                let from = op.ty(locals).ok();
                let mut c = self.operand(op);
                c.val = self.rules.cast(kind, op, from, *to, c.val);
                // A pointer made from a non-pointer (an exposed address, a
                // transmuted integer or byte array) may name any exposed object.
                let to_pointer =
                    matches!(to.kind(), TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)));
                let from_pointer = from.is_some_and(|f| {
                    matches!(f.kind(), TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)))
                });
                if to_pointer && !from_pointer {
                    c.pts.insert(Cell::Ext);
                }
                c
            }
            Rvalue::BinaryOp(op, a, b) | Rvalue::CheckedBinaryOp(op, a, b) => {
                // Pointer arithmetic moves its pointer operand; the count is a
                // number, whatever it was computed from.
                let c = if matches!(op, BinOp::Offset) {
                    self.operand(a)
                } else {
                    self.operand(a).joined(&self.operand(b))
                };
                let ty = rv.ty(locals).ok();
                Contents { val: c.val.and_then(|v| self.rules.arith(Some(op), v, ty)), pts: c.pts }
            }
            Rvalue::UnaryOp(_, a) => {
                let c = self.operand(a);
                let ty = rv.ty(locals).ok();
                Contents { val: c.val.and_then(|v| self.rules.arith(None, v, ty)), pts: c.pts }
            }
            Rvalue::Aggregate(_, ops) => {
                let mut out = Contents::empty();
                for op in ops {
                    out.absorb(&self.operand(op));
                }
                out
            }
            Rvalue::ThreadLocalRef(_) => Contents::address_of(Cell::Ext),
            #[cfg(not(trust_toolchain))]
            Rvalue::ShallowInitBox(op, _) => self.operand(op),
            // A reborrow is a bitwise copy of the value at `place`.
            #[cfg(trust_toolchain)]
            Rvalue::Reborrow(_, _, place) => self.place(place),
            _ => Contents::empty(),
        }
    }
}

/// The pointee of a pointer type.
pub(super) fn pointee(ty: Option<Ty>) -> Option<Ty> {
    match ty?.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => Some(inner),
        _ => None,
    }
}
