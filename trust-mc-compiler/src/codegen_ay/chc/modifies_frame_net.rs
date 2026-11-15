// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! FC-06 frame net: the modifies-frame check for writes that never reach the
//! precise store checks in [`super::modifies_frame`].
//!
//! The precise checks fire from `build_memory_store` and from the register
//! deref-store lane. A write inside a contract-checked function's extent can
//! reach caller-visible storage without either:
//!
//! - a call handler that updates a register directly (`Vec::push` models,
//!   `write_bytes` / `copy` fills of a resolved referent);
//! - the nested inline walker, whose `&mut` argument effects come back to the
//!   caller as alias updates and are written as register updates;
//! - a callee the walker cannot inline at all, whose effect on memory reachable
//!   from its arguments is dropped (the `nested_call_overapprox` havoc keeps
//!   only the return value).
//!
//! Measured 2026-09-14 on `negative/modifies_frame_residual.rs`: all three
//! shapes verified SUCCESSFUL with `PROOF_QUALIFIERS:clean` on the CHC lane.
//!
//! The net enforces the frame at the level where every such write is
//! visible: the state variables of the harness. A *watched* local is
//! address-taken (a pointer to it can reach the checked function) and is
//! mentioned outside the frame's extent (it exists independently of the
//! checked call). Every transition out of an extent block that changes a
//! watched local's state variables, other than by a direct MIR assignment to
//! that local (the caller writing the call's result) or a store the precise
//! check already classified, is classified against the declared footprint:
//!
//! - COVERED: the local lies inside a footprint range — no obligation.
//! - DISJOINT: provably outside every range. A user-named local gets an
//!   error rule that fires when the transition changes its value (the
//!   assignable check), and the harness also records a DEMOTING fallback,
//!   because a store of an unchanged value is not observable here.
//! - UNDECIDED: partial overlap, a non-constant footprint or address, an
//!   unresolved footprint, or a compiler temporary — DEMOTING fallback only.
//!
//! COVERED is also proved by local identity: the MIR that builds the
//! `_wrapper_arg` tuple is traced through single-definition pointer temps
//! (moves, pointee-preserving casts, reborrows) to `&L` or `&L.f.g`
//! ([`static_footprints`]). A changed slot of `L` inside that field's flattened
//! span is covered. The trace only ever PROVES coverage; a shape it does not
//! recognise falls back to the constant-folded classification above.
//!
//! Effects the net cannot see at all fail closed where they are dropped: a
//! call inside the extent that records a sound fallback, is not dispatched, or
//! emits a transition around the rule sinks, while any of its arguments can
//! carry write capability, demotes the harness (`frame_net_after_call`), and
//! the nested walker demotes at its own drop sites.

use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use std::collections::HashSet;
use std::sync::Arc;

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::visit::{Location, MirVisitor, PlaceContext};
use rustc_public::mir::{
    AggregateKind, BasicBlock, Body, BorrowKind, CastKind, LocalDecl, Mutability, Operand, Place,
    PointerCoercion, ProjectionElem, RawPtrKind, Rvalue, Statement, StatementKind, Terminator,
    TerminatorKind, VarDebugInfoContents,
};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::debug;
use trust_mc_core::chc::{RelationApp, Rule, RuleBody};
use trust_mc_core::violation::PropertyKind;

use super::ChcCtx;
use super::call::chc_call_context::DispatchCallContext;
use super::codegen_types::CodegenTypes;
use super::modifies_frame::FootprintRange;

/// A local the net watches inside one modifies frame.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) struct WatchedLocal {
    pub local: usize,
    /// User-visible debug name (`None` for compiler temporaries and kani
    /// internals, which only ever demote).
    pub name: Option<String>,
}

/// Outcome of classifying a written region against the declared footprint.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) enum RegionClass {
    Covered,
    Disjoint,
    Undecided,
}

/// Size component of a constant-folded footprint range.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) enum FootprintSize {
    /// Object-granular: the whole object is assignable.
    Object,
    Bytes(u64),
    Unknown,
}

/// A footprint range after constant folding (`None` = not a constant).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) struct FootprintConst {
    pub obj: Option<u32>,
    pub offset: Option<u64>,
    pub size: FootprintSize,
}

/// Classify the byte region `[start, start + len)` of object `obj`.
///
/// COVERED needs one range that contains the whole region; DISJOINT needs
/// every range to be provably elsewhere. Anything else is UNDECIDED.
pub(in crate::codegen_ay::chc) fn classify_region(
    obj: u32,
    start: u64,
    len: u64,
    footprint: &[FootprintConst],
) -> RegionClass {
    if len == 0 {
        return RegionClass::Covered;
    }
    let end = start.saturating_add(len);
    let mut undecided = false;
    for range in footprint {
        match range.obj {
            None => {
                undecided = true;
                continue;
            }
            Some(other) if other != obj => continue,
            Some(_) => {}
        }
        match (range.offset, range.size) {
            (_, FootprintSize::Object) => return RegionClass::Covered,
            (Some(offset), FootprintSize::Bytes(size)) => {
                let range_end = offset.saturating_add(size);
                if offset <= start && end <= range_end {
                    return RegionClass::Covered;
                }
                if offset < end && start < range_end {
                    undecided = true;
                }
            }
            _ => undecided = true,
        }
    }
    if undecided { RegionClass::Undecided } else { RegionClass::Disjoint }
}

fn const_u64(expr: &Expr) -> Option<u64> {
    let folded = trust_mc_core::chc_const_prop::eval::try_eval_to_const(expr)?;
    ChcCtx::const_usize_from_expr(&folded).map(|v| v as u64)
}

/// Constant-fold one footprint range (BV64 base = obj_id ++ offset).
pub(in crate::codegen_ay::chc) fn fold_footprint_range(range: &FootprintRange) -> FootprintConst {
    let (obj, offset) = if range.base.sort().bitvec_width() == Some(64) {
        let obj =
            const_u64(&range.base.clone().extract(63, 32)).and_then(|v| u32::try_from(v).ok());
        let offset = const_u64(&range.base.clone().extract(31, 0));
        (obj, offset)
    } else {
        (None, None)
    };
    let size = match &range.size {
        None => FootprintSize::Object,
        Some(size) => const_u64(size).map_or(FootprintSize::Unknown, FootprintSize::Bytes),
    };
    FootprintConst { obj, offset, size }
}

/// A footprint element traced statically to a local of the harness body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) struct StaticFootprint {
    pub local: usize,
    /// Field path inside `local`; empty = the whole local.
    pub fields: Vec<usize>,
}

/// Whether a function argument `local` of `body` keeps the value the caller
/// passed for the whole body: never assigned (whole or in part, other than
/// THROUGH it), never a call destination, never borrowed, no inline assembly.
pub(in crate::codegen_ay::chc) fn arg_never_rebound(body: &Body, local: usize) -> bool {
    if local == 0 || local > body.arg_locals().len() {
        return false;
    }
    let writes_own_storage =
        |place: &Place| !matches!(place.projection.first(), Some(ProjectionElem::Deref));
    for block in &body.blocks {
        for stmt in &block.statements {
            match &stmt.kind {
                StatementKind::Assign(place, rvalue) => {
                    if place.local == local && writes_own_storage(place) {
                        return false;
                    }
                    if let Rvalue::Ref(_, _, borrowed) | Rvalue::AddressOf(_, borrowed) = rvalue
                        && borrowed.local == local
                        && writes_own_storage(borrowed)
                    {
                        return false;
                    }
                }
                StatementKind::SetDiscriminant { place, .. } if place.local == local => {
                    return false;
                }
                _ => {}
            }
        }
        match &block.terminator.kind {
            TerminatorKind::Call { destination, .. } if destination.local == local => {
                return false;
            }
            TerminatorKind::InlineAsm { .. } => return false,
            _ => {}
        }
    }
    true
}

/// The single definition of `local`, when it is a whole-local assignment and
/// nothing else can write the local: not the return place, not an argument,
/// not a call destination, never borrowed, never partially assigned.
pub(in crate::codegen_ay::chc) fn unique_def(body: &Body, local: usize) -> Option<&Rvalue> {
    if local == 0 || local <= body.arg_locals().len() {
        return None;
    }
    let mut def = None;
    let mut borrows: Vec<usize> = Vec::new();
    for block in &body.blocks {
        for stmt in &block.statements {
            match &stmt.kind {
                StatementKind::Assign(place, rvalue) => {
                    if place.local == local {
                        if !place.projection.is_empty() || def.is_some() {
                            debug!(
                                local,
                                partial = !place.projection.is_empty(),
                                "FC-06 net: unique_def refused: second or partial definition"
                            );
                            return None;
                        }
                        def = Some(rvalue);
                    }
                    if let Rvalue::Ref(_, _, borrowed) | Rvalue::AddressOf(_, borrowed) = rvalue
                        && borrowed.local == local
                        && !matches!(borrowed.projection.first(), Some(ProjectionElem::Deref))
                    {
                        // A borrow of a PART of the local, or one stored anywhere
                        // but a whole local, can write the local: refuse. A borrow
                        // of the whole local is kept only if every pointer derived
                        // from it reads (`borrows_only_read`).
                        if !borrowed.projection.is_empty() || !place.projection.is_empty() {
                            debug!(local, ?stmt.kind, "FC-06 net: unique_def refused: borrow of a part, or stored into a projection");
                            return None;
                        }
                        borrows.push(place.local);
                    }
                }
                StatementKind::SetDiscriminant { place, .. } if place.local == local => {
                    return None;
                }
                _ => {}
            }
        }
        match &block.terminator.kind {
            TerminatorKind::Call { destination, .. } if destination.local == local => {
                debug!(local, "FC-06 net: unique_def refused: call destination");
                return None;
            }
            TerminatorKind::InlineAsm { .. } => return None,
            _ => {}
        }
    }
    if !borrows.is_empty() && !borrows_only_read(body, local, &borrows) {
        debug!(local, ?borrows, "FC-06 net: unique_def refused: a borrow is not read-only");
        return None;
    }
    if def.is_none() {
        debug!(local, "FC-06 net: unique_def refused: no whole-local assignment");
    }
    def
}

/// Locals a single statement mentions.
///
/// `terminator_for_span` only lends its span to the synthetic `Return`. Its
/// name matters: `tools/port/trust_api_codemod.py`'s `mir_span` pass finds the
/// receivers it must rewrite BY NAME (`RECEIVER_RE`), so a `&Terminator` bound
/// to a name that does not read as one is invisible to it. Measured
/// 2026-09-16: as `span_of`, this site's `.span` silently survived the codemod
/// and broke `trust-mc-engine` on seal 8595 — Trust's `rustc_public` puts the
/// span at `source_info.span`.
fn statement_locals(stmt: &Statement, terminator_for_span: &Terminator) -> HashSet<usize> {
    let block = BasicBlock {
        statements: vec![stmt.clone()],
        terminator: crate::rustc_compat::mir_terminator(
            TerminatorKind::Return,
            mir_span!(terminator_for_span),
        ),
    };
    let mut collector = LocalCollector::default();
    collector.visit_basic_block(&block);
    // `Return` mentions the return place; it is never a tracked pointer.
    collector.locals.remove(&0);
    collector.locals
}

/// Is every pointer derived from the whole-local borrows `roots` used only to
/// READ the borrowed local? Derived pointers are followed through moves and
/// copies, shared reborrows of the pointee, the fields of tuple and closure
/// aggregates, and references to such aggregates (a closure environment). Any
/// other appearance of a derived pointer — a write through it, a mutable
/// reborrow, a cast, a call argument, a terminator — refuses, so an accepted
/// borrow cannot change the local.
fn borrows_only_read(body: &Body, borrowed: usize, roots: &[usize]) -> bool {
    let mut ptrs: HashSet<usize> = roots.iter().copied().collect();
    let mut aggs: HashSet<(usize, usize)> = HashSet::new();
    let mut envs: HashSet<(usize, usize)> = HashSet::new();
    for _pass in 0..32 {
        let before = (ptrs.len(), aggs.len(), envs.len());
        for block in &body.blocks {
            let tracked = |l: usize,
                           ptrs: &HashSet<usize>,
                           aggs: &HashSet<(usize, usize)>,
                           envs: &HashSet<(usize, usize)>| {
                ptrs.contains(&l)
                    || aggs.iter().any(|(a, _)| *a == l)
                    || envs.iter().any(|(e, _)| *e == l)
            };
            let mut term_locals = LocalCollector::default();
            term_locals.visit_basic_block(&BasicBlock {
                statements: Vec::new(),
                terminator: block.terminator.clone(),
            });
            if term_locals.locals.iter().any(|l| tracked(*l, &ptrs, &aggs, &envs)) {
                debug!(?roots, terminator = ?block.terminator.kind, "FC-06 net: borrow refused: derived pointer reaches a terminator");
                return false;
            }
            for stmt in &block.statements {
                let mentioned = statement_locals(stmt, &block.terminator);
                if !mentioned.iter().any(|l| tracked(*l, &ptrs, &aggs, &envs)) {
                    continue;
                }
                match &stmt.kind {
                    StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => continue,
                    StatementKind::Assign(dest, rvalue) if dest.projection.is_empty() => {
                        let d = dest.local;
                        let ok = match rvalue {
                            // A root's own definition: the whole-local borrow.
                            Rvalue::Ref(_, _, src) | Rvalue::AddressOf(_, src)
                                if roots.contains(&d)
                                    && src.local == borrowed
                                    && src.projection.is_empty() =>
                            {
                                true
                            }
                            Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) => {
                                let proj = &src.projection;
                                if proj.is_empty() && ptrs.contains(&src.local) {
                                    ptrs.insert(d);
                                    true
                                } else if proj.is_empty()
                                    && aggs.iter().any(|(a, _)| *a == src.local)
                                {
                                    let marks: Vec<usize> = aggs
                                        .iter()
                                        .filter(|(a, _)| *a == src.local)
                                        .map(|(_, i)| *i)
                                        .collect();
                                    for i in marks {
                                        aggs.insert((d, i));
                                    }
                                    true
                                } else if proj.is_empty()
                                    && envs.iter().any(|(e, _)| *e == src.local)
                                {
                                    // A move or copy of a closure-environment
                                    // reference (the inliner binds `_1 = move _env`).
                                    let marks: Vec<usize> = envs
                                        .iter()
                                        .filter(|(e, _)| *e == src.local)
                                        .map(|(_, i)| *i)
                                        .collect();
                                    for i in marks {
                                        envs.insert((d, i));
                                    }
                                    true
                                } else if let [ProjectionElem::Field(i, _)] = proj.as_slice()
                                    && aggs.iter().any(|(a, _)| *a == src.local)
                                {
                                    if aggs.contains(&(src.local, *i)) {
                                        ptrs.insert(d);
                                    }
                                    true
                                } else if let [ProjectionElem::Deref, ProjectionElem::Field(i, _)] =
                                    proj.as_slice()
                                    && envs.iter().any(|(e, _)| *e == src.local)
                                {
                                    if envs.contains(&(src.local, *i)) {
                                        ptrs.insert(d);
                                    }
                                    true
                                } else if matches!(proj.first(), Some(ProjectionElem::Deref))
                                    && ptrs.contains(&src.local)
                                    && proj[1..]
                                        .iter()
                                        .all(|p| matches!(p, ProjectionElem::Field(..)))
                                {
                                    // A load of (part of) the borrowed local.
                                    true
                                } else {
                                    false
                                }
                            }
                            Rvalue::Ref(_, BorrowKind::Shared, src)
                            | Rvalue::AddressOf(RawPtrKind::Const, src)
                                if matches!(
                                    src.projection.first(),
                                    Some(ProjectionElem::Deref)
                                ) && ptrs.contains(&src.local)
                                    && src.projection[1..]
                                        .iter()
                                        .all(|p| matches!(p, ProjectionElem::Field(..))) =>
                            {
                                ptrs.insert(d);
                                true
                            }
                            Rvalue::Ref(_, _, src) | Rvalue::AddressOf(_, src)
                                if src.projection.is_empty()
                                    && aggs.iter().any(|(a, _)| *a == src.local) =>
                            {
                                let marks: Vec<usize> = aggs
                                    .iter()
                                    .filter(|(a, _)| *a == src.local)
                                    .map(|(_, i)| *i)
                                    .collect();
                                for i in marks {
                                    envs.insert((d, i));
                                }
                                true
                            }
                            Rvalue::Aggregate(
                                AggregateKind::Tuple | AggregateKind::Closure(..),
                                operands,
                            ) => {
                                let mut ok = true;
                                for (i, op) in operands.iter().enumerate() {
                                    match op {
                                        Operand::Copy(src) | Operand::Move(src)
                                            if src.projection.is_empty()
                                                && ptrs.contains(&src.local) =>
                                        {
                                            aggs.insert((d, i));
                                        }
                                        Operand::Copy(src) | Operand::Move(src)
                                            if tracked(src.local, &ptrs, &aggs, &envs) =>
                                        {
                                            ok = false;
                                        }
                                        _ => {}
                                    }
                                }
                                ok
                            }
                            _ => false,
                        };
                        if !ok {
                            debug!(?roots, statement = ?stmt.kind, "FC-06 net: borrow refused: unrecognised use of a derived pointer");
                            return false;
                        }
                    }
                    _ => {
                        debug!(?roots, statement = ?stmt.kind, "FC-06 net: borrow refused: derived pointer in a non-assignment");
                        return false;
                    }
                }
            }
        }
        if (ptrs.len(), aggs.len(), envs.len()) == before {
            return true;
        }
    }
    false
}

/// The local whose value a `Use` of `place` copies, following field reads out of
/// single-definition tuple and closure aggregates (through whole-local moves): `_p = copy (_args.0)` with
/// `_args = (move _q,)` resolves to `_q`. This is how the inliner binds the
/// parameters of a RustCall closure, so the modifies wrapper's `_wrapper_arg`
/// and the checked function's pointer parameters reach the harness this way.
/// `None` for any other projection or definition.
fn use_source_local(body: &Body, place: &Place, depth: usize) -> Option<usize> {
    if depth > 16 {
        return None;
    }
    let Some((first, rest)) = place.projection.split_first() else {
        return Some(place.local);
    };
    let ProjectionElem::Field(idx, _) = first else {
        return None;
    };
    match unique_def(body, place.local)? {
        // A whole-local move or copy of the aggregate (the inliner binds a
        // closure's `self` as `_env = move _closure`): project the source.
        Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) => {
            let mut projection = src.projection.clone();
            projection.extend(place.projection.iter().cloned());
            use_source_local(body, &Place { local: src.local, projection }, depth + 1)
        }
        // A tuple field, or a closure upvar (upvar i is operand i of the
        // closure aggregate): continue from the operand that built it.
        Rvalue::Aggregate(AggregateKind::Tuple | AggregateKind::Closure(..), operands) => {
            let (Operand::Copy(inner) | Operand::Move(inner)) = operands.get(*idx)? else {
                return None;
            };
            let mut projection = inner.projection.clone();
            projection.extend(rest.iter().cloned());
            use_source_local(body, &Place { local: inner.local, projection }, depth + 1)
        }
        _ => None,
    }
}

fn pointee_ty(ty: Ty) -> Option<Ty> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(pointee, _) | RigidTy::Ref(_, pointee, _)) => Some(pointee),
        _ => None,
    }
}

/// The place a pointer local points at, traced through its definitions.
#[derive(Debug)]
struct TracedPlace {
    local: usize,
    fields: Vec<usize>,
    ty: Ty,
    /// The pointer was unsized from `*[T; N]` to `*[T]` (the whole array).
    unsized_array: bool,
}

fn trace_pointer(body: &Body, local: usize, depth: usize) -> Option<TracedPlace> {
    if depth > 16 {
        return None;
    }
    match unique_def(body, local)? {
        // `_v = copy (*p)` with `p` pointing at a whole pointer-typed local `L`
        // (a by-reference closure capture): the loaded value is `L`'s single
        // definition, which `unique_def` only yields while every borrow of `L`
        // reads.
        Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
            if matches!(src.projection.as_slice(), [ProjectionElem::Deref]) =>
        {
            let pointee = trace_pointer(body, src.local, depth + 1)?;
            if !pointee.fields.is_empty() || pointee.unsized_array {
                return None;
            }
            trace_pointer(body, pointee.local, depth + 1)
        }
        Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) => {
            trace_pointer(body, use_source_local(body, src, 0)?, depth + 1)
        }
        Rvalue::Cast(kind, Operand::Copy(src) | Operand::Move(src), target_ty)
            if src.projection.is_empty() =>
        {
            let mut traced = trace_pointer(body, src.local, depth + 1)?;
            let from = pointee_ty(body.locals()[src.local].ty)?;
            let to = pointee_ty(*target_ty)?;
            match kind {
                CastKind::PtrToPtr
                | CastKind::PointerCoercion(PointerCoercion::MutToConstPointer) => {
                    (from == to).then_some(traced)
                }
                CastKind::PointerCoercion(PointerCoercion::Unsize) => {
                    match (from.kind(), to.kind()) {
                        (
                            TyKind::RigidTy(RigidTy::Array(elem, _)),
                            TyKind::RigidTy(RigidTy::Slice(slice_elem)),
                        ) if elem == slice_elem && !traced.unsized_array => {
                            traced.unsized_array = true;
                            Some(traced)
                        }
                        _ => None,
                    }
                }
                _ => None,
            }
        }
        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
            let (mut traced, rest) = match place.projection.first() {
                Some(ProjectionElem::Deref) => {
                    (trace_pointer(body, place.local, depth + 1)?, &place.projection[1..])
                }
                _ => (
                    TracedPlace {
                        local: place.local,
                        fields: Vec::new(),
                        ty: body.locals()[place.local].ty,
                        unsized_array: false,
                    },
                    &place.projection[..],
                ),
            };
            for elem in rest {
                match elem {
                    ProjectionElem::Field(idx, field_ty) if !traced.unsized_array => {
                        traced.fields.push(*idx);
                        traced.ty = *field_ty;
                    }
                    _ => return None,
                }
            }
            Some(traced)
        }
        _ => None,
    }
}

fn trace_tuple(body: &Body, local: usize, depth: usize) -> Option<&[Operand]> {
    if depth > 16 {
        return None;
    }
    match unique_def(body, local)? {
        Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) => {
            trace_tuple(body, use_source_local(body, src, 0)?, depth + 1)
        }
        Rvalue::Aggregate(AggregateKind::Tuple, operands) => Some(operands),
        _ => None,
    }
}

/// Footprint elements of a `modifies_frame_enter(_wrapper_arg)` call that trace
/// statically to a harness local. Elements that do not trace are omitted: the
/// result may only be used to PROVE coverage, never to refute it.
pub(in crate::codegen_ay::chc) fn static_footprints(
    body: &Body,
    enter: &Terminator,
) -> Vec<StaticFootprint> {
    let TerminatorKind::Call { args, .. } = &enter.kind else {
        return Vec::new();
    };
    let Some(Operand::Copy(tuple) | Operand::Move(tuple)) = args.first() else {
        return Vec::new();
    };
    if !tuple.projection.is_empty() {
        return Vec::new();
    }
    let Some(operands) = trace_tuple(body, tuple.local, 0) else {
        debug!(
            tuple = tuple.local,
            def = ?unique_def(body, tuple.local),
            "FC-06 net: footprint tuple does not trace statically"
        );
        return Vec::new();
    };
    let mut out = Vec::new();
    for (i, op) in operands.iter().enumerate() {
        let (Operand::Copy(ptr) | Operand::Move(ptr)) = op else {
            continue;
        };
        if !ptr.projection.is_empty() {
            continue;
        }
        let Some(traced) = trace_pointer(body, ptr.local, 0) else {
            debug!(
                field = i,
                ptr = ptr.local,
                def = ?unique_def(body, ptr.local),
                "FC-06 net: footprint pointer does not trace statically"
            );
            continue;
        };
        let Some(pointee) = op.ty(body.locals()).ok().and_then(pointee_ty) else {
            continue;
        };
        let exact = if traced.unsized_array {
            matches!(
                (traced.ty.kind(), pointee.kind()),
                (TyKind::RigidTy(RigidTy::Array(elem, _)), TyKind::RigidTy(RigidTy::Slice(slice_elem)))
                    if elem == slice_elem
            )
        } else {
            traced.ty == pointee
        };
        if !exact {
            debug!(field = i, ?traced, "FC-06 net: traced footprint type differs from the pointee");
            continue;
        }
        out.push(StaticFootprint { local: traced.local, fields: traced.fields });
    }
    out
}

/// Are all `changed` slot positions inside the union of `spans` (`whole` =
/// some span covers the entire local)?
pub(in crate::codegen_ay::chc) fn slots_covered(
    whole: bool,
    spans: &[(usize, usize)],
    changed: &[usize],
) -> bool {
    if changed.is_empty() {
        return false;
    }
    whole
        || changed.iter().all(|k| spans.iter().any(|(start, len)| *start <= *k && *k < start + len))
}

#[derive(Default)]
struct LocalCollector {
    locals: HashSet<usize>,
}

impl MirVisitor for LocalCollector {
    fn visit_local(&mut self, local: &usize, _ptx: PlaceContext, _location: Location) {
        self.locals.insert(*local);
    }
}

/// Watched locals of a frame whose extent is `extent`: address-taken locals
/// that are also mentioned by some block outside the extent.
pub(in crate::codegen_ay::chc) fn watched_locals_for_extent(
    body: &Body,
    extent: &HashSet<usize>,
) -> Vec<WatchedLocal> {
    let mut address_taken: HashSet<usize> = HashSet::new();
    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(
                _,
                Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place),
            ) = &stmt.kind
            {
                address_taken.insert(place.local);
            }
        }
    }
    let mut outside = LocalCollector::default();
    for (bb, block) in body.blocks.iter().enumerate() {
        if !extent.contains(&bb) {
            outside.visit_basic_block(block);
        }
    }
    let mut watched: Vec<WatchedLocal> = address_taken
        .into_iter()
        .filter(|local| *local != 0 && outside.locals.contains(local))
        .map(|local| WatchedLocal { local, name: user_debug_name(body, local) })
        .collect();
    watched.sort_by_key(|w| w.local);
    watched
}

fn user_debug_name(body: &Body, local: usize) -> Option<String> {
    body.var_debug_info.iter().find_map(|vdi| {
        let name = vdi.name.as_str();
        if name.starts_with("kani") || name.starts_with("__kani") || name.starts_with('_') {
            return None;
        }
        match &vdi.value {
            VarDebugInfoContents::Place(place)
                if place.projection.is_empty() && place.local == local =>
            {
                Some(name.to_string())
            }
            _ => None,
        }
    })
}

/// Locals a block writes by name (no `Deref` in the place): the caller's own
/// assignments, including a call's result destination.
pub(in crate::codegen_ay::chc) fn directly_written_locals(block: &BasicBlock) -> HashSet<usize> {
    fn direct(place: &Place) -> bool {
        !place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
    }
    let mut out = HashSet::new();
    for stmt in &block.statements {
        match &stmt.kind {
            StatementKind::Assign(place, _) | StatementKind::SetDiscriminant { place, .. }
                if direct(place) =>
            {
                out.insert(place.local);
            }
            _ => {}
        }
    }
    if let TerminatorKind::Call { destination, .. } = &block.terminator.kind
        && direct(destination)
    {
        out.insert(destination.local);
    }
    out
}

/// Can a value of this type carry the capability to write memory the callee
/// did not allocate? Fail-closed on anything it cannot see into.
pub(in crate::codegen_ay::chc) fn ty_may_write_through(
    ty: Ty,
    behind_shared: bool,
    depth: usize,
) -> bool {
    if depth > 6 {
        return true;
    }
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Bool | RigidTy::Char | RigidTy::Int(_) | RigidTy::Uint(_))
        | TyKind::RigidTy(RigidTy::Float(_) | RigidTy::Str | RigidTy::Never | RigidTy::FnDef(..)) => {
            false
        }
        TyKind::RigidTy(RigidTy::Ref(_, inner, Mutability::Mut)) => {
            if behind_shared {
                ty_may_write_through(inner, true, depth + 1)
            } else {
                true
            }
        }
        TyKind::RigidTy(RigidTy::Ref(_, inner, Mutability::Not)) => {
            ty_may_write_through(inner, true, depth + 1)
        }
        TyKind::RigidTy(RigidTy::RawPtr(..)) => true,
        TyKind::RigidTy(RigidTy::Tuple(fields)) => {
            fields.iter().any(|f| ty_may_write_through(*f, behind_shared, depth + 1))
        }
        TyKind::RigidTy(RigidTy::Array(elem, _) | RigidTy::Slice(elem)) => {
            ty_may_write_through(elem, behind_shared, depth + 1)
        }
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            let name = def.trimmed_name();
            if name == "UnsafeCell" || name == "SyncUnsafeCell" {
                return true;
            }
            // Behind a shared reference an owning pointer is read-only.
            if behind_shared && matches!(name.as_str(), "NonNull" | "Unique") {
                return false;
            }
            def.variants().iter().any(|variant| {
                variant.fields().iter().any(|field| {
                    mono_ty::field_ty(field, &args)
                        .is_none_or(|t| ty_may_write_through(t, behind_shared, depth + 1))
                })
            })
        }
        _ => true,
    }
}

/// Does any argument of this call carry write capability?
pub(in crate::codegen_ay::chc) fn call_args_may_write(
    ctx: &ChcCtx<'_, '_>,
    args: &[Operand],
    locals: &[LocalDecl],
) -> bool {
    args.iter().any(|arg| match arg.ty(locals) {
        Ok(ty) => ty_may_write_through(ctx.resolve_body_ty(ty), false, 0),
        Err(_) => true,
    })
}

/// Constraint base of a rule the net inspects.
pub(in crate::codegen_ay::chc) enum NetBase<'a> {
    Slice(&'a [Expr]),
    Shared(&'a Arc<[Expr]>),
}

/// Counters snapshotted around a call terminator.
pub(in crate::codegen_ay::chc) struct CallNetSnapshot {
    rules: usize,
    sink_rules: usize,
    sound: usize,
    /// [`ModifiesFrameNetState::call_arg_check_records`] at the snapshot: the
    /// call's own FC-06 argument check books into the same counters as `sound`.
    own_check_records: usize,
}

impl CallNetSnapshot {
    /// Sound-fallback records the call booked that the net cannot see through:
    /// every increment of the fallback counters since the snapshot EXCEPT those
    /// the call's own FC-06 argument check made
    /// (`modifies_frame_call_arg_overapprox`).
    ///
    /// That check does not drop an effect of the call. It ADDS the error rule
    /// "the pointee this argument may write is assignable" and tags that rule an
    /// over-approximation so a counterexample through it is never certified —
    /// which is exactly the check this net exists to insist on. Counting its own
    /// tag as an unseen effect made every call with a `&mut` (or interior-mutable
    /// `&`) argument inside an extent demote the harness it had just checked:
    /// measured 2026-09-24 on `interior-mutability/api/cell.rs` and
    /// `whole-struct/cell.rs`, 20 of 20 rows proved and the proof was reported
    /// `[chc_fallback=2]`. Any OTHER record in the window — a call model's havoc,
    /// an untranslatable argument (`modifies_frame_call_store_untranslatable`),
    /// a nested over-approximation — is still counted, so the net still fails
    /// closed on every effect it cannot see.
    pub(in crate::codegen_ay::chc) fn foreign_sound_records(
        &self,
        sound_now: usize,
        own_check_records_now: usize,
    ) -> usize {
        let booked = sound_now.saturating_sub(self.sound);
        let own = own_check_records_now.saturating_sub(self.own_check_records);
        booked.saturating_sub(own)
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Is the block being encoded inside a modifies frame's extent?
    pub(in crate::codegen_ay::chc) fn in_modifies_frame_extent(&self) -> bool {
        !self.modifies_frames.is_empty()
            && self.modifies_frame_by_bb.contains_key(&self.current_encode_bb)
    }

    /// Demote: a write inside a modifies frame that cannot be classified.
    #[track_caller]
    pub(in crate::codegen_ay::chc) fn modifies_frame_fail_closed(&mut self, what: &str) {
        debug!(
            bb = self.current_encode_bb,
            site = %std::panic::Location::caller(),
            %what,
            "FC-06 net: write inside modifies frame not classifiable (demoting fallback)"
        );
        self.record_fallback();
    }

    /// Record that a precise frame check covered a store to `local`.
    pub(in crate::codegen_ay::chc) fn modifies_frame_certify_local(&mut self, local: usize) {
        self.modifies_frame_net.certified.insert(local);
    }

    /// Excuse a call handler's register rebinding of `local` that mirrors
    /// exactly the bytes of a store whose own precise frame check certified
    /// `local` (the Cell store lane binding the referent's register to the
    /// value it stored, `codegen_call_cell_register.rs`). The rebinding is the
    /// same program write as the store, which that check already classified;
    /// the transition's output slots for `local` are snapshotted like a
    /// statement certificate, so the rule pass excuses exactly this output
    /// and nothing the terminator did beside it.
    pub(in crate::codegen_ay::chc) fn modifies_frame_certify_mirrored_write(
        &mut self,
        local: usize,
        output_args: &[Expr],
    ) {
        if !self.in_modifies_frame_extent() {
            return;
        }
        let slots = self.state_slots_of(local, output_args);
        self.modifies_frame_net.statement_certified.insert(local, slots);
    }

    /// Record that a precise frame check covered a store at `addr`.
    pub(in crate::codegen_ay::chc) fn modifies_frame_certify_addr(&mut self, addr: &Expr) {
        let Some((obj, _)) = self.split_pointer(addr) else {
            return;
        };
        let Some(obj) = const_u64(&obj).and_then(|v| u32::try_from(v).ok()) else {
            return;
        };
        let local = self
            .heap_state
            .local_addresses
            .iter()
            .find_map(|(local, (id, _))| (*id == obj).then_some(*local));
        if let Some(local) = local {
            self.modifies_frame_net.certified.insert(local);
        }
    }

    /// Byte size and object id of a watched local, when both are known.
    fn watched_local_region(&self, local: usize) -> Option<(u32, u64)> {
        let (obj, _) = self.heap_state.local_addresses.get(&local)?;
        let ty = self.body.locals().get(local)?.ty;
        let size = self.get_type_size(ty)? as u64;
        Some((*obj, size))
    }

    /// State-vector indices of a local (flattened locals span several slots).
    fn local_state_indices(&self, local: usize) -> Vec<usize> {
        let Some(base) = self.try_state_idx_for_local(local) else {
            return Vec::new();
        };
        let n = if self.flatten.flattened_tuple_locals.contains(&local) {
            self.flattened_field_count(local).max(1)
        } else {
            1
        };
        (base..base + n).filter(|idx| *idx < self.state_var_mgr.state_vars.len()).collect()
    }

    /// Positions (within the local) of the state slots this transition changes.
    fn changed_slot_positions(&self, local: usize, output_args: &[Expr]) -> Vec<usize> {
        self.local_state_indices(local)
            .into_iter()
            .enumerate()
            .filter_map(|(pos, idx)| {
                let out = output_args.get(idx)?;
                let (in_name, in_sort) = &self.state_var_mgr.state_vars[idx];
                (*out != Expr::var(&**in_name, in_sort.clone())).then_some(pos)
            })
            .collect()
    }

    /// Does a statically traced footprint element cover every changed slot?
    fn statically_covered(&self, frame_idx: usize, local: usize, output_args: &[Expr]) -> bool {
        let elements: Vec<&StaticFootprint> = self.modifies_frames[frame_idx]
            .static_footprint
            .iter()
            .filter(|fp| fp.local == local)
            .collect();
        if elements.is_empty() {
            return false;
        }
        let changed = self.changed_slot_positions(local, output_args);
        let whole = elements.iter().any(|fp| fp.fields.is_empty());
        if tracing::enabled!(tracing::Level::DEBUG) {
            let indices = self.local_state_indices(local);
            let outs: Vec<String> = changed
                .iter()
                .filter_map(|pos| indices.get(*pos).and_then(|idx| output_args.get(*idx)))
                .map(|e| format!("{e:?}").chars().take(160).collect())
                .collect();
            debug!(
                local,
                ?changed,
                slots = indices.len(),
                whole,
                flattened = self.flatten.flattened_tuple_locals.contains(&local),
                ?outs,
                "FC-06 net: static coverage query"
            );
        }
        let mut spans = Vec::new();
        if !whole {
            // Field spans index the recursive leaf flattening of a single
            // constructor datatype; any other slot layout is not trusted.
            if !self.flatten.flattened_tuple_locals.contains(&local)
                || self.flatten.flattened_enum_discr.contains_key(&local)
                || self.flatten.enum_bv_layouts.contains_key(&local)
            {
                return false;
            }
            let Some(sort) = Self::translate_ty(self.body.locals()[local].ty) else {
                debug!(local, "FC-06 net: static coverage refused: local sort untranslatable");
                return false;
            };
            let leaves = super::codegen_decl_flatten::collect_leaf_sorts(&sort, 0).len();
            if leaves != self.flattened_field_count(local) {
                debug!(
                    local,
                    leaves,
                    slots = self.flattened_field_count(local),
                    "FC-06 net: static coverage refused: leaf count differs from the flattening"
                );
                return false;
            }
            // Each recorded path is placed through the checked walk (C5b): a
            // step `translate_ty` collapses has no level in the sort tree, and
            // a raw index there named another leaf's span. A path that does
            // not place faithfully refuses the coverage (the net demotes).
            let local_ty = self.body.locals()[local].ty;
            let mut placed = Vec::with_capacity(elements.len());
            for fp in &elements {
                let span =
                    crate::codegen_ay::chc::expr::codegen_expr_flat_struct_path::typed_field_path(
                        local_ty, &fp.fields,
                    )
                    .and_then(|projs| self.flat_span_for(local, &projs).ok());
                let Some(span) = span else {
                    debug!(local, fields = ?fp.fields, "FC-06 net: static coverage refused: no faithful span");
                    return false;
                };
                placed.push(span);
            }
            spans = placed;
            debug!(local, ?spans, "FC-06 net: static coverage spans");
        }
        slots_covered(whole, &spans, &changed)
    }

    /// Classify a written watched local against the active frame. `None`
    /// when the net must demote without a check.
    fn classify_watched_write(&self, frame_idx: usize, watched: &WatchedLocal) -> RegionClass {
        let frame = &self.modifies_frames[frame_idx];
        if !frame.resolved {
            return RegionClass::Undecided;
        }
        let Some((obj, size)) = self.watched_local_region(watched.local) else {
            return RegionClass::Undecided;
        };
        let footprint: Vec<FootprintConst> =
            frame.footprint.iter().map(fold_footprint_range).collect();
        classify_region(obj, 0, size, &footprint)
    }

    /// Reset the per-block net state (called when a block's encoding starts).
    pub(in crate::codegen_ay::chc) fn modifies_frame_net_reset_block(&mut self) {
        self.modifies_frame_net.certified.clear();
        self.modifies_frame_net.statement_certified.clear();
        self.modifies_frame_net.statement_handled.clear();
    }

    /// Statement-level pass, run once the block's final output args are built.
    /// Returns the frame checks to emit with the block's safety checks.
    pub(in crate::codegen_ay::chc) fn modifies_frame_net_statements(
        &mut self,
        output_args: &[Expr],
        constraints: &[Expr],
    ) -> Vec<Expr> {
        let mut checks = Vec::new();
        let Some(&frame_idx) = self.modifies_frame_by_bb.get(&self.current_encode_bb) else {
            return checks;
        };
        let bb = self.current_encode_bb;
        let direct = directly_written_locals(&self.body.blocks[bb]);
        let watched = self.modifies_frames[frame_idx].watched.clone();
        for w in &watched {
            if direct.contains(&w.local) {
                continue;
            }
            if self.modifies_frame_net.certified.contains(&w.local) {
                // A precise check classified this block's statement store to the
                // local. The certificate covers the STATEMENT effect only: keep
                // the statement-end slots so the rule pass can still see a later
                // write by the terminator (a call handler, the nested walker).
                let slots = self.state_slots_of(w.local, output_args);
                self.modifies_frame_net.statement_certified.insert(w.local, slots);
                continue;
            }
            let changed = self.changed_state_of(w.local, output_args);
            if changed.is_empty() {
                continue;
            }
            self.modifies_frame_net.statement_handled.insert(w.local);
            let class = if self.statically_covered(frame_idx, w.local, output_args) {
                RegionClass::Covered
            } else {
                self.classify_watched_write(frame_idx, w)
            };
            debug!(bb, local = w.local, name = ?w.name, ?class, "FC-06 net: statement-level write");
            match class {
                RegionClass::Covered => {}
                RegionClass::Undecided => {
                    self.modifies_frame_fail_closed("statement write, undecided")
                }
                RegionClass::Disjoint => {
                    if w.name.is_some() && constrained_by(&changed, constraints, &[]) {
                        checks.push(unchanged_expr(&changed));
                    }
                    self.modifies_frame_fail_closed("statement write outside footprint");
                }
            }
        }
        checks
    }

    /// Output expressions of a local's state slots (`None` for a slot past the
    /// output vector).
    fn state_slots_of(&self, local: usize, output_args: &[Expr]) -> Vec<Option<Expr>> {
        self.local_state_indices(local)
            .into_iter()
            .map(|idx| output_args.get(idx).cloned())
            .collect()
    }

    /// `(output, input)` pairs of a local's state slots this transition changes.
    fn changed_state_of(&self, local: usize, output_args: &[Expr]) -> Vec<(Expr, Expr)> {
        self.local_state_indices(local)
            .into_iter()
            .filter_map(|idx| {
                let out = output_args.get(idx)?;
                let (in_name, in_sort) = &self.state_var_mgr.state_vars[idx];
                let input = Expr::var(&**in_name, in_sort.clone());
                (*out != input).then(|| (out.clone(), input))
            })
            .collect()
    }

    /// Rule-level pass, run by every transition-rule sink before the rule is
    /// added. Compares the rule's output state with the block's input state.
    pub(in crate::codegen_ay::chc) fn modifies_frame_net_rule(
        &mut self,
        from_app: &RelationApp,
        output_args: &[Expr],
        base: NetBase<'_>,
        extra: &[Expr],
    ) {
        let Some(&frame_idx) = self.modifies_frame_by_bb.get(&self.current_encode_bb) else {
            return;
        };
        self.modifies_frame_net.sink_rules += 1;
        let bb = self.current_encode_bb;
        let block = &self.body.blocks[bb];
        let terminator_writes = matches!(
            block.terminator.kind,
            TerminatorKind::Call { .. } | TerminatorKind::Drop { .. }
        );
        let direct = directly_written_locals(block);
        let watched = self.modifies_frames[frame_idx].watched.clone();
        for w in &watched {
            if direct.contains(&w.local) {
                continue;
            }
            // A statement-level certificate excuses the rule only while the
            // terminator left the local exactly as the statements did. A
            // certificate issued DURING the terminator (a precise check inside
            // the nested walker) never excuses the rule: it covers one store,
            // not the alias write-backs and handler updates beside it.
            if let Some(snapshot) = self.modifies_frame_net.statement_certified.get(&w.local)
                && *snapshot == self.state_slots_of(w.local, output_args)
            {
                continue;
            }
            if !terminator_writes && self.modifies_frame_net.statement_handled.contains(&w.local) {
                continue;
            }
            let changed = self.changed_state_of(w.local, output_args);
            if changed.is_empty() {
                continue;
            }
            let class = if self.statically_covered(frame_idx, w.local, output_args) {
                RegionClass::Covered
            } else {
                self.classify_watched_write(frame_idx, w)
            };
            debug!(bb, local = w.local, name = ?w.name, ?class, "FC-06 net: transition write");
            match class {
                RegionClass::Covered => {}
                RegionClass::Undecided => {
                    self.modifies_frame_fail_closed("transition write, undecided")
                }
                RegionClass::Disjoint => {
                    let base_exprs: &[Expr] = match &base {
                        NetBase::Slice(stmts) => stmts,
                        NetBase::Shared(shared) => shared,
                    };
                    let checkable = constrained_by(&changed, base_exprs, extra);
                    if let (Some(name), true) = (&w.name, checkable) {
                        let differs = unchanged_expr(&changed).not();
                        let from_app = self.refresh_block_relation_app(from_app);
                        let error_app = self.register_error_head(
                            PropertyKind::MemorySafety,
                            bb,
                            Some(format!("Check that {name} is assignable (modifies frame)")),
                        );
                        let mut extra_all: Vec<Expr> = extra.to_vec();
                        extra_all.push(differs);
                        let body = match base {
                            NetBase::Slice(stmts) => {
                                RuleBody::from_base_and_extra(Some(from_app), stmts, extra_all)
                            }
                            NetBase::Shared(shared) => RuleBody::from_shared_base(
                                Some(from_app),
                                Arc::clone(shared),
                                extra_all,
                            ),
                        };
                        self.vc.add_rule(Rule::new(body, error_app));
                    }
                    self.modifies_frame_fail_closed("transition write outside footprint");
                }
            }
        }
    }

    /// Snapshot taken before a call terminator inside an extent is encoded.
    pub(in crate::codegen_ay::chc) fn frame_net_call_snapshot(&self) -> Option<CallNetSnapshot> {
        if !self.in_modifies_frame_extent() {
            return None;
        }
        Some(CallNetSnapshot {
            rules: self.vc.rules.len(),
            sink_rules: self.modifies_frame_net.sink_rules,
            sound: self.diagnostics.sound_havoc_drop.get()
                + self.diagnostics.place_translation_drop.get(),
            own_check_records: self.modifies_frame_net.call_arg_check_records,
        })
    }

    /// Fail closed on call effects the net cannot see: a call with
    /// write-capable arguments that records a sound fallback, is not
    /// dispatched, or adds transitions around the rule sinks.
    pub(in crate::codegen_ay::chc) fn frame_net_after_call(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        dispatched: bool,
        snapshot: Option<CallNetSnapshot>,
    ) {
        let Some(snapshot) = snapshot else {
            return;
        };
        if !call_args_may_write(self, dcx.args, self.body.locals()) {
            return;
        }
        let sound_now =
            self.diagnostics.sound_havoc_drop.get() + self.diagnostics.place_translation_drop.get();
        let foreign_sound = snapshot
            .foreign_sound_records(sound_now, self.modifies_frame_net.call_arg_check_records);
        let transitions_added = self.vc.rules[snapshot.rules.min(self.vc.rules.len())..]
            .iter()
            .filter(|rule| !rule.head.name.as_str().starts_with("error"))
            .count();
        let sink_added = self.modifies_frame_net.sink_rules - snapshot.sink_rules;
        let callee = dcx.callee_path.as_deref().unwrap_or("<unresolved>");
        if !dispatched {
            self.modifies_frame_fail_closed(&format!("call not dispatched: {callee}"));
        } else if foreign_sound > 0 {
            self.modifies_frame_fail_closed(&format!("call over-approximated: {callee}"));
        } else if transitions_added > sink_added {
            self.modifies_frame_fail_closed(&format!("call transition bypassed the net: {callee}"));
        }
    }
}

/// Conjunction `out == in` over the changed slots.
fn unchanged_expr(changed: &[(Expr, Expr)]) -> Expr {
    changed
        .iter()
        .fold(Expr::bool_const(true), |acc, (out, input)| acc.and(out.clone().eq(input.clone())))
}

/// Is every changed output slot pinned by the transition's constraints?
///
/// An output variable no constraint mentions is a HAVOC: the model says the
/// transition MAY have written the slot, which an imprecise call model does
/// for storage the callee never touches. Accusing on a havoc would be a false
/// failure, so such a write only demotes.
fn constrained_by(changed: &[(Expr, Expr)], base: &[Expr], extra: &[Expr]) -> bool {
    changed.iter().all(|(out, _)| {
        let ay_bindings::ExprValue::Var { name } = out.value() else {
            // A non-variable output is itself the constraint.
            return true;
        };
        base.iter().chain(extra.iter()).any(|c| expr_mentions_var(c, name))
    })
}

fn expr_mentions_var(expr: &Expr, target: &str) -> bool {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if matches!(node.value(), ay_bindings::ExprValue::Var { name } if name == target) {
            return true;
        }
        stack.extend(node.children());
    }
    false
}

/// Per-block state of the frame net.
#[derive(Default)]
pub(in crate::codegen_ay::chc) struct ModifiesFrameNetState {
    /// Locals a precise frame check classified in the current block.
    pub certified: HashSet<usize>,
    /// Statement-end output slots of locals certified by the statements.
    pub statement_certified: std::collections::HashMap<usize, Vec<Option<Expr>>>,
    /// Locals the statement-level pass already classified in the current block.
    pub statement_handled: HashSet<usize>,
    /// Transition rules the net inspected (all blocks).
    pub sink_rules: usize,
    /// `modifies_frame_call_arg_overapprox` records made by the FC-06 call
    /// argument check (`modifies_frame_call_check`). `frame_net_after_call`
    /// subtracts them: they tag the check's own error rule, not an effect the
    /// net cannot see (see [`CallNetSnapshot::foreign_sound_records`]).
    pub call_arg_check_records: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fp(obj: u32, offset: u64, size: u64) -> FootprintConst {
        FootprintConst { obj: Some(obj), offset: Some(offset), size: FootprintSize::Bytes(size) }
    }

    #[test]
    fn region_inside_a_range_is_covered() {
        assert_eq!(classify_region(3, 0, 4, &[fp(3, 0, 4)]), RegionClass::Covered);
        assert_eq!(classify_region(3, 4, 4, &[fp(3, 0, 8)]), RegionClass::Covered);
        let whole = FootprintConst { obj: Some(3), offset: None, size: FootprintSize::Object };
        assert_eq!(classify_region(3, 0, 64, &[whole]), RegionClass::Covered);
    }

    #[test]
    fn region_of_another_object_is_disjoint() {
        // write_bytes_outside: q (obj 6) against modifies(&p.a) (obj 3, [0,4)).
        assert_eq!(classify_region(6, 0, 4, &[fp(3, 0, 4)]), RegionClass::Disjoint);
        // Same object, non-overlapping bytes.
        assert_eq!(classify_region(3, 4, 4, &[fp(3, 0, 4)]), RegionClass::Disjoint);
        // No footprint at all.
        assert_eq!(classify_region(3, 0, 4, &[]), RegionClass::Disjoint);
    }

    #[test]
    fn partial_overlap_and_unknowns_are_undecided() {
        // The whole Pair p (8 bytes) against modifies(&p.a): a store could be p.a or p.b.
        assert_eq!(classify_region(3, 0, 8, &[fp(3, 0, 4)]), RegionClass::Undecided);
        let symbolic_obj =
            FootprintConst { obj: None, offset: Some(0), size: FootprintSize::Bytes(4) };
        assert_eq!(classify_region(6, 0, 4, &[symbolic_obj]), RegionClass::Undecided);
        let symbolic_size =
            FootprintConst { obj: Some(6), offset: Some(0), size: FootprintSize::Unknown };
        assert_eq!(classify_region(6, 0, 4, &[symbolic_size]), RegionClass::Undecided);
        // A covering range wins over an undecided one.
        assert_eq!(classify_region(6, 0, 4, &[symbolic_obj, fp(6, 0, 4)]), RegionClass::Covered);
    }

    #[test]
    fn static_slot_coverage_needs_every_changed_slot() {
        // Pair { a, b } flattened to [a, b]; modifies(&p.a) = span (0, 1).
        assert!(slots_covered(false, &[(0, 1)], &[0]));
        assert!(!slots_covered(false, &[(0, 1)], &[0, 1]));
        assert!(!slots_covered(false, &[(0, 1)], &[1]));
        assert!(slots_covered(false, &[(0, 1), (1, 1)], &[0, 1]));
        // modifies(p): the whole local.
        assert!(slots_covered(true, &[], &[0, 1]));
        // Nothing changed is never a certificate.
        assert!(!slots_covered(true, &[], &[]));
    }

    #[test]
    fn zero_sized_region_is_covered() {
        assert_eq!(classify_region(6, 0, 0, &[]), RegionClass::Covered);
    }

    #[test]
    fn footprint_ranges_fold_through_pointer_concat() {
        let base = Expr::bitvec_const(3u64, 32).concat(Expr::bitvec_const(4u64, 32));
        let range = FootprintRange { base, size: Some(Expr::bitvec_const(4u64, 32)), wide: false };
        assert_eq!(fold_footprint_range(&range), fp(3, 4, 4));
        let offset_base = Expr::bitvec_const(3u64, 32)
            .concat(Expr::bitvec_const(0u64, 32))
            .bvadd(Expr::bitvec_const(4u64, 64));
        let range = FootprintRange { base: offset_base, size: None, wide: false };
        assert_eq!(
            fold_footprint_range(&range),
            FootprintConst { obj: Some(3), offset: Some(4), size: FootprintSize::Object }
        );
        let symbolic = FootprintRange {
            base: Expr::var("p", ay_bindings::Sort::bitvec(64)),
            size: Some(Expr::bitvec_const(4u64, 32)),
            wide: false,
        };
        let folded = fold_footprint_range(&symbolic);
        assert_eq!((folded.obj, folded.offset), (None, None));
    }
}
