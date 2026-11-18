// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! A closed nullness observation of an unchanged, live native empty String.
//!
//! Neither model fields nor a nonzero integer grant this capability. Its birth
//! is the actual native empty constructor; its only consumer is a null test.
//! No allocation, byte image, load, mutation or escaping pointer is certified.

use super::StatementCodegen;
use crate::codegen_ay::shared::{const_pointer, string_identity};
use crate::codegen_ay::stubs::StubKind;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::Expr;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::visit::{Location, PlaceContext, statement_location, terminator_location};
use rustc_public::mir::{
    BinOp, Body, BorrowKind, CastKind, MirVisitor, Mutability, Operand, Place, ProjectionElem,
    Rvalue, StatementKind, TerminatorKind, UnOp,
};
use rustc_public::ty::{RigidTy, Ty, TyKind, UintTy};
use rustc_public::{CrateDef, rustc_internal};

const WORK: usize = 4096;
const CARRIERS: usize = 32;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Role {
    View,
    Pointer,
    Address,
}
#[derive(Clone, Copy, PartialEq, Eq)]
struct Point {
    block: usize,
    statement: usize,
}
#[derive(Clone)]
pub(super) struct Plan {
    view_site: usize,
    owner: usize,
    alignment: usize,
    pointer_calls: Vec<usize>,
}

fn charge(work: &mut usize, amount: usize) -> Option<()> {
    *work = work.checked_sub(amount)?;
    Some(())
}
fn local(operand: &Operand) -> Option<usize> {
    match operand {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
        _ => None,
    }
}
fn shared_str(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, t, Mutability::Not))
        if matches!(t.kind(), TyKind::RigidTy(RigidTy::Str)))
}
fn shared_bytes(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, t, Mutability::Not))
        if matches!(t.kind(), TyKind::RigidTy(RigidTy::Slice(e))
            if matches!(e.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::U8)))))
}
fn pointer(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(t, Mutability::Not))
        if matches!(t.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::U8)))
            || matches!(t.kind(), TyKind::RigidTy(RigidTy::Tuple(ref fields)) if fields.is_empty()))
}
fn role_type(role: Role, ty: Ty) -> bool {
    match role {
        Role::View => shared_str(ty) || shared_bytes(ty),
        Role::Pointer => pointer(ty),
        Role::Address => matches!(ty.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::Usize))),
    }
}
fn zero(operand: &Operand) -> bool {
    matches!(operand, Operand::Constant(c) if const_pointer::const_uint(&c.const_) == Some(0))
}

struct Uses<'a> {
    locals: &'a [usize],
    work: &'a mut usize,
    found: bool,
    failed: bool,
}
fn place_uses(p: &Place, locals: &[usize], work: &mut usize) -> Option<bool> {
    charge(work, p.projection.len().saturating_add(1))?;
    Some(locals.contains(&p.local) || p.projection.iter().any(|projection| {
        matches!(projection, ProjectionElem::Index(index) if locals.contains(index))
    }))
}
impl MirVisitor for Uses<'_> {
    fn visit_place(&mut self, p: &Place, _: PlaceContext, _: Location) {
        match place_uses(p, self.locals, self.work) {
            Some(found) => self.found |= found,
            None => self.failed = true,
        }
    }
    fn visit_rvalue(&mut self, r: &Rvalue, at: Location) {
        let n = if let Rvalue::Aggregate(_, operands) = r { operands.len() } else { 0 };
        if charge(self.work, n.saturating_add(1)).is_none() {
            self.failed = true;
        } else {
            self.super_rvalue(r, at);
        }
    }
}
fn used_rvalue(
    body: &Body,
    at: Point,
    r: &Rvalue,
    locals: &[usize],
    work: &mut usize,
) -> Option<bool> {
    let mut v = Uses { locals, work, found: false, failed: false };
    v.visit_rvalue(r, statement_location(body, &at.block, at.statement));
    (!v.failed).then_some(v.found)
}

fn acyclic(body: &Body, work: &mut usize) -> Option<()> {
    if body.blocks.len() > WORK {
        return None;
    }
    let mut colors = vec![0u8; body.blocks.len()];
    let mut pending = vec![(0usize, false)];
    while let Some((bb, exit)) = pending.pop() {
        charge(work, 1)?;
        let color = colors.get_mut(bb)?;
        if exit {
            *color = 2;
            continue;
        }
        if *color == 1 {
            return None;
        }
        if *color == 2 {
            continue;
        }
        *color = 1;
        let next = body.blocks.get(bb)?.terminator.successors();
        charge(work, next.len())?;
        pending.push((bb, true));
        pending.extend(next.into_iter().map(|b| (b, false)));
    }
    Some(())
}

/// Only the actual immutable core forwarding methods, not their path spellings.
fn core_call(tcx: TyCtxt<'_>, body: &Body, func: &Operand, input: Ty) -> Option<&'static str> {
    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func.ty(body.locals()).ok()?.kind() else {
        return None;
    };
    let original = rustc_internal::internal(tcx, def.def_id());
    if !matches!(
        tcx.item_name(original).as_str(),
        "as_ptr" | "as_bytes" | "len" | "is_empty" | "addr" | "is_null"
    ) {
        return None;
    }
    let instance = Instance::resolve(def, &args).ok()?;
    if matches!(instance.kind, InstanceKind::Virtual { .. }) {
        return None;
    }
    let id = rustc_internal::internal(tcx, instance.def.def_id());
    if id != original || !crate::kani_middle::std_abstraction::is_sysroot_core_definition(tcx, id) {
        return None;
    }
    let owner = tcx.parent(id);
    if !matches!(tcx.def_kind(owner), rustc_hir::def::DefKind::Impl { .. })
        || crate::rustc_compat::impl_opt_trait_ref(tcx, owner).is_some()
    {
        return None;
    }
    let signature = instance.ty().kind().fn_sig()?.skip_binder();
    let [formal] = signature.inputs() else { return None };
    // Reference regions differ between a function signature and erased MIR.
    // Compare the complete permitted pointee/mutability shapes instead.
    if !((shared_str(input) && shared_str(*formal))
        || (shared_bytes(input) && shared_bytes(*formal))
        || (pointer(input) && pointer(*formal)))
    {
        return None;
    }
    let output = signature.output();
    let self_ty =
        crate::rustc_compat::skip_normalization(tcx.type_of(owner).instantiate_identity());
    let native_str = shared_str(input) && matches!(self_ty.kind(), rustc_middle::ty::Str);
    let native_bytes = shared_bytes(input) && matches!(self_ty.kind(), rustc_middle::ty::Slice(_));
    let native_pointer = pointer(input) && matches!(self_ty.kind(), rustc_middle::ty::RawPtr(..));
    match tcx.item_name(id).as_str() {
        "as_ptr" if (native_str || native_bytes) && pointer(output) => Some("pointer"),
        "as_bytes" if native_str && shared_bytes(output) => Some("view"),
        "len"
            if (native_str || native_bytes)
                && matches!(output.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::Usize))) =>
        {
            Some("metadata")
        }
        "is_empty"
            if (native_str || native_bytes)
                && matches!(output.kind(), TyKind::RigidTy(RigidTy::Bool)) =>
        {
            Some("metadata")
        }
        "addr"
            if native_pointer
                && matches!(output.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::Usize))) =>
        {
            Some("address")
        }
        "is_null" if native_pointer && matches!(output.kind(), TyKind::RigidTy(RigidTy::Bool)) => {
            Some("null")
        }
        _ => None,
    }
}

/// Recover a unique shared receiver producer; raw casts and retargets refuse.
fn receiver_owner(body: &Body, receiver: usize, work: &mut usize) -> Option<usize> {
    let mut current = receiver;
    let mut seen = Vec::new();
    loop {
        charge(work, 1)?;
        if seen.len() >= CARRIERS || seen.contains(&current) {
            return None;
        }
        seen.push(current);
        if !matches!(
            body.locals().get(current)?.ty.kind(),
            TyKind::RigidTy(RigidTy::Ref(_, _, Mutability::Not))
        ) {
            return None;
        }
        let mut rhs = None;
        for block in &body.blocks {
            charge(work, 1)?;
            for s in &block.statements {
                charge(work, 1)?;
                if let StatementKind::Assign(p, r) = &s.kind
                    && p.local == current
                {
                    if !p.projection.is_empty() || rhs.is_some() {
                        return None;
                    }
                    rhs = Some(r);
                }
            }
            if let TerminatorKind::Call { destination, .. } = &block.terminator.kind
                && destination.local == current
            {
                return None;
            }
        }
        match rhs? {
            Rvalue::Ref(_, BorrowKind::Shared, p) if p.projection.is_empty() => {
                return Some(p.local);
            }
            Rvalue::Use(op, ..) => current = local(op)?,
            Rvalue::CopyForDeref(p) if p.projection.is_empty() => current = p.local,
            _ => return None,
        }
    }
}

/// One immutable body analysis and one shared work allowance. Both consumers
/// select from the same bounded plans; basic-block numbers never select policy.
fn body_plans(tcx: TyCtxt<'_>, body: &Body) -> Option<Vec<Plan>> {
    if crate::kani_middle::transform::unit_has_stubs() {
        return None;
    }
    let mut work = WORK;
    let mut view_sites = Vec::new();
    for (site, block) in body.blocks.iter().enumerate() {
        charge(&mut work, 1)?;
        let TerminatorKind::Call { func, args, destination, target: Some(_), .. } =
            &block.terminator.kind
        else {
            continue;
        };
        if args.len() == 1
            && destination.projection.is_empty()
            && destination.local != 0
            && shared_str(destination.ty(body.locals()).ok()?)
            && string_identity::string_stub_is_authorized(
                tcx,
                func,
                body.locals(),
                StubKind::StringAsStr,
            )
        {
            if view_sites.len() >= CARRIERS {
                return None;
            }
            view_sites.push(site);
        }
    }
    if view_sites.is_empty() {
        return Some(Vec::new());
    }
    // A later mutation must not reenter an earlier observation. Check this
    // immutable body property once, within the same total allowance.
    acyclic(body, &mut work)?;
    let mut plans = Vec::new();
    for site in view_sites {
        if work == 0 {
            break;
        }
        if let Some(plan) = plan(tcx, body, site, &mut work) {
            plans.push(plan);
        }
    }
    Some(plans)
}

#[cfg(all(test, trust_toolchain))]
pub(super) fn test_body_eligible(tcx: TyCtxt<'_>, body: &Body) -> bool {
    body_plans(tcx, body).is_some_and(|plans| !plans.is_empty())
}

fn plan(tcx: TyCtxt<'_>, body: &Body, view_site: usize, work: &mut usize) -> Option<Plan> {
    if crate::kani_middle::transform::unit_has_stubs() {
        return None;
    }
    let block = body.blocks.get(view_site)?;
    let TerminatorKind::Call { func, args, destination, target: Some(_), .. } =
        &block.terminator.kind
    else {
        return None;
    };
    if args.len() != 1
        || !destination.projection.is_empty()
        || destination.local == 0
        || !shared_str(destination.ty(body.locals()).ok()?)
        || !string_identity::string_stub_is_authorized(
            tcx,
            func,
            body.locals(),
            StubKind::StringAsStr,
        )
    {
        return None;
    }
    let owner = receiver_owner(body, local(&args[0])?, &mut *work)?;
    let alignment =
        string_identity::native_empty_string_alignment(tcx, body.locals().get(owner)?.ty)?;
    let mut facts = vec![(destination.local, Role::View)];
    let mut uses = Vec::new();
    let mut observations = Vec::new();
    let mut pointer_calls = Vec::new();
    loop {
        let before = facts.len();
        uses.clear();
        observations.clear();
        pointer_calls.clear();
        let locals: Vec<_> = facts.iter().map(|f| f.0).collect();
        let mut additions = Vec::new();
        for (bb, block) in body.blocks.iter().enumerate() {
            charge(&mut *work, 1)?;
            for (i, s) in block.statements.iter().enumerate() {
                charge(&mut *work, 1)?;
                let at = Point { block: bb, statement: i };
                if let StatementKind::Assign(lhs, rhs) = &s.kind {
                    if place_uses(lhs, &locals, work)? && !lhs.projection.is_empty() {
                        return None;
                    }
                    if !used_rvalue(body, at, rhs, &locals, &mut *work)? {
                        continue;
                    }
                    uses.push(at);
                    let op_role = |op: &Operand| {
                        local(op).and_then(|l| facts.iter().find(|f| f.0 == l).map(|f| f.1))
                    };
                    let role = match rhs {
                        Rvalue::Use(op, ..) => Some(op_role(op)?),
                        Rvalue::CopyForDeref(p) if p.projection.is_empty() => {
                            Some(facts.iter().find(|f| f.0 == p.local)?.1)
                        }
                        Rvalue::Cast(kind, op, ty) => {
                            let source = op_role(op)?;
                            if source == Role::View
                                && matches!(kind, CastKind::Transmute)
                                && shared_str(op.ty(body.locals()).ok()?)
                                && shared_bytes(*ty)
                            {
                                Some(Role::View)
                            } else if source == Role::Pointer
                                && matches!(kind, CastKind::PtrToPtr)
                                && pointer(*ty)
                            {
                                Some(Role::Pointer)
                            } else if source == Role::Pointer
                                && matches!(kind, CastKind::PointerExposeAddress)
                                && role_type(Role::Address, *ty)
                            {
                                Some(Role::Address)
                            } else {
                                return None;
                            }
                        }
                        Rvalue::UnaryOp(UnOp::PtrMetadata, op)
                            if op_role(op) == Some(Role::View) =>
                        {
                            None
                        }
                        Rvalue::Len(p)
                            if p.projection == [rustc_public::mir::ProjectionElem::Deref]
                                && facts.contains(&(p.local, Role::View)) =>
                        {
                            None
                        }
                        Rvalue::BinaryOp(BinOp::Eq | BinOp::Ne, a, b)
                            if (matches!(op_role(a), Some(Role::Pointer | Role::Address))
                                && zero(b))
                                || (matches!(op_role(b), Some(Role::Pointer | Role::Address))
                                    && zero(a)) =>
                        {
                            observations.push(at);
                            None
                        }
                        _ => return None,
                    };
                    if let Some(role) = role {
                        if lhs.local == 0
                            || !lhs.projection.is_empty()
                            || !role_type(role, lhs.ty(body.locals()).ok()?)
                        {
                            return None;
                        }
                        additions.push((lhs.local, role));
                    }
                } else if !matches!(
                    s.kind,
                    StatementKind::StorageLive(_) | StatementKind::StorageDead(_)
                ) {
                    let mut v =
                        Uses { locals: &locals, work: &mut *work, found: false, failed: false };
                    v.visit_statement(s, statement_location(body, &bb, i));
                    if v.failed || v.found {
                        return None;
                    }
                }
            }
            let at = Point { block: bb, statement: block.statements.len() };
            match &block.terminator.kind {
                TerminatorKind::Call { func, args, destination, .. } => {
                    if place_uses(destination, &locals, work)? && !destination.projection.is_empty()
                    {
                        return None;
                    }
                    charge(&mut *work, args.len().saturating_add(1))?;
                    let mut v =
                        Uses { locals: &locals, work: &mut *work, found: false, failed: false };
                    v.visit_operand(func, terminator_location(body, &bb));
                    for a in args {
                        v.visit_operand(a, terminator_location(body, &bb));
                    }
                    if v.failed {
                        return None;
                    }
                    if !v.found {
                        continue;
                    }
                    uses.push(at);
                    if args.len() != 1
                        || destination.local == 0
                        || !destination.projection.is_empty()
                    {
                        return None;
                    }
                    let source = local(&args[0])?;
                    let source_role = facts.iter().find(|f| f.0 == source)?.1;
                    let role = match (
                        source_role,
                        core_call(tcx, body, func, args[0].ty(body.locals()).ok()?)?,
                    ) {
                        (Role::View, "pointer") => {
                            pointer_calls.push(bb);
                            Some(Role::Pointer)
                        }
                        (Role::View, "view") => Some(Role::View),
                        (Role::View, "metadata") => None,
                        (Role::Pointer, "address") => Some(Role::Address),
                        (Role::Pointer, "null") => {
                            observations.push(at);
                            None
                        }
                        _ => return None,
                    };
                    if let Some(role) = role {
                        if !role_type(role, destination.ty(body.locals()).ok()?) {
                            return None;
                        }
                        additions.push((destination.local, role));
                    }
                }
                _ => {
                    let mut v =
                        Uses { locals: &locals, work: &mut *work, found: false, failed: false };
                    v.visit_terminator(&block.terminator, terminator_location(body, &bb));
                    if v.failed || v.found {
                        return None;
                    }
                }
            }
        }
        for f in additions {
            if facts.iter().any(|old| old.0 == f.0 && old.1 != f.1) {
                return None;
            }
            if !facts.contains(&f) {
                if facts.len() >= CARRIERS {
                    return None;
                }
                facts.push(f);
            }
        }
        if facts.len() == before {
            break;
        }
    }
    if observations.is_empty() || pointer_calls.is_empty() || uses.len() > CARRIERS {
        return None;
    }
    // Every carrier has exactly one whole-value definition. A later unrelated
    // assignment must not wash out the original view's use restrictions.
    for (l, _) in &facts {
        let mut definitions = 0;
        for block in &body.blocks {
            charge(&mut *work, 1)?;
            for s in &block.statements {
                charge(&mut *work, 1)?;
                if let StatementKind::Assign(p, _) = &s.kind
                    && p.local == *l
                {
                    if !p.projection.is_empty() {
                        return None;
                    }
                    definitions += 1;
                }
            }
            if let TerminatorKind::Call { destination, .. } = &block.terminator.kind
                && destination.local == *l
            {
                definitions += 1;
            }
        }
        if definitions != 1 {
            return None;
        }
    }
    unchanged_owner_prefix(tcx, body, owner, view_site, &uses, &mut *work)?;
    Some(Plan { view_site, owner, alignment, pointer_calls })
}

/// A single actual constructor-to-consumer path proves dominance and excludes
/// moves, mutation, raw exposure or expiration before every observation. A
/// branch/cycle before the last view use declines this narrow capability.
fn unchanged_owner_prefix(
    tcx: TyCtxt<'_>,
    body: &Body,
    owner: usize,
    view_site: usize,
    uses: &[Point],
    work: &mut usize,
) -> Option<()> {
    let mut bb = 0;
    let mut seen = Vec::new();
    let mut covered = Vec::new();
    let mut refs = Vec::new();
    let mut born = false;
    let mut viewed = false;
    loop {
        charge(work, 1)?;
        if seen.len() >= CARRIERS || seen.contains(&bb) {
            return None;
        }
        seen.push(bb);
        let block = body.blocks.get(bb)?;
        for (i, s) in block.statements.iter().enumerate() {
            charge(work, 1)?;
            let at = Point { block: bb, statement: i };
            match &s.kind {
                StatementKind::StorageDead(l) if *l == owner => return None,
                StatementKind::Assign(lhs, rhs) => {
                    if lhs.local == owner {
                        return None;
                    }
                    let mut tracked = vec![owner];
                    tracked.extend(&refs);
                    if used_rvalue(body, at, rhs, &tracked, work)? {
                        if !born || !lhs.projection.is_empty() {
                            return None;
                        }
                        match rhs {
                            Rvalue::Ref(_, BorrowKind::Shared, p)
                                if p.local == owner && p.projection.is_empty() => {}
                            Rvalue::Use(op, ..) if local(op).is_some_and(|l| refs.contains(&l)) => {
                            }
                            Rvalue::CopyForDeref(p)
                                if p.projection.is_empty() && refs.contains(&p.local) => {}
                            _ => return None,
                        }
                        if !matches!(
                            lhs.ty(body.locals()).ok()?.kind(),
                            TyKind::RigidTy(RigidTy::Ref(_, _, Mutability::Not))
                        ) {
                            return None;
                        }
                        if !refs.contains(&lhs.local) {
                            if refs.len() >= CARRIERS {
                                return None;
                            }
                            refs.push(lhs.local);
                        }
                    } else if refs.contains(&lhs.local) {
                        return None;
                    }
                }
                StatementKind::StorageLive(l) if *l == owner && born => return None,
                StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => {}
                _ => {
                    let mut tracked = vec![owner];
                    tracked.extend(&refs);
                    let mut v =
                        Uses { locals: &tracked, work: &mut *work, found: false, failed: false };
                    v.visit_statement(s, statement_location(body, &bb, i));
                    if v.failed || v.found {
                        return None;
                    }
                }
            }
            if uses.contains(&at) {
                covered.push(at);
            }
            if viewed && uses.iter().all(|p| covered.contains(p)) {
                return Some(());
            }
        }
        let at = Point { block: bb, statement: block.statements.len() };
        if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind {
            charge(work, args.len().saturating_add(1))?;
            if destination.local == owner {
                if born
                    || !destination.projection.is_empty()
                    || !args.is_empty()
                    || !string_identity::string_stub_is_authorized(
                        tcx,
                        func,
                        body.locals(),
                        StubKind::StringNew,
                    )
                {
                    return None;
                }
                born = true;
            } else {
                if refs.contains(&destination.local) {
                    return None;
                }
                let mut tracked = vec![owner];
                tracked.extend(&refs);
                let mut v =
                    Uses { locals: &tracked, work: &mut *work, found: false, failed: false };
                for a in args {
                    v.visit_operand(a, terminator_location(body, &bb));
                }
                if v.failed {
                    return None;
                }
                if v.found
                    && (!born
                        || args.len() != 1
                        || !local(&args[0]).is_some_and(|l| refs.contains(&l))
                        || ![StubKind::StringAsStr, StubKind::StringLen, StubKind::StringIsEmpty]
                            .iter()
                            .any(|s| {
                                string_identity::string_stub_is_authorized(
                                    tcx,
                                    func,
                                    body.locals(),
                                    *s,
                                )
                            }))
                {
                    return None;
                }
            }
        } else {
            let mut tracked = vec![owner];
            tracked.extend(&refs);
            let mut v = Uses { locals: &tracked, work: &mut *work, found: false, failed: false };
            v.visit_terminator(&block.terminator, terminator_location(body, &bb));
            if v.failed || v.found {
                return None;
            }
        }
        if bb == view_site {
            if !born {
                return None;
            }
            viewed = true;
        }
        if uses.contains(&at) {
            covered.push(at);
        }
        if viewed && uses.iter().all(|p| covered.contains(p)) {
            return Some(());
        }
        let successors = block.terminator.successors();
        let [next] = successors.as_slice() else { return None };
        bb = *next;
    }
}

impl StatementCodegen<'_, '_, '_> {
    fn empty_string_nullness_plans(&self) -> Option<&[Plan]> {
        // Source structure is immutable; replacement authority is not cached.
        if self.ctx.unit_has_stubs() || crate::kani_middle::transform::unit_has_stubs() {
            return None;
        }
        Some(
            self.empty_string_nullness_plans
                .get_or_init(|| body_plans(self.ctx.tcx, self.body).unwrap_or_default())
                .as_slice(),
        )
    }

    pub(super) fn native_empty_string_nullness_view(
        &mut self,
        args: &[Operand],
        destination: &Place,
    ) -> bool {
        let Some(p) = self
            .empty_string_nullness_plans()
            .and_then(|plans| plans.iter().find(|p| p.view_site == self.current_bb))
            .cloned()
        else {
            return false;
        };
        let Some(receiver) = args.first() else { return false };
        p.view_site == self.current_bb
            && self.native_live_string_receiver_owner(receiver) == Some(p.owner)
            && self.native_live_string_owner(p.owner)
            && matches!(&self.body.blocks[self.current_bb].terminator.kind,
                TerminatorKind::Call { destination: actual, .. } if actual == destination)
    }

    pub(super) fn native_empty_string_nullness_as_ptr(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
    ) -> bool {
        let Some(first) = args.first() else { return false };
        let Ok(input) = first.ty(self.body.locals()) else { return false };
        if self.ctx.unit_has_stubs()
            || args.len() != 1
            || (!shared_str(input) && !shared_bytes(input))
            || !matches!(&self.body.blocks[self.current_bb].terminator.kind,
                TerminatorKind::Call { destination: actual, .. } if actual == destination)
            || core_call(self.ctx.tcx, self.body, func, input) != Some("pointer")
        {
            return false;
        }
        let Some(p) = self
            .empty_string_nullness_plans()
            .and_then(|plans| plans.iter().find(|p| p.pointer_calls.contains(&self.current_bb)))
            .cloned()
        else {
            return false;
        };
        if p.pointer_calls.contains(&self.current_bb) && self.native_live_string_owner(p.owner) {
            // Constructor bits for a closed null observation; no heap authority.
            let pointer =
                Expr::bitvec_const(p.alignment as u128, crate::codegen_ay::types::POINTER_WIDTH);
            self.assign_value_to_place(destination, pointer);
            return true;
        }

        false
    }
}
