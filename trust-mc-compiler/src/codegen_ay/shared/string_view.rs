// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Logical String views do not certify their model data pointer or mutable backing.

use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::visit::{Location, PlaceContext, statement_location, terminator_location};
use rustc_public::mir::{
    Body, CastKind, MirVisitor, Mutability, Operand, Place, ProjectionElem, Rvalue, StatementKind,
    TerminatorKind, UnOp,
};
use rustc_public::ty::{RigidTy, Ty, TyKind, UintTy};
use rustc_public::{CrateDef, rustc_internal};

struct Uses<'a> {
    aliases: &'a [usize],
    work: &'a mut usize,
    found: bool,
    failed: bool,
}
impl Uses<'_> {
    fn charge(&mut self, count: usize) -> bool {
        if self.failed {
            return false;
        }
        if let Some(left) = self.work.checked_sub(count) {
            *self.work = left;
            true
        } else {
            self.failed = true;
            false
        }
    }
}
impl MirVisitor for Uses<'_> {
    fn visit_place(&mut self, place: &Place, _: PlaceContext, _: Location) {
        if self.charge(place.projection.len().saturating_add(1)) {
            self.found |= self.aliases.contains(&place.local);
        }
    }
    fn visit_operand(&mut self, operand: &Operand, location: Location) {
        if self.charge(1) {
            self.super_operand(operand, location);
        }
    }
    fn visit_rvalue(&mut self, value: &Rvalue, location: Location) {
        let outer = if let Rvalue::Aggregate(_, operands) = value { operands.len() } else { 0 };
        if self.charge(outer.saturating_add(1)) {
            self.super_rvalue(value, location);
        }
    }
}

fn operand_local(operand: &Operand) -> Option<usize> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(place.local)
        }
        _ => None,
    }
}
fn copy_local(value: &Rvalue) -> Option<usize> {
    match value {
        Rvalue::Use(operand, ..) => operand_local(operand),
        Rvalue::CopyForDeref(place) if place.projection.is_empty() => Some(place.local),
        _ => None,
    }
}
fn native_str_metadata_query(tcx: TyCtxt<'_>, body: &Body, func: &Operand) -> bool {
    (|| {
        if crate::kani_middle::transform::unit_has_stubs() {return None;}
        let TyKind::RigidTy(RigidTy::FnDef(def,args))=func.ty(body.locals()).ok()?.kind() else{return None;};
        let instance=Instance::resolve(def,&args).ok()?;
        if matches!(instance.kind,InstanceKind::Virtual{..}){return None;}
        let id=rustc_internal::internal(tcx,instance.def.def_id());
        if id!=rustc_internal::internal(tcx,def.def_id()) {return None;}
        if !crate::kani_middle::std_abstraction::is_sysroot_core_definition(tcx,id){return None;}
        let owner=tcx.parent(id);
        if !matches!(tcx.def_kind(owner),rustc_hir::def::DefKind::Impl{..}) || crate::rustc_compat::impl_opt_trait_ref(tcx,owner).is_some(){return None;}
        if !matches!(crate::rustc_compat::skip_normalization(tcx.type_of(owner).instantiate_identity()).kind(),rustc_middle::ty::Str){return None;}
        let signature=instance.ty().kind().fn_sig()?.skip_binder();
        if !matches!(signature.inputs(),[input] if matches!(input.kind(),TyKind::RigidTy(RigidTy::Ref(_,inner,_)) if matches!(inner.kind(),TyKind::RigidTy(RigidTy::Str)))){return None;}
        match tcx.item_name(id).as_str() {
            "len"=>matches!(signature.output().kind(),TyKind::RigidTy(RigidTy::Uint(UintTy::Usize))).then_some(()),
            "is_empty"=>matches!(signature.output().kind(),TyKind::RigidTy(RigidTy::Bool)).then_some(()),
            _=>None,
        }
    })().is_some()
}

fn is_str_reference(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, inner, _))
        if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Str)))
}

fn is_shared_byte_slice_reference(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, inner, Mutability::Not))
        if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Slice(element))
            if matches!(element.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::U8)))))
}

/// The held core implements str::len via as_bytes and PtrMetadata. This
/// conversion preserves the length; keep its result in the same use scan so
/// observing the data pointer or bytes still requires physical custody.
fn byte_view_source(body: &Body, rhs: &Rvalue, target: Ty) -> Option<usize> {
    let Rvalue::Cast(CastKind::Transmute, operand, cast_target) = rhs else {
        return None;
    };
    if *cast_target != target || !is_shared_byte_slice_reference(target) {
        return None;
    }
    let source = operand_local(operand)?;
    let ty = body.locals().get(source)?.ty;
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, inner, Mutability::Not))
        if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Str)))
    .then_some(source)
}

/// Allow metadata observations through whole reference copies and the exact
/// shared str-to-byte-slice conversion. Reading or writing backing storage,
/// escaping the view, or exceeding the walk budget retains physical debt.
pub(in crate::codegen_ay) fn string_view_is_logical_only(
    tcx: TyCtxt<'_>,
    body: &Body,
    destination: &Place,
) -> bool {
    logical_view_uses(tcx, body, destination).is_some()
}

fn logical_view_uses(tcx: TyCtxt<'_>, body: &Body, destination: &Place) -> Option<()> {
    if !destination.projection.is_empty()
        || destination.local == 0
        || !is_str_reference(body.locals().get(destination.local)?.ty)
    {
        return None;
    }
    let mut aliases = vec![destination.local];
    let mut work = 4096usize;
    loop {
        let before = aliases.len();
        for (bb, block) in body.blocks.iter().enumerate() {
            work = work.checked_sub(1)?;
            for (index, statement) in block.statements.iter().enumerate() {
                work = work.checked_sub(1)?;
                let location = statement_location(body, &bb, index);
                if let StatementKind::Assign(lhs, rhs) = &statement.kind {
                    work = work.checked_sub(lhs.projection.len())?;
                    if !lhs.projection.is_empty() && aliases.contains(&lhs.local) {
                        return None;
                    }
                    let mut uses =
                        Uses { aliases: &aliases, work: &mut work, found: false, failed: false };
                    uses.visit_rvalue(rhs, location);
                    if uses.failed {
                        return None;
                    }
                    if !uses.found {
                        continue;
                    }
                    match rhs {
                        Rvalue::UnaryOp(UnOp::PtrMetadata, operand)
                            if operand_local(operand)
                                .is_some_and(|local| aliases.contains(&local)) => {}
                        Rvalue::Len(place)
                            if aliases.contains(&place.local)
                                && matches!(
                                    place.projection.as_slice(),
                                    [ProjectionElem::Deref]
                                ) => {}
                        _ => {
                            if !lhs.projection.is_empty() || lhs.local == 0 {
                                return None;
                            }
                            let ty = body.locals().get(lhs.local)?.ty;
                            if !is_str_reference(ty) && !is_shared_byte_slice_reference(ty) {
                                return None;
                            }
                            let source =
                                copy_local(rhs).or_else(|| byte_view_source(body, rhs, ty))?;
                            if !aliases.contains(&source) {
                                return None;
                            }
                            if !aliases.contains(&lhs.local) {
                                if aliases.len() >= 32 {
                                    return None;
                                }
                                aliases.push(lhs.local);
                            }
                        }
                    }
                } else {
                    let mut uses =
                        Uses { aliases: &aliases, work: &mut work, found: false, failed: false };
                    uses.visit_statement(statement, location);
                    if uses.failed || uses.found {
                        return None;
                    }
                }
            }
            work = work.checked_sub(1)?;
            let term = &block.terminator;
            let location = terminator_location(body, &bb);
            let mut uses = Uses { aliases: &aliases, work: &mut work, found: false, failed: false };
            if let TerminatorKind::Call { func, args, destination, .. } = &term.kind {
                if !uses.charge(args.len().saturating_add(destination.projection.len()))
                    || (!destination.projection.is_empty() && aliases.contains(&destination.local))
                {
                    return None;
                }
                uses.visit_operand(func, location);
                for arg in args {
                    uses.visit_operand(arg, location);
                }
                if uses.failed {
                    return None;
                }
                if uses.found
                    && !(args.len() == 1
                        && operand_local(&args[0]).is_some_and(|local| aliases.contains(&local))
                        && native_str_metadata_query(tcx, body, func))
                {
                    return None;
                }
            } else {
                uses.visit_terminator(term, location);
                if uses.failed || uses.found {
                    return None;
                }
            }
        }
        if aliases.len() == before {
            return Some(());
        }
    }
}
