// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Reverse physical-buffer/logical-model boundary with invocation-local work.

use super::ChcCtx;
use super::vec_buffer_access::Site;
use crate::codegen_ay::stubs::StubKind;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::visit::{MirVisitor, statement_location, terminator_location};
use rustc_public::mir::{Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};
use rustc_public::{CrateDef, rustc_internal};
use std::collections::HashSet;
mod work;
use work::{CallFacts, DEFAULT_WORK, Places, RegionWork, TypeFacts};

// Test-only resource probe: no product budget override or semantic verdict.
#[cfg(test)]
#[derive(Debug)]
pub(in crate::codegen_ay::chc) struct VecRegionBudgetProbe {
    pub(in crate::codegen_ay::chc) refused: bool,
    pub(in crate::codegen_ay::chc) exhausted: bool,
    pub(in crate::codegen_ay::chc) setup_complete: bool,
    pub(in crate::codegen_ay::chc) remaining: usize,
    pub(in crate::codegen_ay::chc) warmed_calls: usize,
    pub(in crate::codegen_ay::chc) warmed_types: usize,
    pub(in crate::codegen_ay::chc) warmed_negative_calls: usize,
}

impl ChcCtx<'_, '_> {
    fn vec_region_type_facts(&self, ty: Ty, work: &mut RegionWork) -> Result<TypeFacts, ()> {
        work.charge(1)?;
        if let Some(facts) = work.types.get(&ty).copied() {
            return Ok(facts);
        }
        work.charge(1)?;
        let resolved = self.resolve_body_ty(ty);
        let carrier = match resolved.kind() {
            TyKind::RigidTy(
                RigidTy::Bool
                | RigidTy::Char
                | RigidTy::Int(_)
                | RigidTy::Uint(_)
                | RigidTy::Float(_)
                | RigidTy::Never
                | RigidTy::FnDef(..)
                | RigidTy::FnPtr(..),
            ) => false,
            TyKind::RigidTy(RigidTy::Tuple(fields)) => !fields.is_empty(),
            _ => true,
        };
        let plain_native_owner =
            if carrier { self.vec_region_plain_native_owner(resolved, work)? } else { false };
        let facts = TypeFacts { carrier, plain_native_owner };
        work.types.insert(ty, facts); // Both positive and negative immutable answers.
        Ok(facts)
    }
    fn vec_region_place_carrier(&self, place: &Place, work: &mut RegionWork) -> Result<bool, ()> {
        work.place(place)?;
        match place.ty(self.body.locals()) {
            Ok(ty) => Ok(self.vec_region_type_facts(ty, work)?.carrier),
            Err(_) => Ok(true), // Unknown type cannot prove the region absent.
        }
    }
    fn vec_region_plain_native_owner(&self, mut ty: Ty, work: &mut RegionWork) -> Result<bool, ()> {
        work.charge(1)?;
        // A transitive replacement can change allocator/drop body effects.
        if crate::kani_middle::transform::unit_has_stubs() {
            return Ok(false);
        }
        let custom = match work.custom_global_allocator {
            Some(value) => value,
            None => {
                work.charge(self.tcx.crates(()).len().checked_add(1).ok_or(())?)?;
                let value = crate::codegen_ay::shared::native_box_raw::native_bmc_has_custom_global_allocator(self.tcx);
                work.custom_global_allocator = Some(value);
                value
            }
        };
        if custom {
            return Ok(false);
        }
        for _ in 0..8 {
            work.charge(1)?;
            match self.resolve_body_ty(ty).kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => {
                    ty = inner
                }
                TyKind::RigidTy(RigidTy::Adt(owner, args)) => {
                    work.charge(1)?;
                    let owner_id = rustc_internal::internal(self.tcx, owner.def_id());
                    let native_vec =
                        crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(
                            self.tcx,
                            owner_id,
                            &["vec", "Vec"],
                        );
                    work.charge(1)?;
                    let native_backing =
                        crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(
                            self.tcx,
                            owner_id,
                            &["raw_vec", "RawVec"],
                        );
                    if !native_vec && !native_backing {
                        return Ok(false);
                    }
                    let [GenericArgKind::Type(element), GenericArgKind::Type(allocator)] =
                        args.0.as_slice()
                    else {
                        return Ok(false);
                    };
                    work.charge(2)?;
                    if !matches!(
                        self.resolve_body_ty(*element).kind(),
                        TyKind::RigidTy(
                            RigidTy::Bool
                                | RigidTy::Char
                                | RigidTy::Int(_)
                                | RigidTy::Uint(_)
                                | RigidTy::Float(_)
                        )
                    ) {
                        return Ok(false);
                    }
                    let TyKind::RigidTy(RigidTy::Adt(allocator, _)) =
                        self.resolve_body_ty(*allocator).kind()
                    else {
                        return Ok(false);
                    };
                    work.charge(1)?;
                    return Ok(
                        crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(
                            self.tcx,
                            rustc_internal::internal(self.tcx, allocator.def_id()),
                            &["alloc", "Global"],
                        ),
                    );
                }
                _ => return Ok(false),
            }
        }
        Ok(false)
    }
    fn vec_region_native_drop_identity(
        &self,
        func: &Operand,
        args: &[Operand],
        work: &mut RegionWork,
    ) -> Result<bool, ()> {
        let [arg] = args else { return Ok(false) };
        work.operand(arg)?;
        let (Operand::Copy(_) | Operand::Move(_)) = arg else { return Ok(false) };
        work.charge(1)?;
        // Classify model observation only. Actual drop/deallocation encoding
        // and its memory/provenance checks remain independent.
        let expected_owner: &[&str] = match self.detect_stub(func) {
            Some(StubKind::VecDrop) => &["vec", "Vec"],
            Some(StubKind::RawVecDrop) => &["raw_vec", "RawVec"],
            _ => return Ok(false),
        };
        let Ok(ty) = arg.ty(self.body.locals()) else { return Ok(false) };
        if !self.vec_region_type_facts(ty, work)?.plain_native_owner {
            return Ok(false);
        }
        work.operand(func)?;
        let Some(TyKind::RigidTy(RigidTy::FnDef(def, generics))) =
            func.ty(self.body.locals()).ok().map(|ty| ty.kind())
        else {
            return Ok(false);
        };
        work.charge(1)?;
        let Ok(instance) = Instance::resolve(def, &generics) else { return Ok(false) };
        if matches!(instance.kind, rustc_public::mir::mono::InstanceKind::Virtual { .. })
            || crate::kani_middle::transform::instance_has_unit_stub(&instance)
        {
            return Ok(false);
        }
        work.charge(1)?;
        let Some(signature) = instance.ty().kind().fn_sig() else { return Ok(false) };
        let signature = signature.skip_binder();
        let [input] = signature.inputs() else { return Ok(false) };
        // Function signatures retain a bound receiver lifetime; MIR locals
        // erase it. Require mutable references to the same resolved owner,
        // without assigning semantic significance to that outer lifetime.
        let TyKind::RigidTy(RigidTy::Ref(_, signature_owner, rustc_public::mir::Mutability::Mut)) =
            self.resolve_body_ty(*input).kind()
        else {
            return Ok(false);
        };
        let TyKind::RigidTy(RigidTy::Ref(_, actual_owner, rustc_public::mir::Mutability::Mut)) =
            self.resolve_body_ty(ty).kind()
        else {
            return Ok(false);
        };
        if self.resolve_body_ty(signature_owner) != self.resolve_body_ty(actual_owner)
            || !matches!(signature.output().kind(), TyKind::RigidTy(RigidTy::Tuple(fields)) if fields.is_empty())
        {
            return Ok(false);
        }
        let def = rustc_internal::internal(self.tcx, instance.def.def_id());
        work.charge(1)?;
        if !crate::kani_middle::std_abstraction::is_sysroot_alloc_definition(self.tcx, def)
            || self.tcx.item_name(def).as_str() != "drop"
        {
            return Ok(false);
        }
        let implementation = self.tcx.parent(def);
        if !matches!(self.tcx.def_kind(implementation), rustc_hir::def::DefKind::Impl { .. }) {
            return Ok(false);
        }
        let Some(trait_ref) = crate::rustc_compat::impl_opt_trait_ref(self.tcx, implementation)
        else {
            return Ok(false);
        };
        work.charge(1)?;
        if !crate::kani_middle::std_abstraction::is_sysroot_core_definition_at(
            self.tcx,
            crate::rustc_compat::skip_normalization(trait_ref.instantiate_identity()).def_id,
            &["ops", "drop", "Drop"],
        ) {
            return Ok(false);
        }
        work.charge(1)?;
        let native_self = crate::rustc_compat::skip_normalization(
            self.tcx.type_of(implementation).instantiate_identity(),
        );
        Ok(matches!(native_self.kind(), rustc_middle::ty::Adt(adt, _)
            if crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(self.tcx, adt.did(), expected_owner)))
    }
    #[cfg(test)]
    pub(in crate::codegen_ay::chc) fn vec_region_drop_call_has_no_model_observation_for_test(
        &self,
        func: &Operand,
        args: &[Operand],
    ) -> bool {
        self.vec_region_native_drop_identity(func, args, &mut RegionWork::new(DEFAULT_WORK))
            .unwrap_or(false)
    }

    fn vec_region_call_facts(
        &self,
        block: usize,
        func: &Operand,
        args: &[Operand],
        work: &mut RegionWork,
    ) -> Result<CallFacts, ()> {
        work.charge(1)?;
        if let Some(facts) = work.calls.get(&block).copied() {
            return Ok(facts);
        }
        work.operand(func)?;
        // Cache only immutable identity/signature facts. Receiver alias truth
        // is evaluated from the current fixed point on every visit.
        work.charge(args.len())?;
        let header = if let Some(TyKind::RigidTy(RigidTy::FnDef(def, generics))) =
            func.ty(self.body.locals()).ok().map(|ty| ty.kind())
        {
            work.charge(1)?;
            Instance::resolve(def, &generics).ok().is_some_and(|instance| {
                !crate::kani_middle::transform::instance_has_unit_stub(&instance)
                    && self.vec_call_only_queries_buffer(func, args, &|_| true)
            })
        } else {
            false
        };
        let drop = self.vec_region_native_drop_identity(func, args, work)?;
        work.operand(func)?;
        work.charge(1)?;
        let initializes = self.vec_call_initializes_buffer(func);
        let facts = CallFacts { header, drop, initializes };
        work.calls.insert(block, facts); // Includes failed resolution/negative identities.
        Ok(facts)
    }
    fn vec_region_operands_touch(
        &self,
        args: &[Operand],
        aliases: &HashSet<usize>,
        work: &mut RegionWork,
    ) -> Result<bool, ()> {
        work.charge(args.len())?; // Cached identities never skip the operand work.
        Ok(args.iter().any(
            |op| matches!(op, Operand::Copy(p) | Operand::Move(p) if aliases.contains(&p.local)),
        ))
    }
    fn vec_region_places_touch(
        &self,
        places: &[Place],
        aliases: &HashSet<usize>,
        work: &mut RegionWork,
    ) -> Result<bool, ()> {
        work.charge(places.len())?;
        Ok(places.iter().any(|p| aliases.contains(&p.local)))
    }

    pub(super) fn vec_region_observation_after(
        &self,
        reach: &[HashSet<usize>],
        owner: usize,
        write: Site,
    ) -> Option<Site> {
        let mut work = RegionWork::new(DEFAULT_WORK);
        self.vec_region_observation_with_work(reach, owner, write, &mut work).unwrap_or(Some(write))
    }
    fn vec_region_observation_with_work(
        &self,
        reach: &[HashSet<usize>],
        owner: usize,
        write: Site,
        work: &mut RegionWork,
    ) -> Result<Option<Site>, ()> {
        work.charge(1)?;
        let mut aliases = HashSet::from([owner]); // Replaces the unbudgeted vec_aliases prepass.
        loop {
            work.charge(1)?;
            let before = aliases.len();
            work.charge(aliases.len())?;
            if aliases.iter().any(|&l| l > 0 && l <= self.body.arg_locals().len()) {
                for l in 1..=self.body.arg_locals().len() {
                    work.charge(1)?;
                    if self.vec_region_type_facts(self.body.locals()[l].ty, work)?.carrier {
                        aliases.insert(l);
                    }
                }
            }
            for (bb, block) in self.body.blocks.iter().enumerate() {
                work.charge(1)?; // Includes blocks with zero statements.
                for (si, statement) in block.statements.iter().enumerate() {
                    work.charge(1)?;
                    let StatementKind::Assign(lhs, rhs) = &statement.kind else { continue };
                    let mut collector = Places::new(work);
                    collector.visit_rvalue(rhs, statement_location(self.body, &bb, si));
                    let places = collector.finish()?;
                    let transports = matches!(
                        rhs,
                        Rvalue::Ref(..)
                            | Rvalue::AddressOf(..)
                            | Rvalue::Use(..)
                            | Rvalue::Cast(..)
                            | Rvalue::CopyForDeref(..)
                            | Rvalue::Aggregate(..)
                    );
                    let lhs_carrier = self.vec_region_place_carrier(lhs, work)?;
                    if transports
                        && lhs_carrier
                        && self.vec_region_places_touch(&places, &aliases, work)?
                    {
                        aliases.insert(lhs.local);
                    }
                    if transports && aliases.contains(&lhs.local) {
                        for place in &places {
                            work.charge(1)?;
                            if self.vec_region_place_carrier(place, work)? {
                                aliases.insert(place.local);
                            }
                        }
                    }
                }
                work.charge(1)?; // Every Call/Drop/other terminator, even with an empty block.
                if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                {
                    let facts = self.vec_region_call_facts(bb, func, args, work)?;
                    let touches = self.vec_region_operands_touch(args, &aliases, work)?;
                    if !facts.header
                        && !facts.drop
                        && touches
                        && self.vec_region_place_carrier(destination, work)?
                    {
                        aliases.insert(destination.local);
                    }
                }
            }
            if before == aliases.len() {
                break;
            }
        }
        let after = |at: Site| {
            (at.block == write.block && at.index > write.index)
                || reach.get(write.block).is_some_and(|r| r.contains(&at.block))
        };
        let related = |at: Site| {
            at.block == write.block
                || reach.get(write.block).is_some_and(|r| r.contains(&at.block))
                || reach.get(at.block).is_some_and(|r| r.contains(&write.block))
        };
        for (bb, block) in self.body.blocks.iter().enumerate() {
            work.charge(1)?;
            for (si, statement) in block.statements.iter().enumerate() {
                work.charge(1)?;
                let at = Site { block: bb, index: si };
                match &statement.kind {
                    StatementKind::Assign(lhs, rhs) => {
                        let mut collector = Places::new(work);
                        collector.visit_rvalue(rhs, statement_location(self.body, &bb, si));
                        let places = collector.finish()?;
                        let touches = self.vec_region_places_touch(&places, &aliases, work)?;
                        work.place(lhs)?;
                        let indirect =
                            lhs.projection.iter().any(|p| matches!(p, ProjectionElem::Deref));
                        let transports = matches!(
                            rhs,
                            Rvalue::Ref(..)
                                | Rvalue::AddressOf(..)
                                | Rvalue::Use(..)
                                | Rvalue::Cast(..)
                                | Rvalue::CopyForDeref(..)
                                | Rvalue::Aggregate(..)
                        );
                        if related(at)
                            && (touches && indirect
                                || aliases.contains(&lhs.local)
                                    && (!transports || places.is_empty()))
                        {
                            return Ok(Some(at));
                        }
                        let result_carrier = self.vec_region_place_carrier(lhs, work)?;
                        if related(at) && touches && (!transports || !result_carrier) {
                            return Ok(Some(at));
                        }
                    }
                    StatementKind::StorageLive(_)
                    | StatementKind::StorageDead(_)
                    | StatementKind::FakeRead(..)
                    | StatementKind::PlaceMention(_)
                    | StatementKind::AscribeUserType { .. }
                    | StatementKind::Coverage(_)
                    | StatementKind::ConstEvalCounter
                    | StatementKind::Nop => {}
                    _ => {
                        let mut collector = Places::new(work);
                        collector
                            .visit_statement(statement, statement_location(self.body, &bb, si));
                        let places = collector.finish()?;
                        if related(at) && self.vec_region_places_touch(&places, &aliases, work)? {
                            return Ok(Some(at));
                        }
                    }
                }
            }
            work.charge(1)?;
            let at = Site { block: bb, index: block.statements.len() };
            match &block.terminator.kind {
                TerminatorKind::Call { func, args, destination, .. } => {
                    let facts = self.vec_region_call_facts(bb, func, args, work)?;
                    let touches = self.vec_region_operands_touch(args, &aliases, work)?;
                    if touches && (facts.header || facts.drop) {
                        continue;
                    }
                    if related(at)
                        && (touches || aliases.contains(&destination.local) && !facts.initializes)
                    {
                        return Ok(Some(at));
                    }
                }
                TerminatorKind::Drop { place, .. } if aliases.contains(&place.local) => {
                    work.place(place)?;
                    let plain = match place.ty(self.body.locals()) {
                        Ok(ty) => self.vec_region_type_facts(ty, work)?.plain_native_owner,
                        Err(_) => false,
                    };
                    if related(at) && !plain {
                        return Ok(Some(at));
                    }
                }
                TerminatorKind::Return if aliases.contains(&0) && after(at) => return Ok(Some(at)),
                _ => {
                    let mut collector = Places::new(work);
                    collector
                        .visit_terminator(&block.terminator, terminator_location(self.body, &bb));
                    let places = collector.finish()?;
                    if related(at) && self.vec_region_places_touch(&places, &aliases, work)? {
                        return Ok(Some(at));
                    }
                }
            }
        }
        Ok(None)
    }

    fn vec_region_reach_with_work(&self, work: &mut RegionWork) -> Result<Vec<HashSet<usize>>, ()> {
        // Prepay vectors before allocating, including a call-only CFG.
        work.charge(self.body.blocks.len())?;
        let mut successors = Vec::with_capacity(self.body.blocks.len());
        for block in &self.body.blocks {
            work.charge(2)?; // Block and terminator.
            let edges = match &block.terminator.kind {
                TerminatorKind::SwitchInt { targets, .. } => targets.len(),
                _ => 2,
            };
            work.charge(edges)?; // successors() may allocate/copy every switch edge.
            successors.push(block.terminator.successors());
        }
        work.charge(successors.len())?;
        let mut reach = Vec::with_capacity(successors.len());
        for start in 0..successors.len() {
            work.charge(1)?;
            work.charge(successors[start].len())?;
            let mut stack = successors[start].clone();
            let mut seen = HashSet::new();
            while let Some(bb) = stack.pop() {
                work.charge(1)?;
                if bb >= successors.len() {
                    return Err(());
                }
                if seen.insert(bb) {
                    work.charge(successors[bb].len())?;
                    stack.extend(successors[bb].iter().copied());
                }
            }
            reach.push(seen);
        }
        Ok(reach)
    }
    pub(in crate::codegen_ay::chc) fn book_native_vec_store_model_boundary(
        &self,
        pointer: usize,
        owner: usize,
    ) {
        let mut work = RegionWork::new(DEFAULT_WORK);
        let result = (|| -> Result<bool, ()> {
            let reach = self.vec_region_reach_with_work(&mut work)?;
            let mut found = false;
            for (bb, block) in self.body.blocks.iter().enumerate() {
                work.charge(1)?;
                for (si, statement) in block.statements.iter().enumerate() {
                    work.charge(1)?;
                    if let StatementKind::Assign(lhs, _) = &statement.kind {
                        work.place(lhs)?;
                        if lhs.local == pointer
                            && matches!(lhs.projection.first(), Some(ProjectionElem::Deref))
                        {
                            found = true;
                            if self
                                .vec_region_observation_with_work(
                                    &reach,
                                    owner,
                                    Site { block: bb, index: si },
                                    &mut work,
                                )?
                                .is_some()
                            {
                                return Ok(true);
                            }
                        }
                    }
                }
                work.charge(1)?; // Write-binding scan charges every terminator too.
            }
            Ok(!found)
        })();
        if result.unwrap_or(true) {
            self.record_sound_fallback_reason("vec_model_read_after_buffer_write");
        }
    }
    /// Exercise the real region worker with real MIR and optional immutable
    /// cache warming. Only a smaller cfg(test) allowance is injectable; the
    /// product DEFAULT_WORK remains65536 and has no runtime override.
    #[cfg(test)]
    pub(in crate::codegen_ay::chc) fn vec_region_budget_probe_for_test(
        &self,
        owner: usize,
        anchor: (usize, usize),
        limit: usize,
        warm: bool,
    ) -> VecRegionBudgetProbe {
        let mut setup = RegionWork::new(DEFAULT_WORK);
        let prepared = (|| -> Result<_, ()> {
            let block = self.body.blocks.get(anchor.0).ok_or(())?;
            if anchor.1 > block.statements.len() || owner >= self.body.locals().len() {
                return Err(());
            }
            let reach = self.vec_region_reach_with_work(&mut setup)?;
            if warm {
                for local in self.body.locals() {
                    setup.charge(1)?;
                    self.vec_region_type_facts(local.ty, &mut setup)?;
                }
                for (bb, block) in self.body.blocks.iter().enumerate() {
                    setup.charge(2)?;
                    if let TerminatorKind::Call { func, args, .. } = &block.terminator.kind {
                        self.vec_region_call_facts(bb, func, args, &mut setup)?;
                    }
                }
            }
            setup.charge(setup.calls.len())?;
            let negative_calls = setup
                .calls
                .values()
                .filter(|facts| !facts.header && !facts.drop && !facts.initializes)
                .count();
            Ok((reach, negative_calls))
        })();
        let Ok((reach, warmed_negative_calls)) = prepared else {
            self.record_sound_fallback_reason("vec_model_read_after_buffer_write");
            return VecRegionBudgetProbe {
                refused: true,
                exhausted: setup.exhausted,
                setup_complete: false,
                remaining: setup.remaining,
                warmed_calls: setup.calls.len(),
                warmed_types: setup.types.len(),
                warmed_negative_calls: 0,
            };
        };
        let warmed_calls = setup.calls.len();
        let warmed_types = setup.types.len();
        let mut work = RegionWork::new(limit.min(DEFAULT_WORK));
        if warm {
            work.types = setup.types;
            work.calls = setup.calls;
            work.custom_global_allocator = setup.custom_global_allocator;
        }
        let write = Site { block: anchor.0, index: anchor.1 };
        let refused = self
            .vec_region_observation_with_work(&reach, owner, write, &mut work)
            .unwrap_or(Some(write))
            .is_some();
        if refused {
            self.record_sound_fallback_reason("vec_model_read_after_buffer_write");
        }
        VecRegionBudgetProbe {
            refused,
            exhausted: work.exhausted,
            setup_complete: true,
            remaining: work.remaining,
            warmed_calls,
            warmed_types,
            warmed_negative_calls,
        }
    }
}
