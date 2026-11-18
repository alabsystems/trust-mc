// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Exact storage addresses returned by small pure MIR bodies.
//! A referent value never supplies its own address. This summary follows only
//! typed reference copies/reborrows and raw field-address producers, then binds
//! that path to the caller's unique live, already-addressed stack owner.

mod shared_slice;

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_ctx::RefTarget;
use super::codegen_types::CodegenTypes;
use crate::codegen_ay::chc::decl::codegen_decl_static_alloc::declared_field_tys_for_sort;
use crate::codegen_ay::chc::decl::codegen_types_adt_sort::CodegenTypesAdtSort;
use crate::codegen_ay::chc::decl::static_path::same_ty_modulo_regions;
use crate::codegen_ay::provenance::Loc;
use ay_bindings::Expr;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    Body, BorrowKind, CastKind, Mutability, Operand, Place, ProjectionElem, RawPtrKind, Rvalue,
    StatementKind, TerminatorKind,
};
use rustc_public::ty::{AdtKind, RigidTy, Ty, TyKind};
use std::collections::{BTreeMap, HashMap, HashSet};

const MAX_WORK: usize = 4096;
const MAX_DEPTH: usize = 8;
const MAX_REF_CHAIN: usize = 16;

struct Work(usize);
impl Work {
    fn tick(&mut self, ctx: &mut ChcCtx<'_, '_>) -> Option<()> {
        self.0 = self.0.checked_sub(1)?;
        ctx.spend_inline_work()
    }
}

#[derive(Clone)]
struct StoragePath {
    projections: Vec<ProjectionElem>,
    pointee: Ty,
    reference: bool,
    mutable: bool,
    shared_slice: bool,
}

struct StorageAddress {
    address: Loc,
    target: RefTarget,
    offset: u32,
    object: u32,
}

enum Definition {
    Value(Rvalue),
    Call,
}

fn plain_local(operand: &Operand) -> Option<usize> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(place.local)
        }
        _ => None,
    }
}

impl ChcCtx<'_, '_> {
    // The MIR producer scans and ref-target/address tables below name host
    // locals. Inline frame-local numbers cannot borrow that host authority.
    fn inline_storage_has_host_scope(&self) -> bool {
        self.inline_walk_frames.is_empty() && self.inline_walk_write_mark.is_none()
    }

    // The register representation must be the actual per-declared-field
    // datatype, not a specialised collection/wrapper or pointer-shaped value.
    fn storage_address_shape(&mut self, ty: Ty, depth: usize, work: &mut Work) -> Option<()> {
        work.tick(self)?;
        let ty = self.resolve_body_ty(ty);
        match ty.kind() {
            TyKind::RigidTy(
                RigidTy::Bool
                | RigidTy::Char
                | RigidTy::Int(_)
                | RigidTy::Uint(_)
                | RigidTy::Float(_),
            ) => return Some(()),
            TyKind::RigidTy(RigidTy::Adt(def, args)) if def.kind() == AdtKind::Struct => {
                if Self::translate_ty(ty)? != Self::translate_adt_sort(def, args)? {
                    return None;
                }
            }
            TyKind::RigidTy(RigidTy::Tuple(_)) => {}
            _ => return None,
        }
        if depth == 0 || self.ty_has_interior_mut(ty) {
            return None;
        }
        let sort = Self::translate_ty(ty)?;
        let datatype = sort.datatype_sort()?;
        let [constructor] = datatype.constructors.as_slice() else { return None };
        let fields = declared_field_tys_for_sort(ty, constructor)?;
        for (field, sort_field) in fields.into_iter().zip(&constructor.fields) {
            work.tick(self)?;
            if Self::translate_ty(field)?.ne(&sort_field.sort) {
                return None;
            }
            self.storage_address_shape(field, depth - 1, work)?;
        }
        Some(())
    }

    // An address of the carrier permits aliases to replace it. Projected
    // pointer-value writes and ambiguous whole definitions are denied too;
    // stores through its Deref are pointee writes, not carrier definitions.
    fn storage_address_definition(&mut self, local: usize, work: &mut Work) -> Option<Definition> {
        let body = self.body;
        let mut found = None;
        for block in &body.blocks {
            work.tick(self)?;
            for statement in &block.statements {
                work.tick(self)?;
                if let StatementKind::Assign(lhs, rhs) = &statement.kind {
                    if let Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) = rhs
                        && place.local == local
                        && !matches!(place.projection.first(), Some(ProjectionElem::Deref))
                    {
                        return None;
                    }
                    if lhs.local == local
                        && !lhs.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
                    {
                        if !lhs.projection.is_empty() || found.is_some() {
                            return None;
                        }
                        found = Some(Definition::Value(rhs.clone()));
                    }
                }
            }
            work.tick(self)?;
            if let TerminatorKind::Call { destination, .. } = &block.terminator.kind
                && destination.local == local
                && !destination.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
            {
                if !destination.projection.is_empty() || found.is_some() {
                    return None;
                }
                found = Some(Definition::Call);
            }
        }
        found
    }

    // Ref-target/address caches are path-insensitive. Every whole pointer copy
    // that can inherit this result must retain a unique, unexposed carrier.
    // Aggregate/reference/opaque-call escapes require a richer custody model.
    fn storage_address_result_custody(&mut self, first: usize, work: &mut Work) -> Option<()> {
        let mut seen = HashSet::new();
        let mut pending = vec![first];
        while let Some(local) = pending.pop() {
            work.tick(self)?;
            if seen.contains(&local) {
                continue;
            }
            if seen.len() >= MAX_REF_CHAIN {
                return None;
            }
            seen.insert(local);
            let definition = self.storage_address_definition(local, work)?;
            if local == first && !matches!(definition, Definition::Call) {
                return None;
            }
            let body = self.body;
            for block in &body.blocks {
                work.tick(self)?;
                for statement in &block.statements {
                    work.tick(self)?;
                    let StatementKind::Assign(lhs, rhs) = &statement.kind else { continue };
                    let copied = match rhs {
                        Rvalue::Use(source, ..) | Rvalue::Cast(CastKind::PtrToPtr, source, _) => {
                            plain_local(source)
                        }
                        Rvalue::Cast(_, source, _)
                            if plain_local(source) == Some(local)
                                && matches!(
                                    self.resolve_body_ty(body.locals().get(lhs.local)?.ty).kind(),
                                    TyKind::RigidTy(RigidTy::RawPtr(..))
                                ) =>
                        {
                            return None;
                        }
                        Rvalue::CopyForDeref(place) if place.projection.is_empty() => {
                            Some(place.local)
                        }
                        Rvalue::Aggregate(_, operands)
                            if operands.iter().any(|source| plain_local(source) == Some(local)) =>
                        {
                            return None;
                        }
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)
                            if place.local == local =>
                        {
                            return None;
                        }
                        _ => None,
                    };
                    if copied == Some(local) {
                        let TyKind::RigidTy(RigidTy::RawPtr(_, capability)) =
                            self.resolve_body_ty(body.locals().get(lhs.local)?.ty).kind()
                        else {
                            return None;
                        };
                        let TyKind::RigidTy(RigidTy::RawPtr(_, source_capability)) =
                            self.resolve_body_ty(body.locals().get(local)?.ty).kind()
                        else {
                            return None;
                        };
                        if !lhs.projection.is_empty()
                            || (capability == Mutability::Mut
                                && source_capability != Mutability::Mut)
                        {
                            return None;
                        }
                        pending.push(lhs.local);
                    }
                }
                if let TerminatorKind::Call { args, .. } = &block.terminator.kind
                    && args.iter().any(|source| plain_local(source) == Some(local))
                {
                    return None;
                }
            }
        }
        Some(())
    }

    fn storage_address_host_owner(
        &mut self,
        arg: &Operand,
        root: Ty,
        mutable: bool,
        work: &mut Work,
    ) -> Option<usize> {
        let first = plain_local(arg)?;
        let mut local = first;
        let mut seen = HashSet::new();
        for _ in 0..MAX_REF_CHAIN {
            work.tick(self)?;
            if !seen.insert(local) || self.stack_local_is_live(local) != Some(true) {
                return None;
            }
            let TyKind::RigidTy(RigidTy::Ref(_, pointee, capability)) =
                self.resolve_body_ty(self.body.locals().get(local)?.ty).kind()
            else {
                return None;
            };
            if !same_ty_modulo_regions(self.resolve_body_ty(pointee), root)
                || (mutable && capability != Mutability::Mut)
            {
                return None;
            }
            match self.storage_address_definition(local, work)? {
                Definition::Value(Rvalue::Ref(_, _, place)) if place.projection.is_empty() => {
                    let owner = place.local;
                    if !same_ty_modulo_regions(
                        self.resolve_body_ty(self.body.locals().get(owner)?.ty),
                        root,
                    ) || self.stack_local_is_live(owner) != Some(true)
                        || !self.heap_state.local_addresses.contains_key(&owner)
                    {
                        return None;
                    }
                    let target = self.ref_resolution.ref_targets.get(&first)?;
                    return (target.local == owner && target.projections.is_empty())
                        .then_some(owner);
                }
                Definition::Value(Rvalue::Ref(_, _, place))
                    if place.projection.as_slice() == [ProjectionElem::Deref] =>
                {
                    local = place.local
                }
                Definition::Value(Rvalue::Use(source, ..)) => local = plain_local(&source)?,
                Definition::Value(Rvalue::CopyForDeref(place)) if place.projection.is_empty() => {
                    local = place.local
                }
                _ => return None,
            }
        }
        None
    }

    fn storage_address_project(
        &mut self,
        place: &Place,
        values: &HashMap<usize, StoragePath>,
        work: &mut Work,
    ) -> Option<StoragePath> {
        let [ProjectionElem::Deref, tail @ ..] = place.projection.as_slice() else { return None };
        let mut value = values.get(&place.local)?.clone();
        if value.shared_slice {
            return None;
        }
        for projection in tail {
            work.tick(self)?;
            let ProjectionElem::Field(index, declared) = projection else { return None };
            let ty = self.resolve_body_ty(value.pointee);
            let sort = Self::translate_ty(ty)?;
            let datatype = sort.datatype_sort()?;
            let [constructor] = datatype.constructors.as_slice() else { return None };
            let field = *declared_field_tys_for_sort(ty, constructor)?.get(*index)?;
            if !same_ty_modulo_regions(self.resolve_body_ty(field), self.resolve_body_ty(*declared))
            {
                return None;
            }
            self.get_field_offset(ty, *index)?;
            value.projections.push(projection.clone());
            value.pointee = field;
            if value.projections.len() > MAX_DEPTH {
                return None;
            }
        }
        Some(value)
    }

    fn storage_address_body_path(
        &mut self,
        body: &Body,
        root: Ty,
        mutable: bool,
        work: &mut Work,
    ) -> Option<StoragePath> {
        let mut values = HashMap::from([(
            1,
            StoragePath {
                projections: Vec::new(),
                pointee: root,
                reference: true,
                mutable,
                shared_slice: false,
            },
        )]);
        let mut visited = HashSet::new();
        let mut bb = 0;
        loop {
            work.tick(self)?;
            if !visited.insert(bb) {
                return None;
            }
            let block = body.blocks.get(bb)?;
            for statement in &block.statements {
                work.tick(self)?;
                match &statement.kind {
                    StatementKind::Assign(lhs, rhs)
                        if lhs.local != 1 && lhs.projection.is_empty() =>
                    {
                        let mut value = match rhs {
                            Rvalue::Use(source, ..) => values.get(&plain_local(source)?)?.clone(),
                            Rvalue::CopyForDeref(place) if place.projection.is_empty() => {
                                values.get(&place.local)?.clone()
                            }
                            Rvalue::Ref(_, kind, place) => {
                                // A field reborrow retains the caller's typed
                                // storage path, just as a raw field-address
                                // producer does. Only an existing reference
                                // can lend this path; neither referent values
                                // nor raw pointer bits create reference custody.
                                if !matches!(kind, BorrowKind::Shared | BorrowKind::Mut { .. }) {
                                    return None;
                                }
                                let value = self.storage_address_project(place, &values, work)?;
                                if !value.reference {
                                    return None;
                                }
                                value
                            }
                            Rvalue::AddressOf(kind, place) => {
                                let mut value =
                                    self.storage_address_project(place, &values, work)?;
                                if *kind == RawPtrKind::Mut && !value.mutable {
                                    return None;
                                }
                                value.reference = false;
                                value.mutable = *kind == RawPtrKind::Mut;
                                value
                            }
                            Rvalue::Cast(CastKind::PtrToPtr, source, _) => {
                                let value = values.get(&plain_local(source)?)?.clone();
                                if value.reference {
                                    return None;
                                }
                                value
                            }
                            _ => return None,
                        };
                        let (pointee, reference, capability) =
                            match self.resolve_body_ty(body.locals().get(lhs.local)?.ty).kind() {
                                TyKind::RigidTy(RigidTy::Ref(_, inner, capability)) => {
                                    (inner, true, capability)
                                }
                                TyKind::RigidTy(RigidTy::RawPtr(inner, capability)) => {
                                    (inner, false, capability)
                                }
                                _ => return None,
                            };
                        let actual_pointee = if value.shared_slice {
                            let TyKind::RigidTy(RigidTy::Slice(element)) =
                                self.resolve_body_ty(pointee).kind()
                            else {
                                return None;
                            };
                            element
                        } else {
                            pointee
                        };
                        if value.reference != reference
                            || !same_ty_modulo_regions(
                                self.resolve_body_ty(actual_pointee),
                                self.resolve_body_ty(value.pointee),
                            )
                            || (capability == Mutability::Mut && !value.mutable)
                        {
                            return None;
                        }
                        value.mutable = capability == Mutability::Mut;
                        values.insert(lhs.local, value);
                    }
                    StatementKind::StorageLive(local) | StatementKind::StorageDead(local)
                        if *local != 1 =>
                    {
                        values.remove(local);
                    }
                    StatementKind::Nop
                    | StatementKind::FakeRead(..)
                    | StatementKind::PlaceMention(_)
                    | StatementKind::AscribeUserType { .. }
                    | StatementKind::Coverage(_)
                    | StatementKind::ConstEvalCounter => {}
                    _ => return None,
                }
            }
            work.tick(self)?;
            match &block.terminator.kind {
                TerminatorKind::Goto { target } => bb = *target,
                TerminatorKind::Return => {
                    let value = values.remove(&0)?;
                    return ((!value.reference || value.shared_slice)
                        && !value.projections.is_empty())
                    .then_some(value);
                }
                TerminatorKind::Call { func, args, destination, target: Some(target), .. } => {
                    let element = self.native_shared_slice_from_ref(body, func)?;
                    let [source] = args.as_slice() else { return None };
                    let mut value = values.get(&plain_local(source)?)?.clone();
                    if value.shared_slice
                        || !value.reference
                        || value.mutable
                        || !destination.projection.is_empty()
                        || destination.local == 1
                        || !same_ty_modulo_regions(self.resolve_body_ty(value.pointee), element)
                        || self
                            .shared_storage_slice_element(body.locals().get(destination.local)?.ty)
                            != Some(element)
                    {
                        return None;
                    }
                    value.shared_slice = true;
                    values.insert(destination.local, value);
                    bb = *target;
                }
                _ => return None,
            }
        }
    }

    fn plan_inline_storage_address(
        &mut self,
        body: &Body,
        args: &[Operand],
    ) -> Option<StorageAddress> {
        if !self.inline_storage_has_host_scope()
            || self.track_level < crate::args::ChcTrackLevel::Mem
            || crate::kani_middle::transform::unit_has_stubs()
        {
            return None;
        }
        let [arg] = args else { return None };
        if body.arg_locals().len() != 1 {
            return None;
        }
        let TyKind::RigidTy(RigidTy::Ref(_, root, capability)) =
            self.resolve_body_ty(body.locals().get(1)?.ty).kind()
        else {
            return None;
        };
        let root = self.resolve_body_ty(root);
        if !matches!(root.kind(), TyKind::RigidTy(RigidTy::Adt(..) | RigidTy::Tuple(_))) {
            return None;
        }
        let mut work = Work(MAX_WORK);
        self.storage_address_shape(root, MAX_DEPTH, &mut work)?;
        let value =
            self.storage_address_body_path(body, root, capability == Mutability::Mut, &mut work)?;
        let TyKind::RigidTy(RigidTy::RawPtr(returned, returned_capability)) =
            self.resolve_body_ty(body.locals().get(0)?.ty).kind()
        else {
            return None;
        };
        if !same_ty_modulo_regions(
            self.resolve_body_ty(returned),
            self.resolve_body_ty(value.pointee),
        ) || (returned_capability == Mutability::Mut && !value.mutable)
        {
            return None;
        }
        let owner =
            self.storage_address_host_owner(arg, root, capability == Mutability::Mut, &mut work)?;
        self.bind_inline_storage_path(root, owner, value, &mut work)
    }

    fn bind_inline_storage_path(
        &mut self,
        root: Ty,
        owner: usize,
        value: StoragePath,
        work: &mut Work,
    ) -> Option<StorageAddress> {
        let root_layout = root.layout().ok()?.shape();
        if !root_layout.is_sized() {
            return None;
        }
        let root_size = u32::try_from(root_layout.size.bytes()).ok()?;
        let mut ty = root;
        let mut offset = 0u64;
        for projection in &value.projections {
            work.tick(self)?;
            let ProjectionElem::Field(index, field) = projection else { return None };
            offset = offset.checked_add(self.get_field_offset(ty, *index)?)?;
            ty = self.resolve_body_ty(*field);
        }
        let size = u32::try_from(ty.layout().ok()?.shape().size.bytes()).ok()?;
        let offset = u32::try_from(offset).ok()?;
        if size == 0 || offset.checked_add(size)? > root_size {
            return None;
        }
        // This known producer is the caller's storage address. Neither the
        // referent term nor its equality/width supplies any address evidence.
        let base = self.get_or_create_local_address(owner)?;
        let (object, zero) = Self::try_extract_constant_addr(&base)?;
        if zero != 0 || self.heap_state.local_idx_for_obj_id(object) != Some(owner) {
            return None;
        }
        let address = Loc::of_address(
            Expr::bitvec_const(object as u128, 32).concat(Expr::bitvec_const(offset as u128, 32)),
        );
        Some(StorageAddress {
            address,
            target: RefTarget::with_projections(owner, value.projections),
            offset,
            object,
        })
    }

    pub(in crate::codegen_ay::chc) fn try_inline_storage_address(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        body: &Body,
        instance: Instance,
    ) -> bool {
        if !self.inline_storage_has_host_scope()
            || crate::kani_middle::transform::instance_has_unit_stub(&instance)
            || matches!(instance.kind, rustc_public::mir::mono::InstanceKind::Virtual { .. })
            || !dcx.destination.projection.is_empty()
        {
            return false;
        }
        if self.shared_storage_slice_element(body.locals()[0].ty).is_some() {
            return self.try_inline_shared_storage_slice(dcx, body, instance);
        }
        // Most callees cannot be this summary. Reject them before inspecting
        // caller custody or charging a scan of the host body.
        if dcx.args.len() != 1
            || body.arg_locals().len() != 1
            || !matches!(
                self.resolve_body_ty(body.locals()[0].ty).kind(),
                TyKind::RigidTy(RigidTy::RawPtr(..))
            )
            || !matches!(
                self.resolve_body_ty(body.locals()[1].ty).kind(),
                TyKind::RigidTy(RigidTy::Ref(..))
            )
        {
            return false;
        }
        let Some(target) = *dcx.target else { return false };
        let dest = dcx.destination.local;
        // The caller supplied this exact walker-selected transformed body.
        // Observe it only on explicit debug logging, before any plan decision;
        // a raw/source-derived body is not evidence of the production route.
        if tracing::enabled!(target: "trust_mc_chc_storage_address", tracing::Level::DEBUG) {
            let mut out = Vec::new();
            let _ = body.dump(&mut out, &format!("{instance:?}"));
            tracing::debug!(
                target: "trust_mc_chc_storage_address",
                ?instance, caller = %self.fn_name, arguments = ?dcx.args, destination = ?dcx.destination,
                mir = %String::from_utf8_lossy(&out),
                "Actual transformed storage-address candidate"
            );
        }
        let mut work = Work(MAX_WORK);
        if self.storage_address_result_custody(dest, &mut work).is_none() {
            tracing::debug!(target: "trust_mc_chc_storage_address", ?instance, caller = %self.fn_name, "Storage-address result custody refused");
            return false;
        }
        let Some(plan) = self.plan_inline_storage_address(body, dcx.args) else {
            tracing::debug!(target: "trust_mc_chc_storage_address", ?instance, caller = %self.fn_name, "Storage-address typed live-owner plan refused");
            return false;
        };
        tracing::debug!(target: "trust_mc_chc_storage_address", ?instance, caller = %self.fn_name, owner = ?plan.target, object = plan.object, offset = plan.offset, "Storage-address typed live-owner plan accepted");
        if !same_ty_modulo_regions(
            self.resolve_body_ty(self.body.locals()[dest].ty),
            self.resolve_body_ty(body.locals()[0].ty),
        ) || self.try_state_idx_for_local(dest).is_none()
        {
            return false;
        }
        let address = plan.address.into_expr();
        self.call_replays_body = true;
        let handled = self.emit_translated_inline_call_result(
            dcx,
            target,
            address.clone(),
            None,
            BTreeMap::new(),
            Vec::new(),
            &BTreeMap::new(),
            &HashMap::new(),
            None,
            "inline_storage_address_result",
            "inline_storage_address_alias",
        );
        if handled {
            self.clear_path_insensitive_ref_metadata(dest);
            self.ref_resolution.ref_targets.insert(dest, plan.target);
            self.ref_resolution.call_forwarded_raw_ptrs.insert(dest);
            self.known_alloc_ids.remove(&dest);
            if plan.offset == 0 {
                self.known_alloc_ids.insert(dest, plan.object);
            }
            if self.record_known_stack_addr_expr(dest, address, "inline_storage_address") {
                self.ref_resolution.inline_stack_address_calls.insert(dcx.bb_idx);
            }
        }
        handled
    }

    // Only change store routing when an independently recorded full address
    // agrees with the exact typed target path. The known allocation-id table
    // alone cannot prove a nonzero offset.
    pub(in crate::codegen_ay::chc) fn exact_raw_field_stack_address(
        &mut self,
        local: usize,
        target: &RefTarget,
    ) -> bool {
        if !self.inline_storage_has_host_scope() {
            return false;
        }
        let Some(result) = (|| {
            let TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) =
                self.resolve_body_ty(self.body.locals().get(local)?.ty).kind()
            else {
                return None;
            };
            if target.projections.is_empty() || target.projections.len() > MAX_DEPTH {
                return None;
            }
            let address = self.known_stack_addr_expr(local)?;
            let (object, actual_offset) = Self::try_extract_constant_addr(&address)?;
            if self.heap_state.local_idx_for_obj_id(object) != Some(target.local) {
                return None;
            }
            let mut ty = self.resolve_body_ty(self.body.locals().get(target.local)?.ty);
            let mut expected_offset = 0u64;
            for projection in &target.projections {
                let ProjectionElem::Field(index, field) = projection else { return None };
                expected_offset =
                    expected_offset.checked_add(self.get_field_offset(ty, *index)?)?;
                ty = self.resolve_body_ty(*field);
            }
            Some(
                u64::from(actual_offset) == expected_offset
                    && same_ty_modulo_regions(self.resolve_body_ty(pointee), ty),
            )
        })() else {
            return false;
        };
        result
    }

    #[cfg(test)]
    pub(in crate::codegen_ay::chc) fn inline_storage_address_for_test(
        &mut self,
        body: &Body,
        args: &[Operand],
    ) -> Option<(Loc, RefTarget)> {
        self.plan_inline_storage_address(body, args).map(|plan| (plan.address, plan.target))
    }

    #[cfg(test)]
    pub(in crate::codegen_ay::chc) fn inline_storage_result_custody_for_test(
        &mut self,
        local: usize,
    ) -> bool {
        self.storage_address_result_custody(local, &mut Work(MAX_WORK)).is_some()
    }
}
