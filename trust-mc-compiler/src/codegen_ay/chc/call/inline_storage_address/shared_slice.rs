// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! A shared one-element view of existing, typed caller storage. The native
//! safe helper lends the same allocation; it creates neither bytes nor owner.

use super::*;
use crate::codegen_ay::provenance::Val;
use crate::codegen_ay::ptr_repr::{PtrRepr, PtrSlot};
use crate::codegen_ay::types::POINTER_WIDTH;
use rustc_public::mir::visit::{Location, PlaceContext, statement_location, terminator_location};
use rustc_public::mir::{MirVisitor, UnOp};
use rustc_public::{CrateDef, rustc_internal};

fn scalar(ty: Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(
            RigidTy::Bool | RigidTy::Char | RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_)
        )
    )
}

struct Uses<'a, 'tcx, 'body> {
    ctx: &'a mut ChcCtx<'tcx, 'body>,
    work: &'a mut Work,
    local: usize,
    found: bool,
    failed: bool,
}
impl MirVisitor for Uses<'_, '_, '_> {
    fn visit_place(&mut self, place: &Place, _: PlaceContext, _: Location) {
        if self.failed {
            return;
        }
        for _ in 0..=place.projection.len() {
            if self.work.tick(self.ctx).is_none() {
                self.failed = true;
                return;
            }
        }
        self.found |= place.local == self.local;
    }
    fn visit_operand(&mut self, operand: &Operand, location: Location) {
        if self.failed || self.work.tick(self.ctx).is_none() {
            self.failed = true;
            return;
        }
        self.super_operand(operand, location);
    }
    fn visit_rvalue(&mut self, value: &Rvalue, location: Location) {
        if self.failed || self.work.tick(self.ctx).is_none() {
            self.failed = true;
            return;
        }
        if matches!(value, Rvalue::Aggregate(_, operands) if operands.len() > self.work.0) {
            self.failed = true;
            return;
        }
        self.super_rvalue(value, location);
    }
}

impl ChcCtx<'_, '_> {
    pub(super) fn shared_storage_slice_element(&self, ty: Ty) -> Option<Ty> {
        let TyKind::RigidTy(RigidTy::Ref(_, slice, Mutability::Not)) =
            self.resolve_body_ty(ty).kind()
        else {
            return None;
        };
        let TyKind::RigidTy(RigidTy::Slice(element)) = self.resolve_body_ty(slice).kind() else {
            return None;
        };
        let element = self.resolve_body_ty(element);
        scalar(element).then_some(element)
    }

    pub(super) fn native_shared_slice_from_ref(&self, body: &Body, func: &Operand) -> Option<Ty> {
        let TyKind::RigidTy(RigidTy::FnDef(original, args)) = func.ty(body.locals()).ok()?.kind()
        else {
            return None;
        };
        let instance = Instance::resolve(original, &args).ok()?;
        let id = rustc_internal::internal(self.tcx, instance.def.def_id());
        if matches!(instance.kind, rustc_public::mir::mono::InstanceKind::Virtual { .. })
            || crate::kani_middle::transform::instance_has_unit_stub(&instance)
            || rustc_internal::internal(self.tcx, original.def_id()) != id
            || !crate::kani_middle::std_abstraction::is_sysroot_core_definition_at(
                self.tcx,
                id,
                &["slice", "raw", "from_ref"],
            )
        {
            return None;
        }
        let signature = instance.ty().kind().fn_sig()?.skip_binder();
        let [input] = signature.inputs() else {
            return None;
        };
        let TyKind::RigidTy(RigidTy::Ref(_, element, Mutability::Not)) =
            self.resolve_body_ty(*input).kind()
        else {
            return None;
        };
        let element = self.resolve_body_ty(element);
        (scalar(element) && self.shared_storage_slice_element(signature.output()) == Some(element))
            .then_some(element)
    }

    fn shared_slice_result_custody(
        &mut self,
        first: usize,
        element: Ty,
        work: &mut Work,
    ) -> Option<()> {
        let mut seen = HashSet::new();
        let mut pending = vec![first];
        while let Some(local) = pending.pop() {
            work.tick(self)?;
            if seen.contains(&local) {
                continue;
            }
            if local == 0
                || seen.len() >= MAX_REF_CHAIN
                || self.shared_storage_slice_element(self.body.locals().get(local)?.ty)
                    != Some(element)
            {
                return None;
            }
            seen.insert(local);
            let definition = self.storage_address_definition(local, work)?;
            if local == first && !matches!(definition, Definition::Call) {
                return None;
            }
            let body = self.body;
            for (bb, block) in body.blocks.iter().enumerate() {
                work.tick(self)?;
                for (index, statement) in block.statements.iter().enumerate() {
                    work.tick(self)?;
                    let StatementKind::Assign(lhs, rhs) = &statement.kind else {
                        let mut uses = Uses {
                            ctx: &mut *self,
                            work: &mut *work,
                            local,
                            found: false,
                            failed: false,
                        };
                        uses.visit_statement(statement, statement_location(body, &bb, index));
                        if uses.failed || uses.found {
                            return None;
                        }
                        continue;
                    };
                    if lhs.local == local && !lhs.projection.is_empty() {
                        return None;
                    }
                    let operand = match rhs {
                        Rvalue::Use(source, ..) => Some(source),
                        _ => None,
                    };
                    if let Some(source) = operand {
                        if plain_local(source) == Some(local) {
                            if !lhs.projection.is_empty()
                                || self.shared_storage_slice_element(lhs.ty(body.locals()).ok()?)
                                    != Some(element)
                            {
                                return None;
                            }
                            pending.push(lhs.local);
                            continue;
                        }
                        if let Operand::Copy(place) | Operand::Move(place) = source
                            && place.local == local
                            && matches!(
                                place.projection.as_slice(),
                                [
                                    ProjectionElem::Deref,
                                    ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }
                                ]
                            )
                            && same_ty_modulo_regions(
                                self.resolve_body_ty(place.ty(body.locals()).ok()?),
                                element,
                            )
                        {
                            continue;
                        }
                    }
                    if let Rvalue::Ref(_, BorrowKind::Shared, place) = rhs
                        && place.local == local
                        && place.projection.as_slice() == [ProjectionElem::Deref]
                    {
                        if !lhs.projection.is_empty()
                            || self.shared_storage_slice_element(lhs.ty(body.locals()).ok()?)
                                != Some(element)
                        {
                            return None;
                        }
                        pending.push(lhs.local);
                        continue;
                    }
                    if let Rvalue::UnaryOp(UnOp::PtrMetadata, source) = rhs
                        && plain_local(source) == Some(local)
                    {
                        continue;
                    }
                    let mut uses = Uses {
                        ctx: &mut *self,
                        work: &mut *work,
                        local,
                        found: false,
                        failed: false,
                    };
                    uses.visit_rvalue(rhs, statement_location(body, &bb, index));
                    if uses.failed || uses.found {
                        return None;
                    }
                }
                let operands = match &block.terminator.kind {
                    TerminatorKind::Call { args, .. } => args.as_slice(),
                    _ => &[],
                };
                for operand in operands {
                    work.tick(self)?;
                    if matches!(operand, Operand::Copy(place) | Operand::Move(place) if place.local == local)
                    {
                        return None;
                    }
                }
                if matches!(&block.terminator.kind, TerminatorKind::Drop {place,..} if place.local == local)
                {
                    return None;
                }
                match &block.terminator.kind {
                    TerminatorKind::Call { .. }
                    | TerminatorKind::Drop { .. }
                    | TerminatorKind::Goto { .. }
                    | TerminatorKind::Return
                    | TerminatorKind::Unreachable
                    | TerminatorKind::Abort => {}
                    TerminatorKind::Assert { .. } | TerminatorKind::SwitchInt { .. } => {
                        let mut uses = Uses {
                            ctx: &mut *self,
                            work: &mut *work,
                            local,
                            found: false,
                            failed: false,
                        };
                        uses.visit_terminator(&block.terminator, terminator_location(body, &bb));
                        if uses.failed || uses.found {
                            return None;
                        }
                    }
                    _ => return None,
                }
            }
        }
        Some(())
    }

    pub(super) fn try_inline_shared_storage_slice(
        &mut self,
        dcx: &DispatchCallContext<'_>,
        body: &Body,
        instance: Instance,
    ) -> bool {
        let Some(target) = *dcx.target else {
            return false;
        };
        if !self.inline_storage_has_host_scope()
            || self.track_level < crate::args::ChcTrackLevel::Mem
            || crate::kani_middle::transform::unit_has_stubs()
            || dcx.args.len() != 1
            || body.arg_locals().len() != 1
        {
            return false;
        }
        let Some(element) = self.shared_storage_slice_element(body.locals()[0].ty) else {
            return false;
        };
        let TyKind::RigidTy(RigidTy::Ref(_, root, Mutability::Not)) =
            self.resolve_body_ty(body.locals()[1].ty).kind()
        else {
            return false;
        };
        let root = self.resolve_body_ty(root);
        if !matches!(root.kind(), TyKind::RigidTy(RigidTy::Adt(..) | RigidTy::Tuple(_))) {
            return false;
        }
        let mut work = Work(MAX_WORK);
        if self.storage_address_shape(root, MAX_DEPTH, &mut work).is_none() {
            return false;
        }
        // Ordinary functions without this exact native operation retain their
        // existing dispatcher. No foreign spelling grants a one-element view.
        let mut native = false;
        for block in &body.blocks {
            if work.tick(self).is_none() {
                return false;
            }
            if let TerminatorKind::Call { func, .. } = &block.terminator.kind {
                native |= self.native_shared_slice_from_ref(body, func).is_some();
            }
        }
        if !native {
            return false;
        }
        if tracing::enabled!(target: "trust_mc_chc_storage_address", tracing::Level::DEBUG) {
            let mut dump = Vec::new();
            let _ = body.dump(&mut dump, &format!("{instance:?}"));
            tracing::debug!(target: "trust_mc_chc_storage_address", ?instance, caller = %self.fn_name, arguments = ?dcx.args, destination = ?dcx.destination, mir = %String::from_utf8_lossy(&dump), "Actual transformed shared one-element storage-view candidate");
        }
        let dest = dcx.destination.local;
        let plan = (|| {
            if self.shared_storage_slice_element(self.body.locals().get(dest)?.ty) != Some(element)
                || self.try_state_idx_for_local(dest).is_none()
                || PtrSlot::of_sort(&Self::translate_ty(self.body.locals()[dest].ty)?)
                    != Some(PtrSlot::Fat)
            {
                return None;
            }
            self.shared_slice_result_custody(dest, element, &mut work)?;
            let value = self.storage_address_body_path(body, root, false, &mut work)?;
            if !value.shared_slice
                || !value.reference
                || value.mutable
                || !same_ty_modulo_regions(self.resolve_body_ty(value.pointee), element)
            {
                return None;
            }
            let owner = self.storage_address_host_owner(&dcx.args[0], root, false, &mut work)?;
            self.bind_inline_storage_path(root, owner, value, &mut work)
        })();
        let Some(plan) = plan else {
            self.clear_path_insensitive_ref_metadata(dest);
            self.known_alloc_ids.remove(&dest);
            self.known_stack_addr_exprs.remove(&dest);
            self.record_sound_fallback_reason("inline_shared_slice_storage_unqualified");
            return false;
        };
        tracing::debug!(target: "trust_mc_chc_storage_address", ?instance, owner = ?plan.target, object = plan.object, offset = plan.offset, "Shared one-element storage-view plan accepted");
        let address = plan.address.as_expr().clone();
        let length = Expr::bitvec_const(1u64, POINTER_WIDTH);
        // This forms a real shared reference even when the caller only asks
        // its length. Reuse the ordinary access and enabled scalar-init
        // formation checks; the view never manufactures validity or init bits.
        let checks = self.heap_access_checks(address.clone(), element);
        if !checks.is_empty() {
            self.mark_heap_metadata_read();
        }
        self.heap_state.pending_checks.extend(checks);
        self.emit_slice_from_raw_parts_uninit_check(dcx, &address, &length);
        let value = PtrRepr::from_declared_roles(plan.address, Val::of_value(length.clone()))
            .into_packed()
            .expect("declared shared slice roles pack");
        self.call_replays_body = true;
        let handled = self.emit_translated_inline_call_result(
            dcx,
            target,
            value,
            None,
            BTreeMap::new(),
            Vec::new(),
            &BTreeMap::new(),
            &HashMap::new(),
            None,
            "inline_shared_slice_storage_result",
            "inline_shared_slice_storage_alias",
        );
        if handled {
            self.clear_path_insensitive_ref_metadata(dest);
            // The slice points to scalar storage. Do not install an array-valued
            // ref_target or snapshot backing that bypasses current typed memory.
            self.ref_resolution.subslice_len.insert(dest, length);
            self.ref_resolution
                .subslice_offset
                .insert(dest, Expr::bitvec_const(0u64, POINTER_WIDTH));
            self.known_alloc_ids.remove(&dest);
            if plan.offset == 0 {
                self.known_alloc_ids.insert(dest, plan.object);
            }
            self.record_known_stack_addr_expr(dest, address, "inline_shared_slice_storage");
        }
        handled
    }
}
