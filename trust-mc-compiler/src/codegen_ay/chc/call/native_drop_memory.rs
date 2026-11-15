// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Event-time typed memory for a checked, consumed native Box payload.
//!
//! The existing heap store chains ARE memory SSA. Read their expression now,
//! rather than an eager field snapshot or a mutable final-output name. Positive
//! frame-local address certificates supply native field provenance; neither
//! F2's may-be-address bit nor equal numeric pointer bits supply a certificate.

use super::{ChcCtx, native_dyn_origin::NativeDynOrigin};
use crate::codegen_ay::chc::codegen_types::CodegenTypes;
use crate::codegen_ay::{provenance::Loc, shared::mono_ty};
use crate::kani_middle::abi::LayoutOf;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::{Body, LocalDecl, Operand, Place, ProjectionElem, Rvalue, StatementKind};
use rustc_public::ty::{AdtKind, RigidTy, Ty, TyKind};
use std::{
    cell::Cell,
    collections::{HashMap, HashSet},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) struct NativeDropAddress {
    allocation: u32,
    offset: u32,
    pointee: Ty,
    extent: u64,
    alignment: u64,
    static_image: bool,
    writable: bool,
}

pub(in crate::codegen_ay::chc) struct NativeDropMemory {
    allocation: u32,
    budget: Cell<usize>,
    entry_chains: HashMap<usize, Expr>,
    pub(super) exact: Cell<bool>,
    store_authorized: Cell<bool>,
}

pub(super) fn carrier_exposed(body: &Body, local: usize) -> bool {
    let mut budget = 16_384usize;
    body.blocks.iter().flat_map(|block| &block.statements).any(|statement| {
        let Some(left)=budget.checked_sub(1) else{return true;};budget=left;
        matches!(&statement.kind, StatementKind::Assign(_,Rvalue::Ref(_,_,place)|Rvalue::AddressOf(_,place)) if place.local==local && !matches!(place.projection.first(),Some(ProjectionElem::Deref)))
    })
}

fn pointer_inner(ty: Ty) -> Option<Ty> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => Some(inner),
        _ => None,
    }
}
fn writable_pointer(ty: Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(
            RigidTy::Ref(_, _, rustc_public::mir::Mutability::Mut)
                | RigidTy::RawPtr(_, rustc_public::mir::Mutability::Mut)
        )
    )
}
fn plain(operand: &Operand) -> Option<&Place> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => Some(place),
        _ => None,
    }
}
fn scalar(ty: Ty) -> bool {
    matches!(
        ty.kind(),
        TyKind::RigidTy(
            RigidTy::Bool | RigidTy::Char | RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_)
        )
    )
}
pub(in crate::codegen_ay::chc) fn has_output_or_binder(expr: &Expr) -> bool {
    let mut pending = vec![expr];
    let mut seen = HashSet::new();
    let mut work = 16_384usize;
    while let Some(part) = pending.pop() {
        let Some(left) = work.checked_sub(1) else {
            return true;
        };
        work = left;
        if !seen.insert(std::ptr::from_ref(part.value()) as usize) {
            continue;
        }
        if matches!(part.value(),ExprValue::Var{name} if name.ends_with("__out"))
            || matches!(part.value(), ExprValue::Forall { .. } | ExprValue::Exists { .. })
        {
            return true;
        }
        pending.extend(part.children());
    }
    false
}
impl ChcCtx<'_, '_> {
    pub(in crate::codegen_ay::chc) fn with_native_drop_memory<T>(
        &mut self,
        origin: &NativeDynOrigin,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        // Reg/Loc tracks do not carry this lane's physical typed memory.
        // Keep their existing read/write refusal accounting unchanged.
        if self.track_level != crate::args::ChcTrackLevel::Mem {
            return f(self);
        }
        let saved = self.native_drop_memory.take();
        let seeds = self.inline_walk_param_native_drop_seeds.take();
        let entry_chains = self
            .heap_state
            .store_chains
            .values()
            .map(|(_, expr)| (std::ptr::from_ref(expr.value()) as usize, expr.clone()))
            .chain(
                self.heap_state
                    .drained_store_chain_seeds
                    .values()
                    .map(|expr| (std::ptr::from_ref(expr.value()) as usize, expr.clone())),
            )
            .take(16_385)
            .collect::<HashMap<_, _>>();
        let bounded = entry_chains.len() <= 16_384;
        if !bounded {
            self.record_sound_fallback_reason("native_drop_memory_work_exhausted");
        }
        self.native_drop_memory = Some(NativeDropMemory {
            allocation: origin.allocation,
            budget: Cell::new(if bounded { 16_384 } else { 0 }),
            entry_chains,
            exact: Cell::new(bounded),
            store_authorized: Cell::new(false),
        });
        self.inline_walk_param_native_drop_seeds = Some(vec![(
            1,
            NativeDropAddress {
                allocation: origin.allocation,
                offset: 0,
                pointee: origin.concrete,
                extent: self
                    .get_type_size(origin.concrete)
                    .and_then(|n| u64::try_from(n).ok())
                    .unwrap_or(0),
                alignment: self.get_type_align(origin.concrete).unwrap_or(0),
                static_image: false,
                writable: true,
            },
        )]);
        let result = f(self);
        self.native_drop_memory = saved;
        self.inline_walk_param_native_drop_seeds = seeds;
        result
    }
    fn spend_native_drop_work(&self) -> Option<()> {
        let scope = self.native_drop_memory.as_ref()?;
        let Some(left) = scope.budget.get().checked_sub(1) else {
            self.refuse_native_drop_memory("native_drop_memory_work_exhausted");
            return None;
        };
        scope.budget.set(left);
        Some(())
    }
    pub(in crate::codegen_ay::chc) fn native_drop_address_matches(
        &self,
        address: &NativeDropAddress,
        ty: Option<Ty>,
    ) -> bool {
        self.native_drop_memory
            .as_ref()
            .is_some_and(|scope| scope.allocation == address.allocation || address.static_image)
            && ty.map(|ty| self.resolve_body_ty(ty)).and_then(pointer_inner)
                == Some(address.pointee)
    }
    pub(in crate::codegen_ay::chc) fn inline_native_drop_address(
        &self,
        operand: &Operand,
        locals: &[LocalDecl],
    ) -> Option<NativeDropAddress> {
        self.spend_native_drop_work()?;
        let local = plain(operand)?.local;
        let mut address =
            self.inline_walk_frames.last()?.native_drop_addresses.get(&local)?.clone()?;
        address.writable &= writable_pointer(self.resolve_body_ty(locals.get(local)?.ty));
        self.native_drop_address_matches(&address, locals.get(local).map(|decl| decl.ty))
            .then_some(address)
    }
    fn project_native_drop_address(
        &self,
        place: &Place,
        locals: &[LocalDecl],
    ) -> Option<NativeDropAddress> {
        self.spend_native_drop_work()?;
        if place.projection.len() > 32
            || !matches!(place.projection.first(), Some(ProjectionElem::Deref))
        {
            return None;
        }
        let mut address = self.inline_native_drop_address(
            &Operand::Copy(Place { local: place.local, projection: vec![] }),
            locals,
        )?;
        for projection in &place.projection[1..] {
            self.spend_native_drop_work()?;
            let ProjectionElem::Field(index, mir_ty) = projection else {
                return None;
            };
            let field = match address.pointee.kind() {
                TyKind::RigidTy(RigidTy::Adt(def, args)) if def.kind() == AdtKind::Struct => {
                    mono_ty::field_ty(def.variants().first()?.fields().get(*index)?, &args)?
                }
                TyKind::RigidTy(RigidTy::Tuple(fields)) => *fields.get(*index)?,
                _ => return None,
            };
            if field != self.resolve_body_ty(*mir_ty) {
                return None;
            }
            address.offset = address.offset.checked_add(
                u32::try_from(LayoutOf::new(address.pointee).field_offset(*index)?).ok()?,
            )?;
            address.pointee = field;
        }
        let size = u64::try_from(self.get_type_size(address.pointee)?).ok()?;
        let align = self.get_type_align(address.pointee)?;
        (size > 0
            && align.is_power_of_two()
            // Object-ID/offset bits do not establish allocation alignment.
            // Retain the actual typed birth's minimum native alignment too.
            && address.alignment.is_power_of_two()
            && address.alignment >= align
            && u64::from(address.offset) % align == 0
            && u64::from(address.offset).checked_add(size)? <= address.extent)
            .then_some(address)
    }
    pub(in crate::codegen_ay::chc) fn forget_native_drop_address(&mut self, local: usize) {
        if self.native_drop_memory.is_none() {
            return;
        }
        if let Some(frame) = self.inline_walk_frames.last_mut() {
            // An unknown call result on one arm must dominate a later known
            // assignment on another arm, including previously unseen locals.
            frame.native_drop_addresses.insert(local, None);
        }
    }
    pub(in crate::codegen_ay::chc) fn note_native_drop_assignment(
        &mut self,
        body: &Body,
        local: usize,
        rhs: Option<&Rvalue>,
    ) {
        if self.native_drop_memory.is_none() {
            return;
        }
        let address = (|| {
            if carrier_exposed(body, local) {
                return None;
            }
            let rhs = rhs?;
            let address = match rhs {
                Rvalue::Use(operand, ..) => self
                    .inline_native_drop_address(operand, body.locals())
                    .or_else(|| self.native_drop_static_constant(operand, body.locals())),
                Rvalue::CopyForDeref(place) if place.projection.is_empty() => {
                    self.inline_native_drop_address(&Operand::Copy(place.clone()), body.locals())
                }
                Rvalue::Ref(_, kind, place) => {
                    self.project_native_drop_address(place, body.locals()).map(|mut address| {
                        address.writable &=
                            matches!(kind, rustc_public::mir::BorrowKind::Mut { .. });
                        address
                    })
                }
                Rvalue::AddressOf(kind, place) => {
                    self.project_native_drop_address(place, body.locals()).map(|mut address| {
                        address.writable &= matches!(kind, rustc_public::mir::RawPtrKind::Mut);
                        address
                    })
                }
                Rvalue::Cast(rustc_public::mir::CastKind::PtrToPtr, operand, _) => {
                    self.inline_native_drop_address(operand, body.locals())
                }
                _ => None,
            }?;
            self.native_drop_address_matches(&address, body.locals().get(local).map(|decl| decl.ty))
                .then_some(address)
        })();
        if let Some(frame) = self.inline_walk_frames.last_mut() {
            let previous =
                frame.native_drop_addresses.entry(local).or_insert_with(|| address.clone());
            if *previous != address {
                *previous = None;
            }
        }
    }
    fn native_drop_cell(
        &self,
        values: &HashMap<usize, Expr>,
        place: &Place,
        locals: &[LocalDecl],
    ) -> Option<(Expr, Ty, bool, bool)> {
        let address = self.project_native_drop_address(place, locals)?;
        if !scalar(address.pointee) {
            return None;
        }
        let source = self.inline_native_drop_address(
            &Operand::Copy(Place { local: place.local, projection: vec![] }),
            locals,
        )?;
        let value = values.get(&place.local)?;
        if !super::super::expr::codegen_expr_box_deref::legacy_pointer_tree_is_bounded(value)
            || Self::try_extract_constant_addr(value) != Some((source.allocation, source.offset))
        {
            return None;
        }
        Some((
            Expr::bitvec_const(address.allocation, 32)
                .concat(Expr::bitvec_const(address.offset, 32)),
            address.pointee,
            address.static_image,
            address.writable,
        ))
    }
    pub(in crate::codegen_ay::chc) fn read_native_drop_place(
        &mut self,
        values: &HashMap<usize, Expr>,
        place: &Place,
        locals: &[LocalDecl],
    ) -> Option<Expr> {
        let (address, ty, _, _) = self.native_drop_cell(values, place, locals)?;
        if !self.native_drop_store_order_is_known() {
            self.refuse_native_drop_memory("native_drop_memory_alias_or_order_unmodeled");
            return None;
        }
        let checks = self.heap_access_checks(address.clone(), ty);
        self.heap_state.pending_checks.extend(checks);
        self.mark_heap_metadata_read();
        let key = self.type_key_for_body_ty(ty);
        let sort = Self::translate_ty(ty)?;
        if self.elem_sort_for_memory_array(ty) != sort {
            return None;
        }
        // Flat typed memory keeps each store in order; its immutable RHS freezes
        // this read. Region shortcuts and untyped forwarding are not witnesses.
        let value = self.load_from_type_array(address, &key, sort.clone(), Some(&sort))?;
        if has_output_or_binder(&value) {
            self.refuse_native_drop_memory("native_drop_memory_snapshot_unavailable");
            return None;
        }
        Some(value)
    }
    pub(in crate::codegen_ay::chc) fn store_native_drop_place(
        &mut self,
        values: &HashMap<usize, Expr>,
        place: &Place,
        locals: &[LocalDecl],
        value: &Expr,
    ) -> Option<bool> {
        if self.native_drop_memory.is_none()
            || !matches!(place.projection.first(), Some(ProjectionElem::Deref))
        {
            return None;
        }
        let Some((address, ty, static_image, writable)) =
            self.native_drop_cell(values, place, locals)
        else {
            self.refuse_native_drop_memory("native_drop_store_without_address_certificate");
            return None;
        };
        if !writable {
            self.refuse_native_drop_memory("native_drop_store_through_shared_address");
            return None;
        }
        if static_image {
            return None;
        }
        let expected = Self::translate_ty(ty)?;
        if value.sort() != &expected || has_output_or_binder(value) {
            self.refuse_native_drop_memory("native_drop_store_value_snapshot_unavailable");
            return None;
        }
        let before = self.heap_state.effect_mark();
        self.with_native_drop_store_authority(|ctx| {
            ctx.build_memory_store(Loc::of_address(address), value.clone(), ty)
        });
        if self.heap_state.effect_mark() == before {
            self.refuse_native_drop_memory("native_drop_store_effect_unmodeled");
        }
        Some(true)
    }

    /// The generic heap may also be written by other call/statement routes.
    /// A fresh array/havoc, unknown alias, ITE merge or an unregistered base
    /// cannot inherit this scalar walk's event-time authority. Check every
    /// changed chain, including other keys, before serving a payload read.
    fn native_drop_store_order_is_known(&self) -> bool {
        let result = (|| {
            let scope = self.native_drop_memory.as_ref()?;
            let mut seen = HashSet::new();
            let mut pending = self
                .heap_state
                .store_chains
                .values()
                .map(|(_, expr)| expr)
                .chain(self.heap_state.drained_store_chain_seeds.values())
                .take(16_385)
                .collect::<Vec<_>>();
            if pending.len() > 16_384 {
                return None;
            }
            while let Some(expr) = pending.pop() {
                self.spend_native_drop_work()?;
                let id = std::ptr::from_ref(expr.value()) as usize;
                if !seen.insert(id) || scope.entry_chains.contains_key(&id) {
                    continue;
                }
                match expr.value() {
                    ExprValue::Store { array, index, .. } => {
                        if !super::super::expr::codegen_expr_box_deref::legacy_pointer_tree_is_bounded(index)
                            || Self::try_extract_constant_addr(index).is_none(){return None;}
                        pending.push(array);
                    }
                    ExprValue::Var { name }
                        if self
                            .state_var_mgr
                            .state_vars
                            .iter()
                            .any(|(input, sort)| input.as_ref() == name && sort.is_array()) => {}
                    _ => return None,
                }
            }
            Some(())
        })();
        result.is_some()
    }
    fn native_drop_static_constant(
        &self,
        operand: &Operand,
        locals: &[LocalDecl],
    ) -> Option<NativeDropAddress> {
        use crate::codegen_ay::shared::const_pointer::{const_bytes, const_ref};
        let Operand::Constant(constant) = operand else {
            return None;
        };
        let pointee = pointer_inner(self.resolve_body_ty(operand.ty(locals).ok()?))?;
        let bytes = const_bytes(&constant.const_)?;
        let reference = const_ref(&bytes, 0, pointee)?;
        let key = reference.ptr.key()?;
        key.static_def()?;
        let object = self.global_object(&key)?;
        let index = *self.ref_resolution.static_state_idx_by_obj.get(&object.obj_id)?;
        if reference.ptr.offset() != 0
            || self.ref_resolution.static_state_ty.get(&index) != Some(&pointee)
            || !self.ref_resolution.mutable_static_state_idxs.contains(&index)
        {
            return None;
        }
        Some(NativeDropAddress {
            allocation: object.obj_id,
            offset: 0,
            pointee,
            extent: object.size?,
            alignment: self.get_type_align(pointee)?,
            static_image: true,
            writable: writable_pointer(self.resolve_body_ty(operand.ty(locals).ok()?)),
        })
    }
    pub(in crate::codegen_ay::chc) fn refuse_native_drop_memory(&self, reason: &'static str) {
        if let Some(scope) = &self.native_drop_memory {
            scope.exact.set(false);
        }
        self.record_sound_fallback_reason(reason);
    }
    pub(in crate::codegen_ay::chc) fn native_drop_store_has_authority(&self) -> bool {
        self.native_drop_memory.as_ref().is_none_or(|scope| scope.store_authorized.get())
    }
    pub(in crate::codegen_ay::chc) fn native_drop_static_store(
        &self,
        values: &HashMap<usize, Expr>,
        place: &Place,
        locals: &[LocalDecl],
    ) -> bool {
        self.native_drop_cell(values, place, locals)
            .is_some_and(|(_, _, is_static, writable)| is_static && writable)
    }
    pub(in crate::codegen_ay::chc) fn with_native_drop_store_authority<T>(
        &mut self,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let old =
            self.native_drop_memory.as_ref().map(|scope| scope.store_authorized.replace(true));
        let result = f(self);
        if let (Some(scope), Some(old)) = (&self.native_drop_memory, old) {
            scope.store_authorized.set(old);
        }
        result
    }
}

#[cfg(test)]
mod tests;
