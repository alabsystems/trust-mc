// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! BMC stack custody for the backing of a shared one-element slice.

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::context::{AllocView, SharedScalarSlice};
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::{BorrowKind, Mutability, Operand, Place, ProjectionElem, Rvalue};
use rustc_public::ty::{RigidTy, Ty, TyKind};

const MAX_DEPTH: usize = 64;
const MAX_TERMS: usize = 4096;

struct GuardedPointerTerm {
    guard: Expr,
    address: Expr,
}

impl StatementCodegen<'_, '_, '_> {
    /// Follow asserted SSA definitions and exact datatype field selection.
    /// An unresolved merge gives no authority to use either backing array.
    fn slice_storage_term<'s>(
        &'s self,
        value: &'s Expr,
        depth: usize,
        remaining: &mut usize,
    ) -> Option<&'s Expr> {
        let depth = depth.checked_sub(1)?;
        *remaining = remaining.checked_sub(1)?;
        match value.value() {
            ExprValue::Var { name }
                if !self.ctx.shared_scalar_slices.contains_key(name)
                    && !self.ctx.alloc_views.contains_key(name) =>
            {
                let next = self.asserted_pointer_definition(name)?;
                self.slice_storage_term(next, depth, remaining)
            }
            ExprValue::Ite { cond, then_expr, else_expr } => {
                match self.fold_memory_reads_on_path(cond).value() {
                    ExprValue::BoolConst(true) => {
                        self.slice_storage_term(then_expr, depth, remaining)
                    }
                    ExprValue::BoolConst(false) => {
                        self.slice_storage_term(else_expr, depth, remaining)
                    }
                    _ => {
                        let yes = self.slice_storage_term(then_expr, depth, remaining)?;
                        let no = self.slice_storage_term(else_expr, depth, remaining)?;
                        (yes == no).then_some(yes)
                    }
                }
            }
            ExprValue::DatatypeSelector { expr, selector_name, .. } => {
                let value = self.slice_storage_term(expr, depth, remaining)?;
                let field = Self::slice_storage_field(value, selector_name)?;
                self.slice_storage_term(field, depth, remaining)
            }
            _ => Some(value),
        }
    }

    fn asserted_pointer_definition(&self, name: &str) -> Option<&Expr> {
        self.ssa_concrete_values.get(name).or_else(|| self.ctx.alloc_phi_defs.get(name))
    }

    /// Unlike a backing array read, a thin raw access needs an owner for
    /// each arm. Keep guards paired with their addresses through field
    /// selection, so two different roots never stand in for one another.
    fn guarded_pointer_terms(
        &self,
        value: &Expr,
        guard: Expr,
        depth: usize,
        remaining: &mut usize,
    ) -> Option<Vec<GuardedPointerTerm>> {
        let depth = depth.checked_sub(1)?;
        *remaining = remaining.checked_sub(1)?;
        match value.value() {
            ExprValue::Var { name } if !self.ctx.alloc_views.contains_key(name) => {
                let Some(definition) = self.asserted_pointer_definition(name) else {
                    tracing::debug!(%name, ?guard, "singleton raw pointer has no asserted definition");
                    return None;
                };
                self.guarded_pointer_terms(definition, guard, depth, remaining)
            }
            ExprValue::Ite { cond, then_expr, else_expr } => {
                match self.fold_pointer_branch(cond, &guard).value() {
                    ExprValue::BoolConst(true) => {
                        self.guarded_pointer_terms(then_expr, guard, depth, remaining)
                    }
                    ExprValue::BoolConst(false) => {
                        self.guarded_pointer_terms(else_expr, guard, depth, remaining)
                    }
                    _ => {
                        let mut terms = self.guarded_pointer_terms(
                            then_expr,
                            guard.clone().and(cond.clone()),
                            depth,
                            remaining,
                        )?;
                        terms.extend(self.guarded_pointer_terms(
                            else_expr,
                            guard.and(cond.clone().not()),
                            depth,
                            remaining,
                        )?);
                        Some(terms)
                    }
                }
            }
            ExprValue::BvAdd(pointer, offset) | ExprValue::BvSub(pointer, offset) => {
                let offset = self.fold_pointer_branch(offset, &guard);
                if !matches!(offset.value(), ExprValue::BitVecConst { width: POINTER_WIDTH, .. }) {
                    return Some(vec![GuardedPointerTerm { guard, address: value.clone() }]);
                }
                // First qualify the original pointer through its asserted
                // branch and field definitions. Apply the same bitvector
                // displacement to each resulting address.
                let add = matches!(value.value(), ExprValue::BvAdd(..));
                let mut terms = self.guarded_pointer_terms(pointer, guard, depth, remaining)?;
                for term in &mut terms {
                    term.address = if add {
                        term.address.clone().bvadd(offset.clone())
                    } else {
                        term.address.clone().bvsub(offset.clone())
                    };
                }
                Some(terms)
            }
            ExprValue::DatatypeSelector { expr, selector_name, .. } => {
                let mut selected = Vec::new();
                for term in self.guarded_pointer_terms(expr, guard, depth, remaining)? {
                    let Some(field) = Self::slice_storage_field(&term.address, selector_name)
                    else {
                        tracing::debug!(%selector_name, address = ?term.address, "unresolved singleton pointer field");
                        return None;
                    };
                    selected
                        .extend(self.guarded_pointer_terms(field, term.guard, depth, remaining)?);
                }
                Some(selected)
            }
            _ => Some(vec![GuardedPointerTerm { guard, address: value.clone() }]),
        }
    }

    fn fold_pointer_branch(&self, value: &Expr, guard: &Expr) -> Expr {
        let assumption = self
            .current_path_condition
            .as_ref()
            .map_or_else(|| guard.clone(), |path| path.clone().and(guard.clone()));
        self.ctx
            .byte_memory_facts(&self.ssa_concrete_values)
            .fold_assuming(value, Some(&assumption))
    }

    fn slice_storage_field<'s>(value: &'s Expr, name: &str) -> Option<&'s Expr> {
        let ExprValue::DatatypeConstructor { constructor_name, args, .. } = value.value() else {
            return None;
        };
        let datatype = value.sort().datatype_sort()?;
        let constructor =
            datatype.constructors.iter().find(|c| &*c.name == constructor_name.as_str())?;
        let index = constructor.fields.iter().position(|field| &*field.name == name)?;
        args.get(index)
    }

    fn checked_shared_scalar_slice(&self, value: &Expr) -> Result<Option<SharedScalarSlice>, ()> {
        let mut remaining = MAX_TERMS;
        let slice = self.slice_storage_term(value, MAX_DEPTH, &mut remaining).ok_or(())?;
        let array = Self::slice_storage_field(slice, "fld_data").ok_or(())?;
        let array = self.slice_storage_term(array, MAX_DEPTH, &mut remaining).ok_or(())?;
        let origin = match array.value() {
            ExprValue::Var { name } => self.ctx.shared_scalar_slices.get(name).ok_or(())?,
            ExprValue::ConstArray { .. } => return Ok(None),
            _ => return Err(()),
        };
        let address = Self::slice_storage_field(slice, "fld_ptr").ok_or(())?;
        let len = Self::slice_storage_field(slice, "fld_len").ok_or(())?;
        if *len != Expr::bitvec_const(1u64, POINTER_WIDTH)
            || !self.retains_alloc_address(address, &origin.address)
        {
            return Err(());
        }
        Ok(Some(origin.clone()))
    }

    /// Only element reads compare data with byte memory. Metadata and
    /// pointer extraction keep their existing owner/address checks alone.
    pub(super) fn guard_shared_scalar_slice_data_read(&mut self, value: &Expr, cached: &Expr) {
        if self.ctx.shared_scalar_slices.is_empty()
            || !value
                .sort()
                .datatype_name()
                .is_some_and(crate::codegen_ay::names::is_slice_sort_name)
        {
            return;
        }
        match self.checked_shared_scalar_slice(value) {
            Ok(Some(origin)) => {
                // The byte-memory folder handles stores but cannot unfold a
                // datatype selector backed by a separately defined array.
                // Use the scalar from that definition only when this logical
                // term is a select of that exact backing.
                let mut remaining = MAX_TERMS;
                let actual =
                    self.slice_storage_term(cached, MAX_DEPTH, &mut remaining).and_then(|value| {
                        let ExprValue::Select { array, .. } = value.value() else {
                            return None;
                        };
                        self.slice_storage_term(array, MAX_DEPTH, &mut remaining)
                    });
                let cached = if actual == Some(&origin.backing) { &origin.scalar } else { cached };
                self.guard_shared_scalar_origin_data(&origin, cached);
            }
            Ok(None) => {}
            Err(()) => self.ctx.unsupported_with_fallback(
                "shared_scalar_slice_data_origin_unresolved",
                "a logical slice read has no exact singleton backing and address",
            ),
        }
    }

    /// The place reader has already resolved the scalar value. Re-read only
    /// its pointer prefix here; never materialize a snapshot back into memory.
    pub(super) fn guard_shared_scalar_place_data_read(&mut self, place: &Place, cached: &Expr) {
        if self.ctx.shared_scalar_slices.is_empty()
            || !place.ty(self.body.locals()).into_option().is_some_and(|ty| {
                matches!(ty.kind(), TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_)))
            })
        {
            return;
        }
        let Some(deref) = place.projection.iter().rposition(|p| matches!(p, ProjectionElem::Deref))
        else {
            return;
        };
        let pointer = Place { local: place.local, projection: place.projection[..deref].to_vec() };
        let Some(ty) = pointer.ty(self.body.locals()).into_option() else {
            return;
        };
        if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, pointee, _)
            | RigidTy::RawPtr(pointee, _))
            if matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Slice(_))))
        {
            if let Some(value) = self.codegen_place(&pointer) {
                self.guard_shared_scalar_slice_data_read(&value, cached);
            }
        } else if deref + 1 == place.projection.len() {
            self.guard_shared_scalar_pointer_data_read(&pointer, cached);
        }
    }

    /// `get_value_through_ref` can return a cached scalar without entering
    /// the place reader. Its caller reports that this is a pointee VALUE.
    pub(super) fn guard_shared_scalar_operand_data_read(
        &mut self,
        operand: &Operand,
        cached: &Expr,
    ) {
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            self.guard_shared_scalar_pointer_data_read(place, cached);
        }
    }

    fn guard_shared_scalar_pointer_data_read(&mut self, pointer: &Place, cached: &Expr) {
        if self.ctx.shared_scalar_slices.is_empty()
            || !pointer.ty(self.body.locals()).into_option().is_some_and(|ty| {
                matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
                    if matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_))))
            })
        {
            return;
        }
        let Some(address) = self.codegen_place(pointer) else {
            return;
        };
        let origin = self
            .ctx
            .shared_scalar_slices
            .values()
            .find(|origin| self.retains_alloc_address(&address, &origin.address))
            .cloned();
        if let Some(origin) = origin {
            // A later legitimate borrow can read a newer scalar value. Compare
            // that actual logical read, not the older slice's birth snapshot.
            self.guard_shared_scalar_origin_data(&origin, cached);
        }
    }

    fn guard_shared_scalar_origin_data(&mut self, origin: &SharedScalarSlice, cached: &Expr) {
        let owner =
            Self::resolve_stack_storage_owner(&self.ref_pointees, &origin.owner).ok().flatten();
        if owner.as_ref().and_then(|owner| self.stack_owner_is_live(owner)) != Some(true) {
            self.check_shared_scalar_slice_owner(&origin.owner);
            return;
        }
        if cached.sort() != origin.scalar.sort() {
            self.ctx.unsupported_with_fallback(
                "shared_scalar_slice_data_bytes_unresolved",
                "a logical scalar read changes the singleton element type",
            );
            return;
        }
        let Some(width) = cached.sort().bitvec_width().filter(|width| *width > 0 && width % 8 == 0)
        else {
            self.ctx.unsupported_with_fallback(
                "shared_scalar_slice_data_bytes_unresolved",
                "a logical singleton read is not a byte-aligned integer",
            );
            return;
        };
        let Some(current) =
            self.ctx.load_materialized_memory_bytes(origin.address.clone(), width / 8)
        else {
            self.ctx.unsupported_with_fallback(
                "shared_scalar_slice_data_bytes_unresolved",
                "the scalar address retains an opaque symbolic store",
            );
            return;
        };
        self.guard_cached_memory_value(
            cached,
            current,
            "unsound_shared_scalar_slice_cached_read",
            "shared_scalar_slice_cached_read_guard",
        );
    }

    /// MIR already emits the bounds assertion for indexing a slice. A
    /// decided zero index can borrow the original scalar's storage directly.
    pub(super) fn try_codegen_shared_scalar_slice_element_borrow(
        &mut self,
        destination: &Place,
        rhs: &Rvalue,
    ) -> bool {
        if self.ctx.shared_scalar_slices.is_empty() {
            return false;
        }
        let (Rvalue::Ref(_, _, element) | Rvalue::AddressOf(_, element)) = rhs else {
            return false;
        };
        let [prefix @ .., ProjectionElem::Deref, index] = element.projection.as_slice() else {
            return false;
        };
        if !matches!(index, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }) {
            return false;
        }
        let slice = Place { local: element.local, projection: prefix.to_vec() };
        let Some(ty) = slice.ty(self.body.locals()).into_option() else {
            return false;
        };
        if !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, pointee, _))
            if matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Slice(_))))
        {
            return false;
        }
        let Some(origin) = self
            .codegen_place(&slice)
            .and_then(|slice| self.checked_shared_scalar_slice(&slice).ok().flatten())
        else {
            return false;
        };
        self.check_shared_scalar_slice_owner(&origin.owner);
        let zero = match index {
            ProjectionElem::ConstantIndex { offset, min_length, from_end: true } => {
                *offset == 1 && *min_length <= 1
            }
            _ => self.current_array_index(index) == Some(0),
        };
        if !zero
            || !destination.projection.is_empty()
            || matches!(rhs, Rvalue::Ref(_, kind, _) if !matches!(kind, BorrowKind::Shared))
        {
            self.ctx.unsupported_with_fallback(
                "shared_scalar_slice_element_reference_unqualified",
                "a slice element borrow has an unsupported index or destination",
            );
            return false;
        }

        self.bind_shared_scalar_element_reference(destination, origin);
        true
    }

    fn bind_shared_scalar_element_reference(
        &mut self,
        destination: &Place,
        origin: SharedScalarSlice,
    ) {
        let dest_base = self.ssa_base_name(destination).into();
        self.bind_ssa_result(destination, origin.address);
        self.ref_pointees.insert(dest_base, origin.pointee);
    }

    fn shared_scalar_slice_operand_origin(
        &mut self,
        operand: &Operand,
    ) -> Option<SharedScalarSlice> {
        if self.ctx.shared_scalar_slices.is_empty() {
            return None;
        }
        let ref_value = self.codegen_operand(operand)?;
        self.checked_shared_scalar_slice(&ref_value).ok().flatten()
    }

    /// Use the original scalar address for the known singleton Index call,
    /// before the general stub wraps a copied element in a synthetic reference.
    pub(super) fn try_codegen_shared_scalar_slice_index_ref(
        &mut self,
        operand: &Operand,
        index: &Expr,
        destination: &Place,
    ) -> bool {
        let Some(origin) = self.shared_scalar_slice_operand_origin(operand) else {
            return false;
        };
        self.check_shared_scalar_slice_owner(&origin.owner);
        let shared = destination.ty(self.body.locals()).into_option().is_some_and(|ty| {
            matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, _, Mutability::Not)))
        });
        if !shared
            || !destination.projection.is_empty()
            || self.fold_memory_reads_on_path(index) != Expr::bitvec_const(0u64, POINTER_WIDTH)
        {
            self.ctx.unsupported_with_fallback(
                "shared_scalar_slice_element_reference_unqualified",
                "a slice Index call has an unsupported index or destination",
            );
            return false;
        }
        self.bind_shared_scalar_element_reference(destination, origin);
        true
    }

    /// The flattened option lane stores a copied value as its payload.
    /// It must refuse a singleton reference whose owner it cannot carry.
    pub(super) fn guard_shared_scalar_slice_get(&mut self, operand: &Operand) {
        if let Some(origin) = self.shared_scalar_slice_operand_origin(operand) {
            self.check_shared_scalar_slice_owner(&origin.owner);
            self.ctx.unsupported_with_fallback(
                "shared_scalar_slice_element_option_unqualified",
                "slice get cannot carry the scalar allocation through its option payload",
            );
        }
    }

    fn check_shared_scalar_slice_owner(&mut self, base: &str) {
        self.check_shared_scalar_slice_owner_when(base, Expr::bool_const(true));
    }

    fn check_shared_scalar_slice_owner_when(&mut self, base: &str, guard: Expr) {
        let owner = Self::resolve_stack_storage_owner(&self.ref_pointees, base).ok().flatten();
        match owner.as_ref().and_then(|owner| self.stack_owner_is_live(owner)) {
            Some(true) => {}
            Some(false) => self.record_violation_guarded(guard, "dead_object"),
            None => self
                .ctx
                .unsupported_with_fallback("shared_scalar_slice_owner_unresolved", base.to_owned()),
        }
    }

    /// Check the stack allocation of each possible thin pointer. Its
    /// actual byte load stays independent of the slice's logical backing.
    pub(super) fn guard_shared_scalar_raw_address(
        &mut self,
        address: &Expr,
        access: Option<(usize, usize)>,
    ) {
        if self.ctx.shared_scalar_slices.is_empty() {
            return;
        }
        let mut remaining = MAX_TERMS;
        let accesses = self
            .guarded_pointer_terms(address, Expr::bool_const(true), MAX_DEPTH, &mut remaining)
            .and_then(|terms| {
                terms
                    .into_iter()
                    .map(|term| {
                        let Some((symbol, view)) = self.resolve_alloc(&term.address) else {
                            tracing::debug!(address = ?term.address, guard = ?term.guard, "unresolved singleton raw allocation");
                            return None;
                        };
                        let outside = access.map(|(offset, size)| {
                            Self::allocation_access_outside(
                                &term.address,
                                &symbol,
                                &view,
                                offset,
                                size,
                            )
                        });
                        Some((view.root, term.guard, outside))
                    })
                    .collect::<Option<Vec<_>>>()
            });
        let Some(accesses) = accesses else {
            self.ctx.unsupported_with_fallback(
                "shared_scalar_slice_raw_origin_unresolved",
                "a raw dereference may name a shared slice's stack allocation",
            );
            return;
        };
        for (root, guard, outside) in accesses {
            if !self.ctx.shared_scalar_slices.values().any(|origin| origin.owner == root) {
                continue;
            }
            self.check_shared_scalar_slice_owner_when(&root, guard.clone());
            match outside {
                Some(outside) if outside == Expr::bool_const(false) => {}
                Some(outside) => self.record_violation_guarded_with_message(
                    guard.and(outside),
                    "pointer_bounds_check",
                    Some("dereference failure: pointer outside object bounds".into()),
                ),
                None => self.ctx.unsupported_with_fallback(
                    "shared_scalar_slice_raw_layout_unresolved",
                    "the stack allocation is known but its raw access width is unknown",
                ),
            }
        }
    }

    /// A dereference must fit the entire access in the named allocation.
    /// Subtract the size from the extent first so the test cannot overflow
    /// by adding a size to the actual pointer.
    fn allocation_access_outside(
        address: &Expr,
        symbol: &Expr,
        view: &AllocView,
        field_offset: usize,
        size: usize,
    ) -> Expr {
        let Some(last_start) = view.extent.checked_sub(size as u128) else {
            return Expr::bool_const(true);
        };
        if address == symbol {
            return Expr::bool_const(
                view.offset.checked_add(field_offset as u128).is_none_or(|at| at > last_start),
            );
        }
        let base = symbol.clone().bvsub(Expr::bitvec_const(view.offset, POINTER_WIDTH));
        let field_address = if field_offset == 0 {
            address.clone()
        } else {
            address.clone().bvadd(Expr::bitvec_const(field_offset as u128, POINTER_WIDTH))
        };
        field_address.bvsub(base).bvugt(Expr::bitvec_const(last_start, POINTER_WIDTH))
    }

    /// A shared reference's Rust region may have been widened by unsafe code.
    /// Check the original allocation on the current path before reading data.
    pub(super) fn guard_shared_scalar_slice_place(&mut self, place: &Place, ty: Ty) {
        if self.ctx.shared_scalar_slices.is_empty() {
            return;
        }
        let TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _)) = ty.kind()
        else {
            return;
        };
        if matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_))) {
            if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(..))) {
                self.guard_shared_scalar_element_reference(place);
            }
            return;
        }
        if !matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Slice(element))
            if matches!(element.kind(), TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_))))
        {
            return;
        }
        let origin = self
            .codegen_place(place)
            .ok_or(())
            .and_then(|value| self.checked_shared_scalar_slice(&value));
        match origin {
            Ok(None) => {}
            Ok(Some(origin)) => {
                self.check_shared_scalar_slice_owner(&origin.owner);
            }
            Err(()) => self.ctx.unsupported_with_fallback(
                "shared_scalar_slice_origin_unresolved",
                "a slice access has no exact backing and owner on the current path",
            ),
        }
    }

    /// The same qualified allocation also governs a thin shared reborrow
    /// of the original scalar. Use the current pointer, which can have been
    /// copied or widened after forming the element reference.
    fn guard_shared_scalar_element_reference(&mut self, place: &Place) {
        let base = self.ssa_base_name(place);
        let names_original_pointee = self.ref_pointees.get(base.as_str()).is_some_and(|pointee| {
            self.ctx.shared_scalar_slices.values().any(|origin| &origin.pointee == pointee)
        });
        let pointer = self.codegen_place(place);
        let view = pointer.as_ref().and_then(|pointer| {
            let mut remaining = MAX_TERMS;
            let pointer = self.slice_storage_term(pointer, MAX_DEPTH, &mut remaining)?;
            self.resolve_alloc(pointer).map(|(_, view)| view)
        });
        if let Some(view) = view
            && self.ctx.shared_scalar_slices.values().any(|origin| origin.owner == view.root)
        {
            self.check_shared_scalar_slice_owner(&view.root);
        } else if names_original_pointee {
            self.ctx.unsupported_with_fallback(
                "shared_scalar_slice_element_origin_unresolved",
                "a reference to the slice element has no matching current allocation",
            );
        }
    }

    pub(super) fn guard_shared_scalar_slice_operand(&mut self, operand: &Operand) {
        if !self.ctx.shared_scalar_slices.is_empty()
            && let Operand::Copy(place) | Operand::Move(place) = operand
            && let Some(ty) = place.ty(self.body.locals()).into_option()
            && matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(..)))
        {
            self.guard_shared_scalar_slice_place(place, ty);
        }
    }
}
