// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! An element store through a pointer to an array that has no register
//! referent: `(*p)[i] = v` and `(*p).buf[i] = v`, where `p` is a `Box`'s
//! pointer, a raw pointer, or any other pointer the Reg-level lanes cannot
//! resolve to a local (no `ref_targets`, no argument pointee, no collection
//! reference).
//!
//! The Mem-level deref handler used to defer every Deref+Index store to the
//! Reg-level handler, which answers only a pointer with a register referent.
//! The store then reached `projection_sound_fallback`, which havocked the
//! POINTER local, not the memory it points to: after `b[3] = 8` on a
//! `Box<[u8; 4]>` the read `b[3]` still returned 4, and `assert!(b[3] == 4)`
//! was proved from a false error obligation (tools/soundness-duals/
//! lost_deref_elem_store_dual.rs). Only the FailClose reason of that fallback
//! kept the harness from reading clean.
//!
//! The element is written at `base + i * size_of::<T>()` into every view a
//! reader of it may consult: the region array when the object has one of the
//! element's sort; the type-indexed array under the ARRAY's type key (the
//! `[T; N]` per-element branch of `build_memory_store_untyped`), which the
//! indexed read `b[i]` reconstructs; and the type-indexed array under the
//! ELEMENT's type key, which a read through the element's address selects
//! (`&b[i]`, `&b[i] as *const T`, `b.as_ptr().add(i)`, a helper taking
//! `&T`), as `mirror_array_elements_to_flat_memory` bridges a whole-array
//! store. Writing the array key alone left the element key at the
//! initializer: `b[3] = 8; let e = &b[3]; assert!(*e == 4)` verified
//! SUCCESSFUL clean and the safe twin was certified Genuine (review of
//! fix/chc-lost-writes, 2026-09-27). An element type whose memory sort is not
//! its value sort in either view (a struct, which memory keeps as a flat bit
//! vector; a nested array) is not written: the array's memory is havocked and
//! the store records `deref_elem_store_unplaced`, a FailClose reason.
//!
//! The write is exact only for a heap allocation: one the address names by a
//! constant object lane (a `Box`'s payload, an `alloc` buffer the store's
//! pointer is traced to), or one the store's pointer local is traced to
//! through its MIR definitions (`pointer_local_heap_referent`: a borrow of a
//! place inside a `Box`'s payload, a copy or cast of such a pointer). Memory
//! is not the whole state of any other referent: a `static mut` and a stack
//! slot keep their value in a state variable the lane does not update, and a
//! pointer the encoder could not resolve may name either. Such a store
//! records `deref_store_referent_unresolved`, as the generic deref store does
//! (review of fix/chc-lost-writes, lostwrite round 1, finding 1). Its access
//! is bounds-checked by `heap_access_checks`, through a symbolic object lane
//! by the size of the object the lane names (`symbolic_lane_bounds`, finding
//! 2). Every key the store writes is filed in the heap view ledger, which
//! fails a read of the object closed where another store left one of its
//! views stale (`heap/heap_view_ledger.rs`, finding 3).

use ay_bindings::Expr;
use rustc_public::mir::{Place, ProjectionElem};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use tracing::debug;

use crate::codegen_ay::shared::ty_signedness_shallow;
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};

use super::super::ChcCtx;
use super::super::codegen_types::CodegenTypes;
use super::super::stmt_accumulator::StmtAccumulator;
use crate::codegen_ay::chc::heap::heap_view_ledger::{ViewSpan, view_object_of};

/// Not blessed: an element store through a pointer whose element could not be
/// written exactly; the array's memory is havocked instead.
pub(in crate::codegen_ay::chc) const DEREF_ELEM_STORE_UNPLACED: &str = "deref_elem_store_unplaced";

/// Not blessed: a store through a pointer whose referent the encoder cannot
/// tie to a state variable or a heap allocation (shared with the generic deref
/// store in `deref_mem.rs`).
pub(in crate::codegen_ay::chc) const DEREF_STORE_REFERENT_UNRESOLVED: &str =
    "deref_store_referent_unresolved";

/// The value of a constant index term, folding a constant expression.
pub(super) fn constant_index_value(index: &Expr) -> Option<u64> {
    let folded;
    let value = match index.value() {
        ay_bindings::ExprValue::BitVecConst { .. } => index,
        _ => {
            folded = trust_mc_core::chc_const_prop::eval::try_eval_to_const(index)?;
            &folded
        }
    };
    match value.value() {
        ay_bindings::ExprValue::BitVecConst { value, .. } => {
            let (_, digits) = value.to_u64_digits();
            match digits.as_slice() {
                [] => Some(0),
                [d] => Some(*d),
                _ => None,
            }
        }
        _ => None,
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Write element `index_proj` of the array of type `array_ty` at
    /// `array_addr` (the address a `Deref`, and any Field steps after it,
    /// designate). Returns `false` when `array_ty` is not a sized array or the
    /// index cannot be translated, so the caller keeps its old route.
    pub(in crate::codegen_ay::chc) fn try_store_array_element_through_pointer(
        &mut self,
        lhs: &Place,
        array_addr: Expr,
        array_ty: Ty,
        index_proj: &ProjectionElem,
        rhs_expr: &Expr,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        let array_ty = self.resolve_body_ty(array_ty);
        let TyKind::RigidTy(RigidTy::Array(elem_ty, _)) = array_ty.kind() else {
            return false;
        };
        let Some(index) = self.resolve_index_expr(index_proj, acc) else {
            return false;
        };
        if !array_addr.sort().is_bitvec() {
            return false;
        }
        let array_addr =
            coerce_bitvec_width_safe(array_addr, POINTER_WIDTH, SignExtension::ZeroExtend);
        let names_heap_object = self.element_store_names_heap_object(&array_addr, lhs.local);
        // At a symbolic index the element is somewhere in the array: the heap
        // view ledger files the store over the array's bytes.
        let array_span = view_object_of(&array_addr).and_then(|(_, offset)| {
            let lo = offset?;
            let size = self.get_type_size(array_ty)? as u64;
            Some(ViewSpan::new(lo, Some(lo + size)))
        });

        let elem_sort = self.elem_sort_for_memory_array(array_ty);
        let value_sort = Self::translate_ty(elem_ty);
        let elem_size = self.get_type_size(elem_ty).filter(|&s| s > 0);
        let array_key = self.type_key_for_body_ty(array_ty);
        let elem_key = self.type_key_for_body_ty(elem_ty);
        let exact = value_sort.as_ref() == Some(&elem_sort)
            && *rhs_expr.sort() == elem_sort
            && !elem_sort.is_array()
            && !elem_sort.is_datatype()
            && (elem_key == array_key || self.elem_sort_for_memory_array(elem_ty) == elem_sort);
        let Some(elem_size) = elem_size.filter(|_| exact) else {
            debug!(
                ?lhs,
                ?elem_sort,
                rhs_sort = ?rhs_expr.sort(),
                "CHC: element store through a pointer not placeable exactly — havoc the array (fail closed)"
            );
            let booked = self.record_sound_fallback_reason(DEREF_ELEM_STORE_UNPLACED);
            self.overapproximate_memory_store_target(booked, array_ty, Some(&array_addr));
            if elem_key != array_key {
                self.overapproximate_memory_store_target(booked, elem_ty, None);
            }
            return true;
        };

        // `base + i * size`, spelled as the read's `[T; N]` reconstruction
        // spells a constant element address, so store-to-load forwarding and
        // the region select key on the same term.
        let elem_addr = match constant_index_value(&index) {
            Some(0) => array_addr,
            Some(i) => array_addr
                .bvadd(Expr::bitvec_const(u128::from(i) * elem_size as u128, POINTER_WIDTH)),
            None => {
                array_addr.bvadd(index.bvmul(Expr::bitvec_const(elem_size as u128, POINTER_WIDTH)))
            }
        };

        if !self.suppress_heap_store_checks {
            let checks = self.heap_access_checks(elem_addr.clone(), elem_ty);
            if !checks.is_empty() {
                self.mark_heap_metadata_read();
            }
            self.heap_state.pending_checks.extend(checks);
            self.modifies_frame_store_check(&elem_addr, elem_ty);
        }

        let signed = ty_signedness_shallow(elem_ty).unwrap_or(false);
        // An index the MIR fixes (`let i = 1; (*p)[i] = v`) is a state variable
        // here, but the store writes that one element on every path: the
        // ledger may let it mask an earlier store of those bytes.
        let elem_span = array_span.and_then(|array| {
            let i = self.mir_constant_index(index_proj)?;
            let lo = array.lo().checked_add(i.checked_mul(elem_size as u64)?)?;
            Some(ViewSpan::new(lo, Some(lo + elem_size as u64)))
        });
        self.heap_state.view_ledger.set_write_exact(elem_span);
        self.heap_state.view_ledger.set_write_extent(array_span);
        self.try_store_to_region(&elem_addr, rhs_expr, &elem_sort, signed);
        if elem_key != array_key {
            self.store_to_type_array(
                elem_addr.clone(),
                rhs_expr.clone(),
                &elem_key,
                elem_sort.clone(),
                signed,
            );
        }
        self.store_to_type_array(elem_addr, rhs_expr.clone(), &array_key, elem_sort, signed);
        self.heap_state.view_ledger.set_write_extent(None);
        self.heap_state.view_ledger.set_write_exact(None);
        // The store reached typed memory only. That is the whole effect when
        // the address names a heap allocation, which nothing holds in a state
        // variable. When it may name a static, a stack slot or an object the
        // encoder could not identify, the referent's state variable (a
        // `static mut`'s, a local's) keeps its old value; the generic deref
        // store records the same reason for the same shape
        // (`handle_deref_store_mem_level`). The lane returned before that guard
        // and wrote only memory: `static mut P: *mut [u16; 2] =
        // addr_of_mut!(B); (*P)[1] = 5; assert!(B[1] == 2)` verified SUCCESSFUL
        // clean, and a `MaybeUninit<[u16; 2]>` static's lazy init was
        // certified a Genuine failure (review of fix/chc-lost-writes,
        // lostwrite round 1, finding 1). An address whose object lane is not a
        // constant is exact only when the pointer is traced to a heap
        // allocation (`element_store_names_heap_object`).
        if !names_heap_object {
            debug!(
                ?lhs,
                "CHC: element store through a pointer whose referent is unresolved — fail closed"
            );
            self.record_sound_fallback_reason(DEREF_STORE_REFERENT_UNRESOLVED);
        }
        debug!(
            ?lhs,
            type_key = %array_key,
            elem_type_key = %elem_key,
            "CHC: element store through a pointer to an array"
        );
        true
    }

    /// The element index `index_proj` names when the MIR fixes it: a constant
    /// index, or an index local whose one whole definition is a constant.
    fn mir_constant_index(&self, index_proj: &ProjectionElem) -> Option<u64> {
        use crate::codegen_ay::shared::const_pointer::ConstRead;
        use rustc_public::mir::{Operand, Rvalue, StatementKind};
        match index_proj {
            ProjectionElem::ConstantIndex { offset, from_end: false, .. } => Some(*offset),
            ProjectionElem::Index(local) => {
                if self.local_has_multiple_whole_definitions(*local) {
                    return None;
                }
                self.body.blocks.iter().flat_map(|b| b.statements.iter()).find_map(|st| {
                    let StatementKind::Assign(place, Rvalue::Use(Operand::Constant(c), ..)) =
                        &st.kind
                    else {
                        return None;
                    };
                    if place.local != *local || !place.projection.is_empty() {
                        return None;
                    }
                    let bytes = crate::codegen_ay::shared::const_pointer::const_bytes(&c.const_)?;
                    if bytes.has_relocations() || bytes.len() != 8 {
                        return None;
                    }
                    bytes.read_uint_at(0, 8).and_then(|v| u64::try_from(v).ok())
                })
            }
            _ => None,
        }
    }

    /// Whether the array an element store writes is a heap allocation: no
    /// static, stack slot or promoted constant, whose value a state variable
    /// may also hold. Either the address names it by a constant object lane,
    /// or the store's pointer local `base` is traced to it through the MIR
    /// (`pointer_local_heap_referent`): `let p: *mut [u16; 2] = &mut b[1]`
    /// over a `Box<[[u16; 2]; 2]>` carries a byte offset `known_alloc_ids`
    /// cannot represent, so the address is a state variable, and the store
    /// failed closed where main wrote it exactly (q4
    /// `safe_box_2d_row_store_elem_addr_read`, lostwrite track round 1,
    /// finding 3).
    fn element_store_names_heap_object(&self, array_addr: &Expr, base: usize) -> bool {
        match Self::const_obj_id_u32(&array_addr.clone().extract(63, 32)) {
            Some(lane) => self.is_heap_object_id(lane),
            None => self.pointer_local_heap_referent(base, 0).is_some(),
        }
    }

    /// The heap allocation the pointer local `local` of the harness body
    /// points into, when its definitions say so: a `known_alloc_ids` entry
    /// naming a heap object, or a single whole definition that is a copy or a
    /// pointer-to-pointer cast of such a local, or a borrow `&(*base).f[i]`
    /// of a place inside the pointee of such a `base` (projections after the
    /// one deref stay in that allocation; a second deref loads a pointer from
    /// memory and names another object).
    fn pointer_local_heap_referent(&self, local: usize, depth: u32) -> Option<u32> {
        use rustc_public::mir::{Operand, Rvalue, StatementKind, TerminatorKind};
        if depth > 8 || self.local_has_multiple_whole_definitions(local) {
            return None;
        }
        if let Some(&id) = self.known_alloc_ids.get(&local) {
            return self.is_heap_object_id(id).then_some(id);
        }
        let mut definition = None;
        let mut zero_step_source = None;
        for block in &self.body.blocks {
            for stmt in &block.statements {
                if let StatementKind::Assign(place, rvalue) = &stmt.kind
                    && place.local == local
                    && place.projection.is_empty()
                {
                    definition = Some(rvalue);
                }
            }
            if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind
                && destination.local == local
            {
                // A pointer step by a constant zero count is the identity on
                // the pointer (`p.wrapping_add(0)`), so it names the referent
                // of the pointer it steps; any other call result is unknown.
                zero_step_source = Some(self.zero_step_pointer_source(func, args)?);
            }
        }
        let source = |op: &Operand| match op {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
            _ => None,
        };
        if let Some(stepped) = zero_step_source {
            if definition.is_some() {
                return None;
            }
            return self.pointer_local_heap_referent(stepped, depth + 1);
        }
        match definition? {
            Rvalue::Use(op, ..) => self.pointer_local_heap_referent(source(op)?, depth + 1),
            Rvalue::Cast(
                rustc_public::mir::CastKind::PtrToPtr
                | rustc_public::mir::CastKind::PointerCoercion(
                    rustc_public::mir::PointerCoercion::MutToConstPointer
                    | rustc_public::mir::PointerCoercion::ArrayToPointer,
                ),
                op,
                _,
            ) => self.pointer_local_heap_referent(source(op)?, depth + 1),
            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => {
                let (first, rest) = place.projection.split_first()?;
                if !matches!(first, ProjectionElem::Deref)
                    || rest.iter().any(|p| {
                        !matches!(
                            p,
                            ProjectionElem::Field(..)
                                | ProjectionElem::Index(_)
                                | ProjectionElem::ConstantIndex { .. }
                                | ProjectionElem::Subslice { .. }
                        )
                    })
                {
                    return None;
                }
                self.pointer_local_heap_referent(place.local, depth + 1)
            }
            _ => None,
        }
    }

    /// The pointer local a raw-pointer step call steps when its count is the
    /// constant zero: `<*mut T>::wrapping_add(p, 0)`, `add`, `sub`,
    /// `wrapping_sub`, `offset`, `wrapping_offset` and their `byte_` forms.
    /// Such a call returns `p` itself (`safe_elem_store_wrapping_inbounds`, an
    /// element store through `p.wrapping_add(0)` into a `Box` payload, failed
    /// closed as an unresolved referent). `None` for any other call, or a count
    /// that is not a constant zero.
    fn zero_step_pointer_source(
        &self,
        func: &rustc_public::mir::Operand,
        args: &[rustc_public::mir::Operand],
    ) -> Option<usize> {
        use rustc_public::mir::Operand;
        let path = self.resolve_callee_path(func)?;
        let is_raw_ptr_method =
            path.contains("<impl *mut ") || path.contains("<impl *const ");
        let method = path.rsplit("::").next()?;
        let is_step = matches!(
            method,
            "add"
                | "sub"
                | "wrapping_add"
                | "wrapping_sub"
                | "offset"
                | "wrapping_offset"
                | "byte_add"
                | "byte_sub"
                | "wrapping_byte_add"
                | "wrapping_byte_sub"
                | "byte_offset"
                | "wrapping_byte_offset"
        );
        if !is_raw_ptr_method || !is_step {
            return None;
        }
        let [ptr, Operand::Constant(count)] = args else { return None };
        let zero = count.const_.eval_target_usize().ok() == Some(0);
        if !zero {
            return None;
        }
        match ptr {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
            _ => None,
        }
    }
}
