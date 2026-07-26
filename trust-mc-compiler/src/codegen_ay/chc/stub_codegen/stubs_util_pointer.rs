// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Pointer utility translation + small detection methods.
//!
//! Extracted from `stubs_util_intrinsics.rs` — Part of #4206.

use std::collections::HashSet;

use ay_bindings::{Expr, Sort, SortInner};
use rustc_public::mir::{Operand, Place};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use super::codegen_expr_heap::obj_valid_out;
use super::stubs::StubKind;
use super::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};
use super::{ChcCtx, chc_fresh_name, declare_pending_var};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Translate pointer/NonZero helper calls to direct expressions.
    ///
    /// REQUIRES: `stub` is one of `NonNullAsPtr`, `NonZeroGet`, `PtrAddr`,
    /// `WithoutProvenanceMut`, `PtrNull`, `PtrIsNull`, `PtrIsNullRuntime`.
    pub(in crate::codegen_ay::chc) fn translate_pointer_utility_call(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // Null-related pointer stubs: compare pointer against zero, null/null_mut
        // return a zero pointer.
        if matches!(stub, StubKind::PtrIsNull | StubKind::PtrIsNullRuntime) {
            let ptr = match args
                .first()
                .and_then(|arg| self.translate_operand_with_modified(arg, modified_locals))
            {
                Some(ptr) => Self::coerce_to_pointer(ptr),
                None => {
                    warn!(?stub, "CHC: ptr::is_null missing operand; using symbolic pointer");
                    self.record_sound_fallback_reason("ptr_is_null_missing_operand");
                    declare_pending_var(
                        chc_fresh_name("__ptr_is_null"),
                        Sort::bitvec(POINTER_WIDTH),
                    )
                }
            };
            return Some(ptr.eq(Expr::bitvec_const(0u64, POINTER_WIDTH)));
        }
        if stub == StubKind::PtrNull {
            let result = Expr::bitvec_const(0, POINTER_WIDTH);
            // #3361: Null pointers have no allocation provenance. Invalidate
            // obj_valid so dereference checks catch null pointer use.
            if !self.int_lift {
                if let Some((obj_id, _offset)) = self.split_pointer(&result) {
                    let current_valid = self.current_obj_valid_array();
                    let invalidated = current_valid.store(obj_id, Expr::bool_const(false));
                    self.heap_state.pending_updates.push(obj_valid_out().eq(invalidated));
                    self.mark_heap_metadata_modified();
                    debug!("#3361: invalidated obj_valid for PtrNull");
                }
            }
            return Some(result);
        }

        // #3361: WithoutProvenance/WithoutProvenanceMut create pointers from integers
        // without allocation provenance. Invalidate obj_valid so dereference checks
        // catch use of these never-allocated addresses.
        // Handled before the `first_arg` closure to avoid borrow conflicts with
        // self.split_pointer. PtrAddr (which extracts an address from an existing
        // pointer that has provenance) is handled below without invalidation.
        if matches!(stub, StubKind::WithoutProvenance | StubKind::WithoutProvenanceMut) {
            let arg_expr =
                args.first().and_then(|a| self.translate_operand_with_modified(a, modified_locals));
            let result = Self::coerce_to_pointer(arg_expr?);
            if !self.int_lift {
                if let Some((obj_id, _offset)) = self.split_pointer(&result) {
                    let current_valid = self.current_obj_valid_array();
                    let invalidated = current_valid.store(obj_id, Expr::bool_const(false));
                    self.heap_state.pending_updates.push(obj_valid_out().eq(invalidated));
                    self.mark_heap_metadata_modified();
                    debug!("#3361: invalidated obj_valid for WithoutProvenance stub");
                }
            }
            return Some(result);
        }

        // Identity/cast stubs that pass through or coerce the first argument
        let mut first_arg =
            || args.first().and_then(|a| self.translate_operand_with_modified(a, modified_locals));
        if matches!(stub, StubKind::NonNullAsPtr | StubKind::NonNullCast) {
            return Some(Self::coerce_to_pointer(first_arg()?));
        }
        if matches!(
            stub,
            StubKind::NonZeroGet | StubKind::MaybeUninitAsPtr | StubKind::CharFromU32Unchecked
        ) {
            return first_arg();
        }

        if matches!(stub, StubKind::SliceAsPtr | StubKind::SliceAsMutPtr) {
            // <[T]>::as_ptr/as_mut_ptr — pointer to first element (Part of #3104)
            let value = first_arg()?;
            return Some(match value.sort().inner() {
                SortInner::BitVec(bv) if bv.width == POINTER_WIDTH => value,
                SortInner::BitVec(_) => {
                    coerce_bitvec_width_safe(value, POINTER_WIDTH, SignExtension::ZeroExtend)
                }
                SortInner::Int => value.int2bv(POINTER_WIDTH),
                _ => value,
            });
        }
        // PtrAddr: extract address from existing pointer (has provenance, no invalidation)
        if stub == StubKind::PtrAddr {
            return Some(Self::coerce_to_pointer(first_arg()?));
        }
        // PtrWithAddr: with_addr(self, addr) -> pointer with new address (Part of #3492)
        // with_addr computes self.wrapping_byte_offset((addr as isize).wrapping_sub(self.addr() as isize))
        // which simplifies to just `addr` (self + (addr - self) = addr).
        // Returning the second arg directly avoids the Mem-level operand resolution
        // failure that occurs when with_addr is inlined and intermediate isize values
        // land in typed memory arrays.
        if stub == StubKind::PtrWithAddr {
            let addr_arg =
                args.get(1).and_then(|a| self.translate_operand_with_modified(a, modified_locals));
            return Some(Self::coerce_to_pointer(addr_arg?));
        }

        None
    }

    /// Coerce an expression to pointer width (BV64), handling Int/BV/other sorts.
    fn coerce_to_pointer(expr: Expr) -> Expr {
        match expr.sort().inner() {
            SortInner::BitVec(bv) if bv.width == POINTER_WIDTH => expr,
            SortInner::BitVec(_) => {
                coerce_bitvec_width_safe(expr, POINTER_WIDTH, SignExtension::ZeroExtend)
            }
            SortInner::Int => expr.int2bv(POINTER_WIDTH),
            _ => expr,
        }
    }

    /// Resolve a reference operand to its pointee expression when tracked.
    pub(in crate::codegen_ay::chc) fn resolve_ref_operand(
        &self,
        operand: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let place = match operand {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => return None,
        };
        if !place.projection.is_empty() {
            return None;
        }
        if !matches!(
            self.body.locals().get(place.local).map(|decl| decl.ty.kind()),
            Some(TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)))
        ) {
            return None;
        }
        let ref_local: usize = place.local;
        let ref_target = self.ref_resolution.ref_targets.get(&ref_local)?;
        // Part of #2179 follow-up: preserve tracked projections when resolving
        // references so callers get the referent value (e.g., ((*_r).0), not `_r` root).
        let target_place =
            Place { local: ref_target.local, projection: ref_target.projections.clone() };
        self.translate_place_with_modified(&target_place, modified_locals)
    }

    /// Detect `std::array::IntoIter::<T, N>::unsize_mut` / `unsize` calls.
    ///
    /// These are reference-forwarding identity operations on the array iterator's
    /// internal data buffer. Part of #3711.
    pub(in crate::codegen_ay::chc) fn detect_into_iter_unsize_call(&self, func: &Operand) -> bool {
        self.resolve_callee_path(func).is_some_and(|p| {
            p.contains("IntoIter") && (p.ends_with("::unsize_mut") || p.ends_with("::unsize"))
        })
    }

    /// Detect `<ManuallyDrop<T> as DerefMut>::deref_mut` / `deref` calls.
    ///
    /// ManuallyDrop is a transparent wrapper; deref/deref_mut are identity unwraps.
    /// Part of #3711.
    pub(in crate::codegen_ay::chc) fn detect_manually_drop_deref_call(
        &self,
        func: &Operand,
    ) -> bool {
        self.resolve_callee_path(func).is_some_and(|p| {
            p.contains("ManuallyDrop") && (p.ends_with("::deref_mut") || p.ends_with("::deref"))
        })
    }

    /// Detect `std::mem::ManuallyDrop::<T>::new` constructor calls.
    ///
    /// `ManuallyDrop<T>` is a transparent wrapper in CHC sort translation, so
    /// `ManuallyDrop::new(value)` is a value identity: `dest = arg0`.
    /// Part of #2183: preserve array IntoIter state through nested inline.
    pub(in crate::codegen_ay::chc) fn detect_manually_drop_new_call(&self, func: &Operand) -> bool {
        self.resolve_callee_path(func)
            .is_some_and(|p| p.contains("ManuallyDrop") && p.ends_with("::new"))
    }

    /// Detect `std::pin::Pin::<Ptr>::as_mut` calls.
    ///
    /// `Pin::as_mut` is a transparent wrapper-forwarding operation: it unwraps
    /// `&mut Pin<&mut T>` to `Pin<&mut T>` without changing the underlying
    /// pinned reference. Part of #3807.
    pub(in crate::codegen_ay::chc) fn detect_pin_as_mut_call(&self, func: &Operand) -> bool {
        self.resolve_callee_path(func)
            .is_some_and(|p| p.contains("pin::Pin") && p.ends_with("::as_mut"))
    }

    /// Detect `std::pin::Pin::<Ptr>::new_unchecked` calls.
    ///
    /// `Pin::new_unchecked` wraps an existing pointer/reference without changing
    /// its underlying storage identity. Part of #3807.
    pub(in crate::codegen_ay::chc) fn detect_pin_new_unchecked_call(&self, func: &Operand) -> bool {
        self.resolve_callee_path(func)
            .is_some_and(|p| p.contains("pin::Pin") && p.ends_with("::new_unchecked"))
    }
}
