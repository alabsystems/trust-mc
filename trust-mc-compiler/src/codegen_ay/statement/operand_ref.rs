// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Reference constant extraction via provenance following.
//!
//! Handles `&T` and `&str` constant extraction by following pointer provenance
//! to extract pointee values from target allocations.
//! Split from operand.rs per #3214.

use super::{
    Allocation, ConstantKind, Expr, GlobalAlloc, MirConst, Operand, RigidTy, StatementCodegen,
    TyConstKind, TyKind,
};
use crate::codegen_ay::names;
use crate::codegen_ay::types::{POINTER_WIDTH, bv8_sort, ptr_sort};
use tracing::debug;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Extract the pointee value from a constant reference (#366).
    ///
    /// For promoted constants like `const &0`, this follows provenance to get the actual
    /// pointee value from the target allocation. A constant reference's allocation contains
    /// a pointer (with provenance) to another allocation that holds the actual value.
    ///
    /// REQUIRES: mir_const is a constant with reference type
    /// ENSURES: On Some, returns an expression for the pointee value
    pub(super) fn try_codegen_const_ref_pointee(
        &self,
        mir_const: &MirConst,
        pointee_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        // Extract allocation from the constant
        let alloc = Self::const_allocation(mir_const)?;

        // For reference constants, the allocation contains a POINTER (with provenance)
        // to the actual pointee value. We need to follow the provenance.
        if !alloc.provenance.ptrs.is_empty() {
            let (_, prov) = &alloc.provenance.ptrs[0];
            let alloc_id = prov.0;
            // Follow the provenance to get the target allocation
            match GlobalAlloc::from(alloc_id) {
                GlobalAlloc::Memory(target_alloc) => {
                    if let TyKind::RigidTy(RigidTy::Ref(_, nested_pointee, _)) = pointee_ty.kind()
                        && matches!(nested_pointee.kind(), TyKind::RigidTy(RigidTy::Str))
                    {
                        return self.codegen_const_str_slice_from_fat_ptr_alloc(&target_alloc);
                    }
                    // The target allocation contains the actual pointee value
                    return self.codegen_scalar_from_alloc(&target_alloc, pointee_ty);
                }
                // A reference constant into a STATIC (`static X: i32 = 12;`
                // read through `fn foo() -> i32 { X }`). Without this arm the
                // rvalue codegen returned None, the LHS stayed unconstrained
                // (`[AY:CTREX_CAT:EncodingGap:unconstrained_assignment]`) and
                // every check that reads the static reported FAILURE on values
                // the program cannot produce — `expected/static/main.rs` failed
                // BOTH of its assertions instead of only the first.
                //
                // SOUNDNESS: folding the initializer is exact only while the
                // object cannot change. `immutable_static_initializer` refuses
                // `static mut` (an earlier store is the live value, not the
                // initializer), interior-mutable (non-`Freeze`) types, generic
                // shapes, and foreign statics with no initializer body at all;
                // every refusal returns None, which is the previous behaviour —
                // unconstrained, i.e. any value.
                GlobalAlloc::Static(static_def) => {
                    // The pointer's own bytes hold the offset INTO the target
                    // allocation; only offset 0 names the whole object, which is
                    // what `codegen_scalar_from_alloc` reads.
                    if Self::const_ptr_offset_is_zero(&alloc) != Some(true) {
                        return None;
                    }
                    let target_alloc = self.immutable_static_initializer(static_def)?;
                    if let TyKind::RigidTy(RigidTy::Ref(_, nested_pointee, _)) = pointee_ty.kind()
                        && matches!(nested_pointee.kind(), TyKind::RigidTy(RigidTy::Str))
                    {
                        return self.codegen_const_str_slice_from_fat_ptr_alloc(&target_alloc);
                    }
                    debug!(?pointee_ty, "const ref into an immutable static: folded initializer");
                    return self.codegen_scalar_from_alloc(&target_alloc, pointee_ty);
                }
                _ => {
                    // external enum: GlobalAlloc — Function, VTable not handled yet
                    return None;
                }
            }
        }

        // Fallback: try direct extraction (for cases without provenance)
        self.codegen_scalar_from_alloc(&alloc, pointee_ty)
    }

    /// Whether the pointer stored in `alloc` addresses its target at offset 0.
    ///
    /// Returns `None` when any of the pointer's bytes is uninitialized (the
    /// caller must then decline rather than guess an offset).
    fn const_ptr_offset_is_zero(alloc: &Allocation) -> Option<bool> {
        let ptr_bytes = POINTER_WIDTH as usize / 8;
        let bytes = alloc.bytes.get(..ptr_bytes)?;
        let mut offset: u128 = 0;
        for (i, byte) in bytes.iter().enumerate() {
            let b = (*byte)?;
            offset |= u128::from(b) << (i * 8);
        }
        Some(offset == 0)
    }

    /// The initializer allocation of a static whose value is FIXED for the whole
    /// program run, or `None` when the static may hold something else.
    ///
    /// Declines (in order):
    /// - a foreign (`extern "C" { static X: T; }`) static: it has no MIR
    ///   initializer body and `eval_initializer()` raises a rustc `span_bug`,
    ///   which is an abort `.ok()` cannot catch;
    /// - `static mut`: a store executed earlier in the harness is the live
    ///   value, so the initializer is not what a later read observes;
    /// - a non-`Freeze` type (`UnsafeCell`, and so `Cell`/`RefCell`/atomics):
    ///   an `&`-reference to it can still be written through;
    /// - a still-generic type, which cannot be evaluated at all.
    ///
    /// Every decline is `None`, and `None` is exactly the pre-existing
    /// behaviour (the referent is left unconstrained — any value), so the
    /// fail direction never pins state that could have changed.
    fn immutable_static_initializer(
        &self,
        static_def: rustc_public::mir::mono::StaticDef,
    ) -> Option<Allocation> {
        use rustc_middle::ty::TypeVisitableExt;
        use rustc_public::CrateDef;

        let tcx = self.ctx.tcx;
        let def_id = rustc_public::rustc_internal::internal(tcx, static_def.def_id());
        if tcx.is_foreign_item(def_id) {
            debug!("immutable_static_initializer: foreign static, left unconstrained");
            return None;
        }
        if tcx.is_mutable_static(def_id) {
            debug!("immutable_static_initializer: `static mut`, left unconstrained");
            return None;
        }
        let internal_ty = rustc_public::rustc_internal::internal(tcx, static_def.ty());
        if internal_ty.has_param() {
            return None;
        }
        if !internal_ty.is_freeze(tcx, rustc_middle::ty::TypingEnv::fully_monomorphized()) {
            debug!("immutable_static_initializer: interior-mutable, left unconstrained");
            return None;
        }
        static_def.eval_initializer().ok()
    }

    fn const_allocation(mir_const: &MirConst) -> Option<Allocation> {
        match mir_const.kind() {
            ConstantKind::Allocated(alloc) => Some(alloc.clone()),
            ConstantKind::Ty(ty_const) => match ty_const.kind() {
                TyConstKind::Value(_, alloc) => Some(alloc.clone()),
                _ => None,
            },
            _ => None,
        }
    }

    /// Construct a `Slice_bv8` datatype expression for a constant `&str`.
    ///
    /// Follows provenance to read the string bytes, then builds:
    /// - `fld_ptr`: unique pointer constant (allocation identity)
    /// - `fld_len`: string length as pointer-width bitvec
    /// - `fld_data`: `Array<usize, BV8>` with concrete byte values at each index
    ///
    /// Part of #3189: eliminates the unconstrained_assignment for `&str` constants
    /// in `vec!["tofu", "93"]` patterns, enabling PROOF for parse.rs.
    pub(super) fn try_codegen_const_str_slice(&self, mir_const: &MirConst) -> Option<Expr> {
        let alloc = Self::const_allocation(mir_const)?;
        self.codegen_const_str_slice_from_fat_ptr_alloc(&alloc)
    }

    fn codegen_const_str_slice_from_fat_ptr_alloc(&self, alloc: &Allocation) -> Option<Expr> {
        if alloc.provenance.ptrs.is_empty() {
            return None;
        }

        let (_, prov) = &alloc.provenance.ptrs[0];
        let alloc_id = prov.0;
        let target_alloc = match GlobalAlloc::from(alloc_id) {
            GlobalAlloc::Memory(target) => target,
            _ => return None,
        };

        // Read length from fat pointer (second pointer-width field)
        let ptr_bytes = POINTER_WIDTH as usize / 8;
        let len_bytes = alloc.bytes.get(ptr_bytes..ptr_bytes * 2)?;
        let mut len_value: usize = 0;
        for (i, byte) in len_bytes.iter().take(ptr_bytes).enumerate() {
            if let Some(b) = byte {
                len_value |= (*b as usize) << (i * 8);
            }
        }

        let str_bytes: Vec<u8> =
            target_alloc.bytes.iter().take(len_value).filter_map(|b| *b).collect();
        if str_bytes.len() != len_value {
            debug!(
                expected = len_value,
                got = str_bytes.len(),
                "try_codegen_const_str_slice: truncated string bytes"
            );
            return None;
        }

        // Build Slice_bv8 datatype: (fld_ptr, fld_len, fld_data)
        // Use a unique pointer from a static counter (AllocId fields are private).
        use std::sync::atomic::{AtomicU64, Ordering};
        static STR_CONST_ID: AtomicU64 = AtomicU64::new(0x3000);
        let ptr_val = STR_CONST_ID.fetch_add(1, Ordering::Relaxed);
        let ptr_expr = Expr::bitvec_const(ptr_val as u128, POINTER_WIDTH);
        let len_expr = Expr::bitvec_const(len_value as u128, POINTER_WIDTH);

        let mut data = Expr::const_array(ptr_sort(), Expr::bitvec_const(0u128, 8));
        for (i, &byte) in str_bytes.iter().enumerate() {
            let idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
            let val = Expr::bitvec_const(byte as u128, 8);
            data = data.try_store(idx, val).ok()?;
        }

        let slice_name = names::slice_sort_name("bv8");
        let ctor_name = names::cons_name(&slice_name);
        let slice_sort = Self::slice_sort(bv8_sort());
        let slice = Expr::datatype_constructor(
            slice_name,
            ctor_name,
            vec![ptr_expr, len_expr, data],
            slice_sort,
        );

        debug!(
            len = len_value,
            content = %String::from_utf8_lossy(&str_bytes),
            "try_codegen_const_str_slice: constructed Slice_bv8"
        );
        Some(slice)
    }

    /// Construct a `Slice_T` datatype expression for a constant `&[T]`.
    ///
    /// For non-str slice types (e.g., `&[(u8, u32)]`), follows provenance to
    /// read element data, then builds a Slice_T datatype with ptr, len, and a
    /// data array populated with concrete element values.
    pub(super) fn try_codegen_const_typed_slice(
        &self,
        mir_const: &MirConst,
        elem_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        use crate::kani_middle::abi::LayoutOf;

        let alloc = match mir_const.kind() {
            ConstantKind::Allocated(alloc) => alloc.clone(),
            ConstantKind::Ty(ty_const) => match ty_const.kind() {
                TyConstKind::Value(_, alloc) => alloc.clone(),
                _ => return None,
            },
            _ => return None,
        };
        if alloc.provenance.ptrs.is_empty() {
            return None;
        }
        let (_, prov) = &alloc.provenance.ptrs[0];
        let target_alloc = match GlobalAlloc::from(prov.0) {
            GlobalAlloc::Memory(target) => target,
            _ => return None,
        };
        let ptr_bytes = POINTER_WIDTH as usize / 8;
        let len_bytes = alloc.bytes.get(ptr_bytes..ptr_bytes * 2)?;
        let mut len_value: usize = 0;
        for (i, byte) in len_bytes.iter().take(ptr_bytes).enumerate() {
            if let Some(b) = byte {
                len_value |= (*b as usize) << (i * 8);
            }
        }
        if len_value == 0 {
            return None;
        }
        let elem_sort = Self::infer_sort_from_ty(elem_ty)?;
        let elem_layout = LayoutOf::new(elem_ty);
        let elem_byte_width = elem_layout.size_of()?;
        if elem_byte_width == 0 || target_alloc.bytes.len() < len_value * elem_byte_width {
            return None;
        }
        let default_elem = Self::default_expr_for_sort(&elem_sort)?;
        let mut data = Expr::const_array(ptr_sort(), default_elem);
        for i in 0..len_value {
            let base = i * elem_byte_width;
            let elem_expr = Self::read_typed_element_from_alloc(
                &target_alloc,
                base,
                elem_ty,
                &elem_sort,
                &elem_layout,
            )?;
            let idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
            data = data.try_store(idx, elem_expr).ok()?;
        }
        use std::sync::atomic::{AtomicU64, Ordering};
        static SLICE_CONST_ID: AtomicU64 = AtomicU64::new(0x4000);
        let ptr_val = SLICE_CONST_ID.fetch_add(1, Ordering::Relaxed);
        let ptr_expr = Expr::bitvec_const(ptr_val as u128, POINTER_WIDTH);
        let len_expr = Expr::bitvec_const(len_value as u128, POINTER_WIDTH);
        let slice_short_name = names::sort_short_name(&elem_sort);
        let slice_name = names::slice_sort_name(&slice_short_name);
        let ctor_name = names::cons_name(&slice_name);
        let slice_sort = Self::slice_sort(elem_sort);
        let slice = Expr::datatype_constructor(
            slice_name,
            ctor_name,
            vec![ptr_expr, len_expr, data],
            slice_sort,
        );
        debug!(len = len_value, ?elem_ty, "constructed const typed slice");
        Some(slice)
    }

    /// Create a default (zero/false) expression for a sort.
    fn default_expr_for_sort(sort: &ay_bindings::Sort) -> Option<Expr> {
        use ay_bindings::SortInner;
        match sort.inner() {
            SortInner::Bool => Some(Expr::bool_const(false)),
            SortInner::BitVec(bv) => Some(Expr::bitvec_const(0u128, bv.width)),
            SortInner::Datatype(dt) => {
                let ctor = dt.constructors.first()?;
                let fields: Vec<Expr> = ctor
                    .fields
                    .iter()
                    .filter_map(|f| Self::default_expr_for_sort(&f.sort))
                    .collect();
                if fields.len() != ctor.fields.len() {
                    return None;
                }
                Some(Expr::datatype_constructor(&dt.name, &ctor.name, fields, sort.clone()))
            }
            _ => None,
        }
    }

    /// Read a typed element from an allocation at a given byte offset.
    fn read_typed_element_from_alloc(
        target_alloc: &rustc_public::ty::Allocation,
        base: usize,
        elem_ty: rustc_public::ty::Ty,
        elem_sort: &ay_bindings::Sort,
        elem_layout: &crate::kani_middle::abi::LayoutOf,
    ) -> Option<Expr> {
        use crate::codegen_ay::types::{int_ty_to_bitvec_width, uint_ty_to_bitvec_width};
        use ay_bindings::SortInner;
        match elem_ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => {
                let byte_val: u8 = target_alloc.bytes.get(base).copied()??;
                Some(Expr::bool_const(byte_val != 0))
            }
            TyKind::RigidTy(RigidTy::Uint(ut)) => {
                let bits = uint_ty_to_bitvec_width(ut);
                let bw = (bits / 8) as usize;
                let mut value: u128 = 0;
                for b in 0..bw {
                    let byte_val: u8 = target_alloc.bytes.get(base + b).copied()??;
                    value |= (byte_val as u128) << (b * 8);
                }
                Some(Expr::bitvec_const(value, bits))
            }
            TyKind::RigidTy(RigidTy::Int(it)) => {
                let bits = int_ty_to_bitvec_width(it);
                let bw = (bits / 8) as usize;
                let mut value: u128 = 0;
                for b in 0..bw {
                    let byte_val: u8 = target_alloc.bytes.get(base + b).copied()??;
                    value |= (byte_val as u128) << (b * 8);
                }
                Some(Expr::bitvec_const(value, bits))
            }
            TyKind::RigidTy(RigidTy::Char) => {
                let mut value: u128 = 0;
                for b in 0..4usize {
                    let byte_val: u8 = target_alloc.bytes.get(base + b).copied()??;
                    value |= (byte_val as u128) << (b * 8);
                }
                Some(Expr::bitvec_const(value & 0xFFFFFFFF, 32))
            }
            TyKind::RigidTy(RigidTy::Tuple(field_tys)) => {
                let SortInner::Datatype(dt) = elem_sort.inner() else {
                    return None;
                };
                let ctor = dt.constructors.first()?;
                if ctor.fields.len() != field_tys.len() {
                    return None;
                }
                let mut field_exprs = Vec::with_capacity(field_tys.len());
                for (field_idx, field_info) in ctor.fields.iter().enumerate() {
                    let fld_offset = base + elem_layout.field_offset(field_idx)?;
                    let field_expr = if field_info.sort.is_bool() {
                        let byte_val: u8 = target_alloc.bytes.get(fld_offset).copied()??;
                        Expr::bool_const(byte_val != 0)
                    } else {
                        let bits = field_info.sort.bitvec_width()?;
                        let fw = (bits as usize / 8).max(1);
                        let mut value: u128 = 0;
                        for b in 0..fw {
                            let bv: u8 = target_alloc.bytes.get(fld_offset + b).copied()??;
                            value |= (bv as u128) << (b * 8);
                        }
                        Expr::bitvec_const(value, bits)
                    };
                    field_exprs.push(field_expr);
                }
                Some(Expr::datatype_constructor(
                    &dt.name,
                    &ctor.name,
                    field_exprs,
                    elem_sort.clone(),
                ))
            }
            _ => None,
        }
    }

    /// Try to extract a string constant from an operand.
    ///
    /// This handles `&str` and `&'static str` constants by following provenance
    /// to get the actual string bytes. Used for extracting optional message
    /// arguments (e.g., kani_cover's message parameter).
    ///
    /// REQUIRES: operand is an Operand::Constant with type &str
    /// ENSURES: On Some, returns the string content
    /// ENSURES: On None, operand was not a string constant or extraction failed
    pub(super) fn try_extract_str_constant(&self, operand: &Operand) -> Option<String> {
        let constant = match operand {
            Operand::Constant(c) => c,
            _ => return None, // external enum: Operand
        };

        let mir_const = &constant.const_;
        let ty = mir_const.ty();

        // Check if this is a reference to str
        let TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, _)) = ty.kind() else {
            return None; // external enum: TyKind
        };

        let TyKind::RigidTy(RigidTy::Str) = pointee_ty.kind() else {
            return None; // external enum: TyKind
        };

        // Extract allocation from the constant
        let alloc = match mir_const.kind() {
            ConstantKind::Allocated(alloc) => alloc.clone(),
            ConstantKind::Ty(ty_const) => match ty_const.kind() {
                TyConstKind::Value(_, alloc) => alloc.clone(),
                _ => return None, // external enum: TyConstKind
            },
            _ => return None, // external enum: ConstantKind
        };

        // For &str, the allocation is a fat pointer: [data_ptr (with provenance), len]
        // We need to:
        // 1. Follow the provenance to get the string bytes
        // 2. Read the length from the allocation
        if alloc.provenance.ptrs.is_empty() {
            return None;
        }

        // Get the target allocation containing the string bytes
        let (_, prov) = &alloc.provenance.ptrs[0];
        let alloc_id = prov.0;

        let target_alloc = match GlobalAlloc::from(alloc_id) {
            GlobalAlloc::Memory(target) => target,
            _ => return None, // external enum: GlobalAlloc
        };

        // Read the length from the fat pointer allocation (second field, pointer-width bytes)
        // Fat pointer layout: [ptr (POINTER_WIDTH bits), len (POINTER_WIDTH bits)]
        let ptr_bytes = POINTER_WIDTH as usize / 8;
        let len_bytes = alloc.bytes.get(ptr_bytes..ptr_bytes * 2)?;
        let mut len_value: usize = 0;
        for (i, byte) in len_bytes.iter().take(ptr_bytes).enumerate() {
            if let Some(b) = byte {
                len_value |= (*b as usize) << (i * 8);
            }
        }

        // Read string bytes from target allocation
        let str_bytes: Vec<u8> =
            target_alloc.bytes.iter().take(len_value).filter_map(|b| *b).collect();

        // Validate we got all expected bytes (detect truncation)
        if str_bytes.len() != len_value {
            debug!(
                "try_extract_str_constant: truncated string - expected {} bytes, got {}",
                len_value,
                str_bytes.len()
            );
            return None;
        }

        // Convert to UTF-8 string
        match String::from_utf8(str_bytes) {
            Ok(s) => {
                debug!("try_extract_str_constant: extracted {:?}", s);
                Some(s)
            }
            Err(e) => {
                debug!("try_extract_str_constant: invalid UTF-8: {}", e);
                None
            }
        }
    }
}
