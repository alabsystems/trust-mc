// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Reference constant extraction via provenance following.
//!
//! Handles `&T` and `&str` constant extraction by following pointer provenance
//! to extract pointee values from target allocations.
//! Split from operand.rs per #3214.

use super::{Expr, MirConst, Operand, RigidTy, StatementCodegen, TyKind};
use crate::codegen_ay::names;
use crate::codegen_ay::shared::const_pointer::{self, ConstRead, ConstWindow};
use crate::codegen_ay::types::{POINTER_WIDTH, bv8_sort, ptr_sort};
use tracing::debug;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Extract the pointee value from a constant reference (#366).
    ///
    /// The pointee is the window the reference's pointer names in its
    /// target, at the offset the pointer carries
    /// (`const_pointer::fixed_pointee`, THE reader), and only when the
    /// target's bytes are fixed for the run.
    ///
    /// SOUNDNESS: folding the window is exact only while the object cannot
    /// change. A `Fixedness::Live` target (`static mut`, interior-mutable
    /// types), a target whose bytes cannot be evaluated (generic, foreign), a
    /// function or vtable, and a reference whose bytes carry no relocation
    /// return None: unconstrained, i.e. any value. Before the window, the
    /// target was decoded from byte 0: for `const E: &u32 = &[1u32, 2, 3][1]`,
    /// `*E == 1` PROVED (tools/soundness-duals/bmc_global_alloc_object_dual.rs).
    ///
    /// REQUIRES: mir_const is a constant with reference type
    /// ENSURES: On Some, returns an expression for the pointee value
    pub(super) fn try_codegen_const_ref_pointee(
        &self,
        mir_const: &MirConst,
        pointee_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        let bytes = const_pointer::const_bytes(mir_const)?;
        let (_, window) = const_pointer::fixed_pointee(self.ctx.tcx, &bytes, 0, pointee_ty)?;
        if let TyKind::RigidTy(RigidTy::Ref(_, nested_pointee, _)) = pointee_ty.kind() {
            // `&&str`: one more hop, from the window, at the pointer IT holds.
            if matches!(nested_pointee.kind(), TyKind::RigidTy(RigidTy::Str)) {
                return self.codegen_const_str_slice_at(&window, 0);
            }
            return None;
        }
        self.codegen_scalar_from_bytes(&window, pointee_ty)
    }

    /// Give the target of every `&str` / `&[T]` a constant reference reaches
    /// (itself, or through `&&str` hops) its ONE address symbol
    /// (`global_alloc::global_alloc_address`), so the immutable decoders
    /// below can spell the slice's `fld_ptr` as `base(T) + k`. Called by the
    /// `&mut self` entry points before they decode a constant.
    pub(super) fn premint_const_ref_targets(&mut self, mir_const: &MirConst) {
        let Some(bytes) = const_pointer::const_bytes(mir_const) else {
            return;
        };
        let mut ty = mir_const.ty();
        let mut window: Option<ConstWindow> = None;
        for _ in 0..const_pointer::MAX_PROVENANCE_DEPTH {
            let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) = ty.kind() else {
                return;
            };
            let next = {
                let cur: &dyn ConstRead = match &window {
                    Some(w) => w,
                    None => &bytes,
                };
                let Some(r) = const_pointer::const_ref(cur, 0, pointee) else {
                    return;
                };
                if const_pointer::pointee_has_len_metadata(pointee)
                    && let Some(key) = r.ptr.key()
                {
                    let naming = self.global_alloc_naming();
                    let _ = super::global_alloc::global_alloc_address(self.ctx, &key, naming);
                }
                const_pointer::fixed_pointee(self.ctx.tcx, cur, 0, pointee)
            };
            let Some((_, next)) = next else {
                return;
            };
            window = Some(next);
            ty = pointee;
        }
    }

    /// Construct a `Slice_bv8` datatype expression for a constant `&str`.
    ///
    /// Builds:
    /// - `fld_ptr`: the pointer's value, `base(T) + k` (`const_ptr_value`)
    /// - `fld_len`: the fat pointer's length word
    /// - `fld_data`: `Array<usize, BV8>` with the window's bytes at each index
    ///
    /// Part of #3189: eliminates the unconstrained_assignment for `&str` constants
    /// in `vec!["tofu", "93"]` patterns, enabling PROOF for parse.rs.
    pub(super) fn try_codegen_const_str_slice(&self, mir_const: &MirConst) -> Option<Expr> {
        let bytes = const_pointer::const_bytes(mir_const)?;
        self.codegen_const_str_slice_at(&bytes, 0)
    }

    /// The `&str` stored at `at` in `bytes` as a `Slice_bv8`: its bytes are
    /// the window `[k, k + len)` of its target (`fixed_pointee`), not the
    /// target from byte 0 (for `const T: &str = &"hello"[2..]`, `T.as_bytes()[0]
    /// == b'h'` PROVED); its pointer is `base(T) + k`, the same value a raw
    /// pointer to the same byte gets, not a fresh counter per use (two uses of
    /// one constant compared unequal).
    fn codegen_const_str_slice_at(&self, bytes: &dyn ConstRead, at: usize) -> Option<Expr> {
        let str_ty = rustc_public::ty::Ty::from_rigid_kind(RigidTy::Str);
        let (r, window) = const_pointer::fixed_pointee(self.ctx.tcx, bytes, at, str_ty)?;
        let len_value = usize::try_from(r.metadata?).ok()?;
        let str_bytes = window.read_data_bytes(0, len_value)?;
        let ptr_expr = self.const_ptr_value(&r.ptr)?;
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
    /// The elements are the window `[k, k + len·size)` the fat pointer names
    /// (`fixed_pointee`, the length from its metadata word), each decoded at
    /// its own offset under the slot clause (`read_field_from_alloc`); the
    /// pointer is `base(T) + k`. Before, the elements were read from the
    /// target's byte 0 (`const SL: &[u32] = &[0, 1, 2, 3][1..]` gave `SL[0] ==
    /// 0`), and the pointer was a fresh counter per use.
    pub(super) fn try_codegen_const_typed_slice(
        &self,
        mir_const: &MirConst,
        elem_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        use crate::kani_middle::abi::LayoutOf;

        let bytes = const_pointer::const_bytes(mir_const)?;
        let slice_ty = rustc_public::ty::Ty::from_rigid_kind(RigidTy::Slice(elem_ty));
        let (r, window) = const_pointer::fixed_pointee(self.ctx.tcx, &bytes, 0, slice_ty)?;
        let len_value = usize::try_from(r.metadata?).ok()?;
        if len_value == 0 {
            return None;
        }
        let elem_sort = Self::infer_sort_from_ty(elem_ty)?;
        let elem_byte_width = LayoutOf::new(elem_ty).size_of()?;
        if elem_byte_width == 0 {
            return None;
        }
        let default_elem = Self::default_expr_for_sort(&elem_sort)?;
        let mut data = Expr::const_array(ptr_sort(), default_elem);
        for i in 0..len_value {
            let elem_expr =
                self.read_field_from_alloc(&window, elem_ty, &elem_sort, i * elem_byte_width)?;
            let idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
            data = data.try_store(idx, elem_expr).ok()?;
        }
        let ptr_expr = self.const_ptr_value(&r.ptr)?;
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

        // The string is the window `[k, k + len)` the fat pointer names.
        let bytes = const_pointer::const_bytes(mir_const)?;
        let (r, window) = const_pointer::fixed_pointee(self.ctx.tcx, &bytes, 0, pointee_ty)?;
        let len_value = usize::try_from(r.metadata?).ok()?;
        let str_bytes = window.read_data_bytes(0, len_value)?;

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
