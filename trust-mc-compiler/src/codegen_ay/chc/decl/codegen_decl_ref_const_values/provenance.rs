// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared provenance-resolution helpers for constant-reference encoding.
//!
//! Contains `resolve_const_target_alloc`, `record_promoted_alloc_address`,
//! `const_alloc_byte_count`, and `const_elem_byte_width`.
//!
//! Extracted from codegen_decl_ref_const_values.rs per #3694
//! (collect/provenance-first module split).

use std::collections::HashMap;

use ay_bindings::Expr;
use rustc_public::ty::{RigidTy, TyKind};

use crate::codegen_ay::types::{int_ty_to_bitvec_width, uint_ty_to_bitvec_width};

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Resolve a ConstantKind to its target Allocation by following provenance.
    ///
    /// Returns None if the kind has no provenance or the provenance doesn't point
    /// to a memory allocation. Deduplicates the allocation-resolution pattern
    /// previously repeated at 5 call sites (Part of #4147).
    pub(in crate::codegen_ay::chc::decl) fn resolve_const_target_alloc(
        kind: &rustc_public::ty::ConstantKind,
    ) -> Option<rustc_public::ty::Allocation> {
        use rustc_public::mir::alloc::GlobalAlloc;
        use rustc_public::ty::{ConstantKind, TyConstKind};

        match kind {
            ConstantKind::Allocated(alloc) if !alloc.provenance.ptrs.is_empty() => {
                let alloc_id = alloc.provenance.ptrs[0].1.0;
                match GlobalAlloc::from(alloc_id) {
                    GlobalAlloc::Memory(target) => Some(target),
                    _ => None,
                }
            }
            ConstantKind::Ty(ty_const) => match ty_const.kind() {
                TyConstKind::Value(_value_ty, alloc) => {
                    if !alloc.provenance.ptrs.is_empty() {
                        let alloc_id = alloc.provenance.ptrs[0].1.0;
                        match GlobalAlloc::from(alloc_id) {
                            GlobalAlloc::Memory(target) => Some(target),
                            _ => None,
                        }
                    } else {
                        Some(alloc.clone())
                    }
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Record the mapping from a promoted constant's provenance AllocId to its
    /// per-constant address. Called during `collect_const_ref_values` so that
    /// `pointer_scalar_expr` can resolve promoted refs to the correct address.
    /// Part of #3860: fixes address mismatch between translate_constant and entry rule.
    pub(in crate::codegen_ay::chc::decl) fn record_promoted_alloc_address(
        kind: rustc_public::ty::ConstantKind,
        promoted_addr: &Expr,
        map: &mut HashMap<rustc_public::mir::alloc::AllocId, Expr>,
    ) {
        use rustc_public::ty::ConstantKind;
        let alloc_id = match &kind {
            ConstantKind::Allocated(alloc) if !alloc.provenance.ptrs.is_empty() => {
                Some(alloc.provenance.ptrs[0].1.0)
            }
            ConstantKind::Ty(ty_const) => {
                use rustc_public::ty::TyConstKind;
                match ty_const.kind() {
                    TyConstKind::Value(_value_ty, alloc) if !alloc.provenance.ptrs.is_empty() => {
                        Some(alloc.provenance.ptrs[0].1.0)
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        if let Some(id) = alloc_id {
            map.insert(id, promoted_addr.clone());
        }
    }

    /// Get the byte count of a const allocation by following provenance.
    ///
    /// Part of #3495: Used to compute const slice length for PtrMetadata.
    /// Follows the same provenance chain as `extract_scalar_from_const_ref`
    /// but only returns the byte count of the target allocation.
    pub(in crate::codegen_ay::chc::decl) fn const_alloc_byte_count(
        kind: rustc_public::ty::ConstantKind,
    ) -> Option<usize> {
        Self::resolve_const_target_alloc(&kind).map(|alloc| alloc.bytes.len())
    }

    /// Get the byte width of a primitive element type for slice length computation.
    ///
    /// Part of #3495: Helper for const slice length recording.
    pub(in crate::codegen_ay::chc::decl) fn const_elem_byte_width(
        elem_ty: rustc_public::ty::Ty,
    ) -> Option<usize> {
        match elem_ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => Some(1),
            TyKind::RigidTy(RigidTy::Uint(ut)) => Some((uint_ty_to_bitvec_width(ut) / 8) as usize),
            TyKind::RigidTy(RigidTy::Int(it)) => Some((int_ty_to_bitvec_width(it) / 8) as usize),
            TyKind::RigidTy(RigidTy::Char) => Some(4),
            _ => {
                use crate::kani_middle::abi::LayoutOf;
                LayoutOf::new(elem_ty).size_of()
            }
        }
    }
}
