// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Range-type predicates for slice indexing dispatch.
//! Part of #3981.

use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, TyKind};
use rustc_span::sym;

use crate::codegen_ay::stubs::StubKind;

use super::super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn operand_has_exact_core_adt(
        tcx: TyCtxt<'tcx>,
        op: &Operand,
        locals: &[rustc_public::mir::LocalDecl],
        paths: &[&str],
    ) -> bool {
        let Ok(ty) = op.ty(locals) else { return false };
        matches!(
            ty.kind(),
            TyKind::RigidTy(RigidTy::Adt(def, _)) if {
                let def_id = rustc_internal::internal(tcx, def.def_id());
                let path = tcx.def_path_str(def_id);
                tcx.crate_name(def_id.krate).as_str() == "core"
                    && paths.contains(&path.as_str())
            }
        )
    }

    pub(in crate::codegen_ay::chc) fn is_range_type_operand(
        tcx: TyCtxt<'tcx>,
        op: &Operand,
        locals: &[rustc_public::mir::LocalDecl],
    ) -> bool {
        Self::operand_has_exact_core_adt(
            tcx,
            op,
            locals,
            &[
                "core::ops::range::Range",
                "core::ops::range::RangeInclusive",
                "core::range::Range",
                "core::range::RangeInclusive",
                "std::ops::Range",
                "std::ops::RangeInclusive",
                "std::range::Range",
                "std::range::RangeInclusive",
            ],
        )
    }

    pub(in crate::codegen_ay::chc) fn is_range_inclusive_operand(
        tcx: TyCtxt<'tcx>,
        op: &Operand,
        locals: &[rustc_public::mir::LocalDecl],
    ) -> bool {
        Self::operand_has_exact_core_adt(
            tcx,
            op,
            locals,
            &[
                "core::ops::range::RangeInclusive",
                "core::range::RangeInclusive",
                "std::ops::RangeInclusive",
                "std::range::RangeInclusive",
            ],
        )
    }

    pub(in crate::codegen_ay::chc) fn is_range_full_operand(
        tcx: TyCtxt<'tcx>,
        op: &Operand,
        locals: &[rustc_public::mir::LocalDecl],
    ) -> bool {
        Self::operand_has_exact_core_adt(
            tcx,
            op,
            locals,
            &["core::ops::range::RangeFull", "std::ops::RangeFull"],
        )
    }

    pub(in crate::codegen_ay::chc) fn is_range_from_operand(
        tcx: TyCtxt<'tcx>,
        op: &Operand,
        locals: &[rustc_public::mir::LocalDecl],
    ) -> bool {
        Self::operand_has_exact_core_adt(
            tcx,
            op,
            locals,
            &[
                "core::ops::range::RangeFrom",
                "core::range::RangeFrom",
                "std::ops::RangeFrom",
                "std::range::RangeFrom",
            ],
        )
    }

    pub(in crate::codegen_ay::chc) fn is_range_to_operand(
        tcx: TyCtxt<'tcx>,
        op: &Operand,
        locals: &[rustc_public::mir::LocalDecl],
    ) -> bool {
        Self::operand_has_exact_core_adt(
            tcx,
            op,
            locals,
            &[
                "core::ops::range::RangeTo",
                "core::ops::range::RangeToInclusive",
                "std::ops::RangeTo",
                "std::ops::RangeToInclusive",
            ],
        )
    }

    pub(in crate::codegen_ay::chc) fn is_range_to_inclusive_operand(
        tcx: TyCtxt<'tcx>,
        op: &Operand,
        locals: &[rustc_public::mir::LocalDecl],
    ) -> bool {
        Self::operand_has_exact_core_adt(
            tcx,
            op,
            locals,
            &["core::ops::range::RangeToInclusive", "std::ops::RangeToInclusive"],
        )
    }

    fn is_authenticated_index_carrier(
        &self,
        op: &Operand,
        locals: &[rustc_public::mir::LocalDecl],
    ) -> bool {
        let Ok(mut ty) = op.ty(locals) else { return false };
        for _ in 0..8 {
            ty = self.resolve_body_ty(ty);
            match ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _) | RigidTy::RawPtr(inner, _)) => {
                    ty = inner;
                }
                TyKind::RigidTy(RigidTy::Slice(_) | RigidTy::Array(..) | RigidTy::Str) => {
                    return true;
                }
                TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                    let def_id = rustc_internal::internal(self.tcx, def.def_id());
                    let path = self.tcx.def_path_str(def_id);
                    return self.tcx.crate_name(def_id.krate).as_str() == "alloc"
                        && matches!(path.as_str(), "alloc::vec::Vec" | "std::vec::Vec");
                }
                _ => return false,
            }
        }
        false
    }

    fn function_implements_exact_trait_method(
        &self,
        direct_def_id: rustc_hir::def_id::DefId,
        trait_def_id: rustc_hir::def_id::DefId,
        allowed_names: &[&str],
    ) -> bool {
        let direct_trait_item =
            self.tcx.opt_associated_item(direct_def_id).and_then(|item| item.trait_item_def_id());
        self.tcx.associated_item_def_ids(trait_def_id).iter().copied().any(|trait_method| {
            allowed_names.contains(&self.tcx.item_name(trait_method).as_str())
                && (direct_def_id == trait_method || direct_trait_item == Some(trait_method))
        })
    }

    pub(in crate::codegen_ay::chc) fn authenticated_core_slice_index_method_args<'a>(
        &self,
        func: &Operand,
        args: &'a [Operand],
        locals: &[rustc_public::mir::LocalDecl],
        allowed_names: &[&str],
    ) -> Option<(&'a Operand, &'a Operand)> {
        if args.len() != 2 {
            return None;
        }
        let func_ty = func.ty(locals).ok()?;
        let TyKind::RigidTy(RigidTy::FnDef(fn_def, _)) = func_ty.kind() else {
            return None;
        };
        let direct_def_id = rustc_internal::internal(self.tcx, fn_def.def_id());
        // Trait affiliation is not implementation authority: coherence permits
        // downstream implementations for some local index/self combinations.
        // Only standard-library implementations can enter the semantic stub.
        if !matches!(self.tcx.crate_name(direct_def_id.krate).as_str(), "core" | "alloc" | "std") {
            return None;
        }
        let slice_index_trait = self.tcx.get_diagnostic_item(sym::SliceIndex)?;
        if !self.function_implements_exact_trait_method(
            direct_def_id,
            slice_index_trait,
            allowed_names,
        ) {
            return None;
        }
        let (index, source) = (&args[0], &args[1]);
        self.is_authenticated_index_carrier(source, locals).then_some((source, index))
    }

    /// Authenticate the authority-bearing slice `index` stubs by definition
    /// identity, argument order, and source carrier. The stub registry also has
    /// intentionally broad suffix matches for compatibility; those matches are
    /// routing hints and must not by themselves authorize identity, bounds, or
    /// length facts.
    pub(in crate::codegen_ay::chc) fn authenticated_core_slice_index_args<'a>(
        &self,
        func: &Operand,
        args: &'a [Operand],
    ) -> Option<(StubKind, &'a Operand, &'a Operand)> {
        if args.len() != 2 {
            return None;
        }
        let func_ty = func.ty(self.body.locals()).ok()?;
        let TyKind::RigidTy(RigidTy::FnDef(fn_def, _)) = func_ty.kind() else {
            return None;
        };
        let direct_def_id = rustc_internal::internal(self.tcx, fn_def.def_id());
        if !matches!(self.tcx.crate_name(direct_def_id.krate).as_str(), "core" | "alloc" | "std") {
            return None;
        }
        let (stub, source, index) = if self.function_implements_exact_trait_method(
            direct_def_id,
            self.tcx.lang_items().index_trait()?,
            &["index"],
        ) {
            (StubKind::IndexIndex, &args[0], &args[1])
        } else if self.function_implements_exact_trait_method(
            direct_def_id,
            self.tcx.lang_items().index_mut_trait()?,
            &["index_mut"],
        ) {
            (StubKind::IndexMut, &args[0], &args[1])
        } else if let Some(slice_index_trait) = self.tcx.get_diagnostic_item(sym::SliceIndex)
            && self.function_implements_exact_trait_method(
                direct_def_id,
                slice_index_trait,
                &["index", "index_mut"],
            )
        {
            let trait_method = self
                .tcx
                .opt_associated_item(direct_def_id)
                .and_then(|item| item.trait_item_def_id())
                .unwrap_or(direct_def_id);
            let stub = if self.tcx.item_name(trait_method).as_str() == "index_mut" {
                StubKind::IndexMut
            } else {
                StubKind::SliceIndexIndex
            };
            (stub, &args[1], &args[0])
        } else {
            return None;
        };
        if !self.is_authenticated_index_carrier(source, self.body.locals()) {
            return None;
        }

        Some((stub, source, index))
    }

    pub(in crate::codegen_ay::chc) fn authenticated_core_range_full_source<'a>(
        &self,
        func: &Operand,
        args: &'a [Operand],
    ) -> Option<&'a Operand> {
        let (_, source, index) = self.authenticated_core_slice_index_args(func, args)?;
        Self::is_range_full_operand(self.tcx, index, self.body.locals()).then_some(source)
    }

    pub(in crate::codegen_ay::chc) fn operand_local(op: &Operand) -> Option<usize> {
        match op {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        }
    }
}
