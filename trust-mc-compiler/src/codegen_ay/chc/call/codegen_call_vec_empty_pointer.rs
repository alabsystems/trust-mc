// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The held native RawVec zero-capacity representation has no provenance and
//! the declared element's alignment as its numerical address.

use super::ChcCtx;
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::Expr;
use rustc_public::mir::Operand;
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};
use rustc_public::{CrateDef, rustc_internal};

impl ChcCtx<'_, '_> {
    pub(in crate::codegen_ay::chc) fn native_zero_capacity_vec_pointer(
        &self,
        callee: Option<&Operand>,
        ty: Ty,
        capacity: &Expr,
    ) -> Option<Expr> {
        if !cfg!(all(trust_toolchain, version("1.101")))
            || self.int_lift
            || Self::const_usize_from_expr(capacity) != Some(0)
        {
            return None;
        }
        let TyKind::RigidTy(RigidTy::FnDef(function, _)) =
            callee?.ty(self.body.locals()).ok()?.kind()
        else {
            return None;
        };
        let function = rustc_internal::internal(self.tcx, function.def_id());
        if !crate::kani_middle::std_abstraction::is_sysroot_alloc_definition(self.tcx, function)
            || !["vec_new", "vec_with_capacity"]
                .iter()
                .any(|name| self.tcx.is_diagnostic_item(rustc_span::Symbol::intern(name), function))
        {
            return None;
        }
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = self.resolve_body_ty(ty).kind() else {
            return None;
        };
        if !crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(
            self.tcx,
            rustc_internal::internal(self.tcx, def.def_id()),
            &["vec", "Vec"],
        ) {
            return None;
        }
        let GenericArgKind::Type(element) = args.0.first()? else { return None };
        let layout = self.resolve_body_ty(*element).layout().ok()?.shape();
        // ZST capacity/dangling dereferences require their separate semantics.
        if !layout.is_sized() || layout.size.bytes() == 0 {
            return None;
        }
        let alignment = u32::try_from(
            crate::kani_middle::abi::LayoutOf::new(self.resolve_body_ty(*element)).align_of()?,
        )
        .ok()?;
        if !alignment.is_power_of_two() {
            return None;
        }
        // Object zero denotes no allocation, not a newly live heap object.
        // Keep the constructor's existing validity invalidation for this ID.
        Some(Expr::bitvec_const(u64::from(alignment), POINTER_WIDTH))
    }
}
