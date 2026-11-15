// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Keep construction checks before ownership exists, including when a later
//! unused address expression does not survive the compiler's MIR passes.

use super::*;
use crate::codegen_ay::shared::native_box_raw::{
    native_bmc_box_drop_value, native_bmc_box_from_raw, native_bmc_box_into_raw,
    native_thin_global_box_pointee,
};
use rustc_public::mir::Place;

impl StatementCodegen<'_, '_, '_> {
    pub(in crate::codegen_ay::statement) fn is_native_box_target(&self, ty: Ty) -> bool {
        if !cfg!(all(trust_toolchain, version("1.101"))) {
            return false;
        }
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else { return false };
        crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(
            self.ctx.tcx,
            rustc_internal::internal(self.ctx.tcx, def.def_id()),
            &["boxed", "Box"],
        )
    }

    pub(in crate::codegen_ay::statement) fn codegen_box_construction_cast(
        &mut self,
        operand: &Operand,
        target: Ty,
    ) -> Option<Expr> {
        let result = (|| {
            let pointee = native_thin_global_box_pointee(self.ctx.tcx, target)?;
            let source = operand.ty(self.body.locals()).ok()?;
            if LayoutOf::new(source).size_of()? != LayoutOf::new(target).size_of()? {
                return None;
            }
            let original = self.codegen_operand(operand)?;
            let value = self.box_pointer_value(&original)?;
            if Self::infer_sort_from_ty(target).as_ref() != Some(value.sort()) {
                return None;
            }
            if matches!(source.kind(), TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_)))
                && matches!(value.value(), ExprValue::BitVecConst { .. })
                && self.ctx.box_pointer_origin(&value).is_none()
            {
                self.ctx.record_box_numeric_address(value.clone());
            }
            let checks = self.native_box_pointer_checks(&value, pointee)?;
            if !self.is_native_box_target(source) && LayoutOf::new(pointee).size_of()? != 0 {
                // from_raw requires the original Global allocation, not just
                // readable bytes in an interior subobject. An observed release
                // is positive custody evidence; absent/ambiguous custody is
                // refused rather than reported as an ownership counterexample.
                let mut roots = HashSet::new();
                let mut pending = vec![&value];
                let mut budget = BUDGET;
                while let Some(part) = pending.pop() {
                    budget = budget.checked_sub(1)?;
                    if let Some(BoxPointerOrigin::Allocation(index)) =
                        self.ctx.box_pointer_origin(part)
                    {
                        roots.insert(index);
                    }
                    pending.extend(part.children());
                }
                if roots.len() == 1 {
                    let index = *roots.iter().next()?;
                    let allocation = self.ctx.native_box_allocation(index)?;
                    let layout = LayoutOf::new(pointee);
                    let known_invalid = checks.iter().any(|check| {
                        if !bounded_box_formula(check) {
                            return false;
                        }
                        use trust_mc_core::chc_const_prop::eval::try_eval_to_bool;
                        match check.value() {
                            ExprValue::Implies(antecedent, consequent) => {
                                try_eval_to_bool(antecedent) == Some(true)
                                    && try_eval_to_bool(consequent) == Some(false)
                            }
                            _ => try_eval_to_bool(check) == Some(false),
                        }
                    }) || allocation
                        .alive
                        .as_ref()
                        .is_some_and(|alive| matches!(alive.value(), ExprValue::BoolConst(false)));
                    // These are admission facts, not additional UB claims.
                    // If native metadata itself already fails, its precise
                    // failure remains reportable without inventing ownership.
                    if !known_invalid {
                        let exact_layout = allocation.size == layout.size_of()? as u64
                            && allocation.align == layout.align_of()? as u64;
                        let at_base = value.clone().eq(allocation.pointer.clone());
                        if !exact_layout
                            || !bounded_box_formula(&at_base)
                            || trust_mc_core::chc_const_prop::eval::try_eval_to_bool(&at_base)
                                != Some(true)
                            || !self
                                .ctx
                                .claim_released_native_box(index, self.store_path_condition())
                        {
                            return None;
                        }
                    }
                } else if !roots.is_empty()
                    || !(LayoutOf::new(pointee).size_of()? == 0
                        || matches!(value.value(),ExprValue::BitVecConst{value,..} if value==&0.into()))
                {
                    return None;
                }
            }
            Some((original, checks))
        })();
        let Some((value, checks)) = result else {
            self.ctx.unsupported_with_fallback(
                "BoxConstructionValidity",
                "native thin Global Box representation or source pointer validity is unavailable",
            );
            return None;
        };
        for check in checks {
            self.record_violation_guarded_with_message(
                check.not(),
                "box_deref_validity",
                Some("Box construction source validity".into()),
            );
        }
        Some(value)
    }

    pub(in crate::codegen_ay::statement) fn try_native_box_transfer_call(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
    ) -> bool {
        let instance = (|| {
            let TyKind::RigidTy(RigidTy::FnDef(def, generics)) =
                func.ty(self.body.locals()).ok()?.kind()
            else {
                return None;
            };
            Instance::resolve(def, &generics).ok()
        })();
        let Some(instance) = instance else { return false };
        if let Some(input) = native_bmc_box_drop_value(self.ctx.tcx, &instance) {
            let [value] = args else { return false };
            let (Operand::Copy(place) | Operand::Move(place)) = value else { return false };
            let output = instance.ty().kind().fn_sig().unwrap().skip_binder().output();
            if place.ty(self.body.locals()).ok() != Some(input)
                || destination.ty(self.body.locals()).ok() != Some(output)
            {
                return false;
            }
            if !self.try_native_box_drop(place) {
                return false;
            }
            if let Some(sort) = Self::infer_sort_from_ty(output) {
                self.assign_value_to_place(
                    destination,
                    Expr::datatype_constructor("Unit", "Unit_mk", vec![], sort),
                );
            } else {
                self.ctx.unsupported_with_fallback(
                    "BoxDropReturn",
                    "native unit return sort unavailable",
                );
            }
            return true;
        }
        if let Some((input, output)) = native_bmc_box_into_raw(self.ctx.tcx, &instance) {
            let [value] = args else { return false };
            if value.ty(self.body.locals()).ok() != Some(input)
                || destination.ty(self.body.locals()).ok() != Some(output)
            {
                return false;
            }
            // Construction and release carry the same native pointer validity;
            // release changes ownership only and does not free the allocation.
            if let Some(pointer) = self.codegen_box_construction_cast(value, input) {
                let has_storage = native_thin_global_box_pointee(self.ctx.tcx, input)
                    .and_then(|pointee| LayoutOf::new(pointee).size_of())
                    .is_some_and(|size| size != 0);
                if has_storage && let Some(resolved) = self.box_pointer_value(&pointer) {
                    self.ctx.release_native_box(&resolved, self.store_path_condition());
                }
                self.assign_value_to_place(destination, pointer);
            } else {
                self.codegen_symbolic_result(destination);
            }
            return true;
        }
        let Some((output, _)) = native_bmc_box_from_raw(self.ctx.tcx, &instance) else {
            return false;
        };
        let [pointer] = args else { return false };
        let signature = instance.ty().kind().fn_sig().unwrap().skip_binder();
        if signature.inputs() != [pointer.ty(self.body.locals()).ok().unwrap_or(output)]
            || destination.ty(self.body.locals()).ok() != Some(output)
        {
            return false;
        }
        if let Some(value) = self.codegen_box_construction_cast(pointer, output) {
            self.assign_value_to_place(destination, value);
        } else {
            self.codegen_symbolic_result(destination);
        }
        true
    }
}
