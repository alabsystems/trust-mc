// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! BMC native Box casts carry source validity as guarded safety properties.

use super::{IntoOption, LayoutOf, StatementCodegen};
use crate::codegen_ay::context::BoxPointerOrigin;
use crate::codegen_ay::shared::native_box_raw::native_thin_box_raw_pointer_field;
use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::Operand;
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};
use rustc_public::{CrateDef, rustc_internal};
use std::collections::{HashMap, HashSet};

const BUDGET: usize = 4096;
mod boundaries;
mod checks;
mod compiler_checks;
mod construction;
mod lifecycle;
pub(in crate::codegen_ay::statement) use compiler_checks::compiler_pointer_check_casts;
#[cfg(all(test, feature = "compiler-corpus-tests", trust_toolchain, version("1.101")))]
mod tests;
fn node(value: &Expr) -> usize {
    std::ptr::from_ref(value.value()) as usize
}

/// Bound DAG work and intrinsic depth before recursive constant evaluation or
/// formula serialization; shared subterms do not conceal a longer path.
fn bounded_box_formula(value: &Expr) -> bool {
    let mut pending = vec![(value, false)];
    let mut heights = HashMap::<usize, usize>::new();
    let mut budget = BUDGET;
    while let Some((value, expanded)) = pending.pop() {
        let Some(left) = budget.checked_sub(1) else { return false };
        budget = left;
        if heights.contains_key(&node(value)) {
            continue;
        }
        if !expanded {
            pending.push((value, true));
            pending.extend(value.children().map(|child| (child, false)));
        } else {
            let Some(height) = value
                .children()
                .map(|child| heights.get(&node(child)).copied())
                .collect::<Option<Vec<_>>>()
                .and_then(|children| children.into_iter().max().unwrap_or(0).checked_add(1))
            else {
                return false;
            };
            if height > 64 {
                return false;
            }
            heights.insert(node(value), height);
        }
    }
    true
}

impl StatementCodegen<'_, '_, '_> {
    /// Only exact SSA definitions in this frame: no suffix stripping, cached
    /// first producer or layout-name reconstruction. Memoize expression DAGs.
    pub(super) fn box_pointer_value(&self, value: &Expr) -> Option<Expr> {
        let mut pending = vec![(value.clone(), false, 0usize)];
        let mut memo = HashMap::<usize, Expr>::new();
        let mut budget = BUDGET;
        while let Some((value, expanded, depth)) = pending.pop() {
            budget = budget.checked_sub(1)?;
            if depth > 64 {
                return None;
            }
            let id = node(&value);
            if memo.contains_key(&id) {
                continue;
            }
            if self.ctx.box_pointer_origin(&value).is_some() {
                memo.insert(id, value);
                continue;
            }
            if let ExprValue::Ite { cond, then_expr, else_expr } = value.value()
                && bounded_box_formula(cond)
                && self.current_path_condition.as_ref().is_none_or(bounded_box_formula)
            {
                let facts = self.ctx.byte_memory_facts(&self.ssa_concrete_values);
                let truth =
                    Expr::ite(cond.clone(), Expr::bool_const(true), Expr::bool_const(false));
                let folded = facts.fold_assuming(&truth, self.current_path_condition.as_ref());
                let chosen = match folded.value() {
                    ExprValue::BoolConst(true) => Some(then_expr),
                    ExprValue::BoolConst(false) => Some(else_expr),
                    _ => None,
                };
                if let Some(chosen) = chosen {
                    if expanded {
                        memo.insert(id, memo.get(&node(chosen))?.clone());
                    } else {
                        pending.push((value.clone(), true, depth));
                        pending.push((chosen.clone(), false, depth + 1));
                    }
                    continue;
                }
            }
            if let ExprValue::Var { name } = value.value()
                && let Some(definition) = self.ssa_concrete_values.get(name)
                && definition.sort() == value.sort()
            {
                if expanded {
                    memo.insert(id, memo.get(&node(definition))?.clone());
                } else {
                    pending.push((value.clone(), true, depth));
                    pending.push((definition.clone(), false, depth + 1));
                }
            } else if !expanded {
                pending.push((value.clone(), true, depth));
                pending.extend(value.children().cloned().map(|child| (child, false, depth + 1)));
            } else {
                let children = value
                    .children()
                    .map(|child| memo.get(&node(child)).cloned())
                    .collect::<Option<Vec<_>>>()?;
                let changed =
                    value.children().zip(&children).any(|(old, new)| node(old) != node(new));
                let resolved = if changed {
                    if !value.value().is_known_variant() {
                        return None;
                    }
                    ay_bindings::rebuild_with_children(&value, children)
                } else {
                    value
                };
                memo.insert(id, resolved);
            }
        }
        memo.remove(&node(value))
    }

    pub(super) fn box_pointer_carrier(&self, ty: Ty) -> bool {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(..) | RigidTy::Ref(..)) => true,
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                let id = rustc_internal::internal(self.ctx.tcx, def.def_id());
                native_thin_box_raw_pointer_field(self.ctx.tcx, def, &args).is_some()
                    || crate::kani_middle::std_abstraction::is_sysroot_core_definition_at(
                        self.ctx.tcx,
                        id,
                        &["ptr", "non_null", "NonNull"],
                    )
                    || crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(
                        self.ctx.tcx,
                        id,
                        &["boxed", "Box"],
                    )
            }
            _ => false,
        }
    }

    /// A numeric reinterpretation retains the exact bit equation but not the
    /// native pointer-production tag. There is no reverse scan of equalities
    /// that could grant that authority to an integer later cast back.
    pub(super) fn box_cast_transport(
        &mut self,
        operand: &Operand,
        target: Ty,
        value: Expr,
    ) -> Option<Expr> {
        if !cfg!(all(trust_toolchain, version("1.101"))) {
            return Some(value);
        }
        let source = operand.ty(self.body.locals()).into_option()?;
        let scalar = |ty: Ty| {
            matches!(
                ty.kind(),
                TyKind::RigidTy(
                    RigidTy::Bool
                        | RigidTy::Char
                        | RigidTy::Int(_)
                        | RigidTy::Uint(_)
                        | RigidTy::Float(_)
                )
            )
        };
        if scalar(source) && scalar(target) {
            return Some(value);
        }
        let Some(resolved) = self.box_pointer_value(&value) else {
            self.ctx.unsupported_with_fallback(
                "BoxPointerTransport",
                "bounded pointer-origin resolution exhausted",
            );
            return Some(value);
        };
        if !self.box_pointer_carrier(target) {
            let mut pending = vec![&resolved];
            let mut seen = HashSet::new();
            let mut budget = BUDGET;
            let mut carries_allocation = false;
            while let Some(part) = pending.pop() {
                budget = budget.checked_sub(1)?;
                if !seen.insert(node(part)) {
                    continue;
                }
                carries_allocation |= matches!(
                    self.ctx.box_pointer_origin(part),
                    Some(BoxPointerOrigin::Allocation(_))
                );
                pending.extend(part.children());
            }
            if carries_allocation {
                if self.checked_compiler_numeric_pointer(source, &resolved) {
                    return Some(value);
                }
                self.ctx.unsupported_with_fallback(
                    "BoxNumericAddress",
                    "the native allocation's physical numeric address is not modeled",
                );
                let name = self.ctx.fresh_name("box_numeric_transport");
                let numeric = self.ctx.declare_var(&name, value.sort().clone());
                self.ctx.assert(numeric.clone().eq(value));
                self.ctx.record_erased_box_address(numeric.clone());
                return Some(numeric);
            }
        } else if matches!(source.kind(), TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_)))
            && matches!(resolved.value(), ExprValue::BitVecConst { .. })
            && self.ctx.box_pointer_origin(&resolved).is_none()
        {
            // An actual integer literal's bits are a physical numeric address,
            // never an allocation just because they equal its model address.
            self.ctx.record_box_numeric_address(resolved.clone());
            return Some(resolved);
        }
        Some(value)
    }

    pub(in crate::codegen_ay::statement) fn native_box_new_layout(
        &self,
        func: &Operand,
        args: &[Operand],
    ) -> Option<(u64, u64)> {
        if !cfg!(all(trust_toolchain, version("1.101"))) {
            return None;
        }
        if crate::kani_middle::transform::unit_has_stubs() {
            return None;
        }
        if crate::codegen_ay::shared::native_box_raw::native_bmc_has_custom_global_allocator(
            self.ctx.tcx,
        ) {
            return None;
        }
        let TyKind::RigidTy(RigidTy::FnDef(def, generics)) =
            func.ty(self.body.locals()).ok()?.kind()
        else {
            return None;
        };
        let instance = Instance::resolve(def, &generics).ok()?;
        if matches!(instance.kind, InstanceKind::Virtual { .. }) {
            return None;
        }
        let id = rustc_internal::internal(self.ctx.tcx, instance.def.def_id());
        if id.is_local() || self.ctx.tcx.item_name(id).as_str() != "new" {
            return None;
        }
        let signature = instance.ty().kind().fn_sig()?.skip_binder();
        let [payload] = signature.inputs() else { return None };
        let [argument] = args else { return None };
        if argument.ty(self.body.locals()).ok()? != *payload {
            return None;
        }
        let TyKind::RigidTy(RigidTy::Adt(output, output_args)) = signature.output().kind() else {
            return None;
        };
        if !crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(
            self.ctx.tcx,
            rustc_internal::internal(self.ctx.tcx, output.def_id()),
            &["boxed", "Box"],
        ) || output_args.0.first() != Some(&GenericArgKind::Type(*payload))
        {
            return None;
        }
        if id.krate != rustc_internal::internal(self.ctx.tcx, output.def_id()).krate {
            return None;
        }
        let owner = self.ctx.tcx.parent(id);
        if !matches!(self.ctx.tcx.def_kind(owner), rustc_hir::def::DefKind::Impl { .. })
            || crate::rustc_compat::impl_opt_trait_ref(self.ctx.tcx, owner).is_some()
        {
            return None;
        }
        let self_ty = crate::rustc_compat::skip_normalization(
            self.ctx.tcx.type_of(owner).instantiate_identity(),
        );
        if !matches!(self_ty.kind(), rustc_middle::ty::Adt(adt, _)
            if adt.did() == rustc_internal::internal(self.ctx.tcx, output.def_id()))
        {
            return None;
        }
        if crate::codegen_ay::shared::native_box_raw::native_thin_global_box_pointee(
            self.ctx.tcx,
            signature.output(),
        ) != Some(*payload)
        {
            return None;
        }
        let layout = LayoutOf::new(*payload);
        let size = u64::try_from(layout.size_of()?).ok()?;
        let align = u64::try_from(layout.align_of()?).ok()?;
        (align.is_power_of_two()).then_some((size, align))
    }

    pub(super) fn codegen_native_box_deref(
        &mut self,
        operand: &Operand,
        target: Ty,
    ) -> Option<Expr> {
        let result = self.checked_bmc_box_deref(operand, target);
        let Some((value, checks)) = result else {
            self.ctx.unsupported_with_fallback(
                "BoxDerefTransmute",
                "native Box validity or pointer origin unavailable",
            );
            return None;
        };
        for check in checks {
            self.record_violation_guarded(check.not(), "box_deref_validity");
        }
        Some(value)
    }

    fn checked_bmc_box_deref(
        &mut self,
        operand: &Operand,
        target: Ty,
    ) -> Option<(Expr, Vec<Expr>)> {
        if crate::kani_middle::transform::unit_has_stubs() {
            return None;
        }
        let source = operand.ty(self.body.locals()).ok()?;
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = source.kind() else { return None };
        let TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) = target.kind() else { return None };
        native_thin_box_raw_pointer_field(self.ctx.tcx, def, &args)?;
        if args.0.as_slice() != [GenericArgKind::Type(pointee)]
            || LayoutOf::new(target).size_of()? != 8
            || LayoutOf::new(source).size_of()? != LayoutOf::new(target).size_of()?
        {
            return None;
        }
        let original = self.codegen_operand(operand)?;
        let value = self.box_pointer_value(&original)?;
        if value.sort() != &Self::infer_sort_from_ty(target)?
            || value.sort().bitvec_width() != Some(64)
        {
            return None;
        }
        let checks = self.native_box_pointer_checks(&value, pointee)?;
        Some((original, checks))
    }

    fn native_box_pointee_inhabited(&self, pointee: Ty) -> Option<bool> {
        #[cfg(all(trust_toolchain, version("1.101")))]
        {
            use rustc_middle::ty::{TypingEnv, Unnormalized};
            let env = TypingEnv::fully_monomorphized();
            let ty = rustc_internal::internal(self.ctx.tcx, pointee);
            return std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let normalized = self
                    .ctx
                    .tcx
                    .try_normalize_erasing_regions(env, Unnormalized::new_wip(ty))
                    .ok()?;
                Some(normalized.is_opsem_inhabited(self.ctx.tcx, env))
            }))
            .ok()
            .flatten();
        }
        #[cfg(not(all(trust_toolchain, version("1.101"))))]
        {
            let _ = pointee;
            None
        }
    }
}
