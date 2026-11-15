// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Native thin Box dereference casts return their validity obligations with
//! their value. The value-only inline cast API deliberately cannot use this.

use ay_bindings::{Expr, ExprValue};
use rustc_public::ty::{GenericArgKind, RigidTy, Ty, TyKind};
use std::collections::{HashMap, HashSet};

use super::ChcCtx;
use crate::codegen_ay::chc::decl::codegen_types::CodegenTypes;
use crate::codegen_ay::chc::expr::codegen_expr_heap::{
    obj_size_in, obj_size_out, obj_valid_in, obj_valid_out,
};
use crate::codegen_ay::chc::heap::stack_address::OBJECT_ID_LIMIT;
use crate::codegen_ay::shared::native_box_raw::native_thin_box_raw_pointer_field;

#[must_use]
pub(in crate::codegen_ay::chc) struct CheckedBoxDeref {
    pub(in crate::codegen_ay::chc) value: Expr,
    pub(in crate::codegen_ay::chc) checks: Vec<Expr>,
}

const BOX_CHECK_EXPR_BUDGET: usize = 16_384;

fn node_id(expression: &Expr) -> usize {
    std::ptr::from_ref(expression.value()) as usize
}

fn mentions_mutable_output(expression: &Expr) -> Option<bool> {
    let mut pending = vec![expression];
    let mut visited = HashSet::new();
    let mut budget = BOX_CHECK_EXPR_BUDGET;
    while let Some(node) = pending.pop() {
        budget = budget.checked_sub(1)?;
        if !visited.insert(node_id(node)) {
            continue;
        }
        if matches!(node.value(), ExprValue::Var { name } if name.ends_with("__out")) {
            return Some(true);
        }
        pending.extend(node.children());
    }
    Some(false)
}

/// The legacy pointer evaluator is recursive and does not memoize shared
/// compound terms. Refuse those inputs before calling it on this path.
pub(in crate::codegen_ay::chc) fn legacy_pointer_tree_is_bounded(expression: &Expr) -> bool {
    let mut pending = vec![(expression, 0usize)];
    let mut visited = HashSet::new();
    let mut budget = BOX_CHECK_EXPR_BUDGET;
    while let Some((node, depth)) = pending.pop() {
        let Some(remaining) = budget.checked_sub(1) else {
            return false;
        };
        budget = remaining;
        if depth > 128 {
            return false;
        }
        if !visited.insert(node_id(node)) && node.children().next().is_some() {
            return false;
        }
        pending.extend(node.children().map(|child| (child, depth + 1)));
    }
    true
}

/// Rewrite shared expressions once per node, without recursive tree
/// expansion or structural equality of potentially exponential DAGs.
pub(in crate::codegen_ay::chc) fn freeze_outputs(
    expression: &Expr,
    frozen: &HashMap<String, Expr>,
) -> Option<Expr> {
    let mut pending = vec![(expression.clone(), false)];
    let mut memo = HashMap::<usize, Expr>::new();
    let mut budget = BOX_CHECK_EXPR_BUDGET;
    while let Some((node, expanded)) = pending.pop() {
        budget = budget.checked_sub(1)?;
        let id = node_id(&node);
        if memo.contains_key(&id) {
            continue;
        }
        if let ExprValue::Var { name } = node.value() {
            memo.insert(id, frozen.get(name).cloned().unwrap_or(node));
        } else if !expanded {
            pending.push((node.clone(), true));
            pending.extend(node.children().cloned().map(|child| (child, false)));
        } else {
            let children: Vec<_> = node
                .children()
                .map(|child| memo.get(&node_id(child)).cloned())
                .collect::<Option<_>>()?;
            let changed =
                node.children().zip(&children).any(|(old, new)| node_id(old) != node_id(new));
            let rewritten = if changed {
                if !node.value().is_known_variant() {
                    return None;
                }
                ay_bindings::rebuild_with_children(&node, children)
            } else {
                node
            };
            memo.insert(id, rewritten);
        }
    }
    memo.remove(&node_id(expression))
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Compare the native operand and target under the same normalization
    /// and region erasure that Rule A applies to an instantiated field.
    pub(in crate::codegen_ay::chc) fn normalized_box_ty(&self, ty: Ty) -> Option<Ty> {
        #[cfg(all(trust_toolchain, version("1.101")))]
        {
            use rustc_middle::ty::{TypingEnv, Unnormalized};
            let internal = rustc_public::rustc_internal::internal(self.tcx, ty);
            return std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let normalized = self
                    .tcx
                    .try_normalize_erasing_regions(
                        TypingEnv::fully_monomorphized(),
                        Unnormalized::new_wip(internal),
                    )
                    .ok()?;
                Some(rustc_public::rustc_internal::stable(normalized))
            }))
            .ok()
            .flatten();
        }
        #[cfg(not(all(trust_toolchain, version("1.101"))))]
        {
            let _ = ty;
            None
        }
    }

    fn box_pointee_is_inhabited(&self, pointee: Ty) -> Option<bool> {
        #[cfg(all(trust_toolchain, version("1.101")))]
        {
            use rustc_middle::ty::{TypingEnv, Unnormalized};
            let env = TypingEnv::fully_monomorphized();
            let ty = rustc_public::rustc_internal::internal(self.tcx, pointee);
            return std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let normalized =
                    self.tcx.try_normalize_erasing_regions(env, Unnormalized::new_wip(ty)).ok()?;
                Some(normalized.is_opsem_inhabited(self.tcx, env))
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
    /// Freeze a metadata lane at this statement, before a later inline free
    /// can replace its pending definition. Multiple uncomposed definitions or
    /// output-dependent right sides have no unambiguous snapshot here.
    fn box_metadata_lane_at_cast(&self, input: Expr, output: Expr, modified: bool) -> Option<Expr> {
        let definitions: Vec<_> = self
            .heap_state
            .pending_updates
            .iter()
            .filter_map(|constraint| match constraint.value() {
                ExprValue::Eq(left, right) if *left == output => Some(right),
                _ => None,
            })
            .collect();
        match definitions.as_slice() {
            [] if !modified => Some(input),
            [value] if !mentions_mutable_output(value)? => Some((*value).clone()),
            _ => None,
        }
    }
    /// A static encoding ID cannot authorize a stale allocation generation at
    /// a cyclic host callsite. Inline replay and true fresh generations are a
    /// separate model; this route refuses when that distinction is unavailable.
    pub(in crate::codegen_ay::chc) fn native_box_allocation_is_acyclic(
        &self,
        allocation: u32,
    ) -> bool {
        let Some(&site) = self.heap_state.alloc_block.get(&allocation) else {
            return false;
        };
        let Some(block) = self.body.blocks.get(site) else {
            return false;
        };
        let mut pending = block.terminator.successors();
        let mut visited = HashSet::new();
        let mut budget = BOX_CHECK_EXPR_BUDGET;
        while let Some(next) = pending.pop() {
            let Some(left) = budget.checked_sub(1) else { return false };
            budget = left;
            if next == site {
                return false;
            }
            if visited.insert(next) {
                let Some(block) = self.body.blocks.get(next) else {
                    return false;
                };
                pending.extend(block.terminator.successors());
            }
        }
        true
    }

    /// The metadata identity comes only from an actual compiler Unsize of the
    /// exact native Box type. The logical numeric vtable ID is not itself a
    /// pointer, and zero is a valid first ID in a trait's dispatch table.
    pub(in crate::codegen_ay::chc) fn checked_native_dyn_pointer(
        &mut self,
        value: Expr,
        origin: &crate::codegen_ay::chc::call::native_dyn_origin::NativeDynOrigin,
    ) -> Option<CheckedBoxDeref> {
        if value.sort().bitvec_width() != Some(64)
            || mentions_mutable_output(&value)?
            || !legacy_pointer_tree_is_bounded(&value)
            || !self.native_box_allocation_is_acyclic(origin.allocation)
            || crate::codegen_ay::chc::dyn_coercion::resolve_dyn_target_vtable_id(
                self,
                origin.dynamic,
                origin.concrete,
            ) != Some(origin.vtable)
        {
            return None;
        }
        if let Some((allocation, offset)) = Self::try_extract_constant_addr(&value)
            && (allocation != origin.allocation || offset != 0)
        {
            return None;
        }
        let address =
            Expr::bitvec_const(origin.allocation, 32).concat(Expr::bitvec_const(0u32, 32));
        let target = Ty::from_rigid_kind(RigidTy::RawPtr(
            origin.concrete,
            rustc_public::mir::Mutability::Mut,
        ));
        // Recover the original native allocation address from its typed birth;
        // never extend element bits or substitute another same-sort owner.
        self.checked_native_box_deref(origin.carrier, target, address)
    }

    pub(in crate::codegen_ay::chc) fn checked_native_box_deref_with_origin(
        &mut self,
        source: Ty,
        target: Ty,
        value: Expr,
        origin: Option<&crate::codegen_ay::chc::call::native_dyn_origin::NativeDynOrigin>,
    ) -> Option<CheckedBoxDeref> {
        let source = self.normalized_box_ty(self.resolve_body_ty(source))?;
        let target = self.normalized_box_ty(self.resolve_body_ty(target))?;
        let TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) = target.kind() else {
            return None;
        };
        if !matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
            return self.checked_native_box_deref(source, target, value);
        }
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = source.kind() else {
            return None;
        };
        crate::codegen_ay::shared::native_box_raw::native_box_raw_pointer_field(
            self.tcx, def, &args,
        )?;
        let origin = origin?;
        if args.0.as_slice() != [GenericArgKind::Type(pointee)]
            || origin.dynamic != pointee
            || value.sort() != &Self::translate_ty(source)?
            || value.sort() != &Self::translate_ty(target)?
        {
            return None;
        }
        self.checked_native_dyn_pointer(value, origin)
    }

    /// Model only an authenticated native carrier with its actual pointee,
    /// exact pointer sort, and a known allocation alignment. Unknown/fat
    /// layouts and provenance retain the caller's FailClose refusal.
    pub(in crate::codegen_ay::chc) fn checked_native_box_deref(
        &mut self,
        source_ty: Ty,
        target_ty: Ty,
        value: Expr,
    ) -> Option<CheckedBoxDeref> {
        let source_ty = self.normalized_box_ty(self.resolve_body_ty(source_ty))?;
        let target_ty = self.normalized_box_ty(self.resolve_body_ty(target_ty))?;
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = source_ty.kind() else {
            return None;
        };
        let TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) = target_ty.kind() else {
            return None;
        };
        let (_, pointer_ty) = native_thin_box_raw_pointer_field(self.tcx, def, &args)?;
        if args.0.as_slice() != [GenericArgKind::Type(pointee)]
            || value.sort() != &Self::translate_ty(pointer_ty)?
            || value.sort() != &Self::translate_ty(target_ty)?
            || value.sort().bitvec_width() != Some(64)
            || mentions_mutable_output(&value)?
            || !legacy_pointer_tree_is_bounded(&value)
        {
            return None;
        }
        let size = u32::try_from(self.get_type_size(pointee)?).ok()?;
        let align = self.get_type_align(pointee)?;
        if !align.is_power_of_two() || align > u64::from(u32::MAX) {
            return None;
        }
        let (object, offset) = self.split_pointer(&value)?;
        let id = Self::const_obj_id_u32(&object)?;
        if id >= OBJECT_ID_LIMIT {
            return None;
        }
        // An object-free ZST pointer can be dangling. Every other admitted
        // base must have the allocator's real alignment guarantee; object bits
        // alone make no promise about its physical address alignment.
        if id != 0 && self.heap_state.heap_alloc_alignment(id)? < align {
            return None;
        }
        let mut checks = vec![value.clone().eq(Expr::bitvec_const(0u64, 64)).not()];
        if !self.box_pointee_is_inhabited(pointee)? {
            checks.push(Expr::bool_const(false));
        }
        checks.push(
            offset.clone().bvurem(Expr::bitvec_const(align, 32)).eq(Expr::bitvec_const(0u32, 32)),
        );
        if size != 0 {
            if id == 0 {
                // The null object owns no bytes, even at a nonzero offset.
                checks.push(Expr::bool_const(false));
            } else {
                let valid_at_cast = self.box_metadata_lane_at_cast(
                    obj_valid_in(),
                    obj_valid_out(),
                    self.heap_state.is_obj_valid_modified(),
                )?;
                let size_at_cast = self.box_metadata_lane_at_cast(
                    obj_size_in(),
                    obj_size_out(),
                    self.heap_state.is_obj_size_modified(),
                )?;
                let frozen = HashMap::from([
                    ("obj_valid__out".to_owned(), valid_at_cast.clone()),
                    ("obj_size__out".to_owned(), size_at_cast.clone()),
                ]);
                // Retain the established integer-to-pointer provenance debts
                // and access accounting before adding the strict Box bounds.
                for check in self.heap_access_checks(value.clone(), pointee) {
                    checks.push(freeze_outputs(&check, &frozen)?);
                }
                checks.push(valid_at_cast.select(object.clone()));
                // Widen before addition: the full pointee must fit, without
                // wraparound or the generic zero-allocation-size exemption.
                let end = offset.zero_extend(32).bvadd(Expr::bitvec_const(size, 64));
                let extent = size_at_cast.select(object).zero_extend(32);
                checks.push(end.bvule(extent));
                self.mark_heap_metadata_read();
            }
        }
        for check in &checks {
            if mentions_mutable_output(check)? {
                return None;
            }
        }
        Some(CheckedBoxDeref { value, checks })
    }

    /// Global deallocation must use the exact allocation layout. A larger
    /// live object can hold a T, but freeing it with T's smaller layout is UB.
    pub(in crate::codegen_ay::chc) fn checked_native_box_deallocation(
        &mut self,
        source: Ty,
        target: Ty,
        value: Expr,
    ) -> Option<CheckedBoxDeref> {
        let target = self.normalized_box_ty(self.resolve_body_ty(target))?;
        let TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) = target.kind() else { return None };
        let size = u32::try_from(self.get_type_size(pointee)?).ok()?;
        if size == 0 {
            return None;
        }
        let mut checked = self.checked_native_box_deref(source, target, value)?;
        let (object, _) = self.split_pointer(&checked.value)?;
        let extent = self.box_metadata_lane_at_cast(
            obj_size_in(),
            obj_size_out(),
            self.heap_state.is_obj_size_modified(),
        )?;
        checked.checks.push(extent.select(object).eq(Expr::bitvec_const(size, 32)));
        Some(checked)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_bindings::Sort;

    #[test]
    fn shared_box_check_dags_are_scanned_and_rewritten_once() {
        for name in ["offset", "offset__out"] {
            let mut expression = Expr::var(name, Sort::bitvec(64));
            for _ in 0..64 {
                expression = expression.clone().bvadd(expression);
            }
            assert_eq!(mentions_mutable_output(&expression), Some(name.ends_with("__out")));
            assert!(!legacy_pointer_tree_is_bounded(&expression));
            let untouched = freeze_outputs(&expression, &HashMap::new()).unwrap();
            assert_eq!(node_id(&untouched), node_id(&expression));
            let rewritten = freeze_outputs(
                &expression,
                &HashMap::from([(name.to_owned(), Expr::bitvec_const(0u64, 64))]),
            )
            .unwrap();
            assert_eq!(mentions_mutable_output(&rewritten), Some(false));
        }
    }

    #[test]
    fn deep_box_check_expressions_refuse_before_recursive_evaluation() {
        let mut expression = Expr::var("offset", Sort::bitvec(64));
        for _ in 0..160 {
            expression = expression.bvadd(Expr::bitvec_const(1u64, 64));
        }
        assert!(!legacy_pointer_tree_is_bounded(&expression));
    }
}
