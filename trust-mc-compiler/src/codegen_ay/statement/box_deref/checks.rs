// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

impl StatementCodegen<'_, '_, '_> {
    pub(in crate::codegen_ay::statement) fn native_box_pointer_checks(
        &self,
        pointer: &Expr,
        pointee: Ty,
    ) -> Option<Vec<Expr>> {
        let value = pointer.clone();
        if value.sort().bitvec_width() != Some(64) || !bounded_box_formula(&value) {
            return None;
        }
        let layout = LayoutOf::new(pointee);
        let size = u64::try_from(layout.size_of()?).ok()?;
        let align = u64::try_from(layout.align_of()?).ok()?;
        if !align.is_power_of_two() {
            return None;
        }
        let inhabited = self.native_box_pointee_inhabited(pointee)?;
        let mut scan = vec![&value];
        let mut seen = HashSet::new();
        let mut scan_budget = BUDGET;
        while let Some(part) = scan.pop() {
            scan_budget = scan_budget.checked_sub(1)?;
            if !seen.insert(node(part)) {
                continue;
            }
            if self.ctx.is_erased_box_address(part) {
                return None;
            }
            scan.extend(part.children());
        }
        let mut checks =
            vec![value.clone().ne(Expr::bitvec_const(0u64, 64)), Expr::bool_const(inhabited)];
        let mut pending = vec![(value.clone(), Expr::bool_const(true), 0usize)];
        let mut budget = BUDGET;
        while let Some((pointer, branch, depth)) = pending.pop() {
            budget = budget.checked_sub(1)?;
            if depth > 64 {
                return None;
            }
            let origin = self.ctx.box_pointer_origin(&pointer);
            let zero = matches!(pointer.value(), ExprValue::BitVecConst { value, .. } if value == &0.into());
            match origin {
                Some(BoxPointerOrigin::Allocation(index)) => {
                    let allocation = self.ctx.native_box_allocation(index)?;
                    if allocation.align < align {
                        return None;
                    }
                    // Outside a nonzero object's extent, abstract stride
                    // addresses do not decide whether a derived ZST pointer's
                    // physical address wrapped to null. The actual base itself
                    // remains known non-null, even after deallocation.
                    if size == 0 && node(&value) != node(&allocation.pointer) {
                        return None;
                    }
                    let offset = value.clone().bvsub(allocation.pointer.clone());
                    checks.push(
                        branch.clone().implies(
                            offset
                                .bvurem(Expr::bitvec_const(align, 64))
                                .eq(Expr::bitvec_const(0u64, 64)),
                        ),
                    );
                    if size != 0 {
                        let alive = allocation.alive.clone()?;
                        if !bounded_box_formula(&alive) {
                            return None;
                        }
                        checks.push(branch.clone().implies(alive));
                        checks.push(
                            branch.clone().implies(value.clone().bvuge(allocation.pointer.clone())),
                        );
                        let end = value.clone().zero_extend(1).bvadd(Expr::bitvec_const(size, 65));
                        let extent = allocation
                            .pointer
                            .clone()
                            .zero_extend(1)
                            .bvadd(Expr::bitvec_const(allocation.size, 65));
                        checks.push(branch.implies(end.bvule(extent)));
                    }
                }
                Some(BoxPointerOrigin::Numeric) if size == 0 || zero => {
                    checks.push(
                        branch.implies(
                            value
                                .clone()
                                .bvurem(Expr::bitvec_const(align, 64))
                                .eq(Expr::bitvec_const(0u64, 64)),
                        ),
                    );
                }
                _ if zero => {}
                _ => match pointer.value() {
                    ExprValue::BvAdd(left, right) | ExprValue::BvSub(left, right) => {
                        // Numeric offset terms may not themselves carry another
                        // allocation address. Exposed addresses already refused
                        // above; no sort-based reinterpretation grants origin.
                        let mut scan = vec![right];
                        let mut seen = HashSet::new();
                        while let Some(part) = scan.pop() {
                            budget = budget.checked_sub(1)?;
                            if !seen.insert(node(part)) {
                                continue;
                            }
                            if matches!(
                                self.ctx.box_pointer_origin(part),
                                Some(BoxPointerOrigin::Allocation(_))
                            ) {
                                return None;
                            }
                            scan.extend(part.children());
                        }
                        pending.push((left.clone(), branch, depth + 1));
                    }
                    ExprValue::Ite { cond: condition, then_expr, else_expr } => {
                        pending.push((
                            then_expr.clone(),
                            branch.clone().and(condition.clone()),
                            depth + 1,
                        ));
                        pending.push((
                            else_expr.clone(),
                            branch.and(condition.clone().not()),
                            depth + 1,
                        ));
                    }
                    _ => return None,
                },
            }
        }
        Some(checks)
    }
}
