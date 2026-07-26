// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Entry-rule char validity constraints.
//!
//! Part of #3930: Constrains char-typed state variables to valid Unicode
//! scalar values at function entry so memory mirrors always contain valid data.

use ay_bindings::Expr;
use rustc_public::ty::{RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::chc::decl::codegen_decl_flatten::collect_leaf_sorts;

use super::ChcCtx;
use super::codegen_types::CodegenTypes;

/// Extension trait for char validity constraints on entry rules.
#[allow(dead_code)] // Caller import in codegen_rules_entry.rs staged separately
pub(in crate::codegen_ay::chc) trait EntryCharValidity {
    fn collect_char_validity_constraints(&self, constraints: &mut Vec<Expr>);
}

impl<'tcx, 'body> EntryCharValidity for ChcCtx<'tcx, 'body> {
    fn collect_char_validity_constraints(&self, constraints: &mut Vec<Expr>) {
        let locals = self.body.locals();

        for (local_idx, local_decl) in locals.iter().enumerate() {
            if local_idx == 0 {
                continue;
            }
            let Some(base_state_idx) = self.try_state_idx_for_local(local_idx) else {
                continue;
            };
            match local_decl.ty.kind() {
                TyKind::RigidTy(RigidTy::Char) => {
                    self.constrain_char_var(constraints, base_state_idx, local_idx, "direct");
                }
                TyKind::RigidTy(RigidTy::Adt(def, args))
                    if self.flatten.flattened_tuple_locals.contains(&local_idx)
                        && def.variants().len() == 1 =>
                {
                    collect_adt_char_fields(
                        self,
                        constraints,
                        base_state_idx,
                        local_idx,
                        def,
                        args,
                    );
                }
                TyKind::RigidTy(RigidTy::Tuple(tys))
                    if self.flatten.flattened_tuple_locals.contains(&local_idx) =>
                {
                    for (i, ty) in tys.iter().enumerate() {
                        if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Char)) {
                            self.constrain_char_var(
                                constraints,
                                base_state_idx + i,
                                local_idx,
                                "tuple",
                            );
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

#[allow(dead_code)] // Caller import in codegen_rules_entry.rs staged separately
impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn constrain_char_var(
        &self,
        constraints: &mut Vec<Expr>,
        state_idx: usize,
        local_idx: usize,
        kind: &str,
    ) {
        if let Some((name, sort)) = self.state_var_mgr.state_vars.get(state_idx) {
            let var = Expr::var(&**name, sort.clone());
            if let Some(guard) = char_validity_expr(var) {
                constraints.push(guard);
                debug!(local_idx, name = %name, kind, "entry_rule: char validity (#3930)");
            }
        }
    }
}

/// Walks ADT fields and constrains char-typed leaves.
#[allow(dead_code)] // Caller import in codegen_rules_entry.rs staged separately
fn collect_adt_char_fields(
    ctx: &ChcCtx<'_, '_>,
    constraints: &mut Vec<Expr>,
    base_state_idx: usize,
    local_idx: usize,
    def: rustc_public::ty::AdtDef,
    args: rustc_public::ty::GenericArgs,
) {
    let fields = def.variants()[0].fields();
    let mut leaf_offset = 0usize;
    for field_def in &fields {
        let field_ty = field_def.ty_with_args(&args);
        let num_leaves = match ChcCtx::translate_ty(field_ty) {
            Some(s) => collect_leaf_sorts(&s, 0).len(),
            None => 1,
        };
        if matches!(field_ty.kind(), TyKind::RigidTy(RigidTy::Char)) {
            ctx.constrain_char_var(
                constraints,
                base_state_idx + leaf_offset,
                local_idx,
                "struct_field",
            );
        }
        leaf_offset += num_leaves;
    }
}

/// Unicode scalar value validity predicate: `v <= 0xD7FF || (v >= 0xE000 && v <= 0x10FFFF)`.
pub(in crate::codegen_ay::chc) fn char_validity_expr(value: Expr) -> Option<Expr> {
    if let Some(width) = value.sort().bitvec_width() {
        let low = value.clone().bvule(Expr::bitvec_const(0xD7FFu64, width));
        let hi_lo = value.clone().bvuge(Expr::bitvec_const(0xE000u64, width));
        let hi_hi = value.bvule(Expr::bitvec_const(0x10FFFFu64, width));
        Some(low.or(hi_lo.and(hi_hi)))
    } else if value.sort().is_int() {
        let low = value.clone().int_le(Expr::int_const(0xD7FFi64));
        let hi_lo = value.clone().int_ge(Expr::int_const(0xE000i64));
        let hi_hi = value.int_le(Expr::int_const(0x10FFFFi64));
        Some(low.or(hi_lo.and(hi_hi)))
    } else {
        None
    }
}
