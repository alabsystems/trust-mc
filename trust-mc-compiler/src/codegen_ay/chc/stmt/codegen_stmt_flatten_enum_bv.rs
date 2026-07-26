// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Enum BV-flattened destination value builders for CHC encoding.
//!
//! Extracted from `codegen_stmt_flatten_constrain.rs` for 500-LOC compliance.
//! Provides three related methods:
//! - `build_enum_bv_destination_values`: DT result → per-slot values via ITE
//! - `build_enum_bv_bitvec_destination_values`: BV result → per-slot values via extract
//! - `build_canonical_enum_bv_bridge_value`: either path → single concat'd BV

use ay_bindings::{Expr, ExprValue};

use super::codegen_ctx::clusters::EnumBvLayout;
use super::{ChcCtx, chc_fresh_name, declare_pending_var};
use crate::codegen_ay::chc::decl::codegen_decl_flatten::byte_size_to_bv_width;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn build_enum_bv_destination_values(
        &mut self,
        dest_local: usize,
        result_expr: &Expr,
    ) -> Option<Vec<Option<Expr>>> {
        let layout = self.flatten.enum_bv_layouts.get(&dest_local)?.clone();
        let dt = result_expr.sort().datatype_sort()?;
        if dt.constructors.len() != layout.num_constructors {
            return None;
        }

        if let Some(values) =
            self.build_enum_bv_constructor_tree_values(dest_local, result_expr, &layout, &dt)
        {
            return Some(values);
        }

        // Part of #3984: Ensure the result DT (and its nested field DTs) are
        // declared. When the destination local is BV-flattened, the DT sort is
        // not in any relation signature, so declare_datatype_sorts() misses it.
        self.declare_datatype_sort_if_needed(result_expr.sort());

        let dt_name = dt.name.clone();
        let tag_expr = if layout.num_constructors == 2 {
            let ctor = dt.constructors.get(1)?;
            result_expr.clone().is_constructor(&dt_name, ctor.name.clone())
        } else {
            let last_idx = layout.num_constructors.checked_sub(1)?;
            let mut tag_expr = Expr::bitvec_const(last_idx as u64, layout.tag_bits);
            for ctor_idx in (0..last_idx).rev() {
                let ctor = dt.constructors.get(ctor_idx)?;
                let is_ctor = result_expr.clone().is_constructor(&dt_name, ctor.name.clone());
                tag_expr = Expr::ite(
                    is_ctor,
                    Expr::bitvec_const(ctor_idx as u64, layout.tag_bits),
                    tag_expr,
                );
            }
            tag_expr
        };

        let vec_idx = self.try_state_idx_for_local(dest_local)?;
        let mut ctor_slot_values =
            vec![vec![None; layout.max_payload_slots]; layout.num_constructors];
        for (ctor_idx, ctor) in dt.constructors.iter().enumerate() {
            for (field_idx, field) in ctor.fields.iter().enumerate() {
                let Some(slot_base) = layout.payload_slot(ctor_idx, field_idx) else {
                    continue;
                };
                let field_expr =
                    result_expr.clone().field_select(&dt_name, &field.name, field.sort.clone());
                let mut leaves = Vec::new();
                super::codegen_stmt_flatten::collect_leaf_exprs(&field_expr, &mut leaves);
                for (leaf_offset, leaf_opt) in leaves.into_iter().enumerate() {
                    let Some(leaf_expr) = leaf_opt else {
                        continue;
                    };
                    let slot_idx = slot_base + leaf_offset;
                    if slot_idx >= layout.max_payload_slots {
                        break;
                    }
                    let (_, out_sort) =
                        self.state_var_mgr.output_state_vars.get(vec_idx + 1 + slot_idx)?;
                    let coerced = Self::coerce_flatten_slot_value(out_sort, leaf_expr)?;
                    ctor_slot_values[ctor_idx][slot_idx] = Some(coerced);
                }
            }
        }

        let mut values = Vec::with_capacity(1 + layout.max_payload_slots);
        values.push(Some(tag_expr));
        for slot_idx in 0..layout.max_payload_slots {
            let (_, out_sort) = self.state_var_mgr.output_state_vars.get(vec_idx + 1 + slot_idx)?;
            let has_value =
                ctor_slot_values.iter().any(|slot_values| slot_values[slot_idx].is_some());
            if !has_value {
                // Part of #3994: zero-init unused payload slots.
                values.push(Self::sort_default_expr(out_sort));
                continue;
            }
            // Part of #3994: zero-default base for ITE chain.
            let mut slot_expr = Self::sort_default_expr(out_sort).unwrap_or_else(|| {
                declare_pending_var(chc_fresh_name("__flat_enum_payload"), out_sort.clone())
            });
            for ctor_idx in (0..layout.num_constructors).rev() {
                let Some(value) = ctor_slot_values[ctor_idx][slot_idx].clone() else {
                    continue;
                };
                let ctor = &dt.constructors[ctor_idx];
                let is_ctor = result_expr.clone().is_constructor(&dt_name, ctor.name.clone());
                slot_expr = Expr::ite(is_ctor, value, slot_expr);
            }
            values.push(Some(slot_expr));
        }

        Some(values)
    }

    fn build_enum_bv_constructor_tree_values(
        &self,
        dest_local: usize,
        result_expr: &Expr,
        layout: &EnumBvLayout,
        dt: &ay_bindings::sort::DatatypeSort,
    ) -> Option<Vec<Option<Expr>>> {
        self.decompose_enum_bv_constructor_tree(dest_local, result_expr, layout, dt)
            .map(|values| values.into_iter().map(Some).collect())
    }

    fn decompose_enum_bv_constructor_tree(
        &self,
        dest_local: usize,
        expr: &Expr,
        layout: &EnumBvLayout,
        dt: &ay_bindings::sort::DatatypeSort,
    ) -> Option<Vec<Expr>> {
        match expr.value() {
            ExprValue::DatatypeConstructor { constructor_name, args, .. } => {
                self.enum_bv_constructor_leaf_values(dest_local, constructor_name, args, layout, dt)
            }
            ExprValue::Ite { cond, then_expr, else_expr } => {
                let then_values =
                    self.decompose_enum_bv_constructor_tree(dest_local, then_expr, layout, dt)?;
                let else_values =
                    self.decompose_enum_bv_constructor_tree(dest_local, else_expr, layout, dt)?;
                if then_values.len() != else_values.len() {
                    return None;
                }
                Some(
                    then_values
                        .into_iter()
                        .zip(else_values)
                        .map(|(then_value, else_value)| {
                            merge_enum_bv_constructor_ite(cond, then_value, else_value)
                        })
                        .collect(),
                )
            }
            _ => None,
        }
    }

    fn enum_bv_constructor_leaf_values(
        &self,
        dest_local: usize,
        constructor_name: &str,
        args: &[Expr],
        layout: &EnumBvLayout,
        dt: &ay_bindings::sort::DatatypeSort,
    ) -> Option<Vec<Expr>> {
        let ctor_idx = dt.constructors.iter().position(|ctor| ctor.name == constructor_name)?;
        let vec_idx = self.try_state_idx_for_local(dest_local)?;
        let mut values = Vec::with_capacity(1 + layout.max_payload_slots);
        values.push(enum_bv_constructor_tag(layout, ctor_idx));

        for slot_idx in 0..layout.max_payload_slots {
            let (_, out_sort) = self.state_var_mgr.output_state_vars.get(vec_idx + 1 + slot_idx)?;
            values.push(Self::sort_default_expr(out_sort)?);
        }

        for (field_idx, arg) in args.iter().enumerate() {
            let Some(slot_base) = layout.payload_slot(ctor_idx, field_idx) else {
                continue;
            };
            let mut leaves = Vec::new();
            super::codegen_stmt_flatten::collect_leaf_exprs(arg, &mut leaves);
            for (leaf_offset, leaf_opt) in leaves.into_iter().enumerate() {
                let Some(leaf_expr) = leaf_opt else {
                    continue;
                };
                let slot_idx = slot_base + leaf_offset;
                if slot_idx >= layout.max_payload_slots {
                    break;
                }
                let (_, out_sort) =
                    self.state_var_mgr.output_state_vars.get(vec_idx + 1 + slot_idx)?;
                values[1 + slot_idx] = Self::coerce_flatten_slot_value(out_sort, leaf_expr)?;
            }
        }

        Some(values)
    }

    pub(in crate::codegen_ay::chc) fn build_enum_bv_bitvec_destination_values(
        &self,
        dest_local: usize,
        result_expr: &Expr,
    ) -> Option<Vec<Option<Expr>>> {
        let layout = self.flatten.enum_bv_layouts.get(&dest_local)?;
        let total_width = result_expr.sort().bitvec_width()?;
        let vec_idx = self.try_state_idx_for_local(dest_local)?;
        let slot_count = 1 + layout.max_payload_slots;
        let mut slot_widths = Vec::with_capacity(slot_count);

        for slot_idx in 0..slot_count {
            let (_, out_sort) = self.state_var_mgr.output_state_vars.get(vec_idx + slot_idx)?;
            let width = if out_sort.is_bool() {
                1
            } else if let Some(w) = out_sort.bitvec_width() {
                w
            } else if out_sort.is_array() {
                // Part of #4022: Array(BV_idx, BV_elem) payload slot (e.g., [u8; 8]).
                // Compute BV-equivalent width from the Rust type's byte size.
                Self::array_payload_bv_width(self.body.locals()[dest_local].ty)?
            } else {
                return None;
            };
            slot_widths.push(width);
        }

        if slot_widths.iter().copied().sum::<u32>() != total_width {
            return None;
        }

        let mut remaining = total_width;
        let mut values = Vec::with_capacity(slot_count);
        for (slot_idx, width) in slot_widths.into_iter().enumerate() {
            let hi = remaining.checked_sub(1)?;
            let lo = remaining.checked_sub(width)?;
            remaining = lo;

            let extracted = result_expr.clone().extract(hi, lo);
            let (_, out_sort) = self.state_var_mgr.output_state_vars.get(vec_idx + slot_idx)?;
            let coerced = Self::coerce_flatten_slot_value(out_sort, extracted)?;
            values.push(Some(coerced));
        }

        Some(values)
    }

    /// Canonical whole-value bridge for BV-flattened enum destinations.
    ///
    /// Converts a Datatype/bitvec call result into the same tag||payload bitvec
    /// shape used by flattened-local whole-place reads, zero-initializing
    /// omitted payload slots for unit/ZST constructors.
    pub(in crate::codegen_ay::chc) fn build_canonical_enum_bv_bridge_value(
        &mut self,
        dest_local: usize,
        result_expr: &Expr,
    ) -> Option<Expr> {
        let values = self
            .build_enum_bv_destination_values(dest_local, result_expr)
            .or_else(|| self.build_enum_bv_bitvec_destination_values(dest_local, result_expr))?;

        values
            .into_iter()
            .map(|value_opt| {
                let value = value_opt?;
                if value.sort().is_bool() {
                    Some(Expr::ite(value, Expr::bitvec_const(1u64, 1), Expr::bitvec_const(0u64, 1)))
                } else if value.sort().is_bitvec() {
                    Some(value)
                } else {
                    None
                }
            })
            .collect::<Option<Vec<_>>>()?
            .into_iter()
            .reduce(|acc, part| acc.concat(part))
    }

    /// Part of #4022: Compute the BV-equivalent bit width for an Array-typed
    /// payload field in a BV-flattened enum. Walks the enum's ADT variants to
    /// find the first Array field and returns its byte_size * 8.
    fn array_payload_bv_width(ty: rustc_public::ty::Ty) -> Option<u32> {
        use rustc_public::ty::{RigidTy, TyKind};
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else { return None };
        for variant in def.variants() {
            for field in variant.fields() {
                let fty = field.ty_with_args(&args);
                if matches!(fty.kind(), TyKind::RigidTy(RigidTy::Array(..))) {
                    let byte_size = fty.layout().ok()?.shape().size.bytes();
                    return Some(byte_size_to_bv_width(byte_size));
                }
            }
        }
        None
    }
}

fn enum_bv_constructor_tag(layout: &EnumBvLayout, ctor_idx: usize) -> Expr {
    if layout.num_constructors == 2 {
        Expr::bool_const(ctor_idx == 1)
    } else {
        Expr::bitvec_const(ctor_idx as u64, layout.tag_bits)
    }
}

fn merge_enum_bv_constructor_ite(cond: &Expr, then_value: Expr, else_value: Expr) -> Expr {
    match (then_value.value(), else_value.value()) {
        (ExprValue::BoolConst(true), ExprValue::BoolConst(false)) => cond.clone(),
        (ExprValue::BoolConst(false), ExprValue::BoolConst(true)) => cond.clone().not(),
        _ => Expr::ite(cond.clone(), then_value, else_value),
    }
}
