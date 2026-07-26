// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Unit-aware multi-constructor enum flattening helpers.

use ay_bindings::Sort;
use rustc_abi::VariantIdx as InternalVariantIdx;
use rustc_public::rustc_internal;
use rustc_public::ty::{AdtKind, RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::chc::codegen_ctx::clusters::EnumBvLayout;

use super::ChcCtx;
use super::codegen_decl_flatten::{collect_leaf_sorts, enum_tag_bits, is_recursively_flattenable};
use super::codegen_types::CodegenTypes;

const OMITTED_FIELD_SLOT: usize = usize::MAX;

fn unify_enum_leaf_sorts(existing: &Sort, candidate: &Sort) -> Option<Sort> {
    if existing.is_bitvec() && candidate.is_bitvec() {
        let lhs = existing.bitvec_width()?;
        let rhs = candidate.bitvec_width()?;
        return Some(Sort::bitvec(lhs.max(rhs)));
    }
    if existing.is_bool() && candidate.is_bool() {
        return Some(Sort::bool());
    }
    if existing.is_int() && candidate.is_int() {
        return Some(Sort::int());
    }
    if (existing.is_bool() && candidate.is_bitvec() && candidate.bitvec_width() == Some(1))
        || (candidate.is_bool() && existing.is_bitvec() && existing.bitvec_width() == Some(1))
    {
        return Some(Sort::bool());
    }
    None
}

pub(in crate::codegen_ay::chc) fn unit_aware_multi_ctor_enum_layout<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    local_ty: rustc_public::ty::Ty,
) -> Option<(EnumBvLayout, Vec<Sort>)> {
    let TyKind::RigidTy(RigidTy::Adt(def, args)) = local_ty.kind() else {
        return None;
    };
    if def.kind() != AdtKind::Enum || def.variants().len() < 2 {
        return None;
    }

    let mut ctor_field_slots: Vec<Vec<usize>> = Vec::new();
    let mut ctor_leaf_counts: Vec<usize> = Vec::new();
    let mut all_ctor_leaves: Vec<Vec<Sort>> = Vec::new();

    for variant in def.variants() {
        let mut field_slots = Vec::new();
        let mut ctor_leaves = Vec::new();
        for field in variant.fields() {
            let field_ty = field.ty_with_args(&args);
            // Part of #3994: detect ALL zero-sized types, not just `()`.
            // Empty structs like `struct ZeroSized;` are ZST but don't match
            // the empty-tuple pattern. Use the layout to check size == 0.
            let field_is_unit =
                field_ty.layout().ok().map_or(false, |l| l.shape().size.bytes() == 0);
            if field_is_unit {
                field_slots.push(OMITTED_FIELD_SLOT);
                continue;
            }

            let field_sort = ChcCtx::translate_ty(field_ty)?;
            if !is_recursively_flattenable(&field_sort, 0) {
                return None;
            }

            field_slots.push(ctor_leaves.len());
            ctor_leaves.extend(collect_leaf_sorts(&field_sort, 0));
        }
        ctor_leaf_counts.push(ctor_leaves.len());
        ctor_field_slots.push(field_slots);
        all_ctor_leaves.push(ctor_leaves);
    }

    let max_payload_slots = ctor_leaf_counts.iter().copied().max().unwrap_or(0);
    if max_payload_slots == 0 {
        return None;
    }

    let mut unified_sorts = Vec::with_capacity(max_payload_slots);
    for pos in 0..max_payload_slots {
        let mut sort_at_pos: Option<Sort> = None;
        for ctor_leaves in &all_ctor_leaves {
            if let Some(candidate) = ctor_leaves.get(pos) {
                sort_at_pos = Some(match sort_at_pos {
                    None => candidate.clone(),
                    Some(ref existing) => unify_enum_leaf_sorts(existing, candidate)?,
                });
            }
        }
        unified_sorts.push(sort_at_pos?);
    }

    let num_constructors = def.variants().len();
    let layout = EnumBvLayout {
        num_constructors,
        tag_bits: enum_tag_bits(num_constructors),
        ctor_field_slot: ctor_field_slots,
        max_payload_slots,
        discriminants: {
            let idef = rustc_internal::internal(ctx.tcx, def);
            (0..num_constructors)
                .map(|i| {
                    idef.discriminant_for_variant(ctx.tcx, InternalVariantIdx::from_usize(i)).val
                        as u64
                })
                .collect()
        },
    };
    Some((layout, unified_sorts))
}

pub(in crate::codegen_ay::chc) fn try_flatten_unit_aware_multi_ctor_enum<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    local_idx: usize,
    in_name: &str,
    local_ty: rustc_public::ty::Ty,
) -> bool {
    let Some((layout, unified_sorts)) = unit_aware_multi_ctor_enum_layout(ctx, local_ty) else {
        return false;
    };

    let tag_sort =
        if layout.num_constructors == 2 { Sort::bool() } else { Sort::bitvec(layout.tag_bits) };
    let mut all_sorts = Vec::with_capacity(1 + layout.max_payload_slots);
    all_sorts.push(tag_sort);
    all_sorts.extend(unified_sorts.into_iter().map(|sort| ctx.lift_bv_to_int_if_enabled(sort)));
    ctx.flatten_local_nfield(local_idx, in_name, &all_sorts, None);
    ctx.flatten.enum_bv_layouts.insert(local_idx, layout.clone());
    debug!(
        local_idx,
        ty = ?local_ty,
        num_constructors = layout.num_constructors,
        tag_bits = layout.tag_bits,
        max_payload = layout.max_payload_slots,
        total_state_vars = 1 + layout.max_payload_slots,
        "CHC: unit-aware BV-flattened multi-ctor enum"
    );
    true
}
