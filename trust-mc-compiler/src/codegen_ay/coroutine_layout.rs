// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Shared coroutine sort/layout helpers for CHC and BMC codegen.

use ay_bindings::Sort;
use rustc_abi::{TagEncoding, Variants};
use rustc_middle::ty::layout::{LayoutCx, LayoutOf as _, TyAndLayout};
use rustc_middle::ty::{CoroutineArgs, CoroutineArgsExt, TyCtxt, TypingEnv};
use rustc_public::rustc_internal;
use rustc_public::ty::{RigidTy, Ty, TyKind};

use crate::codegen_ay::names::{
    coroutine_direct_fields_name, coroutine_discriminant_field_name, coroutine_field_index,
    coroutine_field_name, coroutine_sort_name, coroutine_variant_field_name, struct_sort,
};
use crate::rustc_public_bridge::IndexedVal;

#[derive(Clone)]
pub(crate) struct CoroutineFieldInfo {
    pub(crate) name: String,
    pub(crate) sort: Sort,
    pub(crate) is_discriminant: bool,
}

impl CoroutineFieldInfo {
    /// The MIR field index this view field models, recovered from the field
    /// NAME (`coroutine_field_{idx}`); `None` for the discriminant.
    ///
    /// View fields are ordered by increasing byte offset (`build_view_info`),
    /// which need not match MIR field-index order — pairing MIR operands or
    /// projections with view fields positionally silently hits the wrong slot
    /// whenever two fields swap positions. Always map through this
    /// name-derived index.
    pub(crate) fn mir_field_idx(&self) -> Option<usize> {
        if self.is_discriminant { None } else { coroutine_field_index(&self.name) }
    }
}

#[derive(Clone)]
pub(crate) struct CoroutineViewInfo {
    pub(crate) root_field_name: String,
    pub(crate) sort: Sort,
    pub(crate) fields: Vec<CoroutineFieldInfo>,
}

impl CoroutineViewInfo {
    /// Map MIR aggregate operands (indexed by MIR field index) onto this
    /// view's offset-ordered fields, by field NAME.
    ///
    /// Returns one entry per view field, aligned with `self.fields`:
    /// `None` for the discriminant slot, `Some(mir_idx)` for value fields.
    /// Entries may carry `mir_idx >= operand_count` (fields with no
    /// corresponding operand, e.g. promoted saved locals); callers choose
    /// their existing missing-operand behavior (fail-closed or havoc).
    ///
    /// Returns `None` (fail-closed) if any value field's name does not encode
    /// a MIR index, if two fields map to the same operand, or if any operand
    /// is never consumed (excess operands) — the same shapes the previous
    /// positional zip rejected.
    pub(crate) fn operand_map(&self, operand_count: usize) -> Option<Vec<Option<usize>>> {
        let mut used = vec![false; operand_count];
        let mut map = Vec::with_capacity(self.fields.len());
        for field in &self.fields {
            if field.is_discriminant {
                map.push(None);
                continue;
            }
            let mir_idx = field.mir_field_idx()?;
            if let Some(slot) = used.get_mut(mir_idx) {
                if *slot {
                    return None; // duplicate name→operand mapping — malformed view
                }
                *slot = true;
            }
            map.push(Some(mir_idx));
        }
        used.iter().all(|&consumed| consumed).then_some(map)
    }
}

#[derive(Clone)]
pub(crate) struct CoroutineSortInfo {
    pub(crate) root_sort: Sort,
    pub(crate) direct_fields: CoroutineViewInfo,
    pub(crate) variants: Vec<CoroutineViewInfo>,
}

pub(crate) fn build_coroutine_sort_info<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty,
    mut translate_sort: impl FnMut(Ty) -> Sort,
) -> Option<CoroutineSortInfo> {
    let TyKind::RigidTy(RigidTy::Coroutine(def, _)) = ty.kind() else {
        return None;
    };

    let internal_ty = rustc_internal::internal(tcx, ty);
    let layout_cx = LayoutCx::new(tcx, TypingEnv::fully_monomorphized());
    let layout = layout_cx.layout_of(internal_ty).ok()?;
    let (discriminant_field_idx, variants) = match &layout.variants {
        Variants::Multiple { tag_encoding: TagEncoding::Direct, tag_field, variants, .. } => {
            (tag_field.as_usize(), variants)
        }
        _ => return None,
    };

    let root_name = coroutine_sort_name(def.0.to_index());
    let direct_fields = build_view_info(
        &layout_cx,
        layout,
        format!("{root_name}::DirectFields"),
        coroutine_direct_fields_name().to_owned(),
        Some(discriminant_field_idx),
        &mut translate_sort,
    );

    let mut root_fields = vec![(direct_fields.root_field_name.clone(), direct_fields.sort.clone())];
    let mut variant_views = Vec::new();
    for variant_idx in variants.indices() {
        let variant_name = CoroutineArgs::variant_name(variant_idx).to_string();
        let view = build_view_info(
            &layout_cx,
            layout.for_variant(&layout_cx, variant_idx),
            format!("{root_name}::{variant_name}"),
            coroutine_variant_field_name(&variant_name),
            None,
            &mut translate_sort,
        );
        root_fields.push((view.root_field_name.clone(), view.sort.clone()));
        variant_views.push(view);
    }

    Some(CoroutineSortInfo {
        root_sort: struct_sort(root_name, root_fields),
        direct_fields,
        variants: variant_views,
    })
}

fn build_view_info<'tcx>(
    layout_cx: &LayoutCx<'tcx>,
    layout: TyAndLayout<'tcx>,
    view_sort_name: String,
    root_field_name: String,
    discriminant_field_idx: Option<usize>,
    translate_sort: &mut impl FnMut(Ty) -> Sort,
) -> CoroutineViewInfo {
    let fields: Vec<CoroutineFieldInfo> = layout
        .fields
        .index_by_increasing_offset()
        .map(|field_idx| {
            let field_layout = layout.field(layout_cx, field_idx);
            let is_discriminant = discriminant_field_idx == Some(field_idx);
            let field_name = if is_discriminant {
                coroutine_discriminant_field_name().to_owned()
            } else {
                coroutine_field_name(field_idx)
            };
            let stable_ty = rustc_internal::stable(field_layout.ty);
            CoroutineFieldInfo {
                name: field_name,
                sort: translate_sort(stable_ty),
                is_discriminant,
            }
        })
        .collect();

    let view_sort = struct_sort(
        &view_sort_name,
        fields.iter().map(|field| (field.name.as_str(), field.sort.clone())),
    );
    CoroutineViewInfo { root_field_name, sort: view_sort, fields }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn field(name: &str, is_discriminant: bool) -> CoroutineFieldInfo {
        CoroutineFieldInfo { name: name.to_owned(), sort: Sort::bv64(), is_discriminant }
    }

    /// Direct-fields view with fields in the REVERSE of MIR index order —
    /// the offset-reordered shape `build_view_info` produces.
    fn scrambled_view(fields: Vec<CoroutineFieldInfo>) -> CoroutineViewInfo {
        let sort = struct_sort(
            "Coroutine_T::DirectFields",
            fields.iter().map(|f| (f.name.as_str(), f.sort.clone())),
        );
        CoroutineViewInfo { root_field_name: "direct_fields".to_owned(), sort, fields }
    }

    #[test]
    fn mir_field_idx_recovers_index_from_name() {
        assert_eq!(field("coroutine_field_0", false).mir_field_idx(), Some(0));
        assert_eq!(field("coroutine_field_17", false).mir_field_idx(), Some(17));
        // Discriminant never maps to an operand, regardless of name.
        assert_eq!(field(coroutine_discriminant_field_name(), true).mir_field_idx(), None);
        // Non-index-encoding names fail closed.
        assert_eq!(field("case", false).mir_field_idx(), None);
    }

    #[test]
    fn operand_map_pairs_offset_ordered_fields_by_name() {
        let view = scrambled_view(vec![
            field("coroutine_field_1", false),
            field(coroutine_discriminant_field_name(), true),
            field("coroutine_field_0", false),
        ]);
        // Operand 1 feeds slot 0, discriminant gets None, operand 0 feeds slot 2.
        assert_eq!(view.operand_map(2), Some(vec![Some(1), None, Some(0)]));
    }

    #[test]
    fn operand_map_rejects_excess_operands() {
        let view = scrambled_view(vec![
            field("coroutine_field_0", false),
            field(coroutine_discriminant_field_name(), true),
        ]);
        assert_eq!(view.operand_map(2), None);
    }

    #[test]
    fn operand_map_allows_fields_without_operands() {
        // Promoted saved local (coroutine_field_2) has no aggregate operand;
        // the map still succeeds and carries the out-of-range index for the
        // caller to fail-close or havoc per its existing policy.
        let view = scrambled_view(vec![
            field("coroutine_field_1", false),
            field(coroutine_discriminant_field_name(), true),
            field("coroutine_field_2", false),
            field("coroutine_field_0", false),
        ]);
        assert_eq!(view.operand_map(2), Some(vec![Some(1), None, Some(2), Some(0)]));
    }

    #[test]
    fn operand_map_fails_closed_on_unnamed_value_field() {
        let view = scrambled_view(vec![
            field("not_a_coroutine_field", false),
            field(coroutine_discriminant_field_name(), true),
        ]);
        assert_eq!(view.operand_map(0), None);
    }
}
