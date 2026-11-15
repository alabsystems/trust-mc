// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Deref write propagation for parent datatype containers.
//!
//! When `(*ref).field = value` updates a pointee field, the parent
//! container variable must be reconstructed. Also handles array index
//! prefix extraction for place projections.
//!
//! Extracted from `datatype.rs` — Part of #4206.

use super::{
    AYCtx, Expr, Place, ProjectionElem, SortInner, StatementCodegen, constant_index_offset,
};
use tracing::debug;

/// The INNERMOST (rightmost) projection a derived pointee base name records.
///
/// `ssa_base_name_for_projections` appends one marker per projection, so the
/// LAST marker is the projection that must be undone first when a write landed
/// on the derived name and has to travel back to the storage that holds it.
/// `parent_len` is the byte length of the enclosing place's own base name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::codegen_ay::statement) enum DerivedSlot {
    /// `{parent}_field_{M}`, optionally `{parent}_variant_{V}_field_{M}`.
    Field { parent_len: usize, field_idx: usize, variant: Option<usize> },
    /// `{parent}_idx_by_{L}` — an element at the value of local `L`.
    IndexLocal { parent_len: usize, idx_local: usize },
    /// `{parent}_cidx_{N}` — an element at the constant index `N`.
    IndexConst { parent_len: usize, offset: u64 },
    /// `{parent}_cidx_end_{N}`, `{parent}_subslice_{a}_{b}`: a sub-place this
    /// naming scheme records but the write-back cannot place exactly.
    Unencodable { parent_len: usize },
}

impl DerivedSlot {
    pub(in crate::codegen_ay::statement) fn parent_len(&self) -> usize {
        match self {
            DerivedSlot::Field { parent_len, .. }
            | DerivedSlot::IndexLocal { parent_len, .. }
            | DerivedSlot::IndexConst { parent_len, .. }
            | DerivedSlot::Unencodable { parent_len } => *parent_len,
        }
    }
}

fn all_digits(s: &str) -> bool {
    !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit())
}

/// Parse the rightmost projection marker of a derived base name.
///
/// `None` for a plain local, for a `_deref` / `_cast` alias (which names other
/// storage, not a slot of an aggregate), and for anything whose tail does not
/// parse — a marker that is not the LAST projection never parses, because the
/// markers that follow it are still in the tail.
pub(in crate::codegen_ay::statement) fn last_derived_slot(base: &str) -> Option<DerivedSlot> {
    let mut best: Option<DerivedSlot> = None;
    let mut best_pos = 0usize;
    let mut consider = |pos: usize, slot: DerivedSlot| {
        if best.is_none() || pos > best_pos {
            best_pos = pos;
            best = Some(slot);
        }
    };
    if let Some(pos) = base.rfind("_field_")
        && all_digits(&base[pos + 7..])
        && let Ok(field_idx) = base[pos + 7..].parse::<usize>()
    {
        // A `Downcast` immediately before the field names the variant.
        let before = &base[..pos];
        match before.rfind("_variant_") {
            Some(vpos) if all_digits(&before[vpos + 9..]) => {
                let variant = before[vpos + 9..].parse::<usize>().ok();
                consider(pos, DerivedSlot::Field { parent_len: vpos, field_idx, variant });
            }
            _ => {
                consider(pos, DerivedSlot::Field { parent_len: pos, field_idx, variant: None })
            }
        }
    }
    if let Some(pos) = base.rfind("_idx_by_")
        && all_digits(&base[pos + 8..])
        && let Ok(idx_local) = base[pos + 8..].parse::<usize>()
    {
        consider(pos, DerivedSlot::IndexLocal { parent_len: pos, idx_local });
    }
    if let Some(pos) = base.rfind("_cidx_end_")
        && all_digits(&base[pos + 10..])
    {
        consider(pos, DerivedSlot::Unencodable { parent_len: pos });
    }
    if let Some(pos) = base.rfind("_cidx_")
        && all_digits(&base[pos + 6..])
        && let Ok(offset) = base[pos + 6..].parse::<u64>()
    {
        consider(pos, DerivedSlot::IndexConst { parent_len: pos, offset });
    }
    for marker in ["_subslice_end_", "_subslice_"] {
        if let Some(pos) = base.rfind(marker) {
            let tail = &base[pos + marker.len()..];
            if let Some((a, b)) = tail.split_once('_')
                && all_digits(a)
                && all_digits(b)
            {
                consider(pos, DerivedSlot::Unencodable { parent_len: pos });
            }
        }
    }
    best
}

/// The walk's fail-closed contract, as one decidable predicate.
///
/// A RECOGNISED slot (`last_derived_slot` parsed it) that the walk could not
/// place must leave a recorded fail-closed reason behind. When it did not, the
/// walk records one itself: a silent `None` after a recognised slot is a DROPPED
/// STORE, which is the false-proof shape this walk exists to close.
///
/// `placed` is whether the arm returned a new parent; `before`/`after` are the
/// `unsupported_with_fallback` counter around the arm.
pub(in crate::codegen_ay::statement) fn walk_must_record_fallback(
    placed: bool,
    before: usize,
    after: usize,
) -> bool {
    !placed && after == before
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// When MIR writes through a reference to a datatype field (e.g., `(*_ref).field_1`),
    /// the pointee SSA variable is updated but the parent container state variable is
    /// stale. This method reconstructs the parent by replacing the updated field.
    ///
    /// Also handles struct field references (pointee base with `_field_M` suffix).
    ///
    /// Analogous to `try_propagate_indexed_ref_write_to_array` for arrays.
    pub(super) fn try_propagate_deref_write_to_parent_datatype(
        &mut self,
        pointee_base: &str,
        updated_pointee: &Expr,
        place: &Place,
    ) {
        let mut base = pointee_base.to_owned();
        let mut value = updated_pointee.clone();
        let outer_source = self.derived_write_source.replace(pointee_base.to_owned());
        // `&mut g.buf[i]` names `..._field_1_idx_by_L`: two levels, innermost
        // first. Bounded because every step strips one marker.
        for _ in 0..8 {
            match self.propagate_derived_write_one_level(&base, &value, place) {
                Some((parent_base, parent_value)) => {
                    base = parent_base;
                    value = parent_value;
                }
                None => break,
            }
        }
        self.derived_write_source = outer_source;
    }

    /// Undo ONE projection of a derived pointee name: write `value` back into
    /// the slot `base` denotes of its enclosing place, and return that place's
    /// base name and new value so the caller can continue outwards.
    ///
    /// `None` ends the walk — either `base` names no slot of an enclosing place
    /// (a plain local, a `_deref` alias), or the write-back could not be encoded
    /// exactly, in which case it has ALREADY recorded a fail-closed reason. A
    /// silent `None` after a recognised slot would be a DROPPED STORE, which is
    /// the false-proof shape this walk exists to close.
    fn propagate_derived_write_one_level(
        &mut self,
        base: &str,
        value: &Expr,
        place: &Place,
    ) -> Option<(String, Expr)> {
        let slot = last_derived_slot(base)?;
        let parent_base = base[..slot.parent_len()].to_owned();
        // The contract is ENFORCED, not merely documented: whatever an arm below
        // does, a recognised slot the walk cannot place leaves a recorded
        // reason. Commit 7fe93048b routed `&mut a[i].field` through this walk
        // while three of `propagate_field_write_to_parent`'s four `None` returns
        // were silent, and `let p = &mut a[1].x; *p = 9; assert!(a[1].x == 0)`
        // became a clean SUCCESSFUL proof in BMC (fourth adversarial review,
        // 2026-09-14). The arms record their own precise reasons; this counter
        // check is the backstop that makes a future silent `None` a demotion
        // instead of a dropped store.
        let fallbacks_before = crate::codegen_ay::context::get_unsupported_construct_fallback_count();
        let placed = match slot {
            DerivedSlot::Field { field_idx, variant, .. } => {
                self.propagate_field_write_to_parent(&parent_base, field_idx, variant, value, place)
            }
            DerivedSlot::IndexLocal { idx_local, .. } => {
                self.propagate_element_write_to_parent(&parent_base, Some(idx_local), None, value, place)
            }
            DerivedSlot::IndexConst { offset, .. } => {
                self.propagate_element_write_to_parent(&parent_base, None, Some(offset), value, place)
            }
            DerivedSlot::Unencodable { .. } => {
                // A sub-slice or a from-the-end element: the write landed on a
                // name whose slot in `parent_base` is not known here.
                self.ctx.unsupported_with_fallback(
                    "derived pointee write not propagated",
                    format!("{base}: sub-place cannot be placed in {parent_base}"),
                );
                None
            }
        };
        let fallbacks_after = crate::codegen_ay::context::get_unsupported_construct_fallback_count();
        if walk_must_record_fallback(placed.is_some(), fallbacks_before, fallbacks_after) {
            self.ctx.unsupported_with_fallback(
                "derived pointee write not propagated",
                format!("{base}: slot not placed in {parent_base} and no reason was recorded"),
            );
        }
        placed
    }

    /// `{parent}[_variant_V]_field_M` — rebuild the parent datatype.
    ///
    /// EVERY `None` this returns records a fail-closed reason first. It did not:
    /// a missing parent value, a non-datatype parent sort and a
    /// `datatype_field_update` failure each returned `None` SILENTLY, which the
    /// walk reads as "nothing more to do" and the store is DROPPED. That is the
    /// exact false-proof shape the walk exists to close, and it was live:
    /// `let p = &mut a[1].x; *p = 9; assert!(a[1].x == 0)` was
    /// `VERIFICATION:- SUCCESSFUL` with `[AY:PROOF_QUALIFIERS:clean]` in BMC,
    /// and its safe twin `FAILED [AY:CTREX_CAT:Genuine]`, because
    /// `..._cidx_1_field_0`'s parent `..._cidx_1` is an ELEMENT slot that has no
    /// register of its own (fourth adversarial review of m3/soundness-fixes-2,
    /// 2026-09-14, defect B/D1 — a regression of commit 7fe93048b, which routed
    /// this shape through the walk after removing the array-coercion havoc that
    /// used to demote it).
    fn propagate_field_write_to_parent(
        &mut self,
        parent_base: &str,
        field_idx: usize,
        variant_idx: Option<usize>,
        updated_pointee: &Expr,
        place: &Place,
    ) -> Option<(String, Expr)> {
        // A parent that is itself a recognised slot (an element of an array, a
        // field of a struct) has no register until something writes it, so its
        // CURRENT value is read out of its own enclosing place. That is what
        // lets a field be placed under an element: `..._cidx_1_field_0` rebuilds
        // `..._cidx_1` from the array, updates field 0 in it, and hands the new
        // element to the next level, which stores it back into the array.
        let parent_expr = match self.env_lookup(parent_base).cloned() {
            Some(expr) => expr,
            None => match self.derived_place_current_value(parent_base, place, 0) {
                Some(expr) => expr,
                None => {
                    self.ctx.unsupported_with_fallback(
                        "field pointee write not propagated",
                        format!("{parent_base}: enclosing place has no value"),
                    );
                    return None;
                }
            },
        };
        if parent_expr.sort().is_bitvec()
            && self
                .env_lookup(&crate::codegen_ay::names::discrim_name(parent_base))
                .is_some()
        {
            // A flattened Option-like parent keeps its payload word under the base
            // name and its variant under `{base}.0`. A store to the payload slot
            // `{base}_variant_1_field_0` (`if let Some(x) = &mut o { *x = 5 }`)
            // left the payload word at the old value, and `o == Some(5)` read
            // `Some(4)`: the BMC lane proved `assert!(!(o == Some(5)))`
            // (tools/soundness-duals/negative/review_r18_mutate_then_compare.rs).
            if variant_idx == Some(1) && field_idx == 0 && updated_pointee.sort() == parent_expr.sort()
            {
                let parent_ssa = self.ssa_name_from_base(parent_base, true);
                let parent_var = self.ctx.declare_var(&parent_ssa, parent_expr.sort().clone());
                self.assert_ssa_def(parent_var.clone(), updated_pointee.clone(), parent_base);
                self.env_update(parent_base, parent_var.clone());
                debug!(
                    "propagate_field_write_to_parent: flattened payload -> {}",
                    parent_ssa
                );
                return Some((parent_base.to_owned(), parent_var));
            }
            self.ctx.unsupported_with_fallback(
                "deref_write_flattened_parent",
                format!("{parent_base}: store into a flattened parent not propagated"),
            );
            return None;
        }
        if !parent_expr.sort().is_datatype() {
            self.ctx.unsupported_with_fallback(
                "field pointee write not propagated",
                format!("{parent_base}: enclosing place is not a datatype"),
            );
            return None;
        }

        let Some(new_parent) = Self::datatype_field_update(
            &parent_expr,
            field_idx,
            variant_idx,
            updated_pointee.clone(),
            place,
            self.ctx,
        ) else {
            // `datatype_field_update` records `unsupported`, which demotes
            // NOTHING on its own. The write is dropped here, so the demotion has
            // to be recorded here.
            self.ctx.unsupported_with_fallback(
                "field pointee write not propagated",
                format!("{parent_base}: field {field_idx} not written back"),
            );
            return None;
        };

        let parent_ssa = self.ssa_name_from_base(parent_base, true);
        let parent_var = self.ctx.declare_var(&parent_ssa, parent_expr.sort().clone());
        self.assert_ssa_def(parent_var.clone(), new_parent, parent_base);
        self.env_update(parent_base, parent_var.clone());
        debug!(
            "propagate_field_write_to_parent: -> {} (variant={:?}, field={}) (Part of #3041)",
            parent_ssa, variant_idx, field_idx
        );
        Some((parent_base.to_owned(), parent_var))
    }

    /// The CURRENT value of a derived place name that has no register of its
    /// own, read out of the enclosing place it names a slot of.
    ///
    /// `{parent}_field_M` selects field M of `parent`'s value; `{parent}_cidx_N`
    /// and `{parent}_idx_by_L` select an element of `parent`'s element array.
    /// This is what lets the walk PLACE a field under an element: the element
    /// slot `a_cidx_1` has no register, so its value is rebuilt from the array,
    /// the field is updated in it, and the next level stores the new element
    /// back. Without it the field arm had no parent to rebuild and the store was
    /// dropped.
    ///
    /// `None` for a sub-slice or from-the-end slot, for a name that parses as no
    /// slot, and for any enclosing place that is itself unavailable. Every
    /// caller records a fail-closed reason on `None`; this helper deliberately
    /// records none of its own, so a probe that simply cannot read a value never
    /// demotes a harness by itself.
    fn derived_place_current_value(
        &mut self,
        base: &str,
        place: &Place,
        depth: u32,
    ) -> Option<Expr> {
        if let Some(expr) = self.env_lookup(base) {
            return Some(expr.clone());
        }
        if depth >= 8 {
            return None;
        }
        let slot = last_derived_slot(base)?;
        let parent_base = base[..slot.parent_len()].to_owned();
        let parent_expr = self.derived_place_current_value(&parent_base, place, depth + 1)?;
        match slot {
            DerivedSlot::Field { field_idx, variant, .. } => {
                if !parent_expr.sort().is_datatype() {
                    return None;
                }
                Self::datatype_field_select(&parent_expr, field_idx, variant, place, self.ctx)
            }
            DerivedSlot::IndexLocal { idx_local, .. } => {
                self.element_select_quiet(&parent_expr, Some(idx_local), None)
            }
            DerivedSlot::IndexConst { offset, .. } => {
                self.element_select_quiet(&parent_expr, None, Some(offset))
            }
            DerivedSlot::Unencodable { .. } => None,
        }
    }

    /// The element array inside a value that holds elements: the value itself
    /// when it is an array, else its `fld_data` / `fld_buf` field. Records
    /// nothing; mirrors the storage `propagate_element_write_to_parent` writes.
    fn element_storage_array(parent_expr: &Expr) -> Option<Expr> {
        if parent_expr.sort().is_array() {
            return Some(parent_expr.clone());
        }
        let dt = parent_expr.sort().datatype_sort()?;
        let (dt_name, field_name, field_sort) = dt.constructors.first().and_then(|cons| {
            cons.fields.iter().find_map(|f| {
                (matches!(&*f.name, "fld_data" | "fld_buf") && f.sort.is_array())
                    .then(|| (dt.name.to_string(), f.name.to_string(), f.sort.clone()))
            })
        })?;
        Some(parent_expr.clone().field_select(&dt_name, &field_name, field_sort))
    }

    /// Read one element out of `parent_expr`'s element array. Records nothing;
    /// the caller records the fail-closed reason on `None`.
    fn element_select_quiet(
        &mut self,
        parent_expr: &Expr,
        idx_local: Option<usize>,
        const_offset: Option<u64>,
    ) -> Option<Expr> {
        let array = Self::element_storage_array(parent_expr)?;
        let arr_sort = array.sort().array_sort()?;
        let index_width = arr_sort
            .index_sort
            .bitvec_width()
            .unwrap_or(crate::codegen_ay::types::POINTER_WIDTH);
        let idx_expr = if let Some(offset) = const_offset {
            if arr_sort.index_sort.is_int() {
                Expr::int_const(offset as i128)
            } else {
                Expr::bitvec_const(offset as u128, index_width)
            }
        } else {
            let idx_local = idx_local?;
            let idx_name =
                crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), idx_local);
            let raw = self.env_lookup(&idx_name).cloned().or_else(|| {
                let idx_ssa = self.ssa_name_from_base(&idx_name, false);
                self.ctx.lookup_var(&idx_ssa).cloned()
            })?;
            if arr_sort.index_sort.is_int() {
                if raw.sort().is_int() {
                    raw
                } else if raw.sort().is_bitvec() {
                    raw.bv2int()
                } else {
                    return None;
                }
            } else {
                match raw.sort().bitvec_width() {
                    Some(w) if w == index_width => raw,
                    Some(w) if w < index_width => raw.zero_extend(index_width - w),
                    Some(w) if w > index_width => raw.extract(index_width - 1, 0),
                    _ => return None,
                }
            }
        };
        Some(array.select(idx_expr))
    }

    /// `{parent}_idx_by_{L}` / `{parent}_cidx_{N}` — store the element back.
    ///
    /// A `&mut` taken of an ARRAY ELEMENT names the element, not the array, so
    /// a field store through it (`let p = &mut a[1]; p.x = 9`) updated only the
    /// element's own register and the array never changed: the store was
    /// DROPPED and `assert!(a[1].x == 0)` verified SUCCESSFUL with
    /// `[AY:PROOF_QUALIFIERS:clean]` in both lanes (adversarial review of
    /// m3/soundness-fixes-2, 2026-09-14; pre-existing on main).
    fn propagate_element_write_to_parent(
        &mut self,
        parent_base: &str,
        idx_local: Option<usize>,
        const_offset: Option<u64>,
        value: &Expr,
        _place: &Place,
    ) -> Option<(String, Expr)> {
        let location = || format!("{parent_base} element write-back");
        let parent_expr = match self.env_lookup(parent_base).cloned() {
            Some(expr) => expr,
            // A parent that is itself a slot (`a_cidx_1` of a 2-D array) has no
            // register until something writes it; read its current value out of
            // its own enclosing place, exactly as the field arm does.
            None => match self.derived_place_current_value(parent_base, _place, 0) {
                Some(expr) => expr,
                None => {
                    self.ctx.unsupported_with_fallback(
                        "element pointee write not propagated",
                        format!("{}: enclosing place has no value", location()),
                    );
                    return None;
                }
            },
        };
        // The element storage: the value itself, or `fld_data` / `fld_buf` of a
        // slice / Vec datatype.
        let data_field: Option<(String, usize, String, ay_bindings::Sort)> =
            if parent_expr.sort().is_array() {
                None
            } else {
                let Some(dt) = parent_expr.sort().datatype_sort() else {
                    self.ctx.unsupported_with_fallback(
                        "element pointee write not propagated",
                        format!("{}: enclosing place is not indexable", location()),
                    );
                    return None;
                };
                let found = dt.constructors.first().and_then(|cons| {
                    cons.fields.iter().enumerate().find_map(|(i, f)| {
                        (matches!(&*f.name, "fld_data" | "fld_buf") && f.sort.is_array()).then(
                            || (dt.name.to_string(), i, f.name.to_string(), f.sort.clone()),
                        )
                    })
                });
                let Some(found) = found else {
                    self.ctx.unsupported_with_fallback(
                        "element pointee write not propagated",
                        format!("{}: enclosing datatype has no element array", location()),
                    );
                    return None;
                };
                Some(found)
            };
        let array = match &data_field {
            None => parent_expr.clone(),
            Some((dt_name, _, field_name, field_sort)) => {
                parent_expr.clone().field_select(dt_name, field_name, field_sort.clone())
            }
        };
        let Some(arr_sort) = array.sort().array_sort() else {
            self.ctx.unsupported_with_fallback(
                "element pointee write not propagated",
                format!("{}: element storage is not an array", location()),
            );
            return None;
        };
        let index_width = arr_sort
            .index_sort
            .bitvec_width()
            .unwrap_or(crate::codegen_ay::types::POINTER_WIDTH);
        let idx_expr = if let Some(offset) = const_offset {
            if arr_sort.index_sort.is_int() {
                Expr::int_const(offset as i128)
            } else {
                Expr::bitvec_const(offset as u128, index_width)
            }
        } else {
            let Some(idx_local) = idx_local else {
                self.ctx.unsupported_with_fallback(
                    "element pointee write not propagated",
                    format!("{}: no index for the element slot", location()),
                );
                return None;
            };
            let idx_name =
                crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), idx_local);
            let raw = self.env_lookup(&idx_name).cloned().or_else(|| {
                let idx_ssa = self.ssa_name_from_base(&idx_name, false);
                self.ctx.lookup_var(&idx_ssa).cloned()
            });
            let Some(raw) = raw else {
                self.ctx.unsupported_with_fallback(
                    "element pointee write not propagated",
                    format!("{}: index local {idx_local} has no value", location()),
                );
                return None;
            };
            if arr_sort.index_sort.is_int() {
                if raw.sort().is_int() {
                    raw
                } else if raw.sort().is_bitvec() {
                    raw.bv2int()
                } else {
                    self.ctx.unsupported_with_fallback(
                        "element pointee write not propagated",
                        format!("{}: index sort is not numeric", location()),
                    );
                    return None;
                }
            } else {
                match raw.sort().bitvec_width() {
                    Some(w) if w == index_width => raw,
                    Some(w) if w < index_width => raw.zero_extend(index_width - w),
                    Some(w) if w > index_width => raw.extract(index_width - 1, 0),
                    _ => {
                        self.ctx.unsupported_with_fallback(
                            "element pointee write not propagated",
                            format!("{}: index sort is not a bitvector", location()),
                        );
                        return None;
                    }
                }
            }
        };

        let store_val = self.coerce_store_value_for_array(&array, value.clone());
        if let Some(arr) = array.sort().array_sort()
            && *store_val.sort() != arr.element_sort
        {
            self.ctx.unsupported_with_fallback(
                "element pointee write not propagated",
                format!("{}: element sort mismatch", location()),
            );
            return None;
        }
        let new_array = array.store(idx_expr, store_val);
        let new_parent = match &data_field {
            None => new_array,
            Some((_, field_idx, _, _)) => {
                let Some(rebuilt) = Self::datatype_field_update(
                    &parent_expr,
                    *field_idx,
                    None,
                    new_array,
                    _place,
                    self.ctx,
                ) else {
                    self.ctx.unsupported_with_fallback(
                        "element pointee write not propagated",
                        format!("{}: element array not written back", location()),
                    );
                    return None;
                };
                rebuilt
            }
        };
        let parent_ssa = self.ssa_name_from_base(parent_base, true);
        let parent_var = self.ctx.declare_var(&parent_ssa, new_parent.sort().clone());
        self.assert_ssa_def(parent_var.clone(), new_parent, parent_base);
        self.env_update(parent_base.to_owned(), parent_var.clone());
        self.repeat_array_values.remove(parent_base);
        debug!("propagate_element_write_to_parent: element written back into {parent_ssa}");
        Some((parent_base.to_owned(), parent_var))
    }

    pub(super) fn datatype_field_select(
        container: &Expr,
        field_idx: usize,
        cons_idx: Option<usize>,
        place: &Place,
        ctx: &mut AYCtx<'tcx, 't>,
    ) -> Option<Expr> {
        if crate::codegen_ay::types::is_coroutine_root_sort(container.sort()) {
            return crate::codegen_ay::types::coroutine_root_select(
                container.clone(),
                cons_idx,
                field_idx,
            );
        }

        let SortInner::Datatype(dt) = container.sort().inner() else {
            let location = format!("{:?}", place);
            ctx.unsupported("Place field projection sort", location);
            return None;
        };
        let is_option_like_struct = dt.constructors.len() == 1
            && dt.constructors[0].fields.len() == 2
            && dt.constructors[0].fields[0].name == "is_some";
        // For multi-constructor datatypes, require a constructor index (#419)
        let constructor_idx = if dt.constructors.len() > 1 {
            if let Some(idx) = cons_idx {
                idx
            } else {
                let location = format!(
                    "{:?}: multi-constructor datatype '{}' requires Downcast before Field",
                    place, dt.name
                );
                ctx.unsupported("Place field select", location);
                return None;
            }
        } else {
            0
        };
        let actual_field_idx = if is_option_like_struct && cons_idx == Some(1) && field_idx == 0 {
            1
        } else {
            field_idx
        };
        let Some(cons) = dt.constructors.get(constructor_idx) else {
            let location = format!(
                "{:?}: constructor {} out of bounds ('{}' has {} constructors)",
                place,
                constructor_idx,
                dt.name,
                dt.constructors.len()
            );
            ctx.unsupported("Place datatype constructors", location);
            return None;
        };
        let Some(field) = cons.fields.get(actual_field_idx) else {
            let location = format!(
                "{:?}: field {} out of bounds ('{}' has {} fields)",
                place,
                actual_field_idx,
                cons.name,
                cons.fields.len()
            );
            ctx.unsupported("Place datatype field index", location);
            return None;
        };
        Some(container.clone().field_select(&*dt.name, &*field.name, field.sort.clone()))
    }

    pub(super) fn datatype_field_update(
        container: &Expr,
        field_idx: usize,
        cons_idx: Option<usize>,
        new_val: Expr,
        place: &Place,
        ctx: &mut AYCtx<'tcx, 't>,
    ) -> Option<Expr> {
        if crate::codegen_ay::types::is_coroutine_root_sort(container.sort()) {
            return crate::codegen_ay::types::coroutine_root_update(
                container, cons_idx, field_idx, new_val,
            );
        }

        // Clone Sort (O(1) Arc) so dt borrows from sort_ref, not container.
        let sort_ref = container.sort().clone();
        let SortInner::Datatype(dt) = sort_ref.inner() else {
            let location = format!("{:?}", place);
            ctx.unsupported("Place field projection sort", location);
            return None;
        };
        let is_option_like_struct = dt.constructors.len() == 1
            && dt.constructors[0].fields.len() == 2
            && dt.constructors[0].fields[0].name == "is_some";
        // For multi-constructor datatypes, require a constructor index (#419)
        let constructor_idx = if dt.constructors.len() > 1 {
            if let Some(idx) = cons_idx {
                idx
            } else {
                let location = format!(
                    "{:?}: multi-constructor datatype '{}' requires Downcast before Field",
                    place, dt.name
                );
                ctx.unsupported("Place field update", location);
                return None;
            }
        } else {
            0
        };
        let actual_field_idx = if is_option_like_struct && cons_idx == Some(1) && field_idx == 0 {
            1
        } else {
            field_idx
        };
        let Some(cons) = dt.constructors.get(constructor_idx) else {
            let location = format!(
                "{:?}: constructor {} out of bounds ('{}' has {} constructors)",
                place,
                constructor_idx,
                dt.name,
                dt.constructors.len()
            );
            ctx.unsupported("Place datatype constructors", location);
            return None;
        };
        let Some(field) = cons.fields.get(actual_field_idx) else {
            let location = format!(
                "{:?}: field {} out of bounds ('{}' has {} fields)",
                place,
                actual_field_idx,
                cons.name,
                cons.fields.len()
            );
            ctx.unsupported("Place datatype field index", location);
            return None;
        };
        let new_val =
            crate::codegen_ay::types::unwrap_single_field_datatype_to_sort(&new_val, &field.sort)
                .unwrap_or(new_val);
        if new_val.sort() != &field.sort {
            let location = format!(
                "{:?}: field '{}' expects {:?}, got {:?}",
                place,
                field.name,
                field.sort,
                new_val.sort()
            );
            ctx.unsupported("Place datatype field sort mismatch", location);
            return None;
        }

        let mut args = Vec::with_capacity(cons.fields.len());
        let mut new_val_owned = Some(new_val);
        for (idx, field) in cons.fields.iter().enumerate() {
            if idx == actual_field_idx {
                args.push(new_val_owned.take()?);
            } else {
                args.push(container.clone().field_select(
                    &*dt.name,
                    &*field.name,
                    field.sort.clone(),
                ));
            }
        }

        Some(Expr::datatype_constructor(&*dt.name, &*cons.name, args, sort_ref.clone()))
    }

    /// #1262: Extract array index prefix from projections.
    ///
    /// If the first projection is Index or ConstantIndex, returns:
    /// - `(Some((array_base_name, index_expr)), remaining_projections)`
    ///
    /// Otherwise returns `(None, all_projections)`.
    pub(super) fn extract_array_index_prefix<'p>(
        &mut self,
        projections: &'p [ProjectionElem],
        base_name: &'p str,
    ) -> ArrayIndexPrefix<'p> {
        use crate::codegen_ay::types::POINTER_WIDTH;

        if projections.is_empty() {
            return ArrayIndexPrefix::None(projections);
        }

        match projections.first() {
            Some(ProjectionElem::ConstantIndex { offset, min_length, from_end }) => {
                // ConstantIndex: arr[N] where N is compile-time constant
                let Some(actual_offset) = constant_index_offset(*offset, *min_length, *from_end)
                else {
                    self.ctx.unsupported(
                        "ConstantIndex from_end requires runtime slice length",
                        format!("offset={offset}, min_length={min_length}"),
                    );
                    return ArrayIndexPrefix::Unsupported;
                };
                // Verify array is in env before returning
                if let Some(arr_expr) = self.env_lookup(base_name) {
                    let idx_expr = match arr_expr.sort().array_sort() {
                        Some(arr_sort) => match arr_sort.index_sort.inner() {
                            SortInner::BitVec(bv) => {
                                Expr::bitvec_const(actual_offset as i128, bv.width)
                            }
                            SortInner::Int => Expr::int_const(actual_offset as i128),
                            SortInner::Bool
                            | SortInner::Real
                            | SortInner::Array(_)
                            | SortInner::Datatype(_)
                            | SortInner::String
                            | SortInner::FloatingPoint(_, _)
                            | SortInner::Uninterpreted(_)
                            | SortInner::RegLan => {
                                let location =
                                    format!("ConstantIndex on array index sort {:?}", arr_sort);
                                self.ctx.unsupported("Array index sort", location);
                                return ArrayIndexPrefix::Unsupported;
                            }
                            _ => {
                                let location =
                                    format!("ConstantIndex on array index sort {:?}", arr_sort);
                                self.ctx.unsupported("Array index sort", location);
                                return ArrayIndexPrefix::Unsupported;
                            }
                        },
                        None => Expr::bitvec_const(actual_offset as i128, POINTER_WIDTH),
                    };
                    debug!(
                        "extract_array_index_prefix: ConstantIndex offset={} (from_end={}), arr_sort={:?}",
                        actual_offset,
                        from_end,
                        arr_expr.sort()
                    );
                    return ArrayIndexPrefix::Some((base_name, idx_expr), &projections[1..]);
                }
                ArrayIndexPrefix::None(projections)
            }
            Some(ProjectionElem::Index(idx_local)) => {
                // Index: arr[i] where i is a runtime variable
                let idx_name =
                    crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), *idx_local);

                // Look up index in environment
                let idx_expr_opt = self.env_lookup(&idx_name).cloned().or_else(|| {
                    let idx_ssa = self.ssa_name_from_base(&idx_name, false);
                    self.ctx.lookup_var(&idx_ssa).cloned()
                });

                if let Some(idx_expr) = idx_expr_opt
                    && let Some(arr_expr) = self.env_lookup(base_name)
                {
                    let idx_coerced = match arr_expr.sort().array_sort() {
                        Some(arr_sort) => match arr_sort.index_sort.inner() {
                            SortInner::BitVec(bv) => match idx_expr.sort().bitvec_width() {
                                Some(w) if w == bv.width => idx_expr,
                                Some(w) if w < bv.width => idx_expr.zero_extend(bv.width - w),
                                Some(w) if w > bv.width => idx_expr.extract(bv.width - 1, 0),
                                _ => {
                                    // non-enum: Option<u32> from bitvec_width()
                                    let location = format!(
                                        "Index local {} sort {:?}",
                                        idx_local,
                                        idx_expr.sort()
                                    );
                                    self.ctx.unsupported(
                                        "Index projection - non-bitvec index",
                                        &location,
                                    );
                                    return ArrayIndexPrefix::Unsupported;
                                }
                            },
                            SortInner::Int => {
                                if idx_expr.sort().is_int() {
                                    idx_expr
                                } else if idx_expr.sort().is_bitvec() {
                                    idx_expr.bv2int()
                                } else {
                                    let location = format!(
                                        "Index local {} sort {:?}",
                                        idx_local,
                                        idx_expr.sort()
                                    );
                                    self.ctx
                                        .unsupported("Index projection - non-int index", location);
                                    return ArrayIndexPrefix::Unsupported;
                                }
                            }
                            SortInner::Bool
                            | SortInner::Real
                            | SortInner::Array(_)
                            | SortInner::Datatype(_)
                            | SortInner::String
                            | SortInner::FloatingPoint(_, _)
                            | SortInner::Uninterpreted(_)
                            | SortInner::RegLan => {
                                let location =
                                    format!("Index projection array sort {:?}", arr_sort);
                                self.ctx.unsupported("Array index sort", location);
                                return ArrayIndexPrefix::Unsupported;
                            }
                            _ => {
                                let location =
                                    format!("Index projection array sort {:?}", arr_sort);
                                self.ctx.unsupported("Array index sort", location);
                                return ArrayIndexPrefix::Unsupported;
                            }
                        },
                        None => match idx_expr.sort().bitvec_width() {
                            Some(w) if w == POINTER_WIDTH => idx_expr,
                            Some(w) if w < POINTER_WIDTH => idx_expr.zero_extend(POINTER_WIDTH - w),
                            Some(w) if w > POINTER_WIDTH => idx_expr.extract(POINTER_WIDTH - 1, 0),
                            _ => {
                                // non-enum: Option<u32> from bitvec_width()
                                let location =
                                    format!("Index local {} sort {:?}", idx_local, idx_expr.sort());
                                self.ctx
                                    .unsupported("Index projection - non-bitvec index", location);
                                return ArrayIndexPrefix::Unsupported;
                            }
                        },
                    };

                    debug!(
                        "extract_array_index_prefix: Index local={}, arr_sort={:?}",
                        idx_local,
                        arr_expr.sort()
                    );
                    return ArrayIndexPrefix::Some((base_name, idx_coerced), &projections[1..]);
                }
                ArrayIndexPrefix::None(projections)
            }
            _ => ArrayIndexPrefix::None(projections), // external enum: ProjectionElem
        }
    }
}

pub(super) enum ArrayIndexPrefix<'p> {
    None(&'p [ProjectionElem]),
    Some((&'p str, Expr), &'p [ProjectionElem]),
    Unsupported,
}

#[cfg(test)]
mod derived_slot_tests {
    use super::{DerivedSlot, last_derived_slot, walk_must_record_fallback};

    /// A plain local names no slot of an enclosing place: the walk stops.
    #[test]
    fn a_plain_local_has_no_slot() {
        assert_eq!(last_derived_slot("main::local_3"), None);
        assert_eq!(last_derived_slot("main::local_3_deref"), None);
        assert_eq!(last_derived_slot("main::local_3_cast"), None);
    }

    #[test]
    fn a_field_names_its_parent() {
        assert_eq!(
            last_derived_slot("main::local_3_field_2"),
            Some(DerivedSlot::Field { parent_len: 13, field_idx: 2, variant: None })
        );
        let base = "main::local_3_variant_1_field_0";
        let slot = last_derived_slot(base).unwrap();
        assert_eq!(slot, DerivedSlot::Field { parent_len: 13, field_idx: 0, variant: Some(1) });
        assert_eq!(&base[..slot.parent_len()], "main::local_3");
    }

    /// The RIGHTMOST projection is the one to undo first: `&mut g.buf[i]` is
    /// `..._field_1_idx_by_7`, and taking the field first would store a field's
    /// value as if it were a whole element.
    #[test]
    fn the_rightmost_projection_wins() {
        let base = "main::local_3_field_1_idx_by_7";
        let slot = last_derived_slot(base).unwrap();
        assert_eq!(slot, DerivedSlot::IndexLocal { parent_len: 21, idx_local: 7 });
        assert_eq!(&base[..slot.parent_len()], "main::local_3_field_1");

        let base = "main::local_3_idx_by_7_field_1";
        let slot = last_derived_slot(base).unwrap();
        assert_eq!(slot, DerivedSlot::Field { parent_len: 22, field_idx: 1, variant: None });
        assert_eq!(&base[..slot.parent_len()], "main::local_3_idx_by_7");
    }

    #[test]
    fn a_constant_index_names_its_array() {
        let base = "main::local_3_cidx_2";
        let slot = last_derived_slot(base).unwrap();
        assert_eq!(slot, DerivedSlot::IndexConst { parent_len: 13, offset: 2 });
        assert_eq!(&base[..slot.parent_len()], "main::local_3");
    }

    /// A from-the-end index and a sub-slice are recorded by the naming scheme
    /// but cannot be placed: they must FAIL CLOSED, never be silently dropped.
    #[test]
    fn from_the_end_and_subslice_are_unencodable() {
        assert!(matches!(
            last_derived_slot("main::local_3_cidx_end_2"),
            Some(DerivedSlot::Unencodable { .. })
        ));
        assert!(matches!(
            last_derived_slot("main::local_3_subslice_1_3"),
            Some(DerivedSlot::Unencodable { .. })
        ));
        assert!(matches!(
            last_derived_slot("main::local_3_subslice_end_1_3"),
            Some(DerivedSlot::Unencodable { .. })
        ));
    }

    /// A marker inside the FUNCTION name is not a projection: its tail does not
    /// parse, which is exactly what keeps `my_field_3::local_2` a plain local.
    #[test]
    fn a_marker_in_the_function_name_is_not_a_slot() {
        assert_eq!(last_derived_slot("my_field_3::local_2"), None);
        assert_eq!(last_derived_slot("my_cidx_3::local_2"), None);
        assert_eq!(last_derived_slot("idx_by_7::local_2"), None);
    }

    /// The WRITE-BACK's fail-closed contract, which the parser tests never
    /// covered and which is the half that broke: for EVERY recognised slot, if
    /// the walk did not place the store it must record a fail-closed reason, and
    /// when the arm recorded none the walk records one itself.
    #[test]
    fn a_recognised_slot_that_is_not_placed_must_record_a_fallback() {
        // Placed: nothing to record, whatever the counter did.
        assert!(!walk_must_record_fallback(true, 7, 7));
        assert!(!walk_must_record_fallback(true, 7, 9));
        // Not placed, a reason already recorded by the arm: do not double-count.
        assert!(!walk_must_record_fallback(false, 7, 8));
        // Not placed and SILENT: this is the dropped store; the walk must record.
        assert!(walk_must_record_fallback(false, 7, 7));
        assert!(walk_must_record_fallback(false, 0, 0));
    }

    /// Every slot the parser recognises is one the walk must answer for: name
    /// them explicitly so a new variant cannot be added without deciding.
    #[test]
    fn every_recognised_slot_is_covered_by_the_contract() {
        let recognised = [
            last_derived_slot("main::local_3_field_2"),
            last_derived_slot("main::local_3_variant_1_field_0"),
            last_derived_slot("main::local_3_idx_by_7"),
            last_derived_slot("main::local_3_cidx_2"),
            last_derived_slot("main::local_3_cidx_end_2"),
            last_derived_slot("main::local_3_subslice_1_3"),
        ];
        for slot in recognised {
            let slot = slot.expect("a recognised slot");
            match slot {
                DerivedSlot::Field { .. }
                | DerivedSlot::IndexLocal { .. }
                | DerivedSlot::IndexConst { .. }
                | DerivedSlot::Unencodable { .. } => {}
            }
            // Recognised and unplaced with a silent arm: the walk records.
            assert!(walk_must_record_fallback(false, 3, 3), "{slot:?} must fail closed");
        }
    }

    /// The element's FIELD is the shape that regressed: `a[1].x` is
    /// `..._cidx_1_field_0`, whose parent `..._cidx_1` is an element slot with
    /// no register. The walk must undo the FIELD first and then the element, so
    /// the field is placed under the element rather than dropped.
    #[test]
    fn an_element_field_undoes_the_field_then_the_element() {
        let base = "main::local_3_cidx_1_field_0";
        let slot = last_derived_slot(base).unwrap();
        assert_eq!(slot, DerivedSlot::Field { parent_len: 20, field_idx: 0, variant: None });
        let parent = &base[..slot.parent_len()];
        assert_eq!(parent, "main::local_3_cidx_1");
        let parent_slot = last_derived_slot(parent).unwrap();
        assert_eq!(parent_slot, DerivedSlot::IndexConst { parent_len: 13, offset: 1 });
        assert_eq!(&parent[..parent_slot.parent_len()], "main::local_3");
    }

    /// The same two levels with a SYMBOLIC index, and one level deeper
    /// (`a[i].inner.x`), which is the pre-existing half of the same family.
    #[test]
    fn a_nested_element_field_walks_out_one_level_at_a_time() {
        let base = "main::local_3_idx_by_9_field_1_field_0";
        let slot = last_derived_slot(base).unwrap();
        assert_eq!(slot, DerivedSlot::Field { parent_len: 30, field_idx: 0, variant: None });
        let l1 = &base[..slot.parent_len()];
        assert_eq!(l1, "main::local_3_idx_by_9_field_1");
        let s1 = last_derived_slot(l1).unwrap();
        assert_eq!(s1, DerivedSlot::Field { parent_len: 22, field_idx: 1, variant: None });
        let l2 = &l1[..s1.parent_len()];
        assert_eq!(l2, "main::local_3_idx_by_9");
        let s2 = last_derived_slot(l2).unwrap();
        assert_eq!(s2, DerivedSlot::IndexLocal { parent_len: 13, idx_local: 9 });
        assert_eq!(&l2[..s2.parent_len()], "main::local_3");
    }
}
