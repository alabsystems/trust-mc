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
        // Parse _variant_N_field_M or _field_M suffix to find parent container.
        let Some(field_pos) = pointee_base.rfind("_field_") else {
            return;
        };
        let Ok(field_idx) = pointee_base[field_pos + 7..].parse::<usize>() else {
            return;
        };
        let before_field = &pointee_base[..field_pos];

        let (parent_base, variant_idx) = if let Some(variant_pos) = before_field.rfind("_variant_")
        {
            if let Ok(v_idx) = before_field[variant_pos + 9..].parse::<usize>() {
                (&pointee_base[..variant_pos], Some(v_idx))
            } else {
                (before_field, None)
            }
        } else {
            (before_field, None)
        };

        let Some(parent_expr) = self.env_lookup(parent_base).cloned() else {
            return;
        };
        if !parent_expr.sort().is_datatype() {
            return;
        }

        let Some(new_parent) = Self::datatype_field_update(
            &parent_expr,
            field_idx,
            variant_idx,
            updated_pointee.clone(),
            place,
            self.ctx,
        ) else {
            return;
        };

        let parent_ssa = self.ssa_name_from_base(parent_base, true);
        let parent_var = self.ctx.declare_var(&parent_ssa, parent_expr.sort().clone());
        self.assert_ssa_def(parent_var.clone(), new_parent, parent_base);
        self.env_update(parent_base, parent_var);
        debug!(
            "try_propagate_deref_write_to_parent_datatype: {} -> {} (variant={:?}, field={}) (Part of #3041)",
            pointee_base, parent_ssa, variant_idx, field_idx
        );
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
