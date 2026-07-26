// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! IterSizeHint dispatch arm for iterator adapter CHC call codegen.
//!
//! Extracted from `mod.rs` per #4129 (500 LOC threshold).
//! Handles `Iterator::size_hint()` → `(remaining, Some(remaining))` for
//! exact-size iterators (SliceIter, VecIntoIter).
//!
//! Part of #3348: precise size_hint stub.

use ay_bindings::Expr;

use crate::codegen_ay::types::bool_sort;

use super::super::ChcCtx;
use super::super::stubs_option_helpers::OptionHelpers;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Build result expressions for `Iterator::size_hint()`.
    ///
    /// Returns `(remaining, Some(remaining))` for exact-size iterators.
    /// Populates `result_expr` (non-flattened Datatype path) or
    /// `flattened_result_fields` (flattened tuple path).
    ///
    /// Returns `true` if a precise result was built.
    pub(in crate::codegen_ay::chc) fn codegen_iter_size_hint(
        &mut self,
        args: &[rustc_public::mir::Operand],
        modified_locals: &std::collections::HashSet<usize>,
        dest_local: usize,
        dest_vec_idx: usize,
        result_expr: &mut Option<Expr>,
        flattened_result_fields: &mut Option<Vec<Option<Expr>>>,
    ) {
        let Some((iter_expr, _iter_local)) =
            self.iterator_receiver_expr_and_local(args, modified_locals)
        else {
            return;
        };
        let Some(remaining) = self.try_extract_iterator_remaining_len(&iter_expr) else {
            return;
        };

        if self.flatten.flattened_tuple_locals.contains(&dest_local) {
            let field_count = self.flattened_field_count(dest_local);
            let mut fields = Vec::with_capacity(field_count);
            for i in 0..field_count {
                if let Some((_, sort)) =
                    self.state_var_mgr.output_state_vars.get(dest_vec_idx + i).cloned()
                {
                    if sort.bitvec_width().is_some() {
                        // BV field = usize bound -> remaining
                        fields.push(self.coerce_value_to_sort(remaining.clone(), &sort, false));
                    } else if sort == bool_sort() {
                        // Bool = Option discriminant -> Some = true
                        fields.push(Some(Expr::bool_const(true)));
                    } else if sort.datatype_sort().is_some() {
                        // Datatype = Option<usize> -> build Some(remaining)
                        fields.push(self.make_some_expr_for_option(remaining.clone(), &sort));
                    } else {
                        fields.push(None);
                    }
                } else {
                    fields.push(None);
                }
            }
            if !fields.is_empty() {
                *flattened_result_fields = Some(fields);
            }
        } else if let Some((_, out_sort)) =
            self.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
            && let Some(dt) = out_sort.datatype_sort()
            && let Some(ctor) = dt.constructors.first()
            && ctor.fields.len() >= 2
        {
            // Non-flattened: build (remaining, Some(remaining)) tuple Datatype.
            let mut ctor_args = Vec::with_capacity(ctor.fields.len());
            let mut build_ok = true;
            for field in &ctor.fields {
                if field.sort.bitvec_width().is_some() {
                    if let Some(coerced) =
                        self.coerce_value_to_sort(remaining.clone(), &field.sort, false)
                    {
                        ctor_args.push(coerced);
                    } else {
                        build_ok = false;
                        break;
                    }
                } else if field.sort.datatype_sort().is_some() {
                    if let Some(some_expr) =
                        self.make_some_expr_for_option(remaining.clone(), &field.sort)
                    {
                        ctor_args.push(some_expr);
                    } else {
                        build_ok = false;
                        break;
                    }
                } else if field.sort == bool_sort() {
                    ctor_args.push(Expr::bool_const(true));
                } else {
                    build_ok = false;
                    break;
                }
            }
            if build_ok && ctor_args.len() == ctor.fields.len() {
                *result_expr = Some(Expr::datatype_constructor(
                    &*dt.name,
                    &*ctor.name,
                    ctor_args,
                    out_sort.clone(),
                ));
            }
        }
        // Falls through to symbolic fallback if precise result couldn't be built
    }
}
