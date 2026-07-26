// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! IterZip adapter construction and sidecar propagation.
//!
//! Extracted from `codegen_call_iterator_adapter` per #4129 (500 LOC threshold).

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use tracing::debug;

use super::super::ChcCtx;
use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_ctx::types::AdapterSourceData;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle IterZip adapter construction and sidecar propagation.
    pub(in crate::codegen_ay::chc) fn codegen_iter_zip(
        &mut self,
        cx: &ChcCallContext<'_>,
        dest_local: usize,
        dest_vec_idx: usize,
    ) -> Option<Expr> {
        let args = cx.args;
        let modified_locals = cx.modified_locals;

        // Part of #3381: Iterator::zip(self, other) pairs two iterators.
        // Zip<A, B>::remaining_len = min(a.remaining_len, b.remaining_len).
        // The Zip adapter sort is typically BV64 (opaque), so we only propagate
        // remaining_len via adapter_remaining_len for downstream IterMap/IterCollect.
        let len_a = self.iterator_receiver_expr_and_local(args, modified_locals).and_then(
            |(iter_expr, iter_local)| {
                self.try_extract_iterator_remaining_len(&iter_expr).or_else(|| {
                    iter_local
                        .and_then(|il| self.collections.adapter_remaining_len.get(&il).cloned())
                })
            },
        );
        let len_b = args.get(1).and_then(|arg| {
            let expr = self
                .get_collection_arg(arg, modified_locals)
                .or_else(|| self.resolve_ref_operand(arg, modified_locals))
                .or_else(|| self.translate_operand_with_modified(arg, modified_locals))?;
            self.try_extract_iterator_remaining_len(&expr).or_else(|| {
                if let Operand::Copy(place) | Operand::Move(place) = arg {
                    let ref_local: usize = place.local;
                    let resolved = self
                        .ref_resolution
                        .ref_targets
                        .get(&ref_local)
                        .map_or(ref_local, |rt| rt.local);
                    self.collections.adapter_remaining_len.get(&resolved).cloned()
                } else {
                    None
                }
            })
        });
        let zip_remaining = match (len_a, len_b) {
            (Some(a), Some(b)) => {
                // min(a, b) = ite(a <=u b, a, b)
                Some(Expr::ite(a.clone().bvule(b.clone()), a, b))
            }
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => None,
        };
        if let Some(rl) = zip_remaining {
            self.collections.adapter_remaining_len.insert(dest_local, rl);
        }

        // Part of #3348: Combine adapter_source_data from both iterators.
        // Zip(A, B) produces pairs, so the source data arrays from A and B
        // are concatenated. Both source chains must have source data for the
        // combined data to be useful.
        let iter_a_local =
            self.iterator_receiver_expr_and_local(args, modified_locals).and_then(|(_, il)| il);
        let iter_b_local = args.get(1).and_then(|arg| {
            if let Operand::Copy(place) | Operand::Move(place) = arg {
                let ref_local: usize = place.local;
                Some(
                    self.ref_resolution
                        .ref_targets
                        .get(&ref_local)
                        .map_or(ref_local, |rt| rt.local),
                )
            } else {
                None
            }
        });
        {
            let mut combined_arrays = Vec::new();
            let mut combined_has_transform = false;
            let mut both_have_data = true;
            for opt_local in [iter_a_local, iter_b_local] {
                if let Some(il) = opt_local {
                    if let Some(src) = self.collections.adapter_source_data.get(&il) {
                        combined_arrays.extend(src.data_arrays.iter().cloned());
                        combined_has_transform |= src.has_transform;
                    } else {
                        both_have_data = false;
                    }
                } else {
                    both_have_data = false;
                }
            }
            if both_have_data && !combined_arrays.is_empty() {
                self.collections.adapter_source_data.insert(
                    dest_local,
                    AdapterSourceData {
                        data_arrays: combined_arrays,
                        has_transform: combined_has_transform,
                        closure_template: None,
                        concrete_elems: None,
                    },
                );
                debug!(
                    dest_local,
                    "IterZip: combined adapter_source_data from both iterators (#3348)"
                );
            }
        }

        // Zip output sort is typically BV64 (opaque) — attempt Datatype
        // construction but expect fallback to symbolic.
        let (inner_iter, _) = self.iterator_receiver_expr_and_local(args, modified_locals)?;
        let (_, out_sort) = self.state_var_mgr.output_state_vars.get(dest_vec_idx)?;
        self.construct_adapter_with_inner_iter(out_sort, inner_iter)
    }
}
