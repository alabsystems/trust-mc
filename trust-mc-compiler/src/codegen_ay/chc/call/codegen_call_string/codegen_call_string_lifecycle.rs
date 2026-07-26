// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! String lifecycle and mutation stub handlers.
//!
//! Covers `StringNew`, `StringLen`, `StringPush`, `StringPushStr`,
//! `StringClear`, `StringTruncate`, and `StringClone`. These are the basic
//! collection-length-tracking operations that mirror Vec lifecycle stubs.
//!
//! Split from `codegen_call_string.rs` (Part of #4071).

use ay_bindings::Expr;

use super::super::ChcCtx;
use super::super::call_accumulator::CallAccumulator;
use super::super::codegen_call_coerce::CallCoerce;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Extension trait for String lifecycle/mutation stubs on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallStringLifecycle {
    /// Handle `StringNew`: dest = symbolic String, tracked len = 0.
    fn codegen_string_new(
        &mut self,
        dest_local: usize,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    );

    /// Handle `StringLen`: dest = tracked collection length.
    fn codegen_string_len(
        &mut self,
        dest_local: usize,
        collection_local: Option<usize>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    );

    /// Handle `StringPush`: len += 1.
    fn codegen_string_push(
        &mut self,
        collection_local: Option<usize>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    );

    /// Handle `StringPushStr`: leave len unconstrained (over-approximation).
    fn codegen_string_push_str(&mut self, collection_local: Option<usize>);

    /// Handle `StringClear`: len = 0.
    fn codegen_string_clear(
        &mut self,
        collection_local: Option<usize>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    );

    /// Handle `StringTruncate`: len becomes unconstrained.
    fn codegen_string_truncate(&mut self, collection_local: Option<usize>);

    /// Handle `StringClone`: copy tracked len from source to dest.
    fn codegen_string_clone(
        &mut self,
        dest_local: usize,
        collection_local: Option<usize>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    );
}

impl<'tcx, 'body> CallStringLifecycle for ChcCtx<'tcx, 'body> {
    fn codegen_string_new(
        &mut self,
        dest_local: usize,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) {
        if let Some(len_var_name) = self.collections.len_state.get_len_var(dest_local).cloned() {
            self.collection_len_set(
                &len_var_name,
                Expr::bitvec_const(0u64, POINTER_WIDTH),
                &mut CallAccumulator::new(extra_constraints, extra_dests),
            );
        }
        extra_dests.push(dest_local);
    }

    fn codegen_string_len(
        &mut self,
        dest_local: usize,
        collection_local: Option<usize>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) {
        if let Some(coll_local) = collection_local
            && let Some(len_var_name) = self.collections.len_state.get_len_var(coll_local).cloned()
        {
            let len_expr = self.collection_current_len(&len_var_name);
            if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                if let Some(eq) = self.make_coerced_eq_constraint(
                    &dest_var,
                    len_expr,
                    dest_var.sort(),
                    dest_local,
                    "codegen_call_string_core::StringLen",
                ) {
                    extra_constraints.push(eq);
                }
                extra_dests.push(dest_local);
            }
        } else {
            extra_dests.push(dest_local);
        }
    }

    fn codegen_string_push(
        &mut self,
        collection_local: Option<usize>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) {
        if let Some(coll_local) = collection_local
            && let Some(len_var_name) = self.collections.len_state.get_len_var(coll_local).cloned()
        {
            let old_len = self.collection_current_len(&len_var_name);
            let new_len = old_len.bvadd(Expr::bitvec_const(1u64, POINTER_WIDTH));
            self.collection_len_set(
                &len_var_name,
                new_len,
                &mut CallAccumulator::new(extra_constraints, extra_dests),
            );
        }
    }

    fn codegen_string_push_str(&mut self, collection_local: Option<usize>) {
        if let Some(coll_local) = collection_local
            && let Some(len_var_name) = self.collections.len_state.get_len_var(coll_local).cloned()
        {
            self.mark_collection_len_modified(&len_var_name);
        }
    }

    fn codegen_string_clear(
        &mut self,
        collection_local: Option<usize>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) {
        if let Some(coll_local) = collection_local
            && let Some(len_var_name) = self.collections.len_state.get_len_var(coll_local).cloned()
        {
            self.collection_len_set(
                &len_var_name,
                Expr::bitvec_const(0u64, POINTER_WIDTH),
                &mut CallAccumulator::new(extra_constraints, extra_dests),
            );
        }
    }

    fn codegen_string_truncate(&mut self, collection_local: Option<usize>) {
        if let Some(coll_local) = collection_local
            && let Some(len_var_name) = self.collections.len_state.get_len_var(coll_local).cloned()
        {
            self.mark_collection_len_modified(&len_var_name);
        }
    }

    fn codegen_string_clone(
        &mut self,
        dest_local: usize,
        collection_local: Option<usize>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) {
        // Part of #4099: propagate backing data (fld_data) alongside length.
        if let Some(coll_local) = collection_local {
            // Propagate tracked length.
            if let Some(src_len_var) = self.collections.len_state.get_len_var(coll_local).cloned() {
                let src_len = self.collection_current_len(&src_len_var);
                if let Some(dst_len_var) =
                    self.collections.len_state.get_len_var(dest_local).cloned()
                {
                    self.collection_len_set(
                        &dst_len_var,
                        src_len,
                        &mut CallAccumulator::new(extra_constraints, extra_dests),
                    );
                }
            }
            // Propagate full DT value so downstream string equality
            // can compare backing arrays.
            if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                if let Some(src_idx) =
                    self.state_var_mgr.local_to_state_idx.get(&coll_local).copied()
                {
                    if let Some((src_name, src_sort)) = self.state_var_mgr.state_vars.get(src_idx) {
                        let src_expr = Expr::var(&**src_name, src_sort.clone());
                        if src_sort.is_datatype() && dest_var.sort().is_datatype() {
                            if let Some(eq) = self.make_coerced_eq_constraint(
                                &dest_var,
                                src_expr,
                                dest_var.sort(),
                                dest_local,
                                "codegen_call_string_lifecycle::StringClone",
                            ) {
                                extra_constraints.push(eq);
                            }
                        }
                    }
                }
            }
        }
        extra_dests.push(dest_local);
    }
}
