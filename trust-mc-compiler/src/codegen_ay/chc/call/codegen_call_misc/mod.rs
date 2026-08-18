// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Clone, slice, raw_eq, rawvec, try/residual, layout, alloc extras, and misc stubs.
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.
//! Split into submodules per #2408 S1 decomposition.

mod alloc_extra;
mod dyn_wrapper_restore;
mod layout_semantic;
mod primitive_ops;
mod rawvec_extra_checks;
mod rawvec_try;
mod referent_resolve;
pub(in crate::codegen_ay::chc) use referent_resolve::Referent;
mod referent_resolve_chain;

use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use super::ChcCtx;
use super::call_accumulator::CallAccumulator;
use super::chc_call_context::ChcCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_rules::CodegenRules;

/// Extension trait for miscellaneous call handling on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallMisc {
    fn codegen_call_primitive_clone(&mut self, cx: &ChcCallContext<'_>);

    fn codegen_call_raw_eq(&mut self, func: &Operand, cx: &ChcCallContext<'_>);

    /// Look up a bare local's state variable for Copy/Move operands without projection.
    #[must_use]
    fn resolve_bare_local(
        arg: &Operand,
        state_vars: &[(Arc<str>, Sort)],
        output_state_vars: &[(Arc<str>, Sort)],
        modified_locals: &HashSet<usize>,
        local_to_state_idx: &HashMap<usize, usize>,
        fn_name: &str,
    ) -> Option<Expr>;

    #[must_use]
    fn resolve_ref_or_const_referent(
        &mut self,
        arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr>;

    #[must_use]
    fn resolve_raw_eq_referent(
        &mut self,
        arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr>;

    fn codegen_call_rawvec(&mut self, cx: &ChcCallContext<'_>);

    fn codegen_call_try_residual(&mut self, cx: &ChcCallContext<'_>);

    fn codegen_call_unconstrained_stub(&mut self, cx: &ChcCallContext<'_>);

    fn codegen_call_display_cow(&mut self, cx: &ChcCallContext<'_>);

    fn codegen_call_layout_semantic(&mut self, func: &Operand, cx: &ChcCallContext<'_>);

    fn codegen_call_alloc_extra(&mut self, bb_idx: usize, cx: &ChcCallContext<'_>);
}

impl<'tcx, 'body> CallMisc for ChcCtx<'tcx, 'body> {
    fn codegen_call_primitive_clone(&mut self, cx: &ChcCallContext<'_>) {
        self.codegen_call_primitive_clone_impl(
            cx.args,
            cx.destination,
            cx.target,
            cx.from_app,
            cx.stmt_constraints,
            cx.modified_locals,
        );
    }

    fn codegen_call_raw_eq(&mut self, func: &Operand, cx: &ChcCallContext<'_>) {
        let ecx = super::chc_call_context::CallEmitContext::from(cx);
        self.codegen_call_raw_eq_impl(func, &ecx);
    }

    fn resolve_bare_local(
        arg: &Operand,
        state_vars: &[(Arc<str>, Sort)],
        output_state_vars: &[(Arc<str>, Sort)],
        modified_locals: &HashSet<usize>,
        local_to_state_idx: &HashMap<usize, usize>,
        fn_name: &str,
    ) -> Option<Expr> {
        Self::resolve_bare_local_impl(
            arg,
            state_vars,
            output_state_vars,
            modified_locals,
            local_to_state_idx,
            fn_name,
        )
    }

    fn resolve_ref_or_const_referent(
        &mut self,
        arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        self.resolve_ref_or_const_referent_impl(arg, modified_locals)
    }

    fn resolve_raw_eq_referent(
        &mut self,
        arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        self.resolve_raw_eq_referent_impl(arg, modified_locals)
    }

    fn codegen_call_rawvec(&mut self, cx: &ChcCallContext<'_>) {
        self.codegen_call_rawvec_impl(cx);
    }

    fn codegen_call_try_residual(&mut self, cx: &ChcCallContext<'_>) {
        self.codegen_call_try_residual_impl(cx);
    }

    fn codegen_call_unconstrained_stub(&mut self, cx: &ChcCallContext<'_>) {
        self.codegen_call_unconstrained_stub_impl(cx);
    }

    fn codegen_call_display_cow(&mut self, cx: &ChcCallContext<'_>) {
        // Cow<str>::to_string() / DisplayToString returns a fresh String
        // preserving the source's observable length/backing.
        //
        // Part of #4071: When the destination is a flattened RustString
        // (fld_ptr, fld_len, fld_cap), we must constrain fld_len from the
        // resolved backing length. Without this, the flattened fields are
        // existentially quantified and unconstrained in the CHC rule,
        // causing downstream StringAsStr reads to observe garbage values.
        let dest_local = cx.destination.local;
        let mut extra_constraints = Vec::new();
        let mut extra_dests = vec![dest_local];
        let dest_len_var = self.collections.len_state.get_len_var(dest_local).cloned();

        self.ref_resolution.const_ref_values.remove(&dest_local);
        self.ref_resolution.subslice_len.remove(&dest_local);
        self.ref_resolution.subslice_offset.remove(&dest_local);

        // Try resolving the source string backing from the first argument.
        let backing =
            cx.args.first().and_then(|arg| self.resolve_string_backing(arg, cx.modified_locals));

        // Part of #4071: Resolve the source &str length for the destination
        // String's flattened fld_len. Three resolution paths:
        //   (1) backing.len from resolve_string_backing (most precise)
        //   (2) translate_ptr_metadata on the argument operand (BV128 upper bits)
        //   (3) subslice_len of the argument local
        let src_len: Option<Expr> = backing
            .as_ref()
            .map(|b| b.len.clone())
            .or_else(|| {
                cx.args
                    .first()
                    .and_then(|arg| self.translate_ptr_metadata(arg, cx.modified_locals))
                    .map(|len| len.into_expr())
            })
            .or_else(|| {
                if let Some(Operand::Copy(p) | Operand::Move(p)) = cx.args.first() {
                    if p.projection.is_empty() {
                        return self.ref_resolution.subslice_len.get(&p.local).cloned();
                    }
                }
                None
            });

        if let Some(ref backing) = backing {
            self.ref_resolution.const_ref_values.insert(dest_local, backing.data.clone());
            self.ref_resolution.subslice_offset.insert(dest_local, backing.offset.clone());
        }

        // Part of #4071: Constrain flattened String fld_len from source length.
        // RustString layout: fld_ptr(0), fld_len(1), fld_cap(2).
        if let Some(ref len_expr) = src_len {
            if let Some(field_count) =
                self.flatten.flattened_local_field_count.get(&dest_local).copied()
            {
                if field_count >= 2 {
                    if let Some(base_idx) = self.try_state_idx_for_local(dest_local) {
                        let len_slot = base_idx + 1;
                        if let Some((out_name, out_sort)) =
                            self.state_var_mgr.output_state_vars.get(len_slot)
                        {
                            let dest_len_var_expr = Expr::var(&**out_name, out_sort.clone());
                            if let Some(eq) = self.make_coerced_eq_constraint(
                                &dest_len_var_expr,
                                len_expr.clone(),
                                &out_sort.clone(),
                                dest_local,
                                "codegen_call_display_cow::fld_len(#4071)",
                            ) {
                                extra_constraints.push(eq);
                            }
                        }
                    }
                }
            }
        }

        if let Some(len_expr) = src_len {
            if let Some(len_var_name) = dest_len_var.clone() {
                self.collection_len_set(
                    &len_var_name,
                    len_expr,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
        } else if let Some(len_var_name) = dest_len_var {
            self.mark_collection_len_modified(&len_var_name);
        }

        let new_output_args = self.build_output_args(cx.modified_locals, &extra_dests);
        self.emit_goto_rule_extra(
            cx.from_app,
            cx.target,
            &new_output_args,
            cx.stmt_constraints,
            extra_constraints,
        );
    }

    fn codegen_call_layout_semantic(&mut self, func: &Operand, cx: &ChcCallContext<'_>) {
        self.codegen_call_layout_semantic_impl(func, cx);
    }

    fn codegen_call_alloc_extra(&mut self, bb_idx: usize, cx: &ChcCallContext<'_>) {
        self.codegen_call_alloc_extra_impl(bb_idx, cx);
    }
}
