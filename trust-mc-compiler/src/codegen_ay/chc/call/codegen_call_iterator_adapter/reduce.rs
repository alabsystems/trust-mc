// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Reduction dispatch arms (IterFold, IterSum) for iterator adapter CHC call codegen.
//!
//! Extracted from mod.rs per #4129 (500 LOC threshold).

use std::collections::HashSet;

use ay_bindings::{Expr, Sort};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    AggregateKind, Body, LocalDecl, Operand, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{AdtKind, ClosureKind, RigidTy, TyKind};
use tracing::debug;

use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::bool_sort;
use crate::rustc_public_bridge::IndexedVal;

use super::super::ChcCtx;
use super::super::inline_body::translate_closure_inline_body;
use super::super::stubs_option_helpers::{OptionHelpers, option_value_sort};
use crate::codegen_ay::chc::quantifier_encoding::{
    ClosureBodyResult, translate_closure_body_with_params,
};

fn closure_returns_option_like_success(body: &Body) -> bool {
    let mut block_idx = 0;
    let mut visited = HashSet::new();
    let mut return_rvalue = None;

    loop {
        if !visited.insert(block_idx) {
            return false;
        }
        let Some(block) = body.blocks.get(block_idx) else {
            return false;
        };

        for stmt in &block.statements {
            let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                continue;
            };
            if place.local == 0 && place.projection.is_empty() {
                return_rvalue = Some(rvalue);
            }
        }

        match block.terminator.kind {
            TerminatorKind::Goto { target } => block_idx = target,
            TerminatorKind::Return => {
                return return_rvalue.is_some_and(rvalue_is_option_like_payload_variant);
            }
            _ => return false,
        }
    }
}

fn rvalue_is_option_like_payload_variant(rvalue: &Rvalue) -> bool {
    let Rvalue::Aggregate(AggregateKind::Adt(def, variant, _, _, _), operands) = rvalue else {
        return false;
    };
    if def.kind() != AdtKind::Enum || operands.len() != 1 {
        return false;
    }

    let variants = def.variants();
    let Some(returned_variant) = variants.get(variant.to_index()) else {
        return false;
    };
    variants.len() == 2
        && variants.iter().any(|candidate| candidate.fields().is_empty())
        && returned_variant.fields().len() == 1
}

fn resolve_try_fold_closure_body_for_operand(
    operand: &Operand,
    locals: &[LocalDecl],
) -> Option<Body> {
    let closure_ty = operand.ty(locals).ok()?;
    let (closure_def, closure_args, kinds) = match closure_ty.kind() {
        TyKind::RigidTy(RigidTy::Closure(def, args)) => {
            (def, args, [ClosureKind::FnMut, ClosureKind::Fn, ClosureKind::FnOnce])
        }
        TyKind::RigidTy(RigidTy::Ref(_, inner, _))
            if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Closure(..))) =>
        {
            let TyKind::RigidTy(RigidTy::Closure(def, args)) = inner.kind() else {
                unreachable!("guard ensures inner closure type");
            };
            (def, args, [ClosureKind::FnMut, ClosureKind::Fn, ClosureKind::FnOnce])
        }
        _ => return None,
    };

    kinds.into_iter().find_map(|kind| {
        Instance::resolve_closure(closure_def, &closure_args, kind)
            .ok()
            .and_then(|instance| instance.body())
    })
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn try_advance_or_symbolic_remaining(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        fallback_reason: &'static str,
    ) -> Expr {
        if let Some(has_remaining) = self
            .iterator_receiver_expr_and_local(args, modified_locals)
            .and_then(|(iter_expr, _)| {
                self.advance_iterator_expr(&iter_expr).map(|(_, has_remaining)| has_remaining)
            })
        {
            has_remaining
        } else {
            self.record_sound_fallback_reason(fallback_reason);
            self.fresh_adapter_symbol("iter_has_remaining", bool_sort())
        }
    }

    fn try_precise_try_fold_success_result(
        &mut self,
        args: &[Operand],
        dest_local: usize,
        dest_vec_idx: usize,
        init_expr: &Expr,
        has_remaining: &Expr,
        out_sort: &Sort,
    ) -> Option<(Option<Expr>, Option<Vec<Option<Expr>>>)> {
        let closure_body =
            resolve_try_fold_closure_body_for_operand(args.get(2)?, self.body.locals())?;
        if !closure_returns_option_like_success(&closure_body) {
            return None;
        }

        if self.flatten.flattened_tuple_locals.contains(&dest_local)
            && self.flatten.flattened_enum_discr.contains_key(&dest_local)
        {
            let field_count = self.flattened_field_count(dest_local);
            let mut fields = vec![None; field_count];
            let (true_discr, _) = self.flatten.flattened_enum_discr[&dest_local];
            let discr_sort = &self.state_var_mgr.output_state_vars.get(dest_vec_idx)?.1;
            fields[0] = if discr_sort.is_bool() {
                Some(Expr::bool_const(true))
            } else {
                discr_sort.bitvec_width().map(|width| Expr::bitvec_const(true_discr, width))
            };

            if field_count > 1 {
                let payload_sort =
                    self.state_var_mgr.output_state_vars.get(dest_vec_idx + 1)?.1.to_owned();
                let init_payload =
                    self.coerce_value_to_sort(init_expr.to_owned(), &payload_sort, false)?;
                let symbolic_payload = self.fresh_adapter_symbol("iter_try_fold_acc", payload_sort);
                fields[1] =
                    Some(Expr::ite(has_remaining.to_owned(), symbolic_payload, init_payload));
            }
            return Some((None, Some(fields)));
        }

        let payload_sort = option_value_sort(out_sort)?;
        let init_payload = self.coerce_value_to_sort(init_expr.to_owned(), &payload_sort, false)?;
        let symbolic_payload = self.fresh_adapter_symbol("iter_try_fold_acc", payload_sort);
        let payload = Expr::ite(has_remaining.to_owned(), symbolic_payload, init_payload);
        Some((self.make_some_expr_for_option(payload, out_sort), None))
    }

    /// Fold FOR REAL: replay the user closure once per element.
    ///
    /// Returns `Some((acc, fully_covered))` when the element sequence is
    /// addressable AND the closure body could be replayed for every step.
    /// The caller keeps its previous over-approximation on the
    /// `!fully_covered` side, so this lane can only add precision.
    fn try_precise_fold(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        init_expr: &Expr,
        acc_sort: &Sort,
    ) -> Option<(Expr, Expr, Vec<Expr>)> {
        let closure_body =
            resolve_try_fold_closure_body_for_operand(args.get(2)?, self.body.locals())?;
        let reduction = self.precise_reduce_chain(
            args,
            modified_locals,
            init_expr,
            acc_sort,
            |ctx, acc, elem| {
                // Closure locals: 0 = return, 1 = environment, 2 = accumulator,
                // 3 = item. An empty capture list fails CLOSED — a capturing
                // closure leaves its local unresolved and the walk returns None,
                // abandoning the whole chain rather than folding a wrong value.
                let params = [acc.clone(), elem.clone()];
                translate_closure_inline_body(ctx, &closure_body, &params, &[], 0, 0).or_else(
                    || {
                        translate_closure_body_with_params(ctx, &closure_body, &params, &[], 0)
                            .map(|ClosureBodyResult { pred, .. }| pred)
                    },
                )
            },
        )?;
        debug!("iter fold: precise per-element replay emitted (fold folds)");
        Some((reduction.acc, reduction.fully_covered, reduction.constraints))
    }

    /// Sum FOR REAL: `acc + elem` per element, same coverage contract as
    /// [`Self::try_precise_fold`].
    fn try_precise_sum(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        zero: &Expr,
        acc_sort: &Sort,
    ) -> Option<(Expr, Expr, Vec<Expr>)> {
        if acc_sort.bitvec_width().is_none() {
            return None;
        }
        let reduction =
            self.precise_reduce_chain(args, modified_locals, zero, acc_sort, |ctx, acc, elem| {
                let elem = ctx.coerce_value_to_sort(elem.clone(), acc.sort(), true)?;
                Some(acc.clone().bvadd(elem))
            })?;
        debug!("iter sum: precise per-element replay emitted (sum sums)");
        Some((reduction.acc, reduction.fully_covered, reduction.constraints))
    }

    /// Handle IterFold and IterSum reduction arms.
    pub(in crate::codegen_ay::chc) fn codegen_reduce_arm(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        dest_local: usize,
        dest_vec_idx: usize,
        extra_constraints: &mut Vec<Expr>,
    ) -> (Option<Expr>, Option<Vec<Option<Expr>>>) {
        match stub {
            StubKind::IterFold => {
                if args.len() >= 2
                    && let Some(init_expr) = self
                        .translate_operand_with_modified(&args[1], modified_locals)
                        .or_else(|| self.resolve_ref_operand(&args[1], modified_locals))
                {
                    let has_remaining = self.try_advance_or_symbolic_remaining(
                        args,
                        modified_locals,
                        // Part of #3447: Iterator advance failed — has_remaining
                        // is fully symbolic, making fold result nondeterministic.
                        "iter_fold_advance_failed",
                    );
                    // Check if the destination sort differs from init sort.
                    // This happens for try_fold which returns Result<B,E> or
                    // ControlFlow while init is just B. In that case, use the
                    // destination output sort for a fully symbolic result
                    // (sound over-approximation).
                    let dest_sort = self
                        .state_var_mgr
                        .output_state_vars
                        .get(dest_vec_idx)
                        .map(|(_, s)| s.to_owned());
                    let init_sort = init_expr.sort().to_owned();
                    if let Some(ref out_sort) = dest_sort
                        && let Some(success_result) = self.try_precise_try_fold_success_result(
                            args,
                            dest_local,
                            dest_vec_idx,
                            &init_expr,
                            &has_remaining,
                            out_sort,
                        )
                    {
                        return success_result;
                    }
                    if let Some(ref out_sort) = dest_sort
                        && *out_sort != init_sort
                    {
                        // try_fold: destination sort wraps the accumulator.
                        // When the closure may return a residual, keep the
                        // existing sound over-approximation.
                        let symbolic_result =
                            self.fresh_adapter_symbol("iter_try_fold_value", out_sort.to_owned());
                        (Some(symbolic_result), None)
                    } else {
                        let symbolic_result =
                            self.fresh_adapter_symbol("iter_fold_value", init_sort.clone());
                        let overapprox =
                            Expr::ite(has_remaining, symbolic_result, init_expr.clone());
                        let folded = self
                            .try_precise_fold(args, modified_locals, &init_expr, &init_sort)
                            .map_or(overapprox.clone(), |(acc, covered, chain)| {
                                extra_constraints.extend(chain);
                                Expr::ite(covered, acc, overapprox)
                            });
                        (Some(folded), None)
                    }
                } else {
                    (None, None)
                }
            }
            StubKind::IterSum => {
                if !args.is_empty()
                    && let Some((_, out_sort)) =
                        self.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
                    && let Some(zero) = Self::adapter_zero_expr_for_sort(&out_sort)
                {
                    let has_remaining = self.try_advance_or_symbolic_remaining(
                        args,
                        modified_locals,
                        // Part of #3447: Iterator advance failed — has_remaining
                        // is fully symbolic, making sum result nondeterministic.
                        "iter_sum_advance_failed",
                    );
                    let symbolic_result =
                        self.fresh_adapter_symbol("iter_sum_value", out_sort.clone());
                    let overapprox = Expr::ite(has_remaining, symbolic_result, zero.clone());
                    let summed = self
                        .try_precise_sum(args, modified_locals, &zero, &out_sort)
                        .map_or(overapprox.clone(), |(acc, covered, chain)| {
                            extra_constraints.extend(chain);
                            Expr::ite(covered, acc, overapprox)
                        });
                    (Some(summed), None)
                } else {
                    (None, None)
                }
            }
            _other => (None, None), // partial dispatch: StubKind
        }
    }
}
