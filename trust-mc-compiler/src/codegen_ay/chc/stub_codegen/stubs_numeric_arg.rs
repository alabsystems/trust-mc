// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared numeric argument resolution for BigInt and BigRational stubs.
//!
//! Consolidates the duplicated 3-phase pattern from `get_bigint_arg` and
//! `get_bigrational_arg` into a parameterized `resolve_numeric_arg` method.
//!
//! Part of #2878: deduplicate stubs argument resolution.

use std::collections::HashSet;

use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;
use tracing::debug;

use crate::codegen_ay::types::int_sort;

use super::{ChcCtx, chc_fresh_name, declare_pending_var};
use crate::codegen_ay::chc::codegen_ctx::diagnostics::CellCounter;

/// Selects the sort acceptance, coercion, and fallback behavior for numeric
/// stub argument resolution.
///
/// Part of #2878: deduplicate BigInt/BigRational `get_*_arg` patterns.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) enum NumericArgKind {
    /// BigInt: accepts Int sort only, no coercion, fallback `int_sort()`.
    BigInt,
    /// BigRational: accepts Real sort directly; coerces Int → Real via
    /// `int_to_real()`; fallback `Sort::real()`.
    BigRational,
}

impl NumericArgKind {
    /// Returns the expression unchanged if its sort matches, or coerced if
    /// a compatible coercion exists, or `None` if rejected.
    #[must_use]
    pub(in super::super) fn accept_or_coerce(self, expr: &Expr) -> Option<Expr> {
        match self {
            Self::BigInt => {
                if expr.sort().is_int() {
                    Some(expr.clone())
                } else {
                    None
                }
            }
            Self::BigRational => {
                if expr.sort().is_real() {
                    Some(expr.clone())
                } else if expr.sort().is_int() {
                    Some(expr.clone().int_to_real())
                } else {
                    None
                }
            }
        }
    }

    /// Diagnostic label for debug/trace messages.
    pub(in super::super) fn label(self) -> &'static str {
        match self {
            Self::BigInt => "BigInt",
            Self::BigRational => "BigRational",
        }
    }

    /// Prefix for fresh symbolic variable names on fallback.
    pub(in super::super) fn fallback_prefix(self) -> &'static str {
        match self {
            Self::BigInt => "bigint_arg",
            Self::BigRational => "bigrational_arg",
        }
    }

    /// The SMT sort for the symbolic fallback variable.
    pub(in super::super) fn fallback_sort(self) -> Sort {
        match self {
            Self::BigInt => int_sort(),
            Self::BigRational => Sort::real(),
        }
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Shared numeric argument resolution for BigInt and BigRational stubs.
    ///
    /// Consolidates the duplicated 3-phase pattern:
    ///   1. Direct operand translation with sort check + optional coercion
    ///   2. Reference resolution via type-specific ref_targets map
    ///   3. Symbolic fallback with domain sort
    ///
    /// Part of #2878: deduplicate 5 identical get_*_arg patterns.
    pub(in crate::codegen_ay::chc) fn resolve_numeric_arg(
        &mut self,
        operand: &Operand,
        modified_locals: &HashSet<usize>,
        kind: NumericArgKind,
    ) -> Option<Expr> {
        // Phase 1: Direct operand translation with sort acceptance.
        if let Some(expr) = self.translate_operand_with_modified(operand, modified_locals)
            && let Some(accepted) = kind.accept_or_coerce(&expr)
        {
            debug!(
                "resolve_numeric_arg({}) operand={:?} direct result={}",
                kind.label(),
                operand,
                accepted
            );
            return Some(accepted);
        }

        // Phase 2: Reference resolution via type-specific ref_targets.
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            let ref_local: usize = place.local;

            // BigRational: also check state_vars directly for the ref_local itself,
            // since a BigRational local may translate directly to a Real state var.
            if kind == NumericArgKind::BigRational
                && let Some((name, sort)) = self.state_var_mgr.state_vars.get(ref_local)
            {
                let expr = Expr::var(&**name, sort.clone());
                if let Some(accepted) = kind.accept_or_coerce(&expr) {
                    debug!(
                        "resolve_numeric_arg({}) operand={:?} state_var result={}",
                        kind.label(),
                        operand,
                        accepted
                    );
                    return Some(accepted);
                }
            }

            let target_local = match kind {
                NumericArgKind::BigInt => {
                    self.ref_resolution.bigint_ref_targets.get(&ref_local).copied()
                }
                NumericArgKind::BigRational => {
                    self.ref_resolution.bigrational_ref_targets.get(&ref_local).copied()
                }
            };

            if let Some(target_local) = target_local {
                debug!(
                    ref_local,
                    target_local,
                    is_modified = modified_locals.contains(&target_local),
                    "CHC: resolving {} reference",
                    kind.label()
                );

                let (name, sort) = if modified_locals.contains(&target_local) {
                    self.state_var_mgr.output_state_vars.get(target_local)?
                } else {
                    self.state_var_mgr.state_vars.get(target_local)?
                };

                let expr = Expr::var(&**name, sort.clone());
                if let Some(accepted) = kind.accept_or_coerce(&expr) {
                    debug!(
                        "resolve_numeric_arg({}) ref={} target={} modified={} result={}",
                        kind.label(),
                        ref_local,
                        target_local,
                        modified_locals.contains(&target_local),
                        accepted
                    );
                    return Some(accepted);
                }
            }
        }

        // Phase 3: Symbolic fallback.
        //
        // AUDIT (task #65, stub_approximation): keep counting, NOT SoundHavoc.
        // A stub ARGUMENT that could not be resolved is replaced by a fresh
        // symbolic — this severs the data-flow between the program-computed
        // receiver/argument (which other constraints still mention) and the
        // stub's model, so the stub computes on a value decoupled from the one
        // the program actually passed. Widening for proofs, but the decoupling
        // is exactly the "fresh solver-controlled symbolic for a
        // program-produced value" shape that has produced masked violations
        // before (see VecFieldFallback/PointeeSynthesisFallback reclass) —
        // Step-C fail-closes Successes carrying it.
        debug!(?operand, label = kind.label(), "CHC: numeric arg fallback to symbolic");
        self.diagnostics.stub_approximation.inc();
        let sym_name = chc_fresh_name(kind.fallback_prefix());
        let result = declare_pending_var(sym_name, kind.fallback_sort());
        debug!(
            "resolve_numeric_arg({}) operand={:?} FALLBACK result={}",
            kind.label(),
            operand,
            result
        );
        Some(result)
    }
}
