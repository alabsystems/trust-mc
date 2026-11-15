// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Emit-time projection of unconstrained relation arguments, gated on AY's
//! executor admission caps.
//!
//! AY charges the WHOLE emitted problem — every variable occurrence in every
//! clause — against fixed caps inside `ChcProblem::validate()`, which the
//! driver reaches through `query_obligations()` before any per-property slice
//! is cut and before AY's own dead-parameter elimination runs. A wide frame
//! (every block relation carrying every local of the function) over enough
//! rules exceeds `MAX_DT_SORT_NODES` / `MAX_EXECUTOR_EXPR_ROOTS`, AY rejects the
//! slice, and the driver files `ChcParseError` without a solver ever running.
//! Measured on the 2026-09-12 verification corpus: 7 harnesses, charged at
//! 41 k–203 k sort nodes against the 32 768 cap, with 90–99 % of their relation
//! argument positions never read by any clause.
//!
//! `trust_mc_core::chc_optimize::unconstrained` removes exactly those
//! positions (an exact least-fixpoint equivalence). This module decides WHEN
//! to run it:
//!
//! * `TRUST_MC_CHC_UNCONSTRAINED_ARGS` unset or `admission` (the default): run
//!   only when [`estimate_ay_admission`] says the VC would be rejected. A VC AY
//!   admits today is emitted byte-identically, so no verdict elsewhere moves.
//! * `always`: run on every VC — a measurement lever for how much the
//!   projection alone buys the solver.
//! * `off`: never run.
//!
//! The pass runs LAST, after the straight-line discharge and the slot
//! consistency checks, so it cannot defeat a syntactic proof the way frame
//! narrowing once did, and its result is re-checked with the same
//! sort/slot-consistency nets the rest of the emit pipeline uses: if a net
//! that passed before the projection fails after it, the un-projected VC is
//! emitted (fail closed). A net the pipeline had already seen fail — it emits
//! such a VC with a warning — is not held against the projection.

use trust_mc_core::chc::ChcVc;
use trust_mc_core::chc_admission::{AyAdmissionEstimate, estimate_ay_admission};

/// When the projection runs. Read ONCE from the environment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::codegen_ay) enum UnconstrainedArgsMode {
    /// Never project.
    Off,
    /// Project only a VC AY's admission would reject (default).
    Admission,
    /// Project every VC.
    Always,
}

fn unconstrained_args_mode() -> UnconstrainedArgsMode {
    static MODE: std::sync::OnceLock<UnconstrainedArgsMode> = std::sync::OnceLock::new();
    *MODE.get_or_init(|| {
        match std::env::var("TRUST_MC_CHC_UNCONSTRAINED_ARGS")
            .ok()
            .map(|v| v.trim().to_ascii_lowercase())
            .as_deref()
        {
            Some("off" | "0") => UnconstrainedArgsMode::Off,
            Some("always" | "1") => UnconstrainedArgsMode::Always,
            _ => UnconstrainedArgsMode::Admission,
        }
    })
}

/// `TRUST_MC_CHC_ADMISSION_STATS=1`: report the admission estimate of every
/// emitted VC at warn level. Measurement only — it changes no verdict.
fn admission_stats_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var("TRUST_MC_CHC_ADMISSION_STATS").map(|v| v == "1").unwrap_or(false)
    })
}

/// Outcome of one emit-time projection decision, for logging and tests.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::codegen_ay) enum ProjectionOutcome {
    /// The lever is off or the VC is admitted as-is under `admission` mode.
    Skipped,
    /// The pass ran and found nothing to remove.
    Unchanged,
    /// The pass removed `stripped` positions and the result passed the
    /// consistency nets.
    Projected { stripped: usize, before: AyAdmissionEstimate, after: AyAdmissionEstimate },
    /// The pass removed positions but the result failed a consistency net;
    /// the un-projected VC was restored.
    Reverted { stripped: usize },
}

/// Project unconstrained relation arguments out of `vc` according to the
/// configured mode. See the module docs.
pub(in crate::codegen_ay) fn prune_unconstrained_relation_args_for_admission(
    vc: &mut ChcVc,
) -> ProjectionOutcome {
    project_with_mode(vc, unconstrained_args_mode())
}

pub(in crate::codegen_ay) fn project_with_mode(
    vc: &mut ChcVc,
    mode: UnconstrainedArgsMode,
) -> ProjectionOutcome {
    if mode == UnconstrainedArgsMode::Off {
        return ProjectionOutcome::Skipped;
    }
    let before = estimate_ay_admission(vc);
    let exceeded = before.first_exceeded();
    if admission_stats_enabled() {
        tracing::warn!(
            sort_nodes = before.sort_nodes,
            expr_roots = before.expr_roots,
            expr_nodes = before.expr_nodes,
            name_bytes = before.name_bytes,
            exceeded = exceeded.unwrap_or("none"),
            relations = vc.relations.len(),
            rules = vc.rules.len(),
            max_arity = vc.relations.iter().map(|r| r.arg_sorts.len()).max().unwrap_or(0),
            "CHC: AY executor admission estimate (TRUST_MC_CHC_ADMISSION_STATS)"
        );
    }
    if mode == UnconstrainedArgsMode::Admission && exceeded.is_none() {
        return ProjectionOutcome::Skipped;
    }

    // The projection strips the same positions from a relation's declaration
    // and from every one of its applications, so it preserves whatever
    // sort/slot agreement the VC had. Re-run the emit pipeline's two
    // consistency nets and revert only on a REGRESSION: a VC the pipeline
    // already flagged as misaligned and chose to emit anyway (kani/Str/utf8.rs
    // is one) is not the projection's doing, and refusing to project it just
    // hands AY a problem it rejects outright.
    let sorts_consistent_before = super::block_relation_apps_consistent(vc);
    let slots_consistent_before = super::block_relation_slot_names_consistent(vc);
    let snapshot = vc.clone();
    let stripped = vc.prune_unconstrained_relation_args();
    if stripped == 0 {
        return ProjectionOutcome::Unchanged;
    }
    let sorts_regressed = sorts_consistent_before && !super::block_relation_apps_consistent(vc);
    let slots_regressed =
        slots_consistent_before && !super::block_relation_slot_names_consistent(vc);
    if sorts_regressed || slots_regressed {
        tracing::warn!(
            stripped,
            sorts_regressed,
            slots_regressed,
            "CHC: unconstrained-argument projection left a relation application inconsistent \
             with its declaration; emitting the un-projected VC (fail-closed)"
        );
        *vc = snapshot;
        return ProjectionOutcome::Reverted { stripped };
    }

    let after = estimate_ay_admission(vc);
    match exceeded {
        Some(resource) => tracing::warn!(
            stripped,
            resource,
            sort_nodes_before = before.sort_nodes,
            sort_nodes_after = after.sort_nodes,
            expr_roots_before = before.expr_roots,
            expr_roots_after = after.expr_roots,
            admitted_after = after.first_exceeded().is_none(),
            "CHC: VC exceeds AY's executor admission cap; projected unconstrained relation \
             arguments before emission"
        ),
        None => tracing::debug!(
            stripped,
            sort_nodes_before = before.sort_nodes,
            sort_nodes_after = after.sort_nodes,
            "CHC: projected unconstrained relation arguments before emission (always mode)"
        ),
    }
    ProjectionOutcome::Projected { stripped, before, after }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_bindings::{Expr, Sort};
    use trust_mc_core::chc::{ChcQuery, RelationApp, RelationDecl, Rule, RuleBody};
    use trust_mc_core::chc_admission::AY_MAX_DT_SORT_NODES;

    /// `blocks` relations of `width` bit-vector columns chained by identity
    /// transitions; only column 0 of the last block is read by the error edge.
    fn wide_chain(blocks: usize, width: usize) -> ChcVc {
        let bv = Sort::bitvec(32);
        let mut vc = ChcVc::new();
        let cols: Vec<Expr> =
            (0..width).map(|i| vc.declare_var(format!("_{i}"), bv.clone())).collect();
        for b in 0..blocks {
            vc.add_relation(RelationDecl::new(format!("main__bb{b}"), vec![bv.clone(); width]));
        }
        vc.add_relation(RelationDecl::nullary("error"));
        vc.add_rule(Rule::new(
            RuleBody::new(None, vec![cols[0].clone().eq(Expr::bitvec_const(0u64, 32))]),
            RelationApp::new("main__bb0", cols.clone()),
        ));
        for b in 1..blocks {
            vc.add_rule(Rule::new(
                RuleBody::new(
                    Some(RelationApp::new(format!("main__bb{}", b - 1), cols.clone())),
                    vec![],
                ),
                RelationApp::new(format!("main__bb{b}"), cols.clone()),
            ));
        }
        vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new(format!("main__bb{}", blocks - 1), cols.clone())),
                vec![cols[0].clone().bvugt(Expr::bitvec_const(7u64, 32))],
            ),
            RelationApp::nullary("error"),
        ));
        vc.query = ChcQuery::new().with_target("error");
        vc
    }

    #[test]
    fn admission_mode_leaves_an_admitted_vc_untouched() {
        let mut vc = wide_chain(4, 8);
        let before = vc.clone();
        assert_eq!(
            project_with_mode(&mut vc, UnconstrainedArgsMode::Admission),
            ProjectionOutcome::Skipped
        );
        assert_eq!((&vc.relations, &vc.rules), (&before.relations, &before.rules));
    }

    #[test]
    fn off_mode_never_projects() {
        let mut vc = wide_chain(300, 120);
        assert!(estimate_ay_admission(&vc).first_exceeded().is_some());
        let before = vc.clone();
        assert_eq!(
            project_with_mode(&mut vc, UnconstrainedArgsMode::Off),
            ProjectionOutcome::Skipped
        );
        assert_eq!((&vc.relations, &vc.rules), (&before.relations, &before.rules));
    }

    #[test]
    fn admission_mode_projects_a_vc_ay_would_reject() {
        // 300 blocks x 120 columns: ~72 k charged sort nodes against the 32 768 cap.
        let mut vc = wide_chain(300, 120);
        let before = estimate_ay_admission(&vc);
        assert_eq!(before.first_exceeded(), Some("datatype sort nodes"));
        assert!(before.sort_nodes > AY_MAX_DT_SORT_NODES);

        let outcome = project_with_mode(&mut vc, UnconstrainedArgsMode::Admission);
        let ProjectionOutcome::Projected { stripped, after, .. } = outcome else {
            panic!("expected a projection, got {outcome:?}");
        };
        // Every block keeps exactly the one column the error edge reads.
        assert_eq!(stripped, 300 * 119);
        assert!(
            vc.relations.iter().filter(|r| r.name.starts_with("main__bb")).all(|r| r.arity() == 1)
        );
        assert_eq!(after.first_exceeded(), None);
        assert!(super::super::block_relation_apps_consistent(&vc));
        assert!(super::super::block_relation_slot_names_consistent(&vc));
    }

    /// A VC whose applications already disagree on a slot's identity (the
    /// emit pipeline warns and emits it anyway) is still projected: the
    /// projection cannot be blamed for a misalignment it inherited.
    #[test]
    fn inherited_slot_misalignment_does_not_revert_the_projection() {
        let bv = Sort::bitvec(32);
        let mut vc = ChcVc::new();
        let a = vc.declare_var("_a", bv.clone());
        let b = vc.declare_var("_b", bv.clone());
        let dead = vc.declare_var("_dead", bv.clone());
        vc.add_relation(RelationDecl::new("main__bb0", vec![bv.clone(), bv.clone()]));
        vc.add_relation(RelationDecl::nullary("error"));
        vc.add_rule(Rule::new(
            RuleBody::new(None, vec![]),
            RelationApp::new("main__bb0", vec![a.clone(), dead.clone()]),
        ));
        // Position 0 is `_a` in the head above but `_b` here: slot-misaligned.
        vc.add_rule(Rule::new(
            RuleBody::new(
                Some(RelationApp::new("main__bb0", vec![b.clone(), dead.clone()])),
                vec![b.clone().bvugt(Expr::bitvec_const(1u64, 32))],
            ),
            RelationApp::nullary("error"),
        ));
        vc.query = ChcQuery::new().with_target("error");
        assert!(!super::super::block_relation_slot_names_consistent(&vc));

        let outcome = project_with_mode(&mut vc, UnconstrainedArgsMode::Always);
        let ProjectionOutcome::Projected { stripped, .. } = outcome else {
            panic!("expected a projection, got {outcome:?}");
        };
        assert_eq!(stripped, 1);
        assert_eq!(
            vc.relations.iter().find(|r| r.name == "main__bb0").map(RelationDecl::arity),
            Some(1)
        );
    }

    #[test]
    fn always_mode_projects_an_admitted_vc() {
        let mut vc = wide_chain(4, 8);
        let ProjectionOutcome::Projected { stripped, .. } =
            project_with_mode(&mut vc, UnconstrainedArgsMode::Always)
        else {
            panic!("expected a projection");
        };
        assert_eq!(stripped, 4 * 7);
    }
}
