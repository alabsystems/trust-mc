// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

/// Driver-side classification for why CHC solving ended in UNKNOWN.
///
/// ATTRIBUTION ONLY — no variant here affects a verdict. The label is emitted as
/// `[AY:UNKNOWN_REASON:<label>]` and the scoreboard stores it as an opaque string
/// (it only tests `is_some()` to mark a row inconclusive), so adding variants
/// splits a bucket without changing any classification.
///
/// `SolverError` used to be a CATCH-ALL covering three unrelated situations, which
/// made the biggest bucket in the parity gate (139 rows = 12.4% of the denominator)
/// unactionable: you could not tell whether those rows needed a bigger budget or a
/// missing feature. The split below answers that from the gate output alone.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SolverUnknownReason {
    /// A solver guard-timeout: the engine itself ran out of its solve budget.
    Timeout,
    /// The per-harness deadline was exhausted BEFORE/BETWEEN pre-solve phases
    /// (SMT read, bv2int rewrite, CHC parse, nullary-fail expansion, acyclic
    /// witness search, scalarize/split), so no solving was even attempted —
    /// `bail_unknown_if_deadline_exhausted` in `call_ay/chc/native.rs`.
    /// BUDGET-bound: strictly a matter of time, not capability.
    PreSolveDeadline,
    /// The run produced a `Failure`/`Other` with no DECIDED failing property —
    /// solver-side inconclusiveness on a preserved undecided model. A decided
    /// failure keeps `reason = None`, so this shape is exactly "we could not
    /// decide", not "we found a bug".
    UndecidedModel,
    /// ay-chc could not PARSE the emitted CHC problem at all.
    ///
    /// Always OUR bug, never a solver limitation: we wrote SMT2 the CHC dialect
    /// does not accept, and a parse error aborts the WHOLE problem, so the
    /// harness is scored inconclusive having never been solved. Strictly worse
    /// than a hard verification problem, and always fixable on the encoder side.
    /// Two causes seen so far: a non-Bool `declare-fun` (only Bool-returning
    /// predicates are supported) and a predicate applied with an argument sort
    /// that disagrees with its declaration.
    ChcParseError,
    /// ay REJECTED one or more commands of the emitted BMC SMT-LIB query —
    /// `(error "line L column C: ...")` / `(error "unknown constant ...")` —
    /// discarded them, and carried on. The BMC counterpart of
    /// `ChcParseError`, and like it ALWAYS OUR BUG: the encoder wrote a query
    /// the solver does not accept (an undeclared sort, two incompatible sorts
    /// equated, a constructor applied with the wrong arity, a reference to a
    /// constant whose own declaration was rejected).
    ///
    /// NOT budget-bound. ay fail-closes on this shape even with unlimited
    /// memory — `(:reason-unknown "a problem-contributing command was
    /// discarded")` — so the harness is never decided AS EMITTED however long
    /// it runs. Measured on tests/slow/tokio-proofs
    /// `tokio_test::block_on::{async_block,async_fn}` (2026-08-29): 276
    /// rejected commands in a 14 MB query; `memout` at the default budget, the
    /// discarded-command refusal after 142 s / 40 GB without one. Both rows
    /// had been filed as `UndecidedModel` ("solver undecided — try --ay-chc"),
    /// which is the opposite diagnosis.
    SmtParseError,
    /// ay answered `unknown` with `(:reason-unknown "memout")`: the query
    /// exceeded the solver's memory budget. BUDGET-bound, like `Timeout`.
    Memout,
    /// ay-chc synthesized an invariant model that FAILED its own clause
    /// verification, so the driver rejected the proof and fell back to UNKNOWN
    /// ("ay-chc false proof detected: ...").
    ///
    /// This is the self-check doing its job — a would-be FALSE PROOF caught and
    /// refused — so it is neither budget-bound nor a missing feature. It points
    /// at an invariant-synthesis / model-extraction defect on the AY side, which
    /// is why it must not hide inside `SolverError`: this is the one bucket where
    /// an inconclusive row is evidence of a CORRECTNESS bug, not a limitation.
    FalseProofRejected,
    /// ay-chc returned a genuine error (not a deadline bail, not a rejected
    /// false proof, not an undecided model). FEATURE-bound or a real defect —
    /// look at the accompanying `[AY:UNKNOWN-CATEGORY]` line, which names the
    /// specific limit (e.g. the `≥2 Array-sorted state parameters` ceiling, #4259).
    SolverError,
}

impl SolverUnknownReason {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Timeout => "Timeout",
            Self::PreSolveDeadline => "PreSolveDeadline",
            Self::UndecidedModel => "UndecidedModel",
            Self::ChcParseError => "ChcParseError",
            Self::SmtParseError => "SmtParseError",
            Self::Memout => "Memout",
            Self::FalseProofRejected => "FalseProofRejected",
            Self::SolverError => "SolverError",
        }
    }

    /// Classify the `anyhow` error that `try_ay_chc_solver` failed with.
    ///
    /// The deadline gate bails with a stable message
    /// (`"ay-chc per-harness deadline exhausted before pre-solve phase '<phase>'"`),
    /// which is the ONLY budget-bound shape on this path; anything else is a real
    /// solver error. Matching on the message is deliberate: the gate returns
    /// `anyhow::Error`, so there is no typed discriminant to switch on, and
    /// mis-matching can only mislabel a bucket — never change a verdict.
    pub(crate) fn from_chc_error(err: &anyhow::Error) -> Self {
        let text = format!("{err}");
        if text.contains("deadline exhausted before pre-solve phase") {
            Self::PreSolveDeadline
        } else if text.contains("Failed to parse CHC problem") || text.contains("parse error:") {
            Self::ChcParseError
        } else if text.contains("false proof detected") {
            Self::FalseProofRejected
        } else if text.contains("exceeded guard timeout") {
            // `native.rs:1286` — the engine ran out of ITS solve budget. This is
            // BUDGET-bound and was previously indistinguishable from a genuine
            // solver failure, which is a large part of why `SolverError` grew
            // into a ~109-row catch-all covering roughly half the inconclusive
            // bucket. `Timeout` already existed but was only ever set on the
            // dead external-binary path (`call_ay.rs:399`).
            Self::Timeout
        } else {
            // NOTE: `native.rs:1448` "returned Unknown - verification
            // inconclusive" (the adaptive portfolio declining to decide) also
            // lands here. It is CAPABILITY-bound and deserves its own label,
            // but it must NOT be folded into `UndecidedModel`, which is
            // documented as a *preserved undecided model* — a different shape.
            // Splitting it needs a new variant; `any_other_chc_error_stays_
            // solver_error` pins the current behaviour deliberately.
            Self::SolverError
        }
    }
}

#[cfg(test)]
mod tests {
    use super::SolverUnknownReason;

    #[test]
    fn deadline_bail_message_classifies_as_budget_bound() {
        let err = anyhow::anyhow!(
            "ay-chc per-harness deadline exhausted before pre-solve phase 'read_smt_file'"
        );
        assert_eq!(
            SolverUnknownReason::from_chc_error(&err),
            SolverUnknownReason::PreSolveDeadline
        );
        assert_eq!(SolverUnknownReason::PreSolveDeadline.label(), "PreSolveDeadline");
    }

    /// Observed verbatim on kani/DynTrait/main.rs: the solver's invariant model
    /// failed its own clause verification, so a would-be FALSE PROOF was caught
    /// and refused. Must not be filed as a plain solver error — it is the only
    /// inconclusive shape that indicates a correctness bug.
    #[test]
    fn rejected_false_proof_gets_its_own_bucket() {
        let err = anyhow::anyhow!(
            "ay-chc false proof detected: external invariant model fails clause verification"
        );
        assert_eq!(
            SolverUnknownReason::from_chc_error(&err),
            SolverUnknownReason::FalseProofRejected
        );
    }

    /// A parse failure means we emitted SMT2 the CHC dialect rejects, which
    /// aborts the WHOLE problem — the harness is never solved. That is our bug
    /// and must be countable separately from real solver failures. Both observed
    /// causes are covered.
    #[test]
    fn parse_failures_are_their_own_bucket() {
        for msg in [
            "Failed to parse CHC problem: parse error: Non-predicate function declaration: \
             'P_inf_std::alloc' with return sort BitVec(64)",
            "Failed to parse CHC problem: parse error: Predicate 'main__bb40' expected \
             argument sort Bool, got (Array (_ BitVec 64) (_ BitVec 64))",
        ] {
            let err = anyhow::anyhow!("{msg}");
            assert_eq!(
                SolverUnknownReason::from_chc_error(&err),
                SolverUnknownReason::ChcParseError,
                "msg: {msg}"
            );
        }
    }

    /// A guard timeout is BUDGET-bound and must not hide inside the
    /// `SolverError` catch-all — that conflation is most of why the bucket
    /// grew to ~109 rows with no way to tell "needs more time" from "needs a
    /// better solver".
    #[test]
    fn guard_timeout_is_budget_bound_not_solver_error() {
        for msg in [
            "ay-chc adaptive-portfolio exceeded guard timeout (15s)",
            "[AY-chc] Acyclic BMC lane exceeded guard timeout (20s) — falling back",
        ] {
            let err = anyhow::anyhow!("{msg}");
            assert_eq!(
                SolverUnknownReason::from_chc_error(&err),
                SolverUnknownReason::Timeout,
                "msg: {msg}"
            );
        }
    }

    #[test]
    fn any_other_chc_error_stays_solver_error() {
        let err =
            anyhow::anyhow!("adaptive-portfolio returned Unknown - verification inconclusive");
        assert_eq!(SolverUnknownReason::from_chc_error(&err), SolverUnknownReason::SolverError);
    }

    /// The labels must stay distinct — they are the bucket names the parity
    /// gate groups by, and a collision would silently re-merge the split.
    #[test]
    fn labels_are_distinct() {
        let labels = [
            SolverUnknownReason::Timeout.label(),
            SolverUnknownReason::PreSolveDeadline.label(),
            SolverUnknownReason::UndecidedModel.label(),
            SolverUnknownReason::ChcParseError.label(),
            SolverUnknownReason::SmtParseError.label(),
            SolverUnknownReason::Memout.label(),
            SolverUnknownReason::FalseProofRejected.label(),
            SolverUnknownReason::SolverError.label(),
        ];
        let unique: std::collections::HashSet<_> = labels.iter().collect();
        assert_eq!(unique.len(), labels.len(), "labels collided: {labels:?}");
    }
}
