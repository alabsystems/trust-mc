// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! The CHC lane's answer to "can this harness run at all?" (V4 vacuity).
//!
//! # Why this exists
//!
//! The V4 vacuity gate in `harness_runner` fires on ONE shape: every non-cover
//! check `Unreachable` (`verification_result::is_unsat_assumption_vacuous`).
//! The BMC lane produces that shape through `call_ay::probe_harness_reachable`
//! — after a would-be proof it asks the solver whether the program constraints
//! ALONE are satisfiable, and a decided `unsat` re-statuses every check.
//!
//! The CHC lane had no such probe. Its compiler-side straight-line discharge
//! decides the same question STRUCTURALLY (`straightline_proof`, the exit-block
//! reachability test) and emits `; VACUOUS_ALL_CHECKS_UNREACHABLE:`, which
//! `native_result::apply_vacuous_checks_marker` honours — but that test is a
//! block-graph walk, so it cannot see a SEMANTIC contradiction like
//! `assume(x.is_nan() && x > 0.0)`. Measured before this module existed: those
//! harnesses reported `VERIFICATION:- SUCCESSFUL`, `[AY:PROOF_QUALIFIERS:clean]`
//! and every check `Status: SUCCESS` in CHC while BMC reported
//! `VERIFICATION:- VACUOUS`. Two lanes, one source program, opposite verdicts,
//! and the CHC one was fail-OPEN on the project's own default (`--allow-vacuous`
//! says a vacuous harness is a FAILURE unless relaxed).
//!
//! # The probe
//!
//! The BSEM-18 encoding gives every check site its own nullary relation:
//!
//! ```text
//! (rule (=> error_p4 error))
//! (rule (=> (and (f__bb6 x y …) <violation condition>) error_p4))
//! ```
//!
//! so `error_p4` is derivable only when the check's block atom `f__bb6` is
//! derivable — i.e. only when that check SITE is reachable. Drop the violation
//! condition, keep the block atom, and the same program answers the reachability
//! question instead of the safety one:
//!
//! ```text
//! (declare-rel ay_vacuity_reach ())
//! (rule (=> (f__bb6 x y …) ay_vacuity_reach))
//! (query ay_vacuity_reach)
//! ```
//!
//! `unsat` on that query is a PROOF that no check site is reachable, which is
//! exactly the all-UNREACHABLE shape V4 keys on.
//!
//! # Why a decided `unsat` cannot be a false vacuity report
//!
//! Every original rule is kept verbatim; the probe only ADDS a relation, the
//! rules deriving it, and its query (the `(query error)` form is dropped
//! because `error` is no longer the question). So `ay_vacuity_reach` is
//! derivable **iff** one of the check-site block atoms is derivable, under the
//! program's own rules. Dropping the violation condition makes each probe rule
//! strictly WEAKER than the obligation rule it came from, so the probe can only
//! ever be *more* derivable than `error` — it can never claim unreachability
//! that the program does not have.
//!
//! Every shape this module does not fully understand returns `None` and no
//! probe runs: a harness with no `error_pN` obligation rule, an obligation rule
//! whose body carries no block atom (a `false`/`true`-bodied discharge rule,
//! which the straight-line marker already covers), or content with no `(query`
//! form. `None` leaves the pre-probe verdict exactly as it was.
//!
//! # Cost: the witness first
//!
//! Almost every probe answers `sat` — a check site is reachable — which changes
//! nothing, and the external `ay` could spend its whole budget reaching it
//! (13.3 s of 15 s, still undecided, on `history/simple_pass` at ay
//! `6818b5d06`). So the caller first runs [`certified_probe_witness`]: an
//! in-process search for a derivation of `ay_vacuity_reach`, accepted only
//! after every constraint of the derivation re-evaluates to `true` under one
//! total assignment (`vacuity_witness`). It can only ever say "reachable", so it
//! cannot create or suppress a vacuity report; when it finds nothing, the
//! external probe runs with its full, unchanged budget.

use std::collections::BTreeSet;
use std::path::Path;
use std::process::Command;
use std::time::Duration;

use crate::session::{KaniSession, run_piped_with_timeout};

/// The nullary relation the probe queries.
pub(super) const PROBE_RELATION: &str = "ay_vacuity_reach";

/// A parsed s-expression node, carrying its byte range in the source text so a
/// sub-term can be copied out VERBATIM rather than re-printed (re-printing is
/// where an SMT rewriter silently changes a term).
#[derive(Debug)]
struct Node {
    start: usize,
    end: usize,
    /// Empty for an atom.
    children: Vec<Node>,
    is_list: bool,
}

impl Node {
    fn text<'a>(&self, src: &'a str) -> &'a str {
        &src[self.start..self.end]
    }

    /// The leading symbol of a list (`(foo a b)` -> `foo`), or the atom itself.
    fn head_symbol<'a>(&self, src: &'a str) -> Option<&'a str> {
        if self.is_list {
            let first = self.children.first()?;
            if first.is_list { None } else { Some(first.text(src)) }
        } else {
            Some(self.text(src))
        }
    }
}

/// Byte-offset scanner over SMT-LIB2 text: skips `;` comments, `|quoted|`
/// symbols and `"strings"` so a paren inside any of them is not counted.
struct Scanner<'a> {
    src: &'a [u8],
    pos: usize,
}

impl<'a> Scanner<'a> {
    fn new(src: &'a str) -> Self {
        Scanner { src: src.as_bytes(), pos: 0 }
    }

    fn skip_trivia(&mut self) {
        while self.pos < self.src.len() {
            match self.src[self.pos] {
                b' ' | b'\t' | b'\r' | b'\n' => self.pos += 1,
                b';' => {
                    while self.pos < self.src.len() && self.src[self.pos] != b'\n' {
                        self.pos += 1;
                    }
                }
                _ => return,
            }
        }
    }

    /// Parse one s-expression at the current position. `None` at end of input
    /// or on unbalanced text (the caller then abandons the whole probe).
    fn parse(&mut self) -> Option<Node> {
        self.skip_trivia();
        if self.pos >= self.src.len() {
            return None;
        }
        let start = self.pos;
        match self.src[self.pos] {
            b'(' => {
                self.pos += 1;
                let mut children = Vec::new();
                loop {
                    self.skip_trivia();
                    if self.pos >= self.src.len() {
                        return None; // unbalanced
                    }
                    if self.src[self.pos] == b')' {
                        self.pos += 1;
                        return Some(Node { start, end: self.pos, children, is_list: true });
                    }
                    children.push(self.parse()?);
                }
            }
            b')' => None,
            b'|' => {
                self.pos += 1;
                while self.pos < self.src.len() && self.src[self.pos] != b'|' {
                    self.pos += 1;
                }
                if self.pos >= self.src.len() {
                    return None;
                }
                self.pos += 1;
                Some(Node { start, end: self.pos, children: Vec::new(), is_list: false })
            }
            b'"' => {
                self.pos += 1;
                while self.pos < self.src.len() {
                    if self.src[self.pos] == b'"' {
                        // `""` is an escaped quote inside an SMT-LIB2 string.
                        if self.pos + 1 < self.src.len() && self.src[self.pos + 1] == b'"' {
                            self.pos += 2;
                            continue;
                        }
                        self.pos += 1;
                        break;
                    }
                    self.pos += 1;
                }
                Some(Node { start, end: self.pos, children: Vec::new(), is_list: false })
            }
            _ => {
                while self.pos < self.src.len() {
                    match self.src[self.pos] {
                        b' ' | b'\t' | b'\r' | b'\n' | b'(' | b')' | b';' => break,
                        _ => self.pos += 1,
                    }
                }
                Some(Node { start, end: self.pos, children: Vec::new(), is_list: false })
            }
        }
    }
}

/// Every top-level form, in source order. `None` if the text does not parse.
fn parse_forms(src: &str) -> Option<Vec<Node>> {
    let mut scanner = Scanner::new(src);
    let mut forms = Vec::new();
    loop {
        scanner.skip_trivia();
        if scanner.pos >= scanner.src.len() {
            return Some(forms);
        }
        forms.push(scanner.parse()?);
    }
}

/// `true` for the obligation relations the BSEM-18 encoding derives `error`
/// from — `error` itself and `error_p<digits>` / `error_definition_<digits>`.
/// They are never block atoms, so they are never probe sources.
fn is_error_relation(name: &str) -> bool {
    name == "error"
        || name
            .strip_prefix("error_p")
            .or_else(|| name.strip_prefix("error_definition_"))
            .is_some_and(|rest| !rest.is_empty() && rest.bytes().all(|b| b.is_ascii_digit()))
}

/// Collect every sub-term of `node` whose head symbol is a declared relation
/// that is not an `error*` relation — i.e. the block atoms a rule body rests on.
///
/// A block atom is either an application `(f__bb6 x y …)` or, for a NULLARY
/// relation, the bare symbol `f__bb6`. The nullary form is not exotic: frame
/// narrowing and dead-argument pruning strip every column from a block whose
/// only successor is an obligation, leaving `(rule (=> f__bb6 error_p1))`. In a
/// HORN program a declared relation symbol can appear bare only as such an
/// application, never as a term, so the bare form is recognised by the same
/// `rels` membership. Missing it made the whole probe decline ("an obligation
/// with no block atom"), which silently kept a vacuous proof as
/// `[AY:PROOF_QUALIFIERS:clean]` (tools/soundness-duals/lost_error_rules_dual.rs
/// on the array-param-mid-guard branch, where narrowing made the check-site
/// relation nullary).
fn collect_block_atoms(
    node: &Node,
    src: &str,
    rels: &BTreeSet<String>,
    out: &mut BTreeSet<String>,
) {
    if let Some(head) = node.head_symbol(src)
        && rels.contains(head)
        && !is_error_relation(head)
    {
        // `head_symbol` is the atom itself for a bare symbol, so this covers
        // both `(f__bb6 x …)` and the nullary `f__bb6`.
        out.insert(node.text(src).to_string());
        // A block atom's arguments are terms, never nested relation atoms, so
        // there is nothing further to find below it.
        return;
    }
    for child in &node.children {
        collect_block_atoms(child, src, rels, out);
    }
}

/// Build the reachability probe for a CHC harness program.
///
/// Returns `None` — meaning "do not probe, change nothing" — whenever the
/// content is not the shape this transformation is proved correct for.
pub(super) fn build_chc_reachability_probe(smt_content: &str) -> Option<String> {
    let forms = parse_forms(smt_content)?;

    let mut rels: BTreeSet<String> = BTreeSet::new();
    for form in &forms {
        if form.head_symbol(smt_content) == Some("declare-rel")
            && let Some(name) = form.children.get(1)
            && !name.is_list
        {
            rels.insert(name.text(smt_content).to_string());
        }
    }
    if rels.is_empty() {
        return None;
    }
    // A program that already declares the probe relation is not ours to rewrite.
    if rels.contains(PROBE_RELATION) {
        return None;
    }

    let mut query_ranges: Vec<(usize, usize)> = Vec::new();
    let mut atoms: BTreeSet<String> = BTreeSet::new();
    let mut obligation_rules = 0usize;

    for form in &forms {
        match form.head_symbol(smt_content) {
            Some("query") => query_ranges.push((form.start, form.end)),
            Some("rule") => {
                // `(rule (=> BODY HEAD))`. A bare `(rule HEAD)` fact has no
                // body and so states no reachability condition.
                let Some(implication) = form.children.get(1) else { continue };
                if !implication.is_list
                    || implication.head_symbol(smt_content) != Some("=>")
                    || implication.children.len() != 3
                {
                    continue;
                }
                let body = &implication.children[1];
                let head = &implication.children[2];
                let Some(head_name) = head.head_symbol(smt_content) else { continue };
                if head.is_list || !is_error_relation(head_name) || head_name == "error" {
                    continue;
                }
                obligation_rules += 1;
                let before = atoms.len();
                collect_block_atoms(body, smt_content, &rels, &mut atoms);
                if atoms.len() == before {
                    // An obligation with no block atom in its body: a
                    // `false`-bodied straight-line discharge, or a shape this
                    // module does not model. Either way its reachability is not
                    // decided by the atoms collected here, so probing would be
                    // a claim about a program we did not fully read.
                    return None;
                }
            }
            _ => {}
        }
    }

    if obligation_rules == 0 || atoms.is_empty() || query_ranges.is_empty() {
        return None;
    }

    // Drop the original `(query …)` forms: `error` is no longer the question,
    // and a second query would make the run's answer ambiguous.
    let mut probe = String::with_capacity(smt_content.len() + 256);
    let mut cursor = 0usize;
    for (start, end) in &query_ranges {
        probe.push_str(&smt_content[cursor..*start]);
        cursor = *end;
    }
    probe.push_str(&smt_content[cursor..]);
    if !probe.ends_with('\n') {
        probe.push('\n');
    }

    probe.push_str("; V4 vacuity probe: is ANY check site reachable at all?\n");
    probe.push_str(&format!("(declare-rel {PROBE_RELATION} ())\n"));
    for atom in &atoms {
        probe.push_str(&format!("(rule (=> {atom} {PROBE_RELATION}))\n"));
    }
    probe.push_str(&format!("(query {PROBE_RELATION})\n"));
    Some(probe)
}

/// What the probe decided about a would-be CHC proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ProbeOutcome {
    /// A DECIDED proof that no check site is reachable: every check passed only
    /// vacuously. The caller re-statuses them `Unreachable` for V4.
    NoCheckSiteReachable,
    /// A DECIDED counterexample: some check site is reachable, so the proof is
    /// about a harness that runs.
    Reachable,
    /// The same answer as [`ProbeOutcome::Reachable`], decided in process by a
    /// checked derivation (`vacuity_witness`) before any solver was spawned.
    ReachableByWitness,
    /// No answer — the shape was not probeable, no usable `ay`, a rejected
    /// command, a timeout, an `unknown`. Changes nothing.
    Undetermined,
}

impl ProbeOutcome {
    /// Stable label for the stage-timing marker.
    pub(super) fn label(self) -> &'static str {
        match self {
            Self::NoCheckSiteReachable => "no-reachable-check-site",
            Self::Reachable => "reachable",
            Self::ReachableByWitness => "reachable-witness",
            Self::Undetermined => "undetermined",
        }
    }
}

/// Cap on the in-process witness search's slice of the per-harness deadline.
/// Measured 2026-09-25 at ay `6818b5d06`: the search certifies the named slow
/// units' probes in well under a second; an unsuccessful search is bounded
/// here and then the external probe runs with its own, unchanged, budget.
pub(super) const WITNESS_SLICE_CAP: Duration = Duration::from_secs(3);

impl KaniSession {
    /// Ask whether ANY check site of this CHC harness is reachable.
    ///
    /// Only [`ProbeOutcome::NoCheckSiteReachable`] — a decided `unsat` on the
    /// probe query, from a run in which `ay` rejected no command — ever changes
    /// a verdict. Every other answer leaves the run exactly as it was, so a
    /// slow, absent or confused solver cannot invent a vacuity report.
    ///
    /// `probe` is the text [`build_chc_reachability_probe`] built; the caller
    /// has already given [`certified_probe_witness`] its chance to answer.
    pub(super) fn probe_chc_check_sites_reachable(
        &self,
        probe: &str,
        smt_file: &Path,
        budget: Duration,
    ) -> ProbeOutcome {
        let probe = crate::call_ay::normalize_smt_qualified_syntax(probe);

        // Fail closed (no answer) when no usable `ay` exists, including an
        // off-pin one that was not allowed — same rule as every other `ay`
        // subprocess in this driver.
        let solver_path = match crate::ay_binary::pinned_ay() {
            Ok(path) => path,
            Err(err) => {
                if self.args.common_args.verbose {
                    eprintln!("[AY] CHC vacuity probe skipped, no usable ay solver: {err:#}");
                }
                return ProbeOutcome::Undetermined;
            }
        };

        let probe_path = smt_file.with_extension("chc_vacuity_probe.smt2");
        if let Err(err) = std::fs::write(&probe_path, &probe) {
            if self.args.common_args.verbose {
                eprintln!("[AY] Failed to write CHC vacuity probe: {err}");
            }
            return ProbeOutcome::Undetermined;
        }

        // The probe is a REACHABILITY question about a program whose safety
        // proof already finished, so it gets a bounded slice rather than a
        // second full harness budget: an undecided probe is free (it changes
        // nothing), a slow one is not.
        // `budget` is the caller's slice of the per-harness deadline (one
        // per-call timeout at most); PROBE_BUDGET still caps it.
        let timeout = std::cmp::min(budget, PROBE_BUDGET);
        let mut cmd = Command::new(&solver_path);
        // Cooperative deadline inside the hard-kill window, so ay answers
        // `unknown` with stats instead of dying mid-phase.
        let cooperative_ms = timeout
            .as_millis()
            .saturating_sub(std::cmp::min(2_000, (timeout.as_millis() / 10) as u64) as u128);
        if cooperative_ms > 0 {
            cmd.arg("-t");
            cmd.arg(cooperative_ms.to_string());
        }
        cmd.arg(&probe_path);
        let output = run_piped_with_timeout(cmd, timeout);
        let _ = std::fs::remove_file(&probe_path);
        // ay writes its CHC certificate beside the input; the probe's copy is
        // scratch and nothing reads it.
        let _ = std::fs::remove_file(probe_path.with_extension("smt2.chccert"));

        let output = match output {
            Ok(output) => output,
            Err(err) => {
                if self.args.common_args.verbose {
                    eprintln!("[AY] CHC vacuity probe solver failed: {err}");
                }
                return ProbeOutcome::Undetermined;
            }
        };
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        if self.args.common_args.verbose {
            println!("[AY] CHC vacuity probe output:\n{stdout}");
        }

        // A rejected command is the one way an `unsat` here could be a lie:
        // ay discards the offending command and carries on, so a discarded
        // probe RULE would leave `ay_vacuity_reach` underivable for a reason
        // that has nothing to do with the program. Refuse to read that as
        // vacuity.
        let (rejections, first) = crate::call_ay::smt_command_rejections(&stdout, &stderr);
        if rejections > 0 {
            if self.args.common_args.verbose {
                eprintln!(
                    "[AY] CHC vacuity probe ignored: ay rejected {rejections} command(s): {}",
                    first.unwrap_or_default()
                );
            }
            return ProbeOutcome::Undetermined;
        }

        match classify_probe_output(&stdout) {
            Some(true) => ProbeOutcome::Reachable,
            Some(false) => ProbeOutcome::NoCheckSiteReachable,
            None => ProbeOutcome::Undetermined,
        }
    }
}

/// Answer the probe's question in process when a checked derivation of the
/// probe relation exists (`vacuity_witness`), within `slice`.
///
/// `Some(outcome)` is always [`ProbeOutcome::ReachableByWitness`]; `None` means
/// only "not shown here", and the external probe must run. The search reads
/// the probe text with cover metadata stripped, as the native solve reads the
/// harness (`strip_cover_assertions_for_chc_solver`).
pub(super) fn certified_probe_witness(
    probe: &str,
    slice: Duration,
    verbose: bool,
) -> Option<ProbeOutcome> {
    let started = std::time::Instant::now();
    let solver_text = crate::smt_io::strip_cover_assertions_for_chc_solver(probe);
    let search = super::vacuity_witness::certified_reach_witness(
        &solver_text,
        PROBE_RELATION,
        crate::deadline::Deadline::after(slice),
    );
    crate::stage_timing::record("chc-vacuity-witness", started, search.label());
    match search {
        super::vacuity_witness::WitnessSearch::Certified(reach) => {
            if verbose {
                eprintln!(
                    "[AY] CHC vacuity probe answered in process: a check site is reachable \
                     ({} clause instances, {} embedded SMT checks, every constraint \
                     re-evaluated exactly)",
                    reach.clause_instances, reach.smt_checks
                );
            }
            Some(ProbeOutcome::ReachableByWitness)
        }
        super::vacuity_witness::WitnessSearch::NotFound { reason, smt_checks } => {
            if verbose {
                eprintln!(
                    "[AY] CHC vacuity witness not found ({reason}, {smt_checks} embedded SMT \
                     checks); the external probe decides"
                );
            }
            None
        }
    }
}

/// The probe budget cap. A reachability query on an already-proved program is
/// normally trivial; this bounds the pathological case.
const PROBE_BUDGET: Duration = Duration::from_secs(120);

/// `Some(true)` = a check site is reachable (`sat`), `Some(false)` = none is
/// (`unsat`), `None` = no decided answer.
fn classify_probe_output(stdout: &str) -> Option<bool> {
    for line in stdout.lines() {
        match line.trim() {
            "sat" => return Some(true),
            "unsat" => return Some(false),
            _ => {}
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn probe_outcome_labels_are_distinct_and_stable() {
        let labels = [
            ProbeOutcome::NoCheckSiteReachable.label(),
            ProbeOutcome::Reachable.label(),
            ProbeOutcome::ReachableByWitness.label(),
            ProbeOutcome::Undetermined.label(),
        ];
        assert_eq!(
            labels,
            ["no-reachable-check-site", "reachable", "reachable-witness", "undetermined"]
        );
    }

    const PROGRAM: &str = "\
(set-logic HORN)
(declare-var x (_ BitVec 8))
(declare-rel f__bb0 ((_ BitVec 8)))
(declare-rel f__bb1 ((_ BitVec 8)))
(declare-rel error ())
(declare-rel error_p1 ())
(rule (=> true (f__bb0 x)))
(rule (=> (and (f__bb0 x) (bvult x #x05)) (f__bb1 x)))
(rule (=> error_p1 error))
(rule (=> (and (f__bb1 x) (bvult x #x02)) error_p1))
(query error)
";

    #[test]
    fn probe_queries_reachability_of_the_check_site() {
        let probe = build_chc_reachability_probe(PROGRAM).expect("probe built");
        assert!(probe.contains("(declare-rel ay_vacuity_reach ())"));
        assert!(probe.contains("(rule (=> (f__bb1 x) ay_vacuity_reach))"));
        assert!(probe.ends_with("(query ay_vacuity_reach)\n"));
        // The safety question is gone; the program's own rules are all kept.
        assert!(!probe.contains("(query error)"));
        assert!(probe.contains("(rule (=> (and (f__bb0 x) (bvult x #x05)) (f__bb1 x)))"));
        assert!(probe.contains("(rule (=> (and (f__bb1 x) (bvult x #x02)) error_p1))"));
        // The violation condition is NOT part of the probe rule.
        assert!(!probe.contains("(rule (=> (and (f__bb1 x) (bvult x #x02)) ay_vacuity_reach))"));
    }

    #[test]
    fn every_distinct_check_site_becomes_a_probe_source() {
        let program = PROGRAM.replace(
            "(query error)",
            "(declare-rel error_p2 ())\n\
             (rule (=> error_p2 error))\n\
             (rule (=> (and (f__bb0 x) (bvult x #x01)) error_p2))\n\
             (query error)",
        );
        let probe = build_chc_reachability_probe(&program).expect("probe built");
        assert!(probe.contains("(rule (=> (f__bb0 x) ay_vacuity_reach))"));
        assert!(probe.contains("(rule (=> (f__bb1 x) ay_vacuity_reach))"));
    }

    /// The shape frame narrowing leaves behind: the check-site block relation
    /// has lost every column, so the obligation body is the bare symbol. It is
    /// still a check site, and here no rule derives it, so the probe must be
    /// built (and would decide `unsat`, i.e. vacuous) instead of declining.
    const NULLARY_CHECK_SITE_PROGRAM: &str = "\
(set-logic HORN)
(declare-var x (_ BitVec 8))
(declare-rel f__bb0 ((_ BitVec 8)))
(declare-rel f__bb4 ((_ BitVec 8)))
(declare-rel f__bb6 ())
(declare-rel error ())
(declare-rel error_p1 ())
(rule (=> true (f__bb0 x)))
(rule (=> (f__bb0 x) (f__bb4 x)))
(rule (=> error_p1 error))
(rule (=> f__bb6 error_p1))
(query error)
";

    #[test]
    fn a_nullary_block_relation_is_a_check_site() {
        let probe = build_chc_reachability_probe(NULLARY_CHECK_SITE_PROGRAM).expect("probe built");
        assert!(probe.contains("(rule (=> f__bb6 ay_vacuity_reach))"));
        assert!(probe.ends_with("(query ay_vacuity_reach)\n"));
        assert!(!probe.contains("(query error)"));
        // The obligation relation itself is never a probe source.
        assert!(!probe.contains("(rule (=> error_p1 ay_vacuity_reach))"));
    }

    #[test]
    fn a_nullary_check_site_inside_a_conjunction_is_collected() {
        let program = NULLARY_CHECK_SITE_PROGRAM
            .replace("(rule (=> f__bb6 error_p1))", "(rule (=> (and f__bb6 true) error_p1))");
        let probe = build_chc_reachability_probe(&program).expect("probe built");
        assert!(probe.contains("(rule (=> f__bb6 ay_vacuity_reach))"));
    }

    /// End to end: the probe the builder writes is what the witness reads, and
    /// only a check site the program really derives is certified.
    #[test]
    fn the_witness_certifies_a_built_probe_only_when_a_site_is_derivable() {
        let slice = Duration::from_secs(30);
        let reachable = build_chc_reachability_probe(PROGRAM).expect("probe built");
        assert_eq!(
            certified_probe_witness(&reachable, slice, false),
            Some(ProbeOutcome::ReachableByWitness)
        );
        // The guard in front of the site contradicts the entry fact.
        let guarded =
            PROGRAM.replace("(rule (=> true (f__bb0 x)))", "(rule (=> (bvugt x #x09) (f__bb0 x)))");
        let unreachable = build_chc_reachability_probe(&guarded).expect("probe built");
        assert_eq!(certified_probe_witness(&unreachable, slice, false), None);
        let nullary =
            build_chc_reachability_probe(NULLARY_CHECK_SITE_PROGRAM).expect("probe built");
        assert_eq!(certified_probe_witness(&nullary, slice, false), None);
    }

    #[test]
    fn no_probe_without_an_obligation_rule() {
        let program = "\
(set-logic HORN)
(declare-rel error ())
(rule (=> false error))
(query error)
";
        assert!(build_chc_reachability_probe(program).is_none());
    }

    #[test]
    fn no_probe_when_an_obligation_body_has_no_block_atom() {
        // The straight-line discharge's `false`-bodied obligation: its
        // reachability is the compiler's marker to state, not this probe's.
        let program = PROGRAM.replace(
            "(rule (=> (and (f__bb1 x) (bvult x #x02)) error_p1))",
            "(rule (=> false error_p1))",
        );
        assert!(build_chc_reachability_probe(&program).is_none());
    }

    #[test]
    fn no_probe_when_one_obligation_of_several_has_no_block_atom() {
        let program = PROGRAM.replace(
            "(query error)",
            "(declare-rel error_p2 ())\n\
             (rule (=> error_p2 error))\n\
             (rule (=> true error_p2))\n\
             (query error)",
        );
        assert!(build_chc_reachability_probe(&program).is_none());
    }

    #[test]
    fn no_probe_without_a_query() {
        let program = PROGRAM.replace("(query error)", "");
        assert!(build_chc_reachability_probe(&program).is_none());
    }

    #[test]
    fn no_probe_on_unbalanced_content() {
        let program = PROGRAM.replace("(query error)", "(query error");
        assert!(build_chc_reachability_probe(&program).is_none());
    }

    #[test]
    fn a_paren_inside_a_comment_or_string_does_not_confuse_the_scanner() {
        let program = format!(
            "; a comment with ( an unbalanced paren\n{}",
            PROGRAM.replace(
                "(set-logic HORN)",
                "(set-logic HORN)\n(set-info :note \"a string with ( in it\")",
            )
        );
        let probe = build_chc_reachability_probe(&program).expect("probe built");
        assert!(probe.contains("(rule (=> (f__bb1 x) ay_vacuity_reach))"));
        assert!(probe.ends_with("(query ay_vacuity_reach)\n"));
    }

    #[test]
    fn error_definition_relations_are_obligations_not_block_atoms() {
        let program = PROGRAM
            .replace("(declare-rel error_p1 ())", "(declare-rel error_definition_7 ())")
            .replace("(rule (=> error_p1 error))", "(rule (=> error_definition_7 error))")
            .replace("error_p1))", "error_definition_7))");
        let probe = build_chc_reachability_probe(&program).expect("probe built");
        assert!(probe.contains("(rule (=> (f__bb1 x) ay_vacuity_reach))"));
        assert!(!probe.contains("error_definition_7 ay_vacuity_reach"));
    }

    #[test]
    fn a_program_that_already_uses_the_probe_relation_is_left_alone() {
        let program = PROGRAM.replace(
            "(declare-rel error ())",
            "(declare-rel error ())\n(declare-rel ay_vacuity_reach ())",
        );
        assert!(build_chc_reachability_probe(&program).is_none());
    }

    #[test]
    fn is_error_relation_names_only_the_obligation_family() {
        assert!(is_error_relation("error"));
        assert!(is_error_relation("error_p0"));
        assert!(is_error_relation("error_p42"));
        assert!(is_error_relation("error_definition_111"));
        assert!(!is_error_relation("error_px"));
        assert!(!is_error_relation("error_p"));
        assert!(!is_error_relation("errors"));
        assert!(!is_error_relation("f__bb6"));
    }
}
