// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The direct-call-summary census must be COMPLETE, UNAMBIGUOUS and INERT.
//!
//! `try_direct_call_summary` is the modular mechanism that lets a caller be
//! proved panic-free THROUGH a call. It declines through ~80 separate exits.
//! Before the census there was no counter of SUCCESSFUL summaries anywhere in
//! tree, and a decline reached the transport as one undifferentiated
//! `UnsupportedDirectCallSummary` diagnostic — so "why does the call summary
//! decline, and how often" could not be answered without re-deriving it by
//! hand, which three separate campaign runs did and none of which survived.
//!
//! Attribution is reported BY the interpreter, not reconstructed by an
//! external probe that mirrors the ladder. This file is what keeps that true:
//!
//! * `every_direct_call_summary_exit_is_labelled` — the DRIFT CHECK. A new
//!   `return None` or `?` in the interpreter that carries no label fails here,
//!   with its line printed. Without it the census would silently start
//!   attributing declines to `__unlabelled__`.
//! * `census_positive_control_and_zero_false_positives` — the instrument must
//!   be SEEN TO FIRE: a call that summarizes is reported as `Summarized`, a
//!   call that declines is reported at the exact exit, no row is both, and the
//!   row count equals an INDEPENDENT recount of `Inst::Call` sites in the IR.
//! * `census_does_not_perturb_the_translation` — the census is observational.
//!   The generated `ChcVc` must be identical with it on and off.

use std::collections::BTreeSet;

use trust_ir::inst::{Inst, UnOp};
use trust_ir::ty::Ty;
use trust_ir_build::ModuleBuilder;
use trust_mc_trust_bmc::{
    CallSummaryOutcome, TranslateOptions, trust_ir_to_chc_translation_outputs,
};

/// The interpreter's source, read at RUN time rather than `include_str!`d, so a
/// stale test binary cannot report a green about a file it no longer matches.
const TRANSLATE_CHC: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/src/translate_chc.rs");

/// Exits labelled today. Bumping this is the deliberate act of adding an exit —
/// it is not a formality: the census's cause split is only as complete as this.
const EXPECTED_LABELLED_EXITS: usize = 83;

/// Source of `try_direct_call_summary` + `call_summary_successor_state`, with
/// line comments removed.
fn interpreter_region() -> Vec<(usize, String)> {
    let source = std::fs::read_to_string(TRANSLATE_CHC)
        .unwrap_or_else(|error| panic!("read {TRANSLATE_CHC}: {error}"));
    let lines: Vec<&str> = source.lines().collect();

    let start = lines
        .iter()
        .position(|l| l.trim_start().starts_with("fn try_direct_call_summary("))
        .expect("try_direct_call_summary must exist");
    let end = lines
        .iter()
        .position(|l| l.trim_start().starts_with("fn add_transition_rule("))
        .expect("add_transition_rule follows the interpreter");
    assert!(start < end, "interpreter region is inverted");

    lines[start..end]
        .iter()
        .enumerate()
        .map(|(offset, line)| {
            // No string literal in this region contains `//`, so a plain split
            // is exact here. (A `?` or `return None` inside a comment is the
            // whole reason this strip exists: several of the interpreter's
            // comments quote both.)
            let code = line.split("//").next().unwrap_or("");
            (start + offset + 1, code.to_owned())
        })
        .collect()
}

#[test]
fn every_direct_call_summary_exit_is_labelled() {
    let region = interpreter_region();

    // Whitespace-free image plus a map back to source lines, so a violation can
    // be reported at the line a human has to edit.
    let mut image = String::new();
    let mut owner: Vec<usize> = Vec::new();
    for (line, code) in &region {
        for ch in code.chars().filter(|c| !c.is_whitespace()) {
            image.push(ch);
            owner.push(*line);
        }
    }

    let mut unlabelled_question: Vec<usize> = Vec::new();
    for (index, _) in image.match_indices('?') {
        let before = &image[..index];
        if !(before.ends_with("line!())") || before.ends_with("line!(),)")) {
            unlabelled_question.push(owner[index]);
        }
    }
    assert!(
        unlabelled_question.is_empty(),
        "these `?` exits in the call-summary interpreter carry no census label \
         (wrap the fallible expression in `.or_decline(decline, \"<tag>\", line!())`): \
         translate_chc.rs lines {unlabelled_question:?}"
    );

    let mut unlabelled_return: Vec<usize> = Vec::new();
    for (index, _) in image.match_indices("returnNone") {
        let window_start = index.saturating_sub(240);
        if !image[window_start..index].contains("decline.note") {
            unlabelled_return.push(owner[index]);
        }
    }
    assert!(
        unlabelled_return.is_empty(),
        "these `return None` exits in the call-summary interpreter carry no census label \
         (use `decline!(decline, \"<tag>\")`): translate_chc.rs lines {unlabelled_return:?}"
    );

    // Every tag must be unique: a duplicated tag makes the cause split a SUM
    // over unrelated exits, which is exactly the attribution failure the census
    // exists to remove. Scanned off the WHITESPACE-FREE image, so a label that
    // rustfmt wrapped across four lines is still found — a line-oriented
    // scanner silently missed exactly one label the first time this ran.
    let mut tags: Vec<String> = Vec::new();
    for pattern in [".or_decline(decline,\"", "decline!(decline,\"", "note_with_detail(\""] {
        let mut rest = image.as_str();
        while let Some(at) = rest.find(pattern) {
            rest = &rest[at + pattern.len()..];
            let close = rest.find('"').expect("an opened tag literal must close");
            tags.push(rest[..close].to_owned());
            rest = &rest[close + 1..];
        }
    }
    let unique: BTreeSet<&String> = tags.iter().collect();
    assert_eq!(
        unique.len(),
        tags.len(),
        "duplicate census tag — every exit must be separately nameable; tags: {tags:?}"
    );
    assert_eq!(
        tags.len(),
        EXPECTED_LABELLED_EXITS,
        "the labelled-exit count moved. If you ADDED an exit, label it and bump \
         EXPECTED_LABELLED_EXITS; if it dropped, a label was deleted and the census \
         is now attributing that decline to `__unlabelled__`. tags: {tags:?}"
    );
}

/// `summarizable(x) = !x` — a total unop, which the interpreter models.
/// `blocked(x)` allocates, which it does not.
/// `caller(x) = summarizable(x) + blocked(x)`-shaped: two direct calls, one of
/// each kind, so a single translation exercises both outcomes.
fn two_outcome_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("call_summary_census");
    let unary = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);

    let summarizable = {
        let mut fb = mb.function("summarizable", unary);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let x = fb.add_block_param(entry, Ty::I32);
        let y = fb.unop(UnOp::Not, Ty::I32, x);
        fb.ret(vec![y]);
        fb.build()
    };

    let blocked = {
        let mut fb = mb.function("blocked", unary);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let x = fb.add_block_param(entry, Ty::I32);
        // `Alloca` has no arm in the bounded summary interpreter, so this callee
        // takes the anonymous catch-all exit — with `Alloca` as the detail.
        let _slot = fb.alloca(Ty::I32);
        fb.ret(vec![x]);
        fb.build()
    };

    {
        let mut fb = mb.function("caller", unary);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let x = fb.add_block_param(entry, Ty::I32);
        let good = fb.call(summarizable, vec![x]);
        let bad = fb.call(blocked, vec![good]);
        fb.ret(vec![bad]);
        fb.build();
    }

    mb.build()
}

fn census_options() -> TranslateOptions {
    TranslateOptions { collect_call_summary_census: true, ..TranslateOptions::default() }
}

#[test]
fn census_positive_control_and_zero_false_positives() {
    let module = two_outcome_module();
    let outputs = trust_ir_to_chc_translation_outputs(&module, &census_options());
    let rows: Vec<_> = outputs.iter().flat_map(|o| o.call_summary_census.iter()).collect();

    // CONSERVATION / instrument-fired: one row per `Inst::Call`, counted
    // independently off the IR rather than off the census itself. A census that
    // silently produced nothing — the failure mode that once read a corpus of
    // 361 fixtures as "zero obligations" — cannot pass this.
    let call_sites = module
        .functions
        .iter()
        .flat_map(|f| f.blocks.iter())
        .flat_map(|b| b.body.iter())
        .filter(|n| matches!(n.inst, Inst::Call { .. }))
        .count();
    assert!(call_sites > 0, "the fixture must contain direct calls");
    assert_eq!(
        rows.len(),
        call_sites,
        "the census must report exactly one row per direct-call site"
    );

    // POSITIVE CONTROL: the modelled callee is reported as a SUCCESS. This is
    // the number nobody could previously obtain.
    let summarized: Vec<_> = rows
        .iter()
        .filter(|r| r.outcome == CallSummaryOutcome::Summarized)
        .map(|r| r.callee.as_str())
        .collect();
    assert_eq!(
        summarized,
        vec!["summarizable"],
        "the modelled callee must be reported as summarized"
    );

    // ...and the unmodelled callee is attributed to its EXACT exit, split by
    // opcode rather than lumped into one anonymous catch-all.
    let declined: Vec<_> = rows
        .iter()
        .filter_map(|r| match &r.outcome {
            CallSummaryOutcome::Declined { site, detail } => {
                Some((r.callee.as_str(), site.tag, detail.clone()))
            }
            _ => None,
        })
        .collect();
    assert_eq!(
        declined,
        vec![("blocked", "unmodeled_instruction", Some("Alloca".to_owned()))],
        "an unmodelled construct must be attributed to its labelled exit, with the opcode"
    );

    // ZERO FALSE POSITIVES: nothing lands on the unlabelled sentinel, and the
    // four buckets partition the rows exactly — no row is counted twice and
    // none escapes the split.
    let mut buckets = (0usize, 0usize, 0usize, 0usize);
    for row in &rows {
        match &row.outcome {
            CallSummaryOutcome::Summarized => buckets.0 += 1,
            CallSummaryOutcome::SummarizedArityMismatch => buckets.1 += 1,
            CallSummaryOutcome::NotAttempted { .. } => buckets.2 += 1,
            CallSummaryOutcome::Declined { site, .. } => {
                assert_ne!(
                    site.tag, "__unlabelled__",
                    "a decline reached the census with no labelled exit at {}:{} — \
                     an exit lost its label",
                    row.caller, row.instruction_index
                );
                buckets.3 += 1;
            }
            other => panic!("unclassified census outcome: {other:?}"),
        }
    }
    assert_eq!(
        buckets.0 + buckets.1 + buckets.2 + buckets.3,
        rows.len(),
        "the outcome buckets must partition the census rows"
    );
}

#[test]
fn census_is_off_by_default() {
    let module = two_outcome_module();
    let outputs = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
    assert!(
        outputs.iter().all(|o| o.call_summary_census.is_empty()),
        "the census must allocate nothing on the default production path"
    );
}

#[test]
fn census_does_not_perturb_the_translation() {
    // The census is diagnostic: it must observe the translation, never change
    // it. Compare the generated VCs rule-for-rule with the census on and off.
    let module = two_outcome_module();
    let off = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
    let on = trust_ir_to_chc_translation_outputs(&module, &census_options());

    assert_eq!(off.len(), on.len());
    for (a, b) in off.iter().zip(on.iter()) {
        // Compare the ORDERED content only. `ChcVc` also carries a hash set
        // whose `Debug` order varies between two runs of the SAME build, so a
        // whole-struct `{:?}` comparison reports a difference that is not one.
        assert_eq!(
            format!("{:?}", (a.vc.vars(), &a.vc.relations, &a.vc.rules, &a.vc.query)),
            format!("{:?}", (b.vc.vars(), &b.vc.relations, &b.vc.rules, &b.vc.query)),
            "enabling the call-summary census changed the generated CHC VC"
        );
        assert_eq!(
            a.diagnostics, b.diagnostics,
            "enabling the call-summary census changed the fail-closed diagnostics"
        );
    }
}
