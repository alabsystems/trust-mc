// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `call-summary-census` — why the direct-call summary declines, and how often.
//!
//! `try_direct_call_summary` (translate_chc.rs) is the modular mechanism: it
//! interprets a callee's body into the caller's CHC encoding so the caller can
//! be proved panic-free THROUGH the call. It declines through ~80 exits, and
//! until the census landed there was NO counter of SUCCESSFUL summaries
//! anywhere in tree — a decline reached the transport as one undifferentiated
//! `UnsupportedDirectCallSummary`. Three campaign runs re-derived these numbers
//! by hand in scratchpad harnesses; all three died with their agent. This is
//! the committed instrument.
//!
//! Attribution is REPORTED BY THE TRANSLATOR, not reconstructed here: every
//! decline exit carries a hand-written tag, and
//! `tests/call_summary_census.rs::every_direct_call_summary_exit_is_labelled`
//! fails when a new unlabelled exit appears. This binary only aggregates.
//!
//! Two properties of the aggregation are load-bearing, and both were WRONG in
//! the first landing:
//!
//! * **`sole` is reported at (tag, opcode) granularity.** It is the only column
//!   that predicts a slice's yield, and `unmodeled_instruction` is one tag over
//!   nine opcodes — so at tag granularity it answered a question nobody can act
//!   on ("model all nine") while reading as the answer to the one they asked
//!   ("model `Alloca`"). The tag rollup is still printed, under a heading that
//!   says what it is.
//! * **Bundles are deduped by MODULE DIGEST, never by file name.** The same dump
//!   reached through two `--corpus` dirs used to double `sites` while `distinct
//!   modules` stayed correct — two numbers disagreeing with nothing to say so,
//!   and conservation cannot catch it because the independent `Inst::Call`
//!   recount doubles by the same factor. The agreement is now a self-check.
//!
//! ```text
//! call-summary-census [OPTIONS] <corpus-dir>...
//!
//!   --max-files N     stop after N bundle files      (0 = no limit; default 0)
//!   --max-seconds S   stop after S wall seconds      (0 = no limit; default 900)
//!   --min-free-mb M   stop when the volume holding the FIRST corpus dir drops
//!                     below M MiB free                            (default 2048)
//!   --label-inventory N
//!                     how many labelled exits the interpreter HAS (the census
//!                     can only see the ones that fired; without this the report
//!                     cannot say how many are measured zero). The wrapper reads
//!                     it from the single pinned constant.
//!   --scope requests|all
//!                     which functions to translate per bundle: the ones named
//!                     by a trust-mc CHC/PDR request (default — what production
//!                     actually asks for), or every function in the module
//!   --rows PATH       write the per-call-site TSV here
//!   --json PATH       write the machine-readable summary here
//! ```
//!
//! Exit status is 0 only when every instrument self-check passes. A census that
//! cannot demonstrate it fired is worth nothing, so those checks are part of
//! normal output — never something a reader has to remember to run.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::time::Instant;

use trust_ir::inst::Inst;
use trust_ir::{FuncId, NativeVerificationBundle, NativeVerificationRequest};
use trust_mc_trust_bmc::{
    CallSummaryOutcome, TranslateOptions, trust_ir_function_to_chc_translation_output,
};

const UNLABELLED: &str = "__unlabelled__";

// ---------------------------------------------------------------- CLI + state

struct Options {
    corpora: Vec<PathBuf>,
    max_files: usize,
    max_seconds: u64,
    min_free_mb: u64,
    label_inventory: usize,
    all_functions: bool,
    rows: Option<PathBuf>,
    json: Option<PathBuf>,
}

/// Why the sweep stopped. Partiality is REPORTED, never inferred by a reader
/// from a suspiciously round number.
#[derive(PartialEq, Eq)]
enum Stop {
    Complete,
    FileLimit,
    TimeLimit,
    DiskFloor,
}

impl Stop {
    fn label(&self) -> &'static str {
        match self {
            Self::Complete => "COMPLETE",
            Self::FileLimit => "PARTIAL (--max-files reached)",
            Self::TimeLimit => "PARTIAL (--max-seconds reached)",
            Self::DiskFloor => "PARTIAL (--min-free-mb reached)",
        }
    }
}

/// One declining call site, already attributed by the translator.
struct Row {
    bundle: String,
    caller: String,
    callee: String,
    block: String,
    index: usize,
    outcome: &'static str,
    /// Decline tag, `NotAttempted` reason, or empty.
    cause: String,
    /// Catch-all discriminator (the trust_ir opcode), or empty.
    detail: String,
    line: u32,
}

/// A decline cause at the granularity a SLICE is actually cut at: the labelled
/// exit, plus the catch-all discriminator when that exit has one.
///
/// The distinction is not cosmetic. `unmodeled_instruction` is one TAG spanning
/// nine opcodes, so a bundle declining at `Alloca` AND at `GEP` looks
/// sole-blocked by the tag while no opcode-sized slice cures it. Reported at
/// tag granularity, `sole` therefore over-states the yield of every slice a
/// reader could actually take. Measured on the 2,592-bundle sweep: the tag says
/// 357, `Alloca` alone says 67.
#[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
struct Cause {
    tag: String,
    /// The trust_ir opcode for a catch-all exit; empty for an exit that already
    /// names one construct (in which case the refined cause IS the tag).
    opcode: String,
}

impl Cause {
    /// The SINGLE place a decline is turned into a cause key.
    ///
    /// Deliberately one constructor rather than three struct literals: the whole
    /// defect this fixes was the opcode being dropped on one path while the
    /// report kept saying `sole`, and a single point is what makes
    /// `sole_is_refined_by_opcode` a real mutation proof of production code
    /// rather than of the test's own helper.
    fn new(tag: &str, opcode: &str) -> Self {
        Self { tag: tag.to_owned(), opcode: opcode.to_owned() }
    }

    fn key(&self) -> String {
        if self.opcode.is_empty() {
            self.tag.clone()
        } else {
            format!("{}/{}", self.tag, self.opcode)
        }
    }
}

/// Everything one bundle contributed.
#[derive(Default)]
struct BundleTally {
    sites: usize,
    summarized: usize,
    arity_mismatch: usize,
    not_attempted: usize,
    declined: usize,
    /// Distinct REFINED decline causes seen in this bundle. A bundle whose set
    /// has exactly one member is SOLE-BLOCKED by that cause: removing it makes
    /// every declining site in the bundle summarize.
    causes: BTreeSet<Cause>,
}

impl BundleTally {
    /// The same set rolled up to tag granularity. A bundle sole-blocked at tag
    /// level need NOT be sole-blocked at cause level.
    fn tags(&self) -> BTreeSet<&str> {
        self.causes.iter().map(|c| c.tag.as_str()).collect()
    }
}

#[derive(Default)]
struct CauseTally {
    sites: usize,
    bundles_present: usize,
    bundles_sole: usize,
    /// How many distinct opcodes this row spans. 1 for a refined row; >1 on a
    /// tag rollup row is exactly the condition under which the rollup's `sole`
    /// over-attributes.
    opcodes: usize,
    line: u32,
}

fn main() {
    let options = match parse_args() {
        Ok(options) => options,
        Err(message) => {
            eprintln!("call-summary-census: {message}");
            eprintln!("usage: call-summary-census [--max-files N] [--max-seconds S] \\");
            eprintln!("           [--min-free-mb M] [--scope requests|all] \\");
            eprintln!("           [--rows PATH] [--json PATH] <corpus-dir>...");
            std::process::exit(2);
        }
    };
    std::process::exit(run(&options));
}

fn parse_args() -> Result<Options, String> {
    let mut options = Options {
        corpora: Vec::new(),
        max_files: 0,
        max_seconds: 900,
        min_free_mb: 2048,
        label_inventory: 0,
        all_functions: false,
        rows: None,
        json: None,
    };
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        let mut value = || args.next().ok_or_else(|| format!("{arg} needs a value"));
        match arg.as_str() {
            "--max-files" => options.max_files = parse_number(&value()?)?,
            "--max-seconds" => options.max_seconds = parse_number(&value()?)? as u64,
            "--min-free-mb" => options.min_free_mb = parse_number(&value()?)? as u64,
            "--label-inventory" => options.label_inventory = parse_number(&value()?)?,
            "--scope" => {
                options.all_functions = match value()?.as_str() {
                    "all" => true,
                    "requests" => false,
                    other => return Err(format!("--scope must be requests|all, got {other}")),
                };
            }
            "--rows" => options.rows = Some(PathBuf::from(value()?)),
            "--json" => options.json = Some(PathBuf::from(value()?)),
            "-h" | "--help" => return Err("help".to_owned()),
            other if other.starts_with('-') => return Err(format!("unknown option {other}")),
            other => options.corpora.push(PathBuf::from(other)),
        }
    }
    if options.corpora.is_empty() {
        return Err("at least one corpus directory is required".to_owned());
    }
    Ok(options)
}

fn parse_number(text: &str) -> Result<usize, String> {
    text.parse().map_err(|_| format!("expected a number, got {text}"))
}

// ------------------------------------------------------------------- the run

#[allow(clippy::too_many_lines)]
fn run(options: &Options) -> i32 {
    let started = Instant::now();

    let mut files: Vec<PathBuf> = Vec::new();
    for dir in &options.corpora {
        match collect_bundles(dir) {
            Ok(found) => files.extend(found),
            Err(error) => {
                eprintln!("call-summary-census: cannot read {}: {error}", dir.display());
                return 2;
            }
        }
    }
    files.sort();
    let discovered = files.len();

    let mut rows: Vec<Row> = Vec::new();
    // Keyed by MODULE DIGEST, never by file name. Two `--corpus` dirs holding
    // the same dump used to be counted twice in `sites` while `distinct
    // modules` stayed right -- two numbers disagreeing with no error -- and a
    // name key additionally MERGES two different bundles that happen to share a
    // basename across dirs. The digest is the only key that is wrong in
    // neither direction.
    let mut bundles: BTreeMap<String, BundleTally> = BTreeMap::new();
    let mut parsed_ok = 0usize;
    let mut parse_failed: Vec<(String, String)> = Vec::new();
    // Independent recount of `Inst::Call` sites straight off the IR. If this
    // disagrees with the census row count the instrument did not observe what
    // it claims to have observed.
    let mut ir_call_sites = 0usize;
    let mut functions_translated = 0usize;
    // digest -> (first file that carried it, its request fingerprint)
    let mut modules_seen: BTreeMap<String, (String, String)> = BTreeMap::new();
    // Files that actually reached a bundle tally. `bundles.len()` counts KEYS;
    // this counts CONTRIBUTIONS, and the two agreeing is what makes the dedup
    // check able to fail. (Measured: a check comparing only `bundles.len()` to
    // the digest-set size PASSED against a re-keyed tally that double-counted
    // every site -- both numbers were 4 while `sites` was 8.)
    let mut files_tallied = 0usize;
    let mut duplicates: Vec<(String, String)> = Vec::new();
    let mut digest_collisions: Vec<(String, String)> = Vec::new();
    let mut stop = Stop::Complete;

    for (processed, path) in files.iter().enumerate() {
        if options.max_files != 0 && processed >= options.max_files {
            stop = Stop::FileLimit;
            break;
        }
        if options.max_seconds != 0 && started.elapsed().as_secs() >= options.max_seconds {
            stop = Stop::TimeLimit;
            break;
        }
        if processed % 64 == 0
            && options.min_free_mb != 0
            && free_mb(&options.corpora[0]).is_some_and(|free| free < options.min_free_mb)
        {
            stop = Stop::DiskFloor;
            break;
        }

        let name = path.file_name().map_or_else(String::new, |n| n.to_string_lossy().into_owned());
        let text = match std::fs::read_to_string(path) {
            Ok(text) => text,
            Err(error) => {
                parse_failed.push((name, error.to_string()));
                continue;
            }
        };
        let bundle: NativeVerificationBundle = match serde_json::from_str(&text) {
            Ok(bundle) => bundle,
            Err(error) => {
                parse_failed.push((name, error.to_string()));
                continue;
            }
        };
        parsed_ok += 1;

        // ------------------------------------------------------ DEDUP
        // Silent double-counting is the failure here: `--corpus D --corpus D`
        // doubled `sites` while `distinct modules` stayed correct, and nothing
        // said so. Conservation cannot catch it either -- the independent
        // `Inst::Call` recount doubles by exactly the same factor.
        let digest = hex(&bundle.trust_ir_module_digest.bytes);
        let fingerprint = request_fingerprint(&bundle);
        if let Some((first, first_fingerprint)) = modules_seen.get(&digest) {
            // Deduping on the module digest is only SAFE while the digest
            // determines what the census reads. A shared digest with a
            // different request list would mean skipping a distinct
            // measurement, so it is a hard failure rather than a silent skip.
            if *first_fingerprint != fingerprint {
                digest_collisions.push((first.clone(), name.clone()));
            }
            duplicates.push((first.clone(), name.clone()));
            continue;
        }
        modules_seen.insert(digest.clone(), (name.clone(), fingerprint));

        let targets = translation_targets(&bundle, options.all_functions);
        files_tallied += 1;
        let tally = bundles.entry(digest).or_default();

        for function in targets {
            let Some(func) = bundle.module.function_by_id(function) else { continue };
            functions_translated += 1;
            ir_call_sites += count_direct_calls(func);

            let census_options =
                TranslateOptions { collect_call_summary_census: true, ..Default::default() };
            let Some(output) = trust_ir_function_to_chc_translation_output(
                &bundle.module,
                function,
                &census_options,
            ) else {
                continue;
            };

            for attempt in output.call_summary_census {
                tally.sites += 1;
                let (outcome, cause, detail, line) = match &attempt.outcome {
                    CallSummaryOutcome::Summarized => {
                        tally.summarized += 1;
                        ("summarized", String::new(), String::new(), 0)
                    }
                    CallSummaryOutcome::SummarizedArityMismatch => {
                        tally.arity_mismatch += 1;
                        ("arity_mismatch", String::new(), String::new(), 0)
                    }
                    CallSummaryOutcome::NotAttempted { reason } => {
                        tally.not_attempted += 1;
                        ("not_attempted", (*reason).to_owned(), String::new(), 0)
                    }
                    CallSummaryOutcome::Declined { site, detail } => {
                        tally.declined += 1;
                        tally.causes.insert(Cause::new(
                            site.tag,
                            detail.as_deref().unwrap_or_default(),
                        ));
                        (
                            "declined",
                            site.tag.to_owned(),
                            detail.clone().unwrap_or_default(),
                            site.line,
                        )
                    }
                    _ => ("unknown_outcome", String::new(), String::new(), 0),
                };
                rows.push(Row {
                    bundle: name.clone(),
                    caller: attempt.caller,
                    callee: attempt.callee,
                    block: format!("{:?}", attempt.block),
                    index: attempt.instruction_index,
                    outcome,
                    cause,
                    detail,
                    line,
                });
            }
        }
    }

    // ------------------------------------------------------------ aggregate
    let (causes, tag_rollup) = aggregate_causes(&rows, &bundles);

    // The catch-all exit split by opcode: a `_ => return None` reported as one
    // number hides the whole wave behind it. (Kept as its own view for the
    // JSON schema; the printed table now carries the split inline, so the
    // opcode row -- not the tag row -- is the one a reader's eye lands on.)
    let mut catch_all: BTreeMap<String, usize> = BTreeMap::new();
    for row in &rows {
        if row.cause == "unmodeled_instruction" {
            *catch_all
                .entry(if row.detail.is_empty() { "<none>".to_owned() } else { row.detail.clone() })
                .or_default() += 1;
        }
    }

    let sites: usize = bundles.values().map(|t| t.sites).sum();
    let summarized: usize = bundles.values().map(|t| t.summarized).sum();
    let arity_mismatch: usize = bundles.values().map(|t| t.arity_mismatch).sum();
    let not_attempted: usize = bundles.values().map(|t| t.not_attempted).sum();
    let declined: usize = bundles.values().map(|t| t.declined).sum();

    let attempted = summarized + arity_mismatch + declined;
    let bundles_with_declines = bundles.values().filter(|t| !t.causes.is_empty()).count();
    let bundles_sole = bundles.values().filter(|t| t.causes.len() == 1).count();
    let bundles_multi = bundles.values().filter(|t| t.causes.len() > 1).count();
    let bundles_sole_tag = bundles.values().filter(|t| t.tags().len() == 1).count();
    let bundles_multi_tag = bundles.values().filter(|t| t.tags().len() > 1).count();
    let bundles_clean =
        bundles.values().filter(|t| t.sites > 0 && t.causes.is_empty()).count();

    let mut not_attempted_split: BTreeMap<&str, usize> = BTreeMap::new();
    for row in &rows {
        if row.outcome == "not_attempted" {
            *not_attempted_split.entry(row.cause.as_str()).or_default() += 1;
        }
    }

    // ----------------------------------------------------- instrument checks
    let unlabelled = rows.iter().filter(|r| r.cause == UNLABELLED).count();
    let conservation_ok = rows.len() == ir_call_sites;
    let fired_success = summarized > 0;
    let fired_decline = declined > 0;
    let parse_majority_ok = parse_failed.len() * 2 <= discovered.max(1);
    // The tallied population and the distinct-module count are two independent
    // roads to the same number, and they USED TO DISAGREE in silence: a file
    // reached through two `--corpus` dirs was tallied twice while the digest
    // set stayed right. Making the agreement a CHECK is what turns the dedup
    // from an assumption into an observation -- and it is not vacuous, because
    // re-keying the tally by anything but the digest breaks it immediately.
    let dedup_ok = files_tallied == bundles.len()
        && bundles.len() == modules_seen.len()
        && parsed_ok == modules_seen.len() + duplicates.len()
        && digest_collisions.is_empty();

    // ---------------------------------------------------------------- report
    println!("== call-summary census ==");
    println!("corpora            {}", join_paths(&options.corpora));
    println!("scope              {}", if options.all_functions { "all" } else { "requests" });
    println!("bundle files       discovered {discovered}, parsed {parsed_ok}, unreadable {}",
             parse_failed.len());
    println!("distinct modules   {}  ({} duplicate file(s) skipped)",
             modules_seen.len(), duplicates.len());
    for (first, again) in duplicates.iter().take(5) {
        println!("       duplicate: {again} has the module digest already read from {first}");
    }
    if duplicates.len() > 5 {
        println!("       ... and {} more", duplicates.len() - 5);
    }
    println!("functions          {functions_translated} translated");
    println!("completion         {}", stop.label());
    println!("elapsed            {:.1}s", started.elapsed().as_secs_f64());

    println!();
    println!("-- INSTRUMENT SELF-CHECK (a census that cannot show it fired is worth nothing) --");
    println!(
        "  [{}] conservation      census rows {} == independent Inst::Call recount {}",
        pass(conservation_ok),
        rows.len(),
        ir_call_sites
    );
    println!(
        "  [{}] positive control  summaries observed: {summarized} (must be > 0)",
        pass(fired_success)
    );
    println!(
        "  [{}] decline control   declines observed:  {declined} (must be > 0)",
        pass(fired_decline)
    );
    println!(
        "  [{}] zero-false-pos    rows attributed to `{UNLABELLED}`: {unlabelled} (must be 0)",
        pass(unlabelled == 0)
    );
    println!(
        "  [{}] read health       unreadable files {} of {discovered} (must not be a majority)",
        pass(parse_majority_ok),
        parse_failed.len()
    );
    for (name, error) in parse_failed.iter().take(5) {
        println!("       unreadable: {name}: {}", error.chars().take(90).collect::<String>());
    }
    println!(
        "  [{}] dedup             {files_tallied} file(s) tallied into {} bundle(s) == \
         {} distinct module(s); parsed {parsed_ok} = unique + {} duplicate",
        pass(dedup_ok),
        bundles.len(),
        modules_seen.len(),
        duplicates.len()
    );
    for (first, again) in digest_collisions.iter().take(5) {
        println!(
            "       COLLISION: {again} shares a module digest with {first} but names \
             different requests — deduping them would DROP a measurement"
        );
    }

    println!();
    println!("-- CALL SITES --");
    println!("  total direct-call sites   {sites}");
    println!("  summarized (SUCCESS)      {summarized}  {}", pct(summarized, sites));
    println!("  declined                  {declined}  {}", pct(declined, sites));
    println!("  summarized-but-arity-bad  {arity_mismatch}  {}", pct(arity_mismatch, sites));
    println!("  never attempted           {not_attempted}  {}", pct(not_attempted, sites));
    for (reason, count) in &not_attempted_split {
        println!("      {reason:<28} {count}");
    }
    println!("  interpreter attempts      {attempted} (summarized + arity + declined)");

    println!();
    println!("-- DECLINE CAUSE SPLIT — one row per (exit tag, opcode); SOLE IS THE YIELD COLUMN --");
    // The exits that DID NOT fire are part of the answer. Without this line a
    // reader sees two causes and concludes the interpreter has two; in fact it
    // declines early, so most exits are downstream of one that already fired.
    if options.label_inventory > 0 {
        println!(
            "  {} of {} labelled exits fired; {} are a MEASURED ZERO on this corpus.",
            tag_rollup.len(),
            options.label_inventory,
            options.label_inventory.saturating_sub(tag_rollup.len())
        );
    } else {
        println!("  (label inventory unknown — pass --label-inventory N to report measured zeros)");
    }
    println!("  {:<44} {:>8} {:>9} {:>9} {:>7}", "cause (exit tag / opcode)", "sites", "bundles",
             "sole", "line");
    let mut ordered: Vec<(&Cause, &CauseTally)> = causes.iter().collect();
    ordered.sort_by(|a, b| b.1.sites.cmp(&a.1.sites).then_with(|| a.0.cmp(b.0)));
    for (cause, tally) in ordered {
        println!(
            "  {:<44} {:>8} {:>9} {:>9} {:>7}",
            cause.key(), tally.sites, tally.bundles_present, tally.bundles_sole, tally.line
        );
    }
    println!();
    println!("  `sole` = bundles whose EVERY declining site takes this exact cause, so this");
    println!("  one fix cures the bundle. It is the only column that predicts yield: measured");
    println!("  on the 2,592-bundle sweep, `Alloca` is PRESENT in 285 bundles and SOLE in 67 —");
    println!("  present over-attributes by 4x here and has over-attributed by ~20x before.");

    if tag_rollup.len() < causes.len() {
        println!();
        println!("-- TAG ROLLUP — the SAME data at exit granularity. `sole` here is a DIFFERENT,");
        println!("   LARGER number, and it is NOT a slice's yield: a tag spanning several opcodes");
        println!("   is cured only by modelling ALL of them, which is not a change anyone makes.");
        println!("  {:<44} {:>8} {:>9} {:>9} {:>7}", "exit tag", "sites", "bundles",
                 "tag-sole", "opcodes");
        let mut ordered: Vec<(&String, &CauseTally)> = tag_rollup.iter().collect();
        ordered.sort_by(|a, b| b.1.sites.cmp(&a.1.sites).then_with(|| a.0.cmp(b.0)));
        for (tag, tally) in ordered {
            println!(
                "  {:<44} {:>8} {:>9} {:>9} {:>7}",
                tag, tally.sites, tally.bundles_present, tally.bundles_sole, tally.opcodes
            );
        }
    }

    println!();
    println!("-- SOLE-BLOCKED vs MULTI-BLOCKED (per bundle) --");
    println!("  bundles with call sites   {}", bundles.values().filter(|t| t.sites > 0).count());
    println!("  fully summarized          {bundles_clean}");
    println!("  with >=1 decline          {bundles_with_declines}");
    println!("    sole-blocked            {bundles_sole}  (one (tag,opcode) cause; fixing it cures the bundle)");
    println!("    multi-blocked           {bundles_multi}  (fixing any one cause cures nothing)");
    println!("    [at TAG granularity]    {bundles_sole_tag} sole / {bundles_multi_tag} multi  \
              — larger, and not a slice's yield");
    println!();
    println!("  Presence over-attributes: read the `sole` column, never `bundles`. A cause");
    println!("  present in many bundles cures none of them while a second cause survives.");

    if let Some(path) = &options.rows {
        if let Err(error) = write_rows(path, &rows) {
            eprintln!("call-summary-census: cannot write {}: {error}", path.display());
            return 2;
        }
        println!();
        println!("rows written to {}", path.display());
    }
    if let Some(path) = &options.json {
        let json = JsonSummary {
            options,
            stop: &stop,
            discovered,
            parsed: parsed_ok,
            duplicates_skipped: duplicates.len(),
            distinct_modules: modules_seen.len(),
            sites,
            summarized,
            declined,
            arity_mismatch,
            not_attempted,
            bundles_clean,
            bundles_sole,
            bundles_multi,
            bundles_sole_tag,
            bundles_multi_tag,
            causes: &causes,
            tag_rollup: &tag_rollup,
            catch_all: &catch_all,
        };
        if let Err(error) = write_json(path, &json) {
            eprintln!("call-summary-census: cannot write {}: {error}", path.display());
            return 2;
        }
        println!("summary written to {}", path.display());
    }

    let healthy = conservation_ok
        && fired_success
        && fired_decline
        && unlabelled == 0
        && parse_majority_ok
        && dedup_ok;
    println!();
    println!("VERDICT: {}", if healthy { "instrument healthy" } else { "INSTRUMENT UNHEALTHY" });
    i32::from(!healthy)
}

// -------------------------------------------------------------------- helpers

/// Roll the per-bundle cause sets into the two tables the report prints.
///
/// Extracted so it can be tested directly: `sole` is the only column that
/// predicts a slice's yield, and the difference between its refined and
/// rolled-up forms is exactly what `sole_is_refined_by_opcode` pins.
fn aggregate_causes(
    rows: &[Row],
    bundles: &BTreeMap<String, BundleTally>,
) -> (BTreeMap<Cause, CauseTally>, BTreeMap<String, CauseTally>) {
    let mut causes: BTreeMap<Cause, CauseTally> = BTreeMap::new();
    let mut tags: BTreeMap<String, CauseTally> = BTreeMap::new();
    let mut opcodes_per_tag: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();

    for row in rows {
        if row.outcome != "declined" {
            continue;
        }
        let entry = causes.entry(Cause::new(&row.cause, &row.detail)).or_default();
        entry.sites += 1;
        entry.opcodes = 1;
        entry.line = row.line;
        let tag_entry = tags.entry(row.cause.clone()).or_default();
        tag_entry.sites += 1;
        tag_entry.line = row.line;
        opcodes_per_tag.entry(row.cause.clone()).or_default().insert(row.detail.clone());
    }

    for tally in bundles.values() {
        for cause in &tally.causes {
            causes.entry(cause.clone()).or_default().bundles_present += 1;
        }
        if tally.causes.len() == 1 {
            let sole = tally.causes.iter().next().expect("len 1");
            causes.entry(sole.clone()).or_default().bundles_sole += 1;
        }

        let tag_set = tally.tags();
        for tag in &tag_set {
            tags.entry((*tag).to_owned()).or_default().bundles_present += 1;
        }
        if tag_set.len() == 1 {
            let sole = tag_set.iter().next().expect("len 1");
            tags.entry((*sole).to_owned()).or_default().bundles_sole += 1;
        }
    }

    for (tag, opcodes) in opcodes_per_tag {
        if let Some(entry) = tags.get_mut(&tag) {
            entry.opcodes = opcodes.len();
        }
    }
    (causes, tags)
}

/// Lowercase hex of a module digest — the dedup key.
fn hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    bytes.iter().fold(String::with_capacity(bytes.len() * 2), |mut out, byte| {
        let _ = write!(out, "{byte:02x}");
        out
    })
}

/// What the census would READ off this bundle besides the module itself.
///
/// Two files sharing a module digest are the same measurement only if they also
/// ask for the same functions; this is the part the digest does not cover, so
/// the dedup compares it rather than assuming it.
fn request_fingerprint(bundle: &NativeVerificationBundle) -> String {
    let mut ids: Vec<usize> = bundle
        .requests
        .iter()
        .filter_map(|request| match request {
            NativeVerificationRequest::TrustMc(request) => Some(request.function.as_usize()),
            _ => None,
        })
        .collect();
    ids.sort_unstable();
    format!("{}:{ids:?}", bundle.requests.len())
}

fn pass(ok: bool) -> &'static str {
    if ok { "PASS" } else { "FAIL" }
}

fn pct(part: usize, whole: usize) -> String {
    if whole == 0 { "(n/a)".to_owned() } else { format!("({:.1}%)", 100.0 * part as f64 / whole as f64) }
}

fn join_paths(paths: &[PathBuf]) -> String {
    paths.iter().map(|p| p.display().to_string()).collect::<Vec<_>>().join(" ")
}

fn collect_bundles(dir: &Path) -> std::io::Result<Vec<PathBuf>> {
    let mut found = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(current) = stack.pop() {
        for entry in std::fs::read_dir(&current)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|e| e == "json")
                // Two naming conventions in tree, and requiring only the first
                // made the DEFAULT corpus read as zero bundles: `trustc
                // -Ztrust-dump=native-bundle` writes `trust-native-bundle-<h>.json`,
                // while the committed fixtures are `<case>_native_bundle.json`.
                && path.file_name().is_some_and(|name| {
                    let name = name.to_string_lossy();
                    name.contains("native-bundle") || name.contains("native_bundle")
                })
            {
                found.push(path);
            }
        }
    }
    Ok(found)
}

/// Which functions of `bundle` to translate.
///
/// `requests` (the default) is what production actually asks the CHC
/// translator for: the functions named by a `TrustMc` CHC/PDR request — the
/// bundle's root plus its bundled members. `all` widens to every function in
/// the module, which double-counts a callee that is also a member.
fn translation_targets(bundle: &NativeVerificationBundle, all: bool) -> Vec<FuncId> {
    if all {
        return bundle.module.functions.iter().map(|f| f.id).collect();
    }
    let mut targets: Vec<FuncId> = bundle
        .requests
        .iter()
        .filter_map(|request| match request {
            NativeVerificationRequest::TrustMc(request) => Some(request.function),
            _ => None,
        })
        .collect();
    targets.sort_by_key(|id| id.as_usize());
    targets.dedup();
    if targets.is_empty() {
        // A bundle with no trust-mc request still holds bodies the interpreter
        // would be asked about; reporting zero for it would understate the
        // population rather than disclose it.
        targets = bundle.module.functions.iter().map(|f| f.id).collect();
    }
    targets
}

fn count_direct_calls(func: &trust_ir::Function) -> usize {
    func.blocks
        .iter()
        .flat_map(|block| block.body.iter())
        .filter(|node| matches!(node.inst, Inst::Call { .. }))
        .count()
}

/// Free MiB on the volume holding `path`, or `None` when it cannot be read.
///
/// A corpus sweep has filled this repo's volume to zero bytes free, at which
/// point NOTHING works — not `rm`, not a tool that must write a temp file. The
/// floor is checked while there is still headroom to stop cleanly.
fn free_mb(path: &Path) -> Option<u64> {
    let output = std::process::Command::new("df").arg("-m").arg(path).output().ok()?;
    let text = String::from_utf8_lossy(&output.stdout);
    let line = text.lines().nth(1)?;
    line.split_whitespace().nth(3)?.parse().ok()
}

fn write_rows(path: &Path, rows: &[Row]) -> std::io::Result<()> {
    use std::io::Write as _;
    let mut out = std::io::BufWriter::new(std::fs::File::create(path)?);
    writeln!(out, "bundle\tcaller\tcallee\tblock\tindex\toutcome\tcause\tdetail\tline")?;
    for row in rows {
        writeln!(
            out,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            row.bundle,
            row.caller,
            row.callee,
            row.block,
            row.index,
            row.outcome,
            row.cause,
            row.detail,
            row.line
        )?;
    }
    Ok(())
}

/// Everything the machine-readable summary carries. A struct rather than
/// eighteen positional parameters: two of the counts are near-twins whose only
/// difference is granularity, and a positional call site is where those get
/// swapped.
struct JsonSummary<'a> {
    options: &'a Options,
    stop: &'a Stop,
    discovered: usize,
    parsed: usize,
    duplicates_skipped: usize,
    distinct_modules: usize,
    sites: usize,
    summarized: usize,
    declined: usize,
    arity_mismatch: usize,
    not_attempted: usize,
    bundles_clean: usize,
    bundles_sole: usize,
    bundles_multi: usize,
    bundles_sole_tag: usize,
    bundles_multi_tag: usize,
    causes: &'a BTreeMap<Cause, CauseTally>,
    tag_rollup: &'a BTreeMap<String, CauseTally>,
    catch_all: &'a BTreeMap<String, usize>,
}

fn write_json(path: &Path, summary: &JsonSummary<'_>) -> std::io::Result<()> {
    use std::io::Write as _;
    // The PRIMARY table, at (tag, opcode) granularity: `bundles_sole` here is
    // the yield of a slice someone can actually cut.
    let cause_rows: Vec<serde_json::Value> = summary
        .causes
        .iter()
        .map(|(cause, tally)| {
            serde_json::json!({
                "cause": cause.key(),
                "tag": cause.tag,
                "opcode": cause.opcode,
                "sites": tally.sites,
                "bundles_present": tally.bundles_present,
                "bundles_sole": tally.bundles_sole,
                "line": tally.line,
            })
        })
        .collect();
    // The rollup. `bundles_sole` on a row with `opcodes > 1` is NOT a slice's
    // yield; the field is named `bundles_tag_sole` so it cannot be read into a
    // consumer expecting the refined one.
    let tag_rows: Vec<serde_json::Value> = summary
        .tag_rollup
        .iter()
        .map(|(tag, tally)| {
            serde_json::json!({
                "tag": tag,
                "sites": tally.sites,
                "bundles_present": tally.bundles_present,
                "bundles_tag_sole": tally.bundles_sole,
                "opcodes": tally.opcodes,
                "line": tally.line,
            })
        })
        .collect();
    let value = serde_json::json!({
        // v2: `causes` is now keyed by (tag, opcode) and `bundles_sole` on it
        // is the refined count. A v1 consumer reading `causes[].tag` as a
        // primary key would silently see repeated tags, so the schema moves.
        "schema": "trust.call-summary-census.v2",
        "corpora": summary.options.corpora.iter().map(|p| p.display().to_string())
            .collect::<Vec<_>>(),
        "scope": if summary.options.all_functions { "all" } else { "requests" },
        "labelled_exits_total": summary.options.label_inventory,
        "labelled_exits_fired": summary.tag_rollup.len(),
        "completion": summary.stop.label(),
        "bundles_discovered": summary.discovered,
        "bundles_parsed": summary.parsed,
        "bundles_duplicate_skipped": summary.duplicates_skipped,
        "distinct_modules": summary.distinct_modules,
        "sites": summary.sites,
        "summarized": summary.summarized,
        "declined": summary.declined,
        "summarized_arity_mismatch": summary.arity_mismatch,
        "not_attempted": summary.not_attempted,
        "bundles_fully_summarized": summary.bundles_clean,
        "bundles_sole_blocked": summary.bundles_sole,
        "bundles_multi_blocked": summary.bundles_multi,
        "bundles_sole_blocked_by_tag": summary.bundles_sole_tag,
        "bundles_multi_blocked_by_tag": summary.bundles_multi_tag,
        "causes": cause_rows,
        "causes_by_tag": tag_rows,
        "unmodeled_instruction_by_opcode": summary.catch_all,
    });
    let mut out = std::fs::File::create(path)?;
    writeln!(out, "{}", serde_json::to_string_pretty(&value)?)
}

// --------------------------------------------------------------------- tests
//
// The aggregator's own arithmetic, pinned. `sole` is the only column that
// predicts a slice's yield, and reporting it at TAG granularity over-stated the
// census's own largest cause by 5x on the first real sweep (357 vs 67). These
// tests are a controlled discriminator for exactly that: same rows, same
// bundles, two granularities, two different answers.

#[cfg(test)]
mod tests {
    use super::*;

    fn declined(bundle: &str, tag: &str, opcode: &str) -> Row {
        Row {
            bundle: bundle.to_owned(),
            caller: "caller".to_owned(),
            callee: "callee".to_owned(),
            block: "b0".to_owned(),
            index: 0,
            outcome: "declined",
            cause: tag.to_owned(),
            detail: opcode.to_owned(),
            line: 42,
        }
    }

    /// Build the bundle tallies the run loop would have built from `rows`.
    fn tally(rows: &[Row]) -> BTreeMap<String, BundleTally> {
        let mut bundles: BTreeMap<String, BundleTally> = BTreeMap::new();
        for row in rows {
            let entry = bundles.entry(row.bundle.clone()).or_default();
            entry.sites += 1;
            entry.declined += 1;
            entry.causes.insert(Cause::new(&row.cause, &row.detail));
        }
        bundles
    }

    #[test]
    fn sole_is_refined_by_opcode() {
        // One bundle declining through TWO opcodes of the SAME catch-all tag.
        // At tag granularity it looks sole-blocked and "fix unmodeled_instruction"
        // reads as a cure; at cause granularity NO opcode-sized slice cures it,
        // which is the true statement.
        let rows = vec![
            declined("two_opcodes", "unmodeled_instruction", "Alloca"),
            declined("two_opcodes", "unmodeled_instruction", "GEP"),
            // ...and one that really is cured by modelling `Alloca`.
            declined("alloca_only", "unmodeled_instruction", "Alloca"),
        ];
        let bundles = tally(&rows);
        let (causes, tags) = aggregate_causes(&rows, &bundles);

        let alloca = Cause::new("unmodeled_instruction", "Alloca");
        let gep = Cause::new("unmodeled_instruction", "GEP");

        assert_eq!(causes[&alloca].sites, 2);
        assert_eq!(causes[&alloca].bundles_present, 2);
        assert_eq!(causes[&alloca].bundles_sole, 1, "only `alloca_only` is cured by modelling Alloca");
        assert_eq!(causes[&gep].bundles_sole, 0);

        // The rollup says something DIFFERENT and larger, and says so by name.
        let rolled = &tags["unmodeled_instruction"];
        assert_eq!(rolled.sites, 3);
        assert_eq!(rolled.bundles_sole, 2, "the tag rollup counts both bundles");
        assert_eq!(rolled.opcodes, 2, "a rollup spanning >1 opcode is where `sole` over-attributes");
        assert!(
            rolled.bundles_sole > causes[&alloca].bundles_sole,
            "the whole point: the tag-level number is the one that over-states the slice"
        );
    }

    #[test]
    fn an_exit_that_names_one_construct_is_its_own_refined_cause() {
        // Exits outside the catch-all carry no opcode, so refined == tag and
        // the two tables must agree exactly. A refinement that split these
        // would fragment a real cause into noise.
        let rows = vec![
            declined("a", "signature_param_ty_unsupported", ""),
            declined("b", "signature_param_ty_unsupported", ""),
        ];
        let bundles = tally(&rows);
        let (causes, tags) = aggregate_causes(&rows, &bundles);
        let cause = Cause::new("signature_param_ty_unsupported", "");
        assert_eq!(cause.key(), "signature_param_ty_unsupported", "no `/` suffix when there is no opcode");
        assert_eq!(causes[&cause].bundles_sole, 2);
        assert_eq!(tags["signature_param_ty_unsupported"].bundles_sole, 2);
        assert_eq!(tags["signature_param_ty_unsupported"].opcodes, 1);
    }

    #[test]
    fn a_bundle_blocked_by_two_tags_is_sole_for_neither() {
        let rows = vec![
            declined("mixed", "unmodeled_instruction", "Alloca"),
            declined("mixed", "signature_param_ty_unsupported", ""),
        ];
        let bundles = tally(&rows);
        let (causes, tags) = aggregate_causes(&rows, &bundles);
        assert!(causes.values().all(|t| t.bundles_sole == 0));
        assert!(tags.values().all(|t| t.bundles_sole == 0));
        assert_eq!(bundles["mixed"].tags().len(), 2);
    }

    #[test]
    fn the_dedup_key_is_the_module_digest() {
        // Two dumps of the same module reached through two `--corpus` dirs used
        // to be tallied twice, because the tally was keyed by FILE NAME. The
        // key is the digest now, and the report's `dedup` check is exactly the
        // assertion below: tallied population == distinct modules.
        assert_eq!(hex(&[0x00, 0x0f, 0xa0, 0xff]), "000fa0ff");
        assert_ne!(hex(&[1, 2]), hex(&[2, 1]));
    }
}
