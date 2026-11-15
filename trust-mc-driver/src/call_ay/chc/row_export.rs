// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Opt-in exact export of what the CHC lane hands AY (AY asks R20, R21, W5/W6).
//!
//! AY asked for "the exact per-property query and proof mode" trust-mc sends,
//! because a standalone CLI run of the harness `.smt2` is not the in-process
//! route: the driver parses the harness CHC, slices it into one obligation per
//! `error_pN` with [`ChcProblem::query_obligations`], prepares each slice and
//! solves it under its own grant and `EncodeConfig`. Setting
//! `TRUST_MC_CHC_ROW_EXPORT_DIR=<dir>` writes, under `<dir>/<harness>/`:
//!
//! * `source.smt2` — the exact bytes `ChcParser::parse` received (the harness
//!   CHC after the driver's `bv2int` fold and cover-metadata strip);
//!   `source.normalized` — AY's canonical `normalized_input` of the parsed
//!   problem.
//! * `aggregate.normalized` — the post-expansion, post-transform aggregate
//!   problem that the aggregate lanes (acyclic BMC shortcut, forced engines)
//!   receive.
//! * `lemma-hints.txt` — every candidate lemma hint the rows are seeded with.
//! * per row and pass, `rows/NN-<label>.<pass>.prepared.normalized` — AY's
//!   canonical text of the exact `ChcProblem` passed to
//!   `ay_encode::invoke::solve_with_proof_report_with_cancellation` — and
//!   `rows/NN-<label>.<pass>.config.txt` — that call's `EncodeConfig` and the
//!   `AdaptiveConfig` it lowers to.
//! * `witness/QQQQ.normalized` (and `QQQQ.smt2` where the formula renders as
//!   plain SMT-LIB) — each satisfiability query the driver's own acyclic
//!   error-derivation search puts to AY's embedded `SmtContext::check_sat`
//!   before any row runs, as AY's canonical text of a constraint-only query
//!   clause (`constraint => false`, Unsafe iff the formula is satisfiable).
//! * `rows/NN-<label>.validated-invariant.smt2` — for each proved row, the
//!   invariant model the driver re-validates with AY's
//!   `engines::validate_external_invariant_model`, with the outcome.
//! * `external-fallback/` — the file, argv and output of the external `ay`
//!   proof-only fallback, when it runs.
//! * `manifest.json` (schema [`ROW_EXPORT_SCHEMA`]) — identities, digests,
//!   grants, proof mode and outcomes. It is rewritten after every row, so a
//!   watchdog kill still leaves the rows that ran. It also carries:
//!   * `execution_environment` — what an `AdaptiveParallel` row's portfolio
//!     conditions depend on beyond the query and its config: the host's
//!     `std::thread::available_parallelism()`, the harness workers in this
//!     process, the process RSS cap `main()` armed for AY, and every `AY_*`
//!     and `TRUST_MC_*` environment variable set;
//!   * `acyclic_bmc_lane` — when the acyclic-BMC shortcut runs, its exact call
//!     (entrypoint, the aggregate problem's digest, the `BmcConfig`, depth,
//!     budgets, guard), its outcome and its join record (drain time, whether
//!     the drain failed, whether the lane was abandoned at the harness
//!     deadline). AY asked for the inputs of a lane that outlives its drain.
//!
//! Reproduction is the route the driver takes, and `reparse_check` in the
//! manifest re-executes it from the written file: parse `source.smt2`, call
//! `query_obligations()`, select the row by `label` and check
//! `content_sha256`, run `expand_nullary_fail_queries`, apply the listed
//! transforms, check `prepared_normalized_sha256`, and solve under the
//! recorded config.
//!
//! With the export on, stderr also carries `[AY-chc:row-export] ... begin` and
//! `... end` lines around every witness query, row and validation, so AY's own
//! stderr diagnostics (a `MODEL-UNCONFIRMED` line, a proof-checker rejection)
//! can be attributed to the query that produced them.
//!
//! The export costs wall clock (normalization and file writes) inside the
//! batch clock; `export_ms` records how much. Take timing measurements with the
//! knob unset. The export never changes a verdict: an IO failure is reported on
//! stderr and disables the export for that harness, and nothing here returns an
//! error to the solve path.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use ay::chc::{ChcExpr, ChcParser, ChcProblem, ChcSort, ClauseBody, HornClause, LemmaHint};
use serde_json::{Value, json};

/// Directory under which each harness's export is written.
pub(super) const ROW_EXPORT_DIR_ENV: &str = "TRUST_MC_CHC_ROW_EXPORT_DIR";
/// Schema of `manifest.json`.
pub(super) const ROW_EXPORT_SCHEMA: &str = "trust_mc.chc-row-export/v1";
/// Witness-search queries recorded with files; later ones are only counted.
const MAX_WITNESS_QUERIES: usize = 400;
/// Schema of `external-fallback/external-fallback.json`.
pub(super) const EXTERNAL_FALLBACK_SCHEMA: &str = "trust_mc.chc-external-fallback-export/v1";

fn sha256_hex(bytes: &[u8]) -> String {
    trust_mc_core::EvidenceHash::sha256_bytes(bytes).value
}

/// A file-name-safe rendering of a harness name or row label.
pub(super) fn file_component(raw: &str) -> String {
    let mapped: String = raw
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() || matches!(c, '-' | '_' | '.') { c } else { '_' })
        .collect();
    let trimmed = mapped.trim_matches('.');
    let mut component = if trimmed.is_empty() { "_".to_string() } else { trimmed.to_string() };
    if component.len() > 120 {
        let digest = sha256_hex(raw.as_bytes());
        component.truncate(100);
        component.push('-');
        component.push_str(&digest[..16]);
    }
    component
}

/// The export root, when the knob is set to a non-empty path.
pub(super) fn export_root_from_env() -> Option<PathBuf> {
    std::env::var_os(ROW_EXPORT_DIR_ENV).filter(|value| !value.is_empty()).map(PathBuf::from)
}

fn harness_dir(root: &Path, harness: &str) -> PathBuf {
    root.join(file_component(harness))
}

/// The loop-contract retry lane's own export root for `harness`
/// (`<root>/<harness>/loop-contract-retry`, [`crate::loop_two_lane::retry_lane_export_root`]),
/// when the knob is set. The lane child is handed this as its
/// [`ROW_EXPORT_DIR_ENV`], so it writes `<that>/<harness>/` and never the
/// parent's `source.smt2` or `manifest.json`.
pub(crate) fn retry_lane_export_dir(harness: &str) -> Option<PathBuf> {
    let root = export_root_from_env()?;
    Some(crate::loop_two_lane::retry_lane_export_root(&root, &file_component(harness)))
}

/// Record that the loop-contract retry ran for `harness`, when the knob is set:
/// `record` goes to `<root>/<harness>/loop-contract-retry/retry.json`, and the
/// harness's `manifest.json`, when this process wrote one, gains a
/// `loop_contract_retry` field pointing at it. Never changes a verdict; an IO
/// failure is reported on stderr.
pub(crate) fn record_loop_contract_retry(harness: &str, record: Value) {
    if let Some(root) = export_root_from_env() {
        record_loop_contract_retry_under(&root, harness, record);
    }
}

fn record_loop_contract_retry_under(root: &Path, harness: &str, record: Value) {
    let dir = harness_dir(root, harness);
    let retry_dir = dir.join(crate::loop_two_lane::RETRY_LANE_EXPORT_SUBDIR);
    let record_file = format!("{}/retry.json", crate::loop_two_lane::RETRY_LANE_EXPORT_SUBDIR);
    let text = serde_json::to_string_pretty(&record).unwrap_or_default();
    if let Err(err) = std::fs::create_dir_all(&retry_dir)
        .and_then(|()| std::fs::write(retry_dir.join("retry.json"), text.as_bytes()))
    {
        eprintln!(
            "[AY-chc] row export: cannot record the loop-contract retry for {harness} in {}: {err}",
            retry_dir.display()
        );
        return;
    }
    let manifest_path = dir.join("manifest.json");
    let Ok(raw) = std::fs::read_to_string(&manifest_path) else { return };
    let Ok(Value::Object(mut manifest)) = serde_json::from_str::<Value>(&raw) else { return };
    manifest.insert(
        "loop_contract_retry".into(),
        json!({
            "ran": true,
            "record": record_file,
            "lane_export_root": crate::loop_two_lane::RETRY_LANE_EXPORT_SUBDIR,
            "outcome": record.get("outcome").cloned().unwrap_or(Value::Null),
            "note": "the loop-contract retry ran a child driver for this harness after the rows \
                     above; the child exported its own query under lane_export_root/<harness>/. \
                     source.smt2 and every row above are this process's",
        }),
    );
    let text = serde_json::to_string_pretty(&Value::Object(manifest)).unwrap_or_default();
    if let Err(err) = std::fs::write(&manifest_path, text.as_bytes()) {
        eprintln!("[AY-chc] row export: cannot write {}: {err}", manifest_path.display());
    }
}

fn duration_ms(duration: Duration) -> u128 {
    duration.as_millis()
}

/// Environment-variable prefixes the export records values for.
const RECORDED_ENV_PREFIXES: [&str; 2] = ["AY_", "TRUST_MC_"];

/// The execution environment a row's portfolio conditions depend on beyond
/// the query and its config (see the module docs).
fn execution_environment() -> Value {
    let mut env = BTreeMap::new();
    for (name, value) in std::env::vars_os() {
        let (Some(name), Some(value)) = (name.to_str(), value.to_str()) else { continue };
        if RECORDED_ENV_PREFIXES.iter().any(|prefix| name.starts_with(prefix)) {
            env.insert(name.to_string(), value.to_string());
        }
    }
    let harness_workers =
        if rayon::current_thread_index().is_some() { rayon::current_num_threads() } else { 1 };
    let process_cap = super::resource_envelope::armed_process_cap_bytes();
    json!({
        "available_parallelism": std::thread::available_parallelism().ok().map(|n| n.get()),
        "harness_workers": harness_workers,
        "process_memory_cap_bytes": (process_cap != 0).then_some(process_cap),
        "process_memory_cap_note": "the process-wide RSS cap main() armed for AY \
                                    (ay_sys::get_process_memory_limit); null when none is armed",
        "env": env,
        "env_note": "every AY_* and TRUST_MC_* variable set in the driver's environment",
    })
}

/// What a row is solved under, as the export records it.
pub(super) struct RowGrant {
    pub(super) budget: Duration,
    pub(super) rows_left: usize,
    pub(super) batch_remaining: Duration,
    pub(super) harness_deadline_remaining: Duration,
}

impl RowGrant {
    fn to_json(&self) -> Value {
        json!({
            "row_budget_ms": duration_ms(self.budget),
            "rows_left_including_this_one": self.rows_left,
            "batch_clock_remaining_ms_before_row": duration_ms(self.batch_remaining),
            "harness_deadline_remaining_ms_before_row": duration_ms(self.harness_deadline_remaining),
            "rule": "row budget = min(per_row_cap, min(batch_remaining, harness_remaining) / rows_left)",
        })
    }
}

/// One row's query identity, as the export records it.
pub(super) struct RowQuery<'a> {
    /// The exact problem passed to the solve call.
    pub(super) prepared: &'a ChcProblem,
    /// `normalized_input_sha256` of the slice before preparation, when the
    /// caller still had it (first pass).
    pub(super) slice_normalized_sha256: Option<String>,
    pub(super) config: &'a ay_encode::invoke::EncodeConfig,
}

struct ExportState {
    manifest: serde_json::Map<String, Value>,
    rows: Vec<Value>,
    /// Prepared-problem digests the reparse check derived from `source.smt2`,
    /// by row label.
    reparsed_prepared: BTreeMap<String, String>,
    /// The driver's acyclic-witness queries, in issue order.
    witness: Vec<Value>,
    witness_total: usize,
    /// Per-row invariant re-validations.
    validations: Vec<Value>,
    failed: bool,
    spent: Duration,
}

/// One harness's export. Created only when [`ROW_EXPORT_DIR_ENV`] is set.
pub(super) struct RowExport {
    dir: PathBuf,
    state: Mutex<ExportState>,
}

impl RowExport {
    /// Start the export for `harness`, writing the exact parser input.
    ///
    /// `None` when the knob is unset, or when the directory or the source file
    /// cannot be written (reported on stderr; the solve is unaffected).
    pub(super) fn from_env(harness: &str, smt_file: &Path, solver_smt: &str) -> Option<Self> {
        let root = export_root_from_env()?;
        Self::begin(&root, harness, smt_file, solver_smt)
    }

    pub(super) fn begin(
        root: &Path,
        harness: &str,
        smt_file: &Path,
        solver_smt: &str,
    ) -> Option<Self> {
        let started = Instant::now();
        let dir = harness_dir(root, harness);
        let written = std::fs::create_dir_all(dir.join("rows"))
            .and_then(|()| std::fs::write(dir.join("source.smt2"), solver_smt.as_bytes()));
        if let Err(err) = written {
            eprintln!(
                "[AY-chc] row export disabled for {harness}: cannot write {}: {err}",
                dir.display()
            );
            return None;
        }
        let raw = std::fs::read(smt_file).ok();
        let mut manifest = serde_json::Map::new();
        manifest.insert("schema".into(), json!(ROW_EXPORT_SCHEMA));
        manifest.insert("harness".into(), json!(harness));
        manifest.insert(
            "producer".into(),
            json!({
                "trust_mc_git_sha": crate::version::TRUST_MC_GIT_SHA,
                "trust_mc_git_dirty": crate::version::TRUST_MC_GIT_DIRTY,
                "trust_mc_version": crate::version::KANI_VERSION,
                "ay_declared_pin": crate::version::ay_pinned_commit().ok(),
                "note": "the linked ay checkout identity is recorded by the ask manifest \
                         (trust-mc-driver --version-authority), not by the driver at run time",
            }),
        );
        manifest.insert(
            "source".into(),
            json!({
                "file": "source.smt2",
                "sha256": sha256_hex(solver_smt.as_bytes()),
                "bytes": solver_smt.len(),
                "what": "exact bytes passed to ay::chc::ChcParser::parse: the harness CHC after \
                         the driver's (bv2int #x..) literal fold and cover-metadata strip",
                "compiler_smt_file": smt_file.display().to_string(),
                "compiler_smt_sha256": raw.as_deref().map(sha256_hex),
                "compiler_smt_bytes": raw.as_ref().map(Vec::len),
            }),
        );
        manifest.insert("execution_environment".into(), execution_environment());
        manifest.insert("per_property_batch".into(), Value::Null);
        let export = Self {
            dir,
            state: Mutex::new(ExportState {
                manifest,
                rows: Vec::new(),
                reparsed_prepared: BTreeMap::new(),
                witness: Vec::new(),
                witness_total: 0,
                validations: Vec::new(),
                failed: false,
                spent: started.elapsed(),
            }),
        };
        export.flush();
        Some(export)
    }

    fn with_state(&self, update: impl FnOnce(&Path, &mut ExportState)) {
        let started = Instant::now();
        let Ok(mut state) = self.state.lock() else { return };
        if state.failed {
            return;
        }
        update(&self.dir, &mut state);
        state.spent += started.elapsed();
    }

    fn write(dir: &Path, state: &mut ExportState, name: &str, bytes: &[u8]) -> bool {
        if let Err(err) = std::fs::write(dir.join(name), bytes) {
            eprintln!(
                "[AY-chc] row export disabled: cannot write {}: {err}",
                dir.join(name).display()
            );
            state.failed = true;
            return false;
        }
        true
    }

    fn write_problem(
        dir: &Path,
        state: &mut ExportState,
        name: &str,
        problem: &ChcProblem,
    ) -> Option<Value> {
        let text = problem.normalized_input();
        let sha = sha256_hex(text.as_bytes());
        Self::write(dir, state, name, text.as_bytes()).then(|| {
            json!({
                "file": name,
                "normalized_input_sha256": sha,
                "ay_normalized_input_sha256": problem.normalized_input_sha256(),
                "predicates": problem.predicates().len(),
                "clauses": problem.clauses().len(),
            })
        })
    }

    /// The problem exactly as parsed, before any driver pass.
    pub(super) fn source_problem(&self, problem: &ChcProblem) {
        self.with_state(|dir, state| {
            if let Some(entry) = Self::write_problem(dir, state, "source.normalized", problem) {
                state.manifest.insert("source_problem".into(), entry);
            }
        });
    }

    /// The aggregate problem after nullary expansion and the selected
    /// transforms: what the aggregate lanes receive.
    pub(super) fn aggregate_problem(&self, problem: &ChcProblem, transforms: Value) {
        self.with_state(|dir, state| {
            if let Some(mut entry) =
                Self::write_problem(dir, state, "aggregate.normalized", problem)
            {
                entry["passes"] = json!({
                    "expand_nullary_fail_queries": true,
                    "transforms": transforms,
                });
                entry["received_by"] = json!(
                    "the acyclic-BMC shortcut (after an undecided batch by default) and the \
                     forced-engine lanes; the per-property rows are sliced from source.smt2 instead"
                );
                state.manifest.insert("aggregate_problem".into(), entry);
            }
        });
        self.flush();
    }

    /// Record the batch-level inputs, the lemma hints the rows share, and the
    /// reparse check: the written `source.smt2` is parsed again and sliced,
    /// and every obligation's identity and prepared digest is derived from it.
    pub(super) fn begin_batch(
        &self,
        batch: Value,
        obligations: &[(String, String)],
        lemma_hints: &[LemmaHint],
        source_problem: &ChcProblem,
        prepare: &dyn Fn(&mut ChcProblem),
    ) {
        self.with_state(|dir, state| {
            let mut hints = String::new();
            for (index, hint) in lemma_hints.iter().enumerate() {
                let predicate = source_problem
                    .get_predicate(hint.predicate)
                    .map_or("<undeclared>", |predicate| predicate.name.as_str());
                hints.push_str(&format!(
                    "# hint {index}: predicate #{} {predicate}, priority {}, source {}\n{}\n{:?}\n\n",
                    hint.predicate.index(),
                    hint.priority,
                    hint.source,
                    hint.formula,
                    hint,
                ));
            }
            if !Self::write(dir, state, "lemma-hints.txt", hints.as_bytes()) {
                return;
            }
            let reparse = Self::reparse(dir, obligations, prepare);
            if let Some(map) = reparse.get("prepared_by_label").and_then(Value::as_object) {
                for (label, sha) in map {
                    if let Some(sha) = sha.as_str() {
                        state.reparsed_prepared.insert(label.clone(), sha.to_string());
                    }
                }
            }
            let mut batch = batch;
            batch["lemma_hints"] = json!({
                "file": "lemma-hints.txt",
                "count": lemma_hints.len(),
                "debug_sha256": sha256_hex(format!("{lemma_hints:?}").as_bytes()),
                "shared_by_every_row": true,
            });
            batch["obligations"] = json!(
                obligations
                    .iter()
                    .map(|(label, sha)| json!({"label": label, "content_sha256": sha}))
                    .collect::<Vec<_>>()
            );
            batch["reparse_check"] = reparse;
            state.manifest.insert("per_property_batch".into(), batch);
        });
        self.flush();
    }

    fn reparse(
        dir: &Path,
        obligations: &[(String, String)],
        prepare: &dyn Fn(&mut ChcProblem),
    ) -> Value {
        let text = match std::fs::read_to_string(dir.join("source.smt2")) {
            Ok(text) => text,
            Err(err) => return json!({"status": "error", "detail": format!("read: {err}")}),
        };
        let problem = match ChcParser::parse(&text) {
            Ok(problem) => problem,
            Err(err) => return json!({"status": "error", "detail": format!("parse: {err}")}),
        };
        let reparsed = match problem.query_obligations() {
            Ok(reparsed) => reparsed,
            Err(err) => return json!({"status": "error", "detail": format!("slice: {err}")}),
        };
        let identities: Vec<(String, String)> = reparsed
            .iter()
            .map(|obligation| {
                (obligation.id().label().to_string(), obligation.id().content_sha256().to_string())
            })
            .collect();
        let mut prepared_by_label = serde_json::Map::new();
        for obligation in reparsed {
            let (id, mut problem) = obligation.into_parts();
            prepare(&mut problem);
            prepared_by_label
                .insert(id.label().to_string(), json!(problem.normalized_input_sha256()));
        }
        let status = if identities.as_slice() == obligations { "ok" } else { "mismatch" };
        json!({
            "status": status,
            "what": "source.smt2 re-read from disk, parsed, sliced with query_obligations() and \
                     each slice prepared as the driver prepares it; status=ok means the labels \
                     and content_sha256 values equal the in-process obligations in order",
            "reparsed_obligations": identities
                .iter()
                .map(|(label, sha)| json!({"label": label, "content_sha256": sha}))
                .collect::<Vec<_>>(),
            "prepared_by_label": prepared_by_label,
        })
    }

    /// Record one row as it is handed to AY (or, with `query == None`, a row
    /// that was not started). Returns the row's slot for [`Self::row_outcome`].
    pub(super) fn row(
        &self,
        index: usize,
        pass: &str,
        identity: Value,
        grant: Option<&RowGrant>,
        query: Option<RowQuery<'_>>,
    ) -> Option<usize> {
        let mut slot = None;
        self.with_state(|dir, state| {
            let label = identity.get("label").and_then(Value::as_str).unwrap_or("row").to_string();
            let stem = format!("rows/{index:02}-{}.{pass}", file_component(&label));
            let mut entry = json!({
                "index": index,
                "pass": pass,
                "identity": identity,
                "grant": grant.map(RowGrant::to_json),
            });
            if let Some(query) = query {
                let prepared_name = format!("{stem}.prepared.normalized");
                let Some(prepared) =
                    Self::write_problem(dir, state, &prepared_name, query.prepared)
                else {
                    return;
                };
                let config = query.config;
                let config_text = format!(
                    "# EncodeConfig handed to ay_encode::invoke::solve_with_proof_report_with_cancellation\n\
                     {config:#?}\n\n# AdaptiveConfig it lowers to (EncodeConfig::to_adaptive_config)\n\
                     {:#?}\n",
                    config.to_adaptive_config()
                );
                let config_name = format!("{stem}.config.txt");
                if !Self::write(dir, state, &config_name, config_text.as_bytes()) {
                    return;
                }
                let prepared_sha =
                    prepared["normalized_input_sha256"].as_str().unwrap_or_default().to_string();
                let reparse_matches =
                    state.reparsed_prepared.get(&label).map(|sha| *sha == prepared_sha);
                entry["prepared_problem"] = prepared;
                entry["slice_normalized_sha256"] = json!(query.slice_normalized_sha256);
                entry["prepared_matches_reparse"] = json!(reparse_matches);
                entry["solve_call"] = json!({
                    "entry_point": "ay_encode::invoke::solve_with_proof_report_with_cancellation",
                    "proof_mode": format!("{:?}", config.proof_mode),
                    "engine": format!("{:?}", config.engine),
                    "strict_validation": config.strict_validation,
                    "adaptive_strict_proofs": config.to_adaptive_config().strict_proofs,
                    "execution_mode": format!("{:?}", config.execution_mode),
                    "timeout_ms": config.timeout.map(duration_ms),
                    "memory_budget_bytes": config.memory_budget,
                    "lemma_hints": config.lemma_hints.len(),
                    "cancellation": "parent token armed with the batch clock before the call; \
                                     the call runs synchronously on the harness thread",
                    "config_file": config_name,
                });
            }
            slot = Some(state.rows.len());
            state.rows.push(entry);
        });
        self.flush();
        if slot.is_some() {
            eprintln!("[AY-chc:row-export] row {index:02} {pass} begin");
        }
        slot
    }

    /// Attach what the row's AY call returned.
    pub(super) fn row_outcome(&self, slot: Option<usize>, outcome: Value) {
        let Some(slot) = slot else { return };
        let label = outcome.get("outcome").and_then(Value::as_str).unwrap_or("?").to_string();
        let mut marker = None;
        self.with_state(|_, state| {
            if let Some(entry) = state.rows.get_mut(slot) {
                marker = Some(format!(
                    "{:02} {}",
                    entry["index"].as_u64().unwrap_or_default(),
                    entry["pass"].as_str().unwrap_or("?")
                ));
                entry["outcome"] = outcome;
            }
        });
        if let Some(marker) = marker {
            eprintln!("[AY-chc:row-export] row {marker} end outcome={label}");
        }
        self.flush();
    }

    /// The acyclic-BMC lane's exact call, before the lane starts (so a
    /// watchdog kill still leaves it). Marks stderr for attribution.
    pub(super) fn acyclic_bmc_lane_begin(&self, call: Value) {
        eprintln!("[AY-chc:row-export] acyclic-bmc begin");
        self.note("acyclic_bmc_lane", json!({ "call": call }));
    }

    /// The acyclic-BMC lane's outcome and join record.
    pub(super) fn acyclic_bmc_lane_end(&self, outcome: &str, join: Value) {
        eprintln!("[AY-chc:row-export] acyclic-bmc end outcome={outcome}");
        self.with_state(|_, state| {
            if let Some(entry) = state.manifest.get_mut("acyclic_bmc_lane") {
                entry["outcome"] = json!(outcome);
                entry["join"] = join;
            }
        });
        self.flush();
    }

    /// Attach a batch-level fact (validation, reduction) to the manifest.
    pub(super) fn note(&self, key: &str, value: Value) {
        self.with_state(|_, state| {
            state.manifest.insert(key.to_string(), value);
        });
        self.flush();
    }

    /// Record one acyclic-witness query before it is put to AY. Returns its
    /// sequence number for [`Self::witness_result`].
    pub(super) fn witness_query(
        &self,
        clause_index: usize,
        purpose: &'static str,
        formula: &ChcExpr,
        problem: &ChcProblem,
    ) -> usize {
        let mut seq = 0;
        self.with_state(|dir, state| {
            seq = state.witness_total;
            state.witness_total += 1;
            if state.witness.len() >= MAX_WITNESS_QUERIES {
                return;
            }
            if seq == 0 && std::fs::create_dir_all(dir.join("witness")).is_err() {
                state.failed = true;
                return;
            }
            let query = constraint_query_problem(formula, problem);
            let name = format!("witness/{seq:04}.normalized");
            let Some(normalized) = Self::write_problem(dir, state, &name, &query) else {
                return;
            };
            let smtlib = match smtlib_script(formula) {
                Ok(script) => {
                    let smt_name = format!("witness/{seq:04}.smt2");
                    if !Self::write(dir, state, &smt_name, script.as_bytes()) {
                        return;
                    }
                    json!({"file": smt_name, "sha256": sha256_hex(script.as_bytes())})
                }
                Err(reason) => json!({"file": null, "not_rendered": reason}),
            };
            state.witness.push(json!({
                "seq": seq,
                "clause_index": clause_index,
                "purpose": purpose,
                "constraint_query": normalized,
                "formula_debug_sha256": sha256_hex(format!("{formula:?}").as_bytes()),
                "smtlib": smtlib,
            }));
        });
        eprintln!("[AY-chc:row-export] witness-query {seq:04} begin clause={clause_index}");
        seq
    }

    /// Attach the result AY's `check_sat` returned for witness query `seq`.
    pub(super) fn witness_result(&self, seq: usize, result: &str) {
        eprintln!("[AY-chc:row-export] witness-query {seq:04} end result={result}");
        self.with_state(|_, state| {
            if let Some(entry) =
                state.witness.iter_mut().find(|entry| entry["seq"].as_u64() == Some(seq as u64))
            {
                entry["result"] = json!(result);
            }
        });
    }

    /// Mark the start of a proved row's invariant re-validation on stderr.
    pub(super) fn validation_begin(&self, index: usize) {
        eprintln!("[AY-chc:row-export] validation row {index:02} begin");
    }

    /// Record a proved row's invariant re-validation: the model as SMT-LIB and
    /// what AY's external validator said about it.
    pub(super) fn validation(
        &self,
        index: usize,
        label: &str,
        invariant_smtlib: &str,
        timeout: Duration,
        elapsed: Duration,
        result: Result<(), String>,
    ) {
        let outcome = match &result {
            Ok(()) => "valid".to_string(),
            Err(err) => err.clone(),
        };
        eprintln!("[AY-chc:row-export] validation row {index:02} end result={outcome}");
        self.with_state(|dir, state| {
            let name = format!("rows/{index:02}-{}.validated-invariant.smt2", file_component(label));
            if !Self::write(dir, state, &name, invariant_smtlib.as_bytes()) {
                return;
            }
            state.validations.push(json!({
                "index": index,
                "label": label,
                "invariant_file": name,
                "invariant_sha256": sha256_hex(invariant_smtlib.as_bytes()),
                "validator": "ay::chc::engines::validate_external_invariant_model against the row's \
                              own prepared problem (PdrConfig::default, solve_timeout = timeout)",
                "timeout_ms": duration_ms(timeout),
                "elapsed_ms": duration_ms(elapsed),
                "valid": result.is_ok(),
                "result": outcome,
            }));
        });
        self.flush();
    }

    /// Rewrite `manifest.json` with everything recorded so far.
    pub(super) fn flush(&self) {
        let Ok(mut state) = self.state.lock() else { return };
        if state.failed {
            return;
        }
        let started = Instant::now();
        let mut manifest = state.manifest.clone();
        manifest.insert("rows".into(), Value::Array(state.rows.clone()));
        if state.witness_total > 0 {
            manifest.insert(
                "acyclic_witness_search".into(),
                json!({
                    "what": "satisfiability queries the driver's acyclic error-derivation search \
                             (native_nullary::satisfiable_acyclic_error_derivation_witness) puts to \
                             AY's embedded SmtContext::check_sat, one fresh reset() per query, on \
                             the context ChcProblem::make_smt_context builds for the aggregate problem",
                    "queries_issued": state.witness_total,
                    "queries_recorded": state.witness.len(),
                    "queries": state.witness.clone(),
                }),
            );
        }
        if !state.validations.is_empty() {
            manifest.insert(
                "row_invariant_validations".into(),
                Value::Array(state.validations.clone()),
            );
        }
        manifest.insert("export_ms".into(), json!(duration_ms(state.spent)));
        let text = serde_json::to_string_pretty(&Value::Object(manifest)).unwrap_or_default();
        let dir = self.dir.clone();
        Self::write(&dir, &mut state, "manifest.json", text.as_bytes());
        state.spent += started.elapsed();
    }
}

/// A constraint-only query problem carrying `problem`'s datatype definitions:
/// `formula => false`, Unsafe exactly when `formula` is satisfiable.
fn constraint_query_problem(formula: &ChcExpr, problem: &ChcProblem) -> ChcProblem {
    let mut query = ChcProblem::new();
    for (name, constructors) in problem.datatype_defs() {
        query.add_datatype_def(name.clone(), constructors.clone());
    }
    query.add_clause(HornClause::query(ClauseBody::constraint(formula.clone())));
    query
}

/// Why `formula` has no plain SMT-LIB rendering through `ChcExpr`'s
/// `Display`, if it has none: `Display` prints constructor, selector, tester
/// and uninterpreted applications as `name:sort`, predicate applications as
/// `name#id`, and an operator it does not name by its `Debug` spelling.
fn non_smtlib_shape(formula: &ChcExpr) -> Option<String> {
    let mut stack = vec![formula];
    while let Some(expr) = stack.pop() {
        match expr {
            ChcExpr::PredicateApp(name, ..) => {
                return Some(format!("predicate application {name}"));
            }
            ChcExpr::FuncApp(name, _, args) => {
                if !(matches!(name.as_str(), "to_real" | "to_int" | "is_int") && args.len() == 1) {
                    return Some(format!("function application {name}"));
                }
                stack.extend(args.iter().map(AsRef::as_ref));
            }
            ChcExpr::Op(op, args) => {
                let bare = ChcExpr::Op(op.clone(), Vec::new()).to_string();
                if bare.chars().nth(1).is_some_and(|c| c.is_ascii_uppercase()) {
                    return Some(format!("operator {op:?} has no SMT-LIB spelling in Display"));
                }
                stack.extend(args.iter().map(AsRef::as_ref));
            }
            ChcExpr::ConstArray(_, value) => stack.push(value),
            ChcExpr::Var(var) => {
                if matches!(var.sort, ChcSort::Datatype { .. } | ChcSort::Uninterpreted(_)) {
                    return Some(format!("variable {} has sort {}", var.name, var.sort));
                }
            }
            ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(..) | ChcExpr::BitVec(..) => {}
            other => return Some(format!("internal marker {other:?}")),
        }
    }
    None
}

/// `formula` as a standalone SMT-LIB script, or why it has none.
fn smtlib_script(formula: &ChcExpr) -> Result<String, String> {
    if let Some(reason) = non_smtlib_shape(formula) {
        return Err(reason);
    }
    let mut vars = formula.vars();
    vars.sort_by(|a, b| a.name.cmp(&b.name));
    vars.dedup_by(|a, b| a.name == b.name);
    let mut script = String::from("(set-logic ALL)\n");
    for var in &vars {
        script.push_str(&format!("(declare-fun {} () {})\n", var.name, var.sort));
    }
    script.push_str(&format!("(assert {formula})\n(check-sat)\n"));
    Ok(script)
}

/// Export the external `ay` fallback's exact input, argv and output.
///
/// Free-standing because the fallback runs outside the per-property seam. A
/// write failure is reported and ignored.
pub(super) fn record_external_fallback(
    harness: &str,
    solver_file: &Path,
    args: &[String],
    timeout: Duration,
    elapsed: Duration,
    result: Result<&std::process::Output, String>,
) {
    let Some(root) = export_root_from_env() else { return };
    let dir = harness_dir(&root, harness).join("external-fallback");
    let input = match std::fs::read(solver_file) {
        Ok(input) => input,
        Err(err) => {
            eprintln!("[AY-chc] external-fallback export skipped: cannot read input: {err}");
            return;
        }
    };
    let (status, stdout, stderr) = match &result {
        Ok(output) => (
            json!(output.status.code()),
            String::from_utf8_lossy(&output.stdout).into_owned(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
        ),
        Err(err) => (Value::Null, String::new(), err.clone()),
    };
    let record = json!({
        "schema": EXTERNAL_FALLBACK_SCHEMA,
        "harness": harness,
        "input": {
            "file": "input.smt2",
            "sha256": sha256_hex(&input),
            "bytes": input.len(),
            "what": "exact file given to the external ay CLI (cover assertions stripped)",
        },
        "argv_after_binary": args,
        "binary_resolution": "crate::ay_binary::pinned_ay ($TRUST_MC_AY_BIN, else PATH)",
        "timeout_ms": duration_ms(timeout),
        "elapsed_ms": duration_ms(elapsed),
        "exit_code": status,
        "stdout_file": "stdout.txt",
        "stderr_file": "stderr.txt",
    });
    let written = std::fs::create_dir_all(&dir)
        .and_then(|()| std::fs::write(dir.join("input.smt2"), &input))
        .and_then(|()| std::fs::write(dir.join("stdout.txt"), stdout.as_bytes()))
        .and_then(|()| std::fs::write(dir.join("stderr.txt"), stderr.as_bytes()))
        .and_then(|()| {
            std::fs::write(
                dir.join("external-fallback.json"),
                serde_json::to_string_pretty(&record).unwrap_or_default(),
            )
        });
    if let Err(err) = written {
        eprintln!("[AY-chc] external-fallback export failed: {err}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const TWO_PROPERTIES: &str = r#"
(set-logic HORN)
(declare-rel Inv (Int))
(declare-rel error_p0 ())
(declare-rel error_p1 ())
(declare-rel error ())
(declare-var x Int)
(rule (=> (= x 0) (Inv x)))
(rule (=> (and (Inv x) (< x 0)) error_p0))
(rule (=> (and (Inv x) (> x 100)) error_p1))
(rule (=> error_p0 error))
(rule (=> error_p1 error))
(query error)
"#;

    #[test]
    fn file_components_are_safe_and_bounded() {
        assert_eq!(file_component("check_u8"), "check_u8");
        assert_eq!(file_component("a::b<T>"), "a__b_T_");
        assert_eq!(file_component(".."), "_");
        let long = "x".repeat(300);
        let component = file_component(&long);
        assert!(component.len() <= 120, "{}", component.len());
    }

    #[test]
    fn the_export_reparses_the_written_source_to_the_same_obligations() {
        let root = tempfile::tempdir().expect("tempdir");
        let smt_file = root.path().join("harness.smt2");
        std::fs::write(&smt_file, TWO_PROPERTIES).expect("fixture");
        let export = RowExport::begin(root.path(), "demo::harness", &smt_file, TWO_PROPERTIES)
            .expect("export");
        let problem = ChcParser::parse(TWO_PROPERTIES).expect("parses");
        export.source_problem(&problem);
        let obligations: Vec<(String, String)> = problem
            .query_obligations()
            .expect("slices")
            .iter()
            .map(|o| (o.id().label().to_string(), o.id().content_sha256().to_string()))
            .collect();
        assert_eq!(obligations.len(), 2);
        let prepare = |p: &mut ChcProblem| {
            p.expand_nullary_fail_queries(false);
        };
        export.begin_batch(json!({}), &obligations, &[], &problem, &prepare);

        let config = ay_encode::invoke::EncodeConfig::new()
            .with_timeout(Duration::from_millis(1234))
            .with_strict_validation(true);
        let (id, mut slice) =
            problem.query_obligations().expect("slices").into_iter().next().unwrap().into_parts();
        let slice_sha = slice.normalized_input_sha256();
        assert_eq!(slice_sha, id.content_sha256(), "AY's content digest is the slice digest");
        prepare(&mut slice);
        let grant = RowGrant {
            budget: Duration::from_millis(1234),
            rows_left: 2,
            batch_remaining: Duration::from_secs(3),
            harness_deadline_remaining: Duration::from_secs(9),
        };
        let slot = export.row(
            0,
            "first",
            json!({"label": id.label(), "content_sha256": id.content_sha256()}),
            Some(&grant),
            Some(RowQuery {
                prepared: &slice,
                slice_normalized_sha256: Some(slice_sha),
                config: &config,
            }),
        );
        export.row_outcome(slot, json!({"outcome": "proved"}));

        let dir = root.path().join("demo__harness");
        let manifest: Value = serde_json::from_str(
            &std::fs::read_to_string(dir.join("manifest.json")).expect("manifest"),
        )
        .expect("json");
        assert_eq!(manifest["schema"], ROW_EXPORT_SCHEMA);
        assert_eq!(
            std::fs::read_to_string(dir.join("source.smt2")).expect("source"),
            TWO_PROPERTIES
        );
        assert_eq!(manifest["source"]["sha256"], sha256_hex(TWO_PROPERTIES.as_bytes()));
        assert_eq!(manifest["per_property_batch"]["reparse_check"]["status"], "ok");
        let row = &manifest["rows"][0];
        assert_eq!(row["prepared_matches_reparse"], true);
        assert_eq!(row["solve_call"]["proof_mode"], "None");
        assert_eq!(row["solve_call"]["strict_validation"], true);
        assert_eq!(row["solve_call"]["adaptive_strict_proofs"], true);
        assert_eq!(row["solve_call"]["timeout_ms"], 1234);
        assert_eq!(row["grant"]["row_budget_ms"], 1234);
        assert_eq!(row["outcome"]["outcome"], "proved");
        let prepared = std::fs::read_to_string(
            dir.join(row["prepared_problem"]["file"].as_str().expect("file")),
        )
        .expect("prepared");
        assert_eq!(
            sha256_hex(prepared.as_bytes()),
            row["prepared_problem"]["normalized_input_sha256"].as_str().unwrap()
        );
        assert_eq!(
            row["prepared_problem"]["normalized_input_sha256"],
            row["prepared_problem"]["ay_normalized_input_sha256"],
            "the written text is exactly what AY hashes"
        );
    }

    /// Review round 3: the loop-contract retry's child driver inherited the
    /// parent's `TRUST_MC_CHC_ROW_EXPORT_DIR` and wrote the same
    /// `<dir>/<harness>/`, so the export's `source.smt2` and `manifest.json`
    /// ended up holding the child's query and environment (measured on
    /// `skipped_loop_assumes_no_invariant`: source sha256 `81f3b17c…` against
    /// the parent's `6f0137d9…`). The child now exports below the parent's
    /// directory, and the parent's record says a retry ran. Against the old
    /// behaviour (the child handed the parent's root) the first assertion fails.
    #[test]
    fn a_retry_lane_export_never_overwrites_the_parent_export() {
        const LANE_QUERY: &str = "(set-logic HORN)\n(declare-rel error ())\n(query error)\n";
        let root = tempfile::tempdir().expect("tempdir");
        let smt_file = root.path().join("harness.smt2");
        std::fs::write(&smt_file, TWO_PROPERTIES).expect("fixture");
        let harness = "demo::retried";
        let parent =
            RowExport::begin(root.path(), harness, &smt_file, TWO_PROPERTIES).expect("parent");
        drop(parent);

        // The child, as the retry starts it: its own root below the parent's.
        let lane_root =
            crate::loop_two_lane::retry_lane_export_root(root.path(), &file_component(harness));
        let lane_smt = root.path().join("lane.smt2");
        std::fs::write(&lane_smt, LANE_QUERY).expect("lane fixture");
        let child = RowExport::begin(&lane_root, harness, &lane_smt, LANE_QUERY).expect("child");
        drop(child);

        let dir = harness_dir(root.path(), harness);
        assert_eq!(
            std::fs::read_to_string(dir.join("source.smt2")).expect("parent source"),
            TWO_PROPERTIES,
            "the parent's source survives the retry"
        );
        assert_eq!(
            read_manifest(root.path(), harness)["source"]["sha256"],
            sha256_hex(TWO_PROPERTIES.as_bytes())
        );
        assert_eq!(
            std::fs::read_to_string(harness_dir(&lane_root, harness).join("source.smt2"))
                .expect("lane source"),
            LANE_QUERY,
            "the lane's own query is exported too, beside the parent's"
        );

        record_loop_contract_retry_under(
            root.path(),
            harness,
            json!({"outcome": "inconclusive: test", "argv": ["--exact"]}),
        );
        let manifest = read_manifest(root.path(), harness);
        assert_eq!(manifest["loop_contract_retry"]["ran"], true);
        assert_eq!(manifest["loop_contract_retry"]["outcome"], "inconclusive: test");
        assert_eq!(manifest["source"]["sha256"], sha256_hex(TWO_PROPERTIES.as_bytes()));
        let record: Value = serde_json::from_str(
            &std::fs::read_to_string(dir.join("loop-contract-retry/retry.json")).expect("record"),
        )
        .expect("json");
        assert_eq!(record["argv"][0], "--exact");
    }

    /// A parent that wrote no manifest (a BMC-lane parent never reaches the CHC
    /// export) still gets the retry record, and nothing else is invented.
    #[test]
    fn a_retry_record_without_a_parent_manifest_writes_only_the_record() {
        let root = tempfile::tempdir().expect("tempdir");
        record_loop_contract_retry_under(root.path(), "bmc_parent", json!({"outcome": "proved"}));
        let dir = harness_dir(root.path(), "bmc_parent");
        assert!(dir.join("loop-contract-retry/retry.json").is_file());
        assert!(!dir.join("manifest.json").exists());
    }

    fn read_manifest(root: &Path, harness: &str) -> Value {
        let text = std::fs::read_to_string(harness_dir(root, harness).join("manifest.json"))
            .expect("manifest");
        serde_json::from_str(&text).expect("json")
    }

    /// AY's review of the exports: an `AdaptiveParallel` row also depends on
    /// the host's parallelism, the armed process cap and the AY environment,
    /// which the manifest did not record.
    #[test]
    fn the_manifest_records_the_execution_environment() {
        let root = tempfile::tempdir().expect("tempdir");
        let smt_file = root.path().join("harness.smt2");
        std::fs::write(&smt_file, TWO_PROPERTIES).expect("fixture");
        let _export = RowExport::begin(root.path(), "env::harness", &smt_file, TWO_PROPERTIES)
            .expect("export");
        let manifest = read_manifest(root.path(), "env::harness");
        let environment = &manifest["execution_environment"];
        assert_eq!(
            environment["available_parallelism"],
            json!(std::thread::available_parallelism().unwrap().get())
        );
        assert!(environment["harness_workers"].as_u64().is_some_and(|n| n >= 1), "{environment}");
        let cap = crate::call_ay::chc::resource_envelope::armed_process_cap_bytes();
        assert_eq!(
            environment["process_memory_cap_bytes"],
            if cap == 0 { Value::Null } else { json!(cap) }
        );
        let env = environment["env"].as_object().expect("env map");
        for (name, value) in std::env::vars() {
            if name.starts_with("AY_") || name.starts_with("TRUST_MC_") {
                assert_eq!(env.get(&name), Some(&json!(value)), "{name}");
            }
        }
        assert!(
            env.keys().all(|name| name.starts_with("AY_") || name.starts_with("TRUST_MC_")),
            "{env:?}"
        );
    }

    /// The acyclic-BMC lane's exact call and join record reach the manifest,
    /// begin before the lane runs and end after it is joined.
    #[test]
    fn the_acyclic_bmc_lane_call_and_join_are_recorded() {
        let root = tempfile::tempdir().expect("tempdir");
        let smt_file = root.path().join("harness.smt2");
        std::fs::write(&smt_file, TWO_PROPERTIES).expect("fixture");
        let export = RowExport::begin(root.path(), "lane::harness", &smt_file, TWO_PROPERTIES)
            .expect("export");
        export.acyclic_bmc_lane_begin(json!({"max_depth": 3, "time_budget_ms": 30000}));
        let begun = read_manifest(root.path(), "lane::harness");
        assert_eq!(begun["acyclic_bmc_lane"]["call"]["max_depth"], json!(3));
        assert!(begun["acyclic_bmc_lane"].get("join").is_none());
        export.acyclic_bmc_lane_end(
            "guard-timeout",
            json!({"drain_ms": 4480, "drain_failed": true, "abandoned": false}),
        );
        let ended = read_manifest(root.path(), "lane::harness");
        let lane = &ended["acyclic_bmc_lane"];
        assert_eq!(lane["call"]["time_budget_ms"], json!(30000));
        assert_eq!(lane["outcome"], json!("guard-timeout"));
        assert_eq!(lane["join"]["drain_ms"], json!(4480));
        assert_eq!(lane["join"]["drain_failed"], json!(true));
    }

    #[test]
    fn a_reparse_that_disagrees_is_reported_not_hidden() {
        let root = tempfile::tempdir().expect("tempdir");
        let smt_file = root.path().join("harness.smt2");
        std::fs::write(&smt_file, TWO_PROPERTIES).expect("fixture");
        let export = RowExport::begin(root.path(), "h", &smt_file, TWO_PROPERTIES).expect("export");
        let problem = ChcParser::parse(TWO_PROPERTIES).expect("parses");
        let wrong = vec![("error_p0".to_string(), "0".repeat(64))];
        export.begin_batch(json!({}), &wrong, &[], &problem, &|_| {});
        let manifest: Value = serde_json::from_str(
            &std::fs::read_to_string(root.path().join("h").join("manifest.json"))
                .expect("manifest"),
        )
        .expect("json");
        assert_eq!(manifest["per_property_batch"]["reparse_check"]["status"], "mismatch");
    }

    #[test]
    fn witness_formulas_render_as_smtlib_only_when_display_is_plain_smtlib() {
        let x = ChcExpr::Var(ay::chc::ChcVar::new("x", ChcSort::BitVec(8)));
        let formula = ChcExpr::eq(x.clone(), ChcExpr::BitVec(3, 8));
        let script = smtlib_script(&formula).expect("plain BV renders");
        assert_eq!(
            script,
            "(set-logic ALL)\n(declare-fun x () (_ BitVec 8))\n(assert (= x (_ bv3 8)))\n(check-sat)\n"
        );
        let ctor = ChcExpr::FuncApp("mk".to_string(), ChcSort::Int, vec![std::sync::Arc::new(x)]);
        let refused = smtlib_script(&ChcExpr::eq(ctor, ChcExpr::Int(0))).expect_err("refused");
        assert!(refused.contains("function application mk"), "{refused}");
    }

    #[test]
    fn witness_queries_are_recorded_with_their_results() {
        let root = tempfile::tempdir().expect("tempdir");
        let smt_file = root.path().join("h.smt2");
        std::fs::write(&smt_file, TWO_PROPERTIES).expect("fixture");
        let export = RowExport::begin(root.path(), "h", &smt_file, TWO_PROPERTIES).expect("export");
        let problem = ChcParser::parse(TWO_PROPERTIES).expect("parses");
        let x = ChcExpr::Var(ay::chc::ChcVar::new("x", ChcSort::Int));
        let formula = ChcExpr::eq(x, ChcExpr::Int(1));
        let seq = export.witness_query(3, "is-sat", &formula, &problem);
        export.witness_result(seq, "sat");
        export.flush();
        let dir = root.path().join("h");
        let manifest: Value =
            serde_json::from_str(&std::fs::read_to_string(dir.join("manifest.json")).unwrap())
                .unwrap();
        let search = &manifest["acyclic_witness_search"];
        assert_eq!(search["queries_issued"], 1);
        let query = &search["queries"][0];
        assert_eq!(query["seq"], 0);
        assert_eq!(query["clause_index"], 3);
        assert_eq!(query["result"], "sat");
        let normalized = std::fs::read_to_string(
            dir.join(query["constraint_query"]["file"].as_str().expect("file")),
        )
        .unwrap();
        assert_eq!(
            sha256_hex(normalized.as_bytes()),
            query["constraint_query"]["ay_normalized_input_sha256"].as_str().unwrap(),
            "the written text is what AY hashes for the constraint-only query"
        );
        let script =
            std::fs::read_to_string(dir.join(query["smtlib"]["file"].as_str().expect("smt2")))
                .unwrap();
        assert!(script.contains("(assert (= x 1))"), "{script}");
    }

    #[test]
    fn an_unwritable_root_disables_the_export_without_failing() {
        let root = tempfile::tempdir().expect("tempdir");
        let blocker = root.path().join("file");
        std::fs::write(&blocker, "not a directory").expect("fixture");
        assert!(RowExport::begin(&blocker, "h", &blocker, TWO_PROPERTIES).is_none());
    }
}
