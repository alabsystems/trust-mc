// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The `trust-mc` front door.
//!
//! This module tree is a **wrapper**. It contains no verification logic:
//! every real action is performed by `trust-mc-driver` (the engine), which the
//! front door locates, sanity-checks, and `exec`s with a translated argument
//! list ([`engine`]). What it adds on top of the engine is the part a person
//! meets first:
//!
//! * `--help`, `--version`, `explain`, `quickstart`, `example` and `doctor`
//!   answer with **nothing installed** — no sysroot, no solver, no network.
//! * `explain <topic>` describes how the tool works (pipeline, bounded vs
//!   unbounded proving, reading verdicts, soundness, ...) in the tool itself
//!   ([`topics`]), and `example <name>` hands out harnesses that are known to
//!   verify or fail the way they say ([`examples`]).
//! * A zero-setup single-file path: `trust-mc example > demo.rs && trust-mc demo.rs`.
//! * Actionable diagnostics: a missing engine, an incomplete library sysroot,
//!   or a missing / mismatched `ay` solver each print exactly what is absent
//!   and the command that fixes it ([`doctor`]).
//! * A small set of friendly flags (`--unwind`, `--timeout`, `--list`,
//!   `--solver`) mapped onto the engine's real flags, with every other flag
//!   forwarded untouched so the engine's whole surface stays reachable
//!   ([`args`]). Flags trust-mc cannot honor are rejected by name.
//!
//! The same engine discovery serves `cargo-trust-mc` / `targo-trust-mc`
//! ([`cargo_proxy`]), so a local `cargo build-dev` works for both entry points.

mod args;
mod cancel;
mod doctor;
mod engine;
mod examples;
mod help;
mod summary;
mod topics;

use std::env;
use std::ffi::OsString;
use std::path::Path;
use std::process::ExitCode;

/// Comes from our Cargo.toml manifest file.
pub(crate) const VERSION: &str = env!("CARGO_PKG_VERSION");

/// The engine binary this front door drives. Everything real happens there.
pub(crate) const DRIVER: &str = "trust-mc-driver";

/// The rustc driver the engine runs; it must sit beside the engine.
pub(crate) const COMPILER: &str = "trust-mc-compiler";

/// The exact command that builds the engine plus its library sysroot in place.
pub(crate) const BUILD_CMD: &str = "cargo run --release -p build-trust-mc -- build-dev --release";

/// Exit code for a usage error (bad or unsupported flag, missing input).
pub(crate) const EXIT_USAGE: u8 = 2;
/// Exit code for "the machine isn't ready" (engine, sysroot or solver missing).
pub(crate) const EXIT_NOT_READY: u8 = 3;

/// Subcommands that belong to the engine and are forwarded verbatim.
pub(crate) const ENGINE_SUBCOMMANDS: &[&str] = &["list", "autoharness", "playback", "verify-std"];

/// Front-door commands, in the order the help lists them. `help` and the
/// engine subcommands are dispatched separately.
pub(crate) const COMMANDS: &[&str] = &[
    "verify",
    "list",
    "example",
    "explain",
    "quickstart",
    "doctor",
    "flags",
    "version",
    "setup",
    "help",
];

/// A front-door failure: a message already formatted for the user, and the exit
/// code to leave with.
#[derive(Debug)]
pub(crate) struct Fail {
    pub(crate) msg: String,
    pub(crate) code: u8,
}

impl Fail {
    pub(crate) fn usage(msg: impl Into<String>) -> Self {
        Fail { msg: msg.into(), code: EXIT_USAGE }
    }

    pub(crate) fn not_ready(msg: impl Into<String>) -> Self {
        Fail { msg: msg.into(), code: EXIT_NOT_READY }
    }

    pub(crate) fn other(msg: impl Into<String>) -> Self {
        Fail { msg: msg.into(), code: 1 }
    }
}

pub(crate) type Front<T> = Result<T, Fail>;

/// Entry point for the `trust-mc` binary.
pub fn front_door() -> ExitCode {
    let argv: Vec<OsString> = env::args_os().skip(1).collect();
    match run(&argv) {
        Ok(code) => code,
        Err(fail) => {
            eprintln!("{}", fail.msg);
            ExitCode::from(fail.code)
        }
    }
}

/// Entry point for the `cargo-trust-mc` / `targo-trust-mc` proxies.
///
/// `bin` is the invocation identity handed to the engine as `argv[0]`
/// (`cargo-trust-mc`, a private compat protocol shared by both proxies). The
/// engine is located exactly as for `trust-mc`, so a local build serves
/// `cargo trust-mc` too; `cargo trust-mc setup` installs a release bundle.
pub fn cargo_proxy(bin: &str) -> ExitCode {
    let argv: Vec<OsString> = env::args_os().collect();
    match crate::parse_args(argv.clone()) {
        crate::ArgsResult::ExplicitSetup { use_local_bundle, use_local_toolchain } => {
            match crate::setup::setup(use_local_bundle, use_local_toolchain) {
                Ok(()) => ExitCode::SUCCESS,
                Err(e) => {
                    eprintln!("error: {e:#}");
                    ExitCode::FAILURE
                }
            }
        }
        crate::ArgsResult::Default => {
            // `cargo trust-mc <args>` arrives as `cargo-trust-mc trust-mc <args>`;
            // the engine reads that identity from argv[1], so it must stay in
            // front. Everything after it gets the SAME translation the
            // single-file front door applies, so the flags `--help` and
            // `explain cargo` teach — `--timeout`, `--unwind`, `--list` — work
            // in both modes instead of hitting the engine's own parser.
            // Kept for the post-run hint: `argv` is consumed just below.
            let argv_for_hint: Vec<OsString> = argv.clone();
            // `--summary` is a front-door flag; strip it before the engine.
            let (want_summary, argv) = summary::take_summary_flag(&argv);
            let mut rest: Vec<OsString> = argv.into_iter().skip(1).collect();
            let identity = if rest.first().is_some_and(|a| a == "trust-mc" || a == "kani") {
                Some(rest.remove(0))
            } else {
                None
            };

            // A subcommand (`list`, `playback`, …) owns its own flags, and
            // `--help`/`--version` are answered by the engine's parser without
            // solving anything; both pass through untouched.
            let untranslated = rest
                .first()
                .and_then(|a| a.to_str())
                .is_some_and(|first| ENGINE_SUBCOMMANDS.contains(&first))
                || rest.iter().any(|a| a == "--help" || a == "-h" || a == "--version" || a == "-V");

            let plan = if untranslated {
                let listing = rest.first().is_some_and(|a| a == "list")
                    || rest.iter().any(|a| {
                        a == "--harnesses"
                            || a == "--help"
                            || a == "-h"
                            || a == "--version"
                            || a == "-V"
                    });
                let verbose = rest.iter().any(|a| a == "--verbose" || a == "-v" || a == "--debug");
                args::Plan { args: rest, needs_solver: !listing, verbose }
            } else {
                match args::translate_cargo(&rest) {
                    Ok(plan) => plan,
                    Err(fail) => {
                        eprintln!("{}", fail.msg);
                        return ExitCode::from(fail.code);
                    }
                }
            };

            let mut args = Vec::with_capacity(plan.args.len() + 1);
            args.extend(identity);
            args.extend(plan.args);
            // Only the translated path is the engine's ordinary verification
            // flow, which is the one that records verdicts. A subcommand
            // (`playback`, `autoharness`, ...) accepts the flag but runs its
            // own flow and writes nothing, so asking there would produce a
            // silent "no verdicts" for a run that had them — it gets no
            // artifact and keeps the exit-code-only behaviour instead.
            let artifact = attach_run_artifact(&want_summary, &mut args, !untranslated);
            match engine::drive_as(bin, args, plan.needs_solver, plan.verbose) {
                Ok(code) => {
                    if artifact.render
                        && let Some(path) = &artifact.path
                    {
                        summary::render(path);
                    }
                    // A crate-wide run needs the "which input?" pointer at
                    // least as much as a single file does — more, since the
                    // failing harness is one of many. `needs_solver` is what
                    // distinguishes a verification from `list` / `--help`,
                    // which must stay silent. No `.rs` argument to look for
                    // here: the package IS the target.
                    if plan.needs_solver {
                        next_step_after_failure(
                            &argv_for_hint,
                            code,
                            false,
                            artifact.a_harness_reached_a_verdict(),
                        );
                    }
                    artifact.discard_if_ours();
                    code
                }
                Err(fail) => {
                    eprintln!("{}", fail.msg);
                    ExitCode::from(fail.code)
                }
            }
        }
    }
}

fn run(argv: &[OsString]) -> Front<ExitCode> {
    // An engine subcommand may be preceded by front-door flags — `trust-mc -v
    // list demo.rs` reads naturally and used to be routed to `verify`, where
    // the engine rejected `list` as a stray positional. Accept the subcommand
    // wherever it appears before the first non-flag argument, and hand the
    // whole line to the engine with the subcommand moved to the front.
    let argv = &hoist_engine_subcommand(argv);
    let first = argv.first().and_then(|a| a.to_str());
    let engine_sub = first.is_some_and(|s| ENGINE_SUBCOMMANDS.contains(&s));

    // `--help` / `--version` are answered here, before anything touches the
    // filesystem, so they work on a machine with no sysroot and no solver.
    // After an engine subcommand they belong to the engine's own parser.
    if !engine_sub {
        if argv.iter().any(|a| a == "--help" || a == "-h") {
            // `trust-mc example --help` → help for `example`. `trust-mc
            // demo.rs --help` is a question about verifying, not a mistyped
            // command, so it gets the `verify` page rather than an error.
            let subject = match first.filter(|f| !f.starts_with('-')) {
                Some(word) if help::for_command(word).is_some() => Some(word),
                Some(word) if topics::find(word).is_some() => Some(word),
                Some(_) => Some("verify"),
                None => None,
            };
            return help::command(subject);
        }
        if argv.iter().any(|a| a == "--version" || a == "-V") {
            println!("trust-mc {VERSION}");
            return Ok(ExitCode::SUCCESS);
        }
    }

    match first {
        None => {
            // The landing page is the right thing to show someone who typed
            // the bare name -- but the exit code has to stay honest. For a
            // verifier, 0 is a claim, and what this run verified is nothing:
            //
            //     trust-mc $FILE      # $FILE unset -> a bare invocation
            //
            // exits 0 and the pipeline goes green having checked no code at
            // all. That is the same false pass the vacuity gates exist to
            // stop, and the same answer applies -- fail closed. rustc and gcc
            // treat "no input files" the same way.
            //
            // An explicit request for the page (`trust-mc --help`, `trust-mc
            // help`) is handled above and still exits 0; it asked for help and
            // got it.
            print!("{}", help::top_level());
            eprintln!(
                "\nerror: no input file — nothing was verified\n                        Run `trust-mc <FILE.rs>`, or `trust-mc --help` for this page                  without an error."
            );
            Ok(ExitCode::from(2))
        }
        Some("help") => help::command(argv.get(1).and_then(|a| a.to_str())),
        Some("version") => doctor::version_command(&argv[1..]),
        Some("verify") => verify(&argv[1..]),
        Some("example") => examples::command(&argv[1..]),
        Some("explain") => topics::command(&argv[1..]),
        Some("quickstart") => topics::command(&[OsString::from("quickstart")]),
        Some("doctor") => doctor::command(&argv[1..]),
        Some("flags") => engine::show_engine_flags(&argv[1..]),
        Some("setup") => run_setup(),
        Some(_) if engine_sub => {
            // `list` enumerates metadata and never calls the solver.
            let needs_solver = first != Some("list");
            let verbose = argv.iter().any(|a| a == "--verbose" || a == "-v" || a == "--debug");
            engine::drive(argv.to_vec(), needs_solver, verbose)
        }
        Some(word) if looks_like_a_command(word) => Err(unknown_command(word)),
        Some(_) => verify(argv),
    }
}

/// Move an engine subcommand that appears after front-door flags to the front.
///
/// Only the tokens before the first non-flag argument are considered, and a
/// token consumed as the value of a value-taking flag is skipped, so a harness
/// legitimately named `list` (`--harness list file.rs`) is not mistaken for the
/// subcommand. Returns `argv` unchanged when there is nothing to hoist.
fn hoist_engine_subcommand(argv: &[OsString]) -> Vec<OsString> {
    /// Front-door flags that take a separate value token.
    // The front end's own value-taking flags, plus every one the engine
    // defines -- a subcommand name must never be confused with a flag's value.
    const FRONT_VALUE_FLAGS: &[&str] = &["--timeout", "--solver"];
    let takes_a_value =
        |text: &str| FRONT_VALUE_FLAGS.contains(&text) || args::takes_a_value(text);

    let mut idx = 0;
    while idx < argv.len() {
        let Some(text) = argv[idx].to_str() else { return argv.to_vec() };
        if text == "--" {
            return argv.to_vec();
        }
        if text.starts_with('-') {
            // `--flag=value` carries its value inline; `--flag value` eats the
            // next token, which must not be read as a subcommand.
            if takes_a_value(text) {
                idx += 1;
            }
            idx += 1;
            continue;
        }
        if idx > 0 && ENGINE_SUBCOMMANDS.contains(&text) {
            let mut hoisted = Vec::with_capacity(argv.len());
            hoisted.push(argv[idx].clone());
            hoisted.extend(argv[..idx].iter().cloned());
            hoisted.extend(argv[idx + 1..].iter().cloned());
            return hoisted;
        }
        return argv.to_vec();
    }
    argv.to_vec()
}

/// `trust-mc [OPTIONS] <FILE.rs>` and `trust-mc verify ...`.
fn verify(argv: &[OsString]) -> Front<ExitCode> {
    let (want, argv_rest) = summary::take_summary_flag(argv);
    let mut plan = args::translate(&argv_rest)?;
    // Always ask for the verdict artifact here: this is the engine's ordinary
    // verification flow, so the artifact appearing (or not) is what tells us
    // afterwards whether a harness actually ran. A `--list` run parses the
    // flag and writes nothing, which is the answer we want from it.
    let artifact = attach_run_artifact(&want, &mut plan.args, true);
    let code = engine::drive(plan.args, plan.needs_solver, plan.verbose)?;
    if artifact.render
        && let Some(path) = &artifact.path
    {
        summary::render(path);
    }
    next_step_after_failure(argv, code, true, artifact.a_harness_reached_a_verdict());
    artifact.discard_if_ours();
    Ok(code)
}

/// The engine's per-run verdict artifact (`--proof-summary-json`): where it
/// will land, whether `--summary` asked us to render it, and whether we are
/// the ones who requested it and so must clean it up.
///
/// It serves two readers. `--summary` renders it as a table; and every run
/// consults it for one bit — did any harness actually reach a verdict? — which
/// the front door cannot learn any other way, because it streams the engine's
/// stdout straight through rather than capturing it.
struct RunArtifact {
    /// Where the artifact will be, if one was asked for at all.
    path: Option<std::path::PathBuf>,
    /// `--summary` wants the table printed.
    render: bool,
    /// We added the flag, so the file is ours to delete.
    ours: bool,
}

impl RunArtifact {
    /// Did at least one harness produce a verdict in this run?
    ///
    /// `None` means "we did not ask", not "no": a caller who gets `None` must
    /// fall back to whatever it did before rather than read it as a denial.
    ///
    /// The engine writes this file at the end of the verification flow, after
    /// the harnesses have run. So a compile error, an unreadable file, or any
    /// other early exit leaves no file at all; a run that reached the flow but
    /// selected nothing (an unmatched `--harness` filter) leaves one with an
    /// empty `harnesses` array. Both are "nothing was verified".
    fn a_harness_reached_a_verdict(&self) -> Option<bool> {
        let text = std::fs::read_to_string(self.path.as_ref()?);
        let Ok(text) = text else { return Some(false) };
        // The same shape `summary::parse` reads: a top-level `"harnesses"`
        // array holding one object per harness, each keyed `"harness"`. The
        // leading quote is part of the needle, so the `"total_harnesses"` /
        // `"manual_harnesses"` counters in the summary block do not match.
        Some(text.find("\"harnesses\"").is_some_and(|at| text[at..].contains("\"harness\":")))
    }

    /// Remove the scratch file we asked for. A path the CALLER named is
    /// theirs: they asked for that artifact and must still have it.
    fn discard_if_ours(&self) {
        if self.ours
            && let Some(path) = &self.path
        {
            let _ = std::fs::remove_file(path);
        }
    }
}

/// Point the engine at its verdict artifact and say what to do with it.
///
/// A caller who already passed `--proof-summary-json` gets THEIR file read
/// back; we do not write a second copy of the same data, and we must not
/// silently redirect the artifact they asked for somewhere else.
///
/// `may_request` is false on the paths where the flag would be accepted but
/// never honored, so an absent file there means "we cannot tell", not "no
/// harness ran".
fn attach_run_artifact(
    want: &summary::SummaryRequest,
    args: &mut Vec<OsString>,
    may_request: bool,
) -> RunArtifact {
    if let Some(existing) = &want.existing {
        return RunArtifact {
            path: Some(std::path::PathBuf::from(existing)),
            render: want.wanted,
            ours: false,
        };
    }
    if !want.wanted && !may_request {
        return RunArtifact { path: None, render: false, ours: false };
    }
    let path = summary::scratch_artifact_path();
    // The scratch name is keyed by pid, which the OS reuses. A file left by an
    // earlier trust-mc that happened to hold this pid would answer for THIS
    // run — and would answer "a harness ran" for a run that never compiled.
    let _ = std::fs::remove_file(&path);
    args.push(OsString::from("--proof-summary-json"));
    args.push(OsString::from(&path));
    RunArtifact { path: Some(path), render: want.wanted, ours: true }
}

/// After a failed verification, name the flag that answers the first question
/// anyone asks: WHICH input breaks it?
///
/// The engine can produce the failing values — `--concrete-playback print`
/// prints a runnable `#[test]` with the exact bytes — but a failing run said
/// nothing about it, so the feature was effectively undiscoverable. A verifier
/// that reports "attempt to add with overflow" and stops has told you the
/// least useful half of what it knows.
///
/// Written to STDERR, and never when the user asked for quiet or already asked
/// for playback:
///   * stdout stays byte-identical, so `--sarif` / `--proof-summary-json`
///     consumers and the expected-output corpora are untouched;
///   * this lives in the frontend, which is what a person runs — the corpora
///     drive `trust-mc-driver` directly and never see it.
///
/// `saw_verdict` gates it on something having actually been verified. Exit 1
/// is not that: the engine leaves with 1 for a compile error, an unmatched
/// `--harness` filter and an unreadable input as well as for a failing check,
/// and offering a playback flag to someone whose code did not compile is noise
/// that costs the real hint its credibility. `None` means the caller had no
/// way to tell, and keeps the exit-code-only behaviour.
fn next_step_after_failure(
    argv: &[OsString],
    code: ExitCode,
    require_rs_file: bool,
    saw_verdict: Option<bool>,
) {
    // ExitCode has no accessor, so compare against the one value that means
    // "checks failed". Anything else (success, or a usage/setup error that
    // already printed its own guidance) gets no hint.
    if format!("{code:?}") != format!("{:?}", ExitCode::from(1u8)) {
        return;
    }
    if saw_verdict == Some(false) {
        return;
    }
    let mut saw_file = false;
    for arg in argv {
        let Some(a) = arg.to_str() else { continue };
        if a == "--quiet" || a == "-q" || a.starts_with("--concrete-playback") {
            return;
        }
        // Machine-readable consumers do not want prose, even on stderr.
        if a == "--sarif" || a.starts_with("--proof-summary-json") {
            return;
        }
        if a.ends_with(".rs") {
            saw_file = true;
        }
    }
    if require_rs_file && !saw_file {
        return;
    }
    eprintln!();
    eprintln!("hint: which input triggers this? re-run with");
    eprintln!("          -Z concrete-playback --concrete-playback print");
    eprintln!("      to print a runnable #[test] holding the failing values.");
    eprintln!("      If the run said [AY:CTREX_NOT_CERTIFIED] or VACUOUS, read");
    eprintln!("      `trust-mc explain limits` first — the failure may be the");
    eprintln!("      encoding, not your code.");
}

/// A bare word that is neither a flag nor a Rust file nor an existing path is
/// a (mistyped) command, and deserves a command-shaped error rather than
/// "no such file".
fn looks_like_a_command(word: &str) -> bool {
    if word.starts_with('-') {
        return false;
    }
    let path = Path::new(word);
    if path.extension().is_some_and(|e| e == "rs") {
        return false;
    }
    !path.exists()
}

fn unknown_command(word: &str) -> Fail {
    let mut msg = format!("error: unknown command `{word}`\n");
    if let Some(near) = closest_command(word) {
        msg.push_str(&format!("       did you mean `trust-mc {near}`?\n"));
    }
    msg.push_str(&format!(
        "\n{}Commands: {}.\nA file to verify must end in `.rs`; to verify a Cargo package use `cargo trust-mc`.",
        help::usage_lines(),
        COMMANDS.join(", ")
    ));
    Fail::usage(msg)
}

/// The command with the smallest edit distance to `word`, if it is close.
pub(crate) fn closest_command(word: &str) -> Option<&'static str> {
    closest(word, COMMANDS.iter().copied().chain(ENGINE_SUBCOMMANDS.iter().copied()))
}

/// Closest candidate by Levenshtein distance, accepting at most two edits (or
/// a prefix / containment match for longer words).
pub(crate) fn closest<'a>(
    word: &str,
    candidates: impl IntoIterator<Item = &'a str>,
) -> Option<&'a str> {
    let word = word.to_ascii_lowercase();
    let mut best: Option<(usize, &'a str)> = None;
    for candidate in candidates {
        let distance = if candidate.starts_with(&word) || word.starts_with(candidate) {
            1
        } else {
            levenshtein(&word, candidate)
        };
        if distance <= 2 && best.is_none_or(|(d, _)| distance < d) {
            best = Some((distance, candidate));
        }
    }
    best.map(|(_, c)| c)
}

fn levenshtein(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    let mut cur = vec![0; b.len() + 1];
    for (i, ca) in a.iter().enumerate() {
        cur[0] = i + 1;
        for (j, cb) in b.iter().enumerate() {
            let cost = usize::from(ca != cb);
            cur[j + 1] = (prev[j + 1] + 1).min(cur[j] + 1).min(prev[j] + cost);
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev[b.len()]
}

fn run_setup() -> Front<ExitCode> {
    match crate::parse_args(env::args_os().collect()) {
        crate::ArgsResult::ExplicitSetup { use_local_bundle, use_local_toolchain } => {
            crate::setup::setup(use_local_bundle, use_local_toolchain)
                .map(|()| ExitCode::SUCCESS)
                .map_err(|e| Fail::other(format!("error: {e:#}")))
        }
        crate::ArgsResult::Default => Err(Fail::usage(
            "error: unrecognized `setup` arguments\n       \
             Usage: trust-mc setup [--use-local-bundle <FILE>] [--use-local-toolchain <DIR>]",
        )),
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "a panicking assertion is the point in tests")]
mod tests {
    use super::*;

    #[test]
    fn mistyped_commands_are_suggested() {
        assert_eq!(closest_command("exmaple"), Some("example"));
        assert_eq!(closest_command("explian"), Some("explain"));
        assert_eq!(closest_command("doc"), Some("doctor"));
        assert_eq!(closest_command("quick"), Some("quickstart"));
        assert_eq!(closest_command("lst"), Some("list"));
        assert_eq!(closest_command("verfy"), Some("verify"));
        assert_eq!(closest_command("zzzzzzzz"), None);
    }

    #[test]
    fn a_bare_word_is_a_command_but_a_rust_file_is_not() {
        assert!(looks_like_a_command("exmaple"));
        assert!(!looks_like_a_command("demo.rs"));
        assert!(!looks_like_a_command("--unwind"));
        // An existing directory is not a command either; `translate` explains it.
        assert!(!looks_like_a_command(env!("CARGO_MANIFEST_DIR")));
    }

    #[test]
    fn every_command_has_help_and_is_listed_in_the_top_level_help() {
        let top = help::top_level();
        for command in COMMANDS {
            assert!(top.contains(command), "top-level help does not mention `{command}`");
            assert!(help::for_command(command).is_some(), "no help page for `{command}`");
        }
    }

    #[test]
    fn the_unknown_command_error_is_a_usage_error_that_suggests() {
        let fail = unknown_command("exmaple");
        assert_eq!(fail.code, EXIT_USAGE);
        assert!(fail.msg.contains("did you mean `trust-mc example`"), "{}", fail.msg);
        assert!(fail.msg.contains("Commands:"), "{}", fail.msg);
    }

    #[test]
    fn levenshtein_is_sane() {
        assert_eq!(levenshtein("", ""), 0);
        assert_eq!(levenshtein("abc", "abc"), 0);
        assert_eq!(levenshtein("abc", "abd"), 1);
        assert_eq!(levenshtein("kitten", "sitting"), 3);
    }
}
