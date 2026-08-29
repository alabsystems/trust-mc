// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Argument translation: the front door's few friendly spellings, mapped onto
//! the engine's real flags. Everything not named here is forwarded unchanged.

use std::ffi::OsString;
use std::path::{Path, PathBuf};

use super::{Fail, Front, help};

/// The translated engine invocation.
#[derive(Debug)]
pub(crate) struct Plan {
    /// Arguments for `trust-mc-driver`, input file first.
    pub(crate) args: Vec<OsString>,
    /// Whether this run will need the `ay` solver binary.
    pub(crate) needs_solver: bool,
    /// Whether the user asked for verbose output (we echo the engine command).
    pub(crate) verbose: bool,
}

/// Flags we deliberately refuse, with the alternative to offer instead.
///
/// These are all flags a user of the comparable academic tool has muscle memory
/// for, and which trust-mc cannot honor because it solves with AY rather than a
/// CBMC/goto pipeline. Rejecting them here (loudly, by name, with the
/// replacement) beats the engine's drop-in behavior of warning and continuing:
/// a flag that silently does nothing is a wrong answer waiting to happen. The
/// engine keeps its permissive shims for `cargo-trust-mc` drop-in scripts.
pub(crate) const UNSUPPORTED: &[(&str, &str)] = &[
    (
        "--cbmc-args",
        "trust-mc has no CBMC backend, so there is nothing to pass CBMC arguments to.\n       \
         Tune the AY backend instead: --unwind <N>, --timeout <T>, --ay-chc, or the\n       \
         engine's --ay-chc-* flags (see `trust-mc explain flags`).",
    ),
    (
        "--solver-args",
        "trust-mc has no CBMC backend. Tune the AY backend with --solver / the engine's --ay-* flags.",
    ),
    (
        "--gen-c",
        "trust-mc has no C code generator (that is a CBMC-pipeline feature). Drop the flag.",
    ),
    ("--print-llbc", "trust-mc has no Lean/LLBC backend. Drop the flag."),
    ("--write-json-symtab", "obsolete: trust-mc has no CBMC symbol table. Drop the flag."),
    (
        "--synthesize-loop-contracts",
        "trust-mc synthesizes loop invariants itself (--ay-chc, PDR) and needs no CBMC\n       \
         loop-contract pass. Drop the flag, or bound the loops explicitly with --unwind <N>.",
    ),
    (
        "--no-slice-formula",
        "CBMC-only formula slicing; trust-mc builds no CBMC formula. Drop the flag.",
    ),
    (
        "--run-sanity-checks",
        "CBMC-only goto-program sanity checks; trust-mc builds no goto program. Drop the flag.",
    ),
    (
        "--visualize",
        "removed: use --coverage for coverage output, or --output-format terse for compact results.",
    ),
    (
        "--enable-unstable",
        "obsolete: enable one named feature with `-Z <feature>`, e.g. `-Z function-contracts`.",
    ),
    ("--dry-run", "obsolete: use --verbose to see the commands trust-mc runs."),
];

/// Solver names the AY backend understands. `direct` is a build-time feature of
/// the engine; we forward it and let the engine be the authority on whether it
/// was compiled in.
pub(crate) const SOLVERS: &[&str] = &["auto", "ay", "direct"];

/// Map the front door's familiar flag spellings onto the engine's real flags.
///
/// | front door              | engine                                           |
/// |-------------------------|--------------------------------------------------|
/// | `--unwind N`            | `--default-unwind N`, or `--unwind N` with a `--harness` |
/// | `--timeout T`           | `-Z unstable-options --harness-timeout T`        |
/// | `--list` / `--harnesses`| `--harnesses` (no solver needed)                 |
/// | `--solver NAME`         | `--smt-solver NAME` (auto, ay, direct)           |
/// | `-v`, `-q`, `--debug`   | unchanged                                        |
///
/// Everything not named here is forwarded unchanged, so the whole
/// `trust-mc-driver` surface (`-Z` features, `--output-format`, `--coverage`,
/// `--concrete-playback`, the `--ay-chc*` family, ...) stays reachable.
pub(crate) fn translate(argv: &[OsString]) -> Front<Plan> {
    let (out, input, needs_solver, verbose) = translate_flags(argv)?;

    let Some(input) = input else {
        return Err(Fail::usage(format!(
            "error: no input file\n\n{}The input must be a path ending in `.rs`. To get one:\n\
             \n    trust-mc example > demo.rs\n    trust-mc demo.rs\n\n\
             To verify a Cargo package instead, use `cargo trust-mc`.",
            help::usage_lines()
        )));
    };

    let path = PathBuf::from(&input);
    if !path.is_file() {
        return Err(Fail::usage(format!(
            "error: no such file: {}\n       \
             trust-mc verifies one Rust source file. To get a sample you can run right now:\n\
             \n    trust-mc example > demo.rs\n    trust-mc demo.rs",
            path.display()
        )));
    }

    let mut args = vec![input];
    args.extend(out);
    Ok(Plan { args, needs_solver, verbose })
}

/// Translate the same friendly flags for `cargo trust-mc`, which verifies a
/// package and so takes no input file.
///
/// Without this the two entry points disagree: `--timeout`, `--unwind` and
/// `--list` are documented in `--help` and `explain cargo`, work for a single
/// file, and were rejected by the engine's own parser under `cargo trust-mc`
/// (`--timeout` is gated behind `-Z unstable-options` as `--harness-timeout`,
/// bare `--unwind` requires `--harness`, and the listing flag is spelled
/// `--harnesses`).
pub(crate) fn translate_cargo(argv: &[OsString]) -> Front<Plan> {
    let (out, input, needs_solver, verbose) = translate_flags(argv)?;
    if let Some(input) = input {
        return Err(Fail::usage(format!(
            "error: `cargo trust-mc` verifies the package, not a file ({})\n       \
             To verify one file on its own, run `trust-mc {}`.",
            PathBuf::from(&input).display(),
            PathBuf::from(&input).display()
        )));
    }
    Ok(Plan { args: out, needs_solver, verbose })
}

/// The shared flag translation. Returns the engine arguments, the input file
/// if one was named, whether the run needs the solver, and the verbose flag.
/// Engine flags that consume a following value.
///
/// The front end hands anything it does not recognize straight to the engine,
/// which is the right default -- but a flag's VALUE is a bare word, and the
/// positional logic below would then read it as the input file. `--sarif` shows
/// the shape: it works once, and the second run in the same directory dies,
/// because by then the report file exists and looks like a positional path.
///
/// ```text
/// trust-mc --sarif report.sarif demo.rs    # first run: fine
/// trust-mc --sarif report.sarif demo.rs    # second run:
/// error: report.sarif is not a Rust source file
/// ```
///
/// That is every CI job that writes a report and re-runs. Knowing which flags
/// take a value is the only way to tell a value from a positional, so the list
/// has to be complete; `value_flags_match_the_engine` re-derives it from
/// `trust-mc-driver --help` and fails when the engine grows a new one.
///
/// Short forms are listed separately because `-p pkg` and `-ppkg` are both
/// legal and only the former eats the next token.
pub(crate) const ENGINE_VALUE_FLAGS: &[&str] = &[
    "--backend",
    "--bench",
    "--bin",
    "--concrete-playback",
    "--conformance-harness",
    "--default-unwind",
    "--example",
    "--exclude",
    "--export-smtlib",
    "--features",
    "--harness",
    "--harness-timeout",
    "--manifest-path",
    "--message-format",
    "--output-format",
    "--package",
    "--proof-summary-json",
    "--sarif",
    "--target-dir",
    "--test",
    "--trust-vc-bundle",
    "--unstable",
    "--unwind",
];

/// Short aliases of [`ENGINE_VALUE_FLAGS`] that also consume the next token.
pub(crate) const ENGINE_VALUE_FLAGS_SHORT: &[&str] = &["-Z", "-e", "-F", "-p"];

/// Does `name` consume the token after it?
pub(crate) fn takes_a_value(name: &str) -> bool {
    ENGINE_VALUE_FLAGS.contains(&name) || ENGINE_VALUE_FLAGS_SHORT.contains(&name)
}

fn translate_flags(argv: &[OsString]) -> Front<(Vec<OsString>, Option<OsString>, bool, bool)> {
    let mut out: Vec<OsString> = Vec::new();
    let mut input: Option<OsString> = None;
    let mut harness_seen = false;
    let mut list_mode = false;
    let mut verbose = false;
    let mut unwind: Option<OsString> = None;
    let mut timeout: Option<OsString> = None;
    let mut unstable_options_seen = false;
    let mut jobs_seen = false;
    let mut output_format_seen = false;

    let mut idx = 0;
    while idx < argv.len() {
        let raw = &argv[idx];
        idx += 1;

        let Some(text) = raw.to_str() else {
            // Not UTF-8: it can only be a path or an opaque value. Preserve it.
            if input.is_none() && Path::new(raw).extension().is_some_and(|e| e == "rs") {
                input = Some(raw.clone());
            } else {
                out.push(raw.clone());
            }
            continue;
        };

        if text == "--" {
            out.extend_from_slice(&argv[idx..]);
            break;
        }

        let (name, attached) = match text.split_once('=') {
            Some((n, v)) if n.starts_with('-') => (n, Some(OsString::from(v))),
            _ => (text, None),
        };

        if let Some((flag, why)) = UNSUPPORTED.iter().find(|(f, _)| *f == name) {
            return Err(Fail::usage(format!(
                "error: {flag} is not supported by trust-mc\n       {why}"
            )));
        }

        match name {
            "--harness" => {
                let value = take_value(name, attached, argv, &mut idx)?;
                if value.is_empty() {
                    return Err(Fail::usage(
                        "error: --harness needs a name, e.g. `--harness my_proof`\n       An empty filter matches nothing; omit the flag to run every harness.",
                    ));
                }
                harness_seen = true;
                out.push(OsString::from("--harness"));
                out.push(value);
            }
            "--list" | "--harnesses" => list_mode = true,
            "--unwind" => {
                let value = take_value(name, attached, argv, &mut idx)?;
                check_unwind(&value)?;
                unwind = Some(value);
            }
            "--timeout" => {
                let value = take_value(name, attached, argv, &mut idx)?;
                check_timeout(&value)?;
                timeout = Some(value);
            }
            "--solver" => {
                let value = take_value(name, attached, argv, &mut idx)?;
                out.push(OsString::from("--smt-solver"));
                out.push(check_solver(&value)?);
            }
            "--jobs" | "-j" => {
                // The engine refuses `--jobs` without `--output-format=terse`,
                // because parallel harnesses interleave and the regular format
                // is unreadable when they do:
                //
                //     error: Conflicting options: --jobs requires
                //            `--output-format=terse`
                //
                // Supplying it is honouring that constraint, not overriding a
                // choice — and only when the user has not stated a format
                // themselves, in which case the engine's error is the right
                // answer and is left alone.
                jobs_seen = true;
                out.push(OsString::from("--jobs"));
                if let Some(value) = attached {
                    out.push(value);
                } else if let Some(value) = argv.get(idx) {
                    out.push(value.clone());
                    idx += 1;
                }
            }
            "--output-format" => {
                output_format_seen = true;
                let value = take_value(name, attached, argv, &mut idx)?;
                out.push(OsString::from("--output-format"));
                out.push(value);
            }
            "--verbose" | "-v" => {
                verbose = true;
                out.push(OsString::from("--verbose"));
            }
            "--debug" => {
                verbose = true;
                out.push(raw.clone());
            }
            "--quiet" | "-q" => out.push(OsString::from("--quiet")),
            "-Z" | "--unstable" => {
                // Remember whether the user enabled the gate `--timeout` needs,
                // so we never pass it twice.
                let value = take_value(name, attached, argv, &mut idx)?;
                if value == "unstable-options" {
                    unstable_options_seen = true;
                }
                out.push(OsString::from("-Z"));
                out.push(value);
            }
            _ if text.starts_with("-Z") && text.len() > 2 => {
                // `-Zunstable-options` spelled as one token.
                if &text[2..] == "unstable-options" {
                    unstable_options_seen = true;
                }
                out.push(raw.clone());
            }
            _ if !text.starts_with('-')
                && input.is_none()
                && Path::new(text).extension().is_some_and(|e| e == "rs") =>
            {
                input = Some(raw.clone());
            }
            _ if !text.starts_with('-')
                && input.is_none()
                && Path::new(text).is_file()
                && Path::new(text).extension().is_none_or(|e| e != "rs") =>
            {
                return Err(Fail::usage(format!(
                    "error: {text} is not a Rust source file\n       trust-mc verifies one `.rs` file. If this really is Rust source,\n       rename it with a `.rs` extension."
                )));
            }
            _ if !text.starts_with('-') && input.is_none() && Path::new(text).is_dir() => {
                return Err(Fail::usage(format!(
                    "error: {text} is a directory\n       \
                     trust-mc verifies one Rust source file (`trust-mc path/to/file.rs`).\n       \
                     To verify a Cargo package, run `cargo trust-mc` inside it."
                )));
            }
            // Unrecognized: hand it to the engine untouched. The engine's
            // parser is the authority on it -- but if it is a flag that takes a
            // value, that value travels with it, so the positional logic above
            // never sees a bare word that was only ever an argument.
            _ => {
                out.push(raw.clone());
                if attached.is_none() && takes_a_value(name) {
                    if let Some(value) = argv.get(idx) {
                        out.push(value.clone());
                        idx += 1;
                    }
                }
            }
        }
    }

    if jobs_seen && !output_format_seen {
        out.push(OsString::from("--output-format"));
        out.push(OsString::from("terse"));
    }

    if list_mode {
        out.push(OsString::from("--harnesses"));
    }

    if let Some(bound) = unwind {
        // The engine's `--unwind` is per-harness and *requires* `--harness`;
        // its crate-wide bound is `--default-unwind`. Pick the one that fits so
        // a bare `--unwind 5` does not die on a missing-required-argument error.
        out.push(OsString::from(if harness_seen { "--unwind" } else { "--default-unwind" }));
        out.push(bound);
    }

    if let Some(budget) = timeout {
        // The engine gates `--harness-timeout` behind `-Z unstable-options`.
        if !unstable_options_seen {
            out.push(OsString::from("-Z"));
            out.push(OsString::from("unstable-options"));
        }
        out.push(OsString::from("--harness-timeout"));
        out.push(budget);
    }

    Ok((out, input, !list_mode, verbose))
}

/// Pull the value of a flag, either from `--flag=value` or the next argument.
fn take_value(
    name: &str,
    attached: Option<OsString>,
    argv: &[OsString],
    idx: &mut usize,
) -> Front<OsString> {
    if let Some(value) = attached {
        return Ok(value);
    }
    if let Some(value) = argv.get(*idx) {
        *idx += 1;
        return Ok(value.clone());
    }
    Err(Fail::usage(format!("error: {name} needs a value, e.g. `{name} <VALUE>`")))
}

fn check_solver(value: &OsString) -> Front<OsString> {
    let text = value.to_string_lossy().to_lowercase();
    if SOLVERS.contains(&text.as_str()) {
        return Ok(OsString::from(text));
    }
    Err(Fail::usage(format!(
        "error: --solver {}: not a trust-mc solver\n       \
         trust-mc discharges obligations with the AY solver; it has no CBMC SAT-solver\n       \
         selection, so names like `cadical`, `kissat`, `minisat`, `z3` or `bin=<PATH>`\n       \
         have no meaning here.\n       \
         Use `--solver ay`, or `--solver auto` (the default).",
        value.to_string_lossy()
    )))
}

/// `--unwind` takes a loop bound. Validated here so a bad value names
/// `--unwind` — the flag the user typed — rather than the engine's
/// `--default-unwind`, which [`translate`] substitutes and they never saw.
fn check_unwind(value: &OsString) -> Front<()> {
    let text = value.to_string_lossy();
    if text.parse::<u32>().is_ok() {
        return Ok(());
    }
    Err(Fail::usage(format!(
        "error: --unwind {text}: not a number\n       Give a whole number of loop iterations, e.g. `--unwind 5`. The bound\n       is the maximum iteration count plus one; see `trust-mc explain bmc`."
    )))
}

/// `--timeout` takes the engine's grammar: digits with an optional `s`, `m`
/// or `h` suffix. Checking here gives a front-door error instead of a clap one.
fn check_timeout(value: &OsString) -> Front<()> {
    let text = value.to_string_lossy();
    let digits = text.trim_end_matches(['s', 'm', 'h']);
    let suffix = &text[digits.len()..];
    if !digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit()) && suffix.len() <= 1 {
        // A zero budget is accepted by the engine and then expires immediately,
        // turning every harness into INCONCLUSIVE with no hint as to why. That
        // is never what someone means; `--timeout` has no "unlimited" spelling
        // (omit it instead).
        if digits.chars().all(|c| c == '0') {
            return Err(Fail::usage(
                "error: --timeout 0 gives every harness no time at all, so all of them\n       report INCONCLUSIVE. Omit --timeout for no limit, or give a real\n       budget such as `--timeout 30s`.",
            ));
        }
        return Ok(());
    }
    Err(Fail::usage(format!(
        "error: --timeout {text}: expected a number with an optional unit, e.g. `30s`, `5m`, `1h`\n       \
         (a bare number is seconds)"
    )))
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "a panicking assertion is the point in tests")]
mod tests {
    use super::*;

    fn args(list: &[&str]) -> Vec<OsString> {
        list.iter().map(OsString::from).collect()
    }

    /// Translate without the "input must exist" check by pointing at this file.
    fn plan_for(list: &[&str]) -> Vec<String> {
        let plan = translate(&args(list)).expect("expected a valid plan");
        plan.args.iter().map(|a| a.to_string_lossy().into_owned()).collect()
    }

    /// A real `.rs` path that is guaranteed to exist while tests run.
    fn this_file() -> String {
        concat!(env!("CARGO_MANIFEST_DIR"), "/src/frontend/args.rs").to_string()
    }

    #[test]
    fn bare_unwind_becomes_the_crate_wide_bound() {
        let file = this_file();
        let got = plan_for(&[&file, "--unwind", "5"]);
        assert_eq!(got, vec![file, "--default-unwind".to_string(), "5".to_string()]);
    }

    #[test]
    fn unwind_with_a_harness_stays_per_harness() {
        let file = this_file();
        let got = plan_for(&[&file, "--harness", "foo", "--unwind=5"]);
        assert_eq!(
            got,
            vec![
                file,
                "--harness".to_string(),
                "foo".to_string(),
                "--unwind".to_string(),
                "5".to_string(),
            ]
        );
    }

    #[test]
    fn timeout_expands_to_the_gated_engine_flag() {
        let file = this_file();
        assert_eq!(
            plan_for(&[&file, "--timeout", "30s"]),
            vec![
                file,
                "-Z".to_string(),
                "unstable-options".to_string(),
                "--harness-timeout".to_string(),
                "30s".to_string(),
            ]
        );
    }

    #[test]
    fn timeout_does_not_duplicate_an_explicit_unstable_options_gate() {
        let file = this_file();
        let got = plan_for(&[&file, "-Z", "unstable-options", "--timeout=2m"]);
        assert_eq!(got.iter().filter(|a| *a == "unstable-options").count(), 1);
        assert!(got.windows(2).any(|w| w[0] == "--harness-timeout" && w[1] == "2m"));
        let got = plan_for(&[&file, "-Zunstable-options", "--timeout", "90"]);
        assert_eq!(got.iter().filter(|a| a.contains("unstable-options")).count(), 1);
    }

    #[test]
    fn a_malformed_timeout_is_a_usage_error() {
        let file = this_file();
        let err = translate(&args(&[&file, "--timeout", "5k"])).unwrap_err();
        assert_eq!(err.code, super::super::EXIT_USAGE);
        assert!(err.msg.contains("--timeout 5k"), "{}", err.msg);
        let err = translate(&args(&[&file, "--timeout", "abc"])).unwrap_err();
        assert!(err.msg.contains("30s"), "{}", err.msg);
    }

    #[test]
    fn list_maps_onto_the_engine_listing_shortcut() {
        let file = this_file();
        let plan = translate(&args(&[&file, "--list"])).unwrap();
        let got: Vec<String> = plan.args.iter().map(|a| a.to_string_lossy().into_owned()).collect();
        assert_eq!(got, vec![file, "--harnesses".to_string()]);
        assert!(!plan.needs_solver, "listing metadata must not require the solver");
    }

    #[test]
    fn solver_maps_onto_the_ay_selector() {
        let file = this_file();
        assert_eq!(
            plan_for(&[&file, "--solver", "AY"]),
            vec![file, "--smt-solver".to_string(), "ay".to_string()]
        );
    }

    #[test]
    fn a_cbmc_solver_name_is_rejected_by_name() {
        let file = this_file();
        let err = translate(&args(&[&file, "--solver", "cadical"])).unwrap_err();
        assert_eq!(err.code, super::super::EXIT_USAGE);
        assert!(err.msg.contains("--solver cadical"), "{}", err.msg);
        assert!(err.msg.contains("--solver ay"), "{}", err.msg);
    }

    #[test]
    fn unsupported_flags_fail_loudly_with_an_alternative() {
        let file = this_file();
        for (flag, _) in UNSUPPORTED {
            let err = translate(&args(&[&file, flag])).unwrap_err();
            assert_eq!(err.code, super::super::EXIT_USAGE, "{flag}");
            assert!(err.msg.contains(flag), "{flag}: {}", err.msg);
        }
    }

    #[test]
    fn unknown_flags_and_their_values_pass_through_in_order() {
        let file = this_file();
        assert_eq!(
            plan_for(&[&file, "--output-format", "terse", "--ay-chc", "-Z", "concrete-playback"]),
            vec![
                file,
                "--output-format".to_string(),
                "terse".to_string(),
                "--ay-chc".to_string(),
                "-Z".to_string(),
                "concrete-playback".to_string(),
            ]
        );
    }

    #[test]
    fn flags_may_come_before_the_file() {
        let file = this_file();
        assert_eq!(
            plan_for(&["--ay-chc", "--harness", "h", &file]),
            vec![file, "--ay-chc".to_string(), "--harness".to_string(), "h".to_string()]
        );
    }

    #[test]
    fn double_dash_passes_the_remainder_verbatim() {
        let file = this_file();
        assert_eq!(
            plan_for(&[&file, "--", "--cbmc-args", "--solver", "z3"]),
            vec![file, "--cbmc-args".to_string(), "--solver".to_string(), "z3".to_string(),]
        );
    }

    #[test]
    fn a_missing_input_is_a_usage_error_that_names_the_example_verb() {
        let err = translate(&args(&["--harness", "foo"])).unwrap_err();
        assert_eq!(err.code, super::super::EXIT_USAGE);
        assert!(err.msg.contains("trust-mc example"), "{}", err.msg);
    }

    #[test]
    fn a_nonexistent_input_names_the_file_and_the_way_out() {
        let err = translate(&args(&["definitely-not-here.rs"])).unwrap_err();
        assert_eq!(err.code, super::super::EXIT_USAGE);
        assert!(err.msg.contains("definitely-not-here.rs"), "{}", err.msg);
        assert!(err.msg.contains("trust-mc example"), "{}", err.msg);
    }

    #[test]
    fn a_directory_is_explained_not_rejected_as_a_missing_file() {
        let err = translate(&args(&[env!("CARGO_MANIFEST_DIR")])).unwrap_err();
        assert_eq!(err.code, super::super::EXIT_USAGE);
        assert!(err.msg.contains("is a directory"), "{}", err.msg);
        assert!(err.msg.contains("cargo trust-mc"), "{}", err.msg);
    }
}
