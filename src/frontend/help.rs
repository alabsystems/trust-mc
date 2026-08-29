// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `--help`, `help <command>`, and the per-command pages. Topic pages
//! (`help <topic>` / `explain <topic>`) live in [`super::topics`].

use std::process::ExitCode;

use super::{COMMANDS, ENGINE_SUBCOMMANDS, Fail, Front, VERSION, closest, topics};

pub(crate) fn usage_lines() -> String {
    "Usage:\n    trust-mc [OPTIONS] <FILE.rs>\n    trust-mc <COMMAND> [ARGS...]\n\n".to_string()
}

/// `trust-mc help [SUBJECT]` / `trust-mc --help` / `trust-mc <cmd> --help`.
pub(crate) fn command(subject: Option<&str>) -> Front<ExitCode> {
    match subject {
        None => {
            print!("{}", top_level());
            Ok(ExitCode::SUCCESS)
        }
        Some(name) => {
            if let Some(page) = for_command(name) {
                print!("{page}");
                return Ok(ExitCode::SUCCESS);
            }
            if let Some(page) = topics::render(name) {
                print!("{page}");
                return Ok(ExitCode::SUCCESS);
            }
            let mut msg = format!("error: no help for `{name}`\n");
            let candidates = COMMANDS
                .iter()
                .copied()
                .chain(ENGINE_SUBCOMMANDS.iter().copied())
                .chain(topics::names());
            if let Some(near) = closest(name, candidates) {
                msg.push_str(&format!("       did you mean `trust-mc help {near}`?\n"));
            }
            msg.push_str(&format!(
                "\nCommands: {}, {}\nTopics:   {}\n",
                COMMANDS.join(", "),
                ENGINE_SUBCOMMANDS.join(", "),
                topics::names().collect::<Vec<_>>().join(", ")
            ));
            Err(Fail::usage(msg))
        }
    }
}

/// The top-level help page. Everything here works with nothing installed.
pub(crate) fn top_level() -> String {
    format!(
        "trust-mc {VERSION} — a model checker for Rust

Proves the assertions in a Rust source file for every possible input, or names
the check that fails and where. Bounded proofs by default; unbounded ones with
--ay-chc. The solver is AY; the harness language is Kani's (#[kani::proof],
kani::any(), kani::assume()).

{usage}First run — no project, no configuration, no network:

    trust-mc example > demo.rs
    trust-mc demo.rs

Commands:
    verify <FILE.rs>     verify every #[kani::proof] harness in FILE (the
                         default when the first argument is a .rs file)
    list <FILE.rs>       list the harnesses in FILE (also: --list)
    example [NAME]       write a sample harness; `example --list` shows them
    explain [TOPIC]      how trust-mc works; `explain` alone lists the topics
    quickstart           a five-minute walkthrough of standalone use
    doctor               what verification needs and whether it is here
    flags [--all]        the engine's complete flag reference
    version [-v]         version; -v adds engine and solver provenance
    setup                install a published release bundle (~/.kani)
    help [CMD|TOPIC]     this page, a command's page, or an explain topic
    autoharness | playback | verify-std
                         engine subcommands, forwarded as-is (each has --help)

Verify options (the rest of the engine's flags pass through unchanged):
    --harness <NAME>     verify only harnesses matching NAME; repeatable
    --unwind <N>         loop bound; with --harness, that harness's bound
    --timeout <T>        per-harness solver budget, e.g. 30s, 2m, 1h
    --ay-chc             unbounded mode: prove loops by induction instead of
                         unrolling them (see `trust-mc explain chc`)
    -Z concrete-playback --concrete-playback print
                         when a harness fails, print the failing input as a
                         runnable #[test] — the fastest way to see WHICH
                         value broke it (`inplace` writes it into the source)
    --summary            after the run, a sorted verdict table: every failed
                         harness with its reason and file:line, then the
                         proved ones. Deterministic, so two runs diff cleanly
    --output-format <F>  regular (default) | terse | old
    --solver <NAME>      auto (default) | ay — the AY backend's selector
    -v, --verbose        show each stage and the engine command line
    -q, --quiet          print nothing but the exit code and requested artifacts
    -h, --help           this page (works with nothing installed)
    -V, --version        the version (works with nothing installed)
    --                   pass every remaining argument to the engine verbatim

For CI (the exit code is the contract; nothing else needs parsing):
    --sarif <FILE>       findings as SARIF, for code scanning — a failing
                         harness always leaves one, even when no single
                         property failed
    --proof-summary-json <FILE>
                         per-run counts as JSON
    --jobs <N>           verify N harnesses at once
    doctor --json        installation readiness as one object, if you would
                         rather gate on that than on a missing binary

Exit codes:
    0  verified (or a listing / help / example / doctor-ready run)
    1  a harness failed or was inconclusive, or the engine hit an error
    2  usage error                3  engine, sysroot or solver not installed

Learn more:  trust-mc explain        trust-mc quickstart        trust-mc flags
To verify a Cargo package rather than a single file, use `cargo trust-mc`.
",
        usage = usage_lines()
    )
}

/// The per-command page, if `name` is a front-door command.
pub(crate) fn for_command(name: &str) -> Option<String> {
    let page = match name {
        "verify" => {
            "trust-mc verify [OPTIONS] <FILE.rs>
trust-mc [OPTIONS] <FILE.rs>

Compile FILE as one crate with the `kani` crate in scope, collect every
#[kani::proof] (and #[kani::proof_for_contract]) harness it contains, encode
each one, and hand the obligations to the AY solver. One block of output and
one VERIFICATION:- verdict per harness; exit 0 only if all of them verify.

Options trust-mc translates (everything else goes to the engine unchanged):
    --harness <NAME>     only harnesses matching NAME (substring; --exact for
                         the full path); repeatable
    --unwind <N>         loop bound: the crate-wide default (engine flag
                         --default-unwind), or this harness's bound when
                         --harness is present (engine flag --unwind)
    --timeout <T>        per-harness solver budget: 30s, 2m, 1h, or seconds
                         (engine: -Z unstable-options --harness-timeout T)
    --list               list harnesses instead of verifying (no solver needed)
    --solver <NAME>      auto | ay (engine flag --smt-solver)
    --summary            front-door only: print a sorted verdict table after
                         the run. Stripped before the engine, which has never
                         heard of it
    -v/--verbose, -q/--quiet, --debug

Engine flags you will reach for (see `trust-mc flags` for all of them):
    --ay-chc                      unbounded proofs (explain chc)
    --output-format terse         verdicts only, no per-check block
    --sarif <FILE>                SARIF 2.1.0 report of failed checks
    --proof-summary-json <FILE>   per-harness JSON summary
    --tests                       build with --test; #[test] fns are harnesses
    -Z <feature>                  enable an unstable feature (concrete-playback,
                                  source-coverage, stubbing, function-contracts,
                                  loop-contracts, autoharness, quantifiers, ...)
    --fail-fast, --no-default-checks, --fail-on-unvalidated-success, ...

Flags trust-mc cannot honor (CBMC-era) are rejected by name with the
alternative: --cbmc-args, --solver <cbmc solver>, --gen-c, --print-llbc,
--synthesize-loop-contracts, --no-slice-formula, --run-sanity-checks, ...

Examples:
    trust-mc demo.rs
    trust-mc --harness parse_header --unwind 8 src/parser.rs
    trust-mc --timeout 60s --ay-chc queue.rs
    trust-mc --output-format terse -q ci.rs ; echo $?
"
        }
        "list" => {
            "trust-mc list <FILE.rs> [--format pretty|markdown|json]
trust-mc --list <FILE.rs>

Compile FILE and print the harnesses and contracts it contains without
solving anything; the solver need not be installed. `--format markdown` and
`--format json` write trust_mc-list.md / trust_mc-list.json in the current
directory. `trust-mc list --help` shows the engine's own options.
"
        }
        "example" => {
            return Some(format!(
                "trust-mc example [NAME] [PATH] [--list] [--force]

Write a sample harness file to stdout (or to PATH). Every example is verified
before it ships and says at the top what to expect when it runs.

{}",
                super::examples::catalog()
            ));
        }
        "explain" => {
            return Some(format!(
                "trust-mc explain [TOPIC]
trust-mc help <TOPIC>

How trust-mc works, from inside the tool. With no TOPIC, an overview of the
pipeline and the topic list.

{}",
                topics::list_lines()
            ));
        }
        "quickstart" => {
            "trust-mc quickstart

A five-minute walkthrough: check the installation, run a harness, see a
failure, write your own, and the everyday flags. Same as
`trust-mc explain quickstart`.
"
        }
        "doctor" => {
            "trust-mc doctor [--verbose] [--json]

Report what verification needs and whether it is present:

  * the engine (trust-mc-driver), searched in $TRUST_MC_SYSROOT, the nearest
    target/trust-mc of a checkout, and ${KANI_HOME:-~/.kani}/kani-<VERSION>
  * trust-mc-compiler beside it, and that it can load its rustc
  * the library sysroot: lib/, no_core/lib, playback/lib
  * the engine's version and its linked-AY provenance (--version-authority)
  * the `ay` solver on PATH, its version, and whether its commit matches
    the AY the engine links

Exit 0 when a verification can run, 3 otherwise — with the exact command that
fixes each missing piece. --verbose prints the probes it runs.

--json reports the same run as one JSON object for CI: ready, exit_code,
version, target, engine, engine_source, solver, warnings, fixes. The exit code
is unchanged, and is still the thing worth gating on.
"
        }
        "flags" => {
            "trust-mc flags [--all]

Print the verification engine's own flag reference (`trust-mc-driver -h`);
--all includes the less common flags (`--help`). Needs the engine to be
installed; `trust-mc explain flags` summarizes the families without it.
"
        }
        "version" => {
            "trust-mc version [--verbose]
trust-mc --version

Print the version. --verbose adds the engine path and version, the AY
revision it links (and whether that is the pinned one), and the `ay` solver
binary on PATH with its build stamp.
"
        }
        "setup" => {
            "trust-mc setup [--use-local-bundle <FILE>] [--use-local-toolchain <DIR>]

Install a published release bundle (engine + compiler + library sysroot) into
${KANI_HOME:-~/.kani}/kani-<VERSION> and the Rust toolchain it was built
with. Needs curl, tar and rustup. Use --use-local-bundle to install a bundle
you built with `cargo bundle`. A local checkout does not need setup:
`cargo run --release -p build-trust-mc -- build-dev --release` builds an
engine that trust-mc finds by itself.
"
        }
        "help" => {
            "trust-mc help [COMMAND|TOPIC]

With no argument, the top-level page. With a command name, that command's
page; with a topic name, the `explain` page for it.
"
        }
        _ => return None,
    };
    Some(page.to_string())
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "a panicking assertion is the point in tests")]
mod tests {
    use super::*;

    #[test]
    fn help_and_version_need_no_filesystem() {
        let top = top_level();
        assert!(top.contains("trust-mc example > demo.rs"));
        assert!(top.contains("Exit codes"));
        assert!(top.contains("--ay-chc"));
        assert!(top.contains("--timeout"));
    }

    #[test]
    fn the_top_level_page_fits_in_eighty_columns() {
        for line in top_level().lines() {
            assert!(line.len() <= 80, "overlong help line ({}): {line}", line.len());
        }
    }

    #[test]
    fn every_command_page_fits_in_eighty_columns() {
        for command in COMMANDS {
            for line in for_command(command).unwrap().lines() {
                assert!(line.len() <= 80, "`{command}`: overlong line ({}): {line}", line.len());
            }
        }
    }

    #[test]
    fn help_for_an_unknown_subject_suggests_and_lists() {
        let err = command(Some("explian")).unwrap_err();
        assert_eq!(err.code, super::super::EXIT_USAGE);
        assert!(err.msg.contains("did you mean `trust-mc help explain`"), "{}", err.msg);
        assert!(err.msg.contains("Topics:"), "{}", err.msg);
    }

    #[test]
    fn help_reaches_topics_as_well_as_commands() {
        assert!(for_command("bmc").is_none());
        assert!(topics::render("bmc").is_some());
        assert!(command(Some("bmc")).is_ok());
        assert!(command(Some("doctor")).is_ok());
    }
}
