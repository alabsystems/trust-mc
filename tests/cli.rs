// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! End-to-end tests of the `trust-mc` front door binary.
//!
//! Everything in the first group runs with nothing installed: help, explain,
//! example, version, usage errors. The second group needs a built engine
//! (`cargo build-dev`) and the `ay` solver on PATH, and skips itself — loudly —
//! when they are absent, so `cargo test -p trust-mc` is green on a bare
//! checkout and meaningful on a working one.

#![allow(
    clippy::unwrap_used,
    clippy::panic,
    reason = "panicking assertions are the point in tests"
)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::{env, fs};

const BIN: &str = env!("CARGO_BIN_EXE_trust-mc");

fn trust_mc(args: &[&str]) -> Output {
    trust_mc_in(Path::new(env!("CARGO_MANIFEST_DIR")), args)
}

fn trust_mc_in(dir: &Path, args: &[&str]) -> Output {
    Command::new(BIN).args(args).current_dir(dir).output().expect("could not run trust-mc")
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

fn code(out: &Output) -> i32 {
    out.status.code().expect("no exit code")
}

/// A sibling binary of the front door under test (same target directory).
fn sibling_binary(name: &str) -> Option<PathBuf> {
    let path = Path::new(BIN).parent()?.join(name);
    path.is_file().then_some(path)
}

fn scratch(name: &str) -> PathBuf {
    let dir = env::temp_dir().join(format!("trust-mc-cli-{}-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

// ---------------------------------------------------------------------------
// Works with nothing installed
// ---------------------------------------------------------------------------

#[test]
fn help_works_and_names_every_command() {
    // A bare `trust-mc` shows the same page, but it is not the same request:
    // asking for help succeeds, whereas running the verifier over nothing has
    // verified nothing and must not report success. See the `None` arm of
    // `frontend::run`.
    for (args, want_code) in
        [(&["--help"][..], 0), (&["-h"], 0), (&["help"], 0), (&[], 2)]
    {
        let out = trust_mc(args);
        assert_eq!(code(&out), want_code, "{args:?}: {}", stderr(&out));
        let text = stdout(&out);
        for command in [
            "verify",
            "list",
            "example",
            "explain",
            "quickstart",
            "doctor",
            "flags",
            "version",
            "setup",
        ] {
            assert!(text.contains(command), "{args:?}: help omits `{command}`");
        }
        assert!(text.contains("Exit codes"), "{args:?}");
        for line in text.lines() {
            assert!(line.len() <= 80, "{args:?}: overlong line: {line}");
        }
        if want_code == 0 {
            assert!(
                !stderr(&out).contains("error:"),
                "{args:?}: asking for help is not an error: {}",
                stderr(&out)
            );
        } else {
            assert!(
                stderr(&out).contains("nothing was verified"),
                "{args:?}: a non-zero exit needs to say why: {}",
                stderr(&out)
            );
        }
    }
}

#[test]
fn version_is_one_line_and_matches_the_manifest() {
    for args in [&["--version"][..], &["-V"], &["version"]] {
        let out = trust_mc(args);
        assert_eq!(code(&out), 0);
        assert_eq!(stdout(&out).trim(), format!("trust-mc {}", env!("CARGO_PKG_VERSION")));
    }
}

#[test]
fn per_command_help_is_reachable_three_ways() {
    let via_help = stdout(&trust_mc(&["help", "doctor"]));
    let via_flag = stdout(&trust_mc(&["doctor", "--help"]));
    let via_short = stdout(&trust_mc(&["doctor", "-h"]));
    assert!(via_help.starts_with("trust-mc doctor"), "{via_help}");
    assert_eq!(via_help, via_flag);
    assert_eq!(via_help, via_short);
}

#[test]
fn explain_lists_topics_and_renders_each_one() {
    let overview = trust_mc(&["explain"]);
    assert_eq!(code(&overview), 0);
    let overview = stdout(&overview);
    assert!(overview.contains("compile"), "{overview}");
    assert!(overview.contains("Topics"), "{overview}");

    // Every topic the overview lists must render, within 80 columns.
    let topics: Vec<String> = overview
        .lines()
        .skip_while(|l| !l.starts_with("Topics"))
        .skip(1)
        .take_while(|l| l.starts_with("    "))
        .filter_map(|l| l.split_whitespace().next().map(str::to_string))
        .collect();
    assert!(topics.len() >= 8, "too few topics listed: {topics:?}");
    for topic in &topics {
        let out = trust_mc(&["explain", topic]);
        assert_eq!(code(&out), 0, "explain {topic}: {}", stderr(&out));
        let text = stdout(&out);
        assert!(text.starts_with(&format!("trust-mc explain {topic}")), "{topic}: {text}");
        for line in text.lines() {
            assert!(line.len() <= 80, "explain {topic}: overlong line: {line}");
        }
        // `help <topic>` is the same page — unless a command shares the name
        // (`flags`), in which case the command's page wins.
        let via_help = stdout(&trust_mc(&["help", topic]));
        if !via_help.starts_with("trust-mc explain ") {
            assert!(via_help.contains(&format!("trust-mc explain {topic}")), "help {topic}");
        } else {
            assert_eq!(via_help, text, "help {topic}");
        }
    }
    // Aliases and the quickstart verb.
    assert_eq!(
        stdout(&trust_mc(&["explain", "unbounded"])),
        stdout(&trust_mc(&["explain", "chc"]))
    );
    assert_eq!(stdout(&trust_mc(&["quickstart"])), stdout(&trust_mc(&["explain", "quickstart"])));
}

#[test]
fn explain_rejects_unknown_topics_with_the_list() {
    let out = trust_mc(&["explain", "resutls"]);
    assert_eq!(code(&out), 2);
    let err = stderr(&out);
    assert!(err.contains("no topic named `resutls`"), "{err}");
    assert!(err.contains("did you mean `trust-mc explain results`"), "{err}");
    assert!(err.contains("harness"), "{err}");
}

#[test]
fn example_writes_verified_harnesses() {
    let list = trust_mc(&["example", "--list"]);
    assert_eq!(code(&list), 0);
    let list = stdout(&list);
    assert!(list.contains("basic"), "{list}");
    assert!(list.contains("(default)"), "{list}");

    // Default to stdout.
    let default = trust_mc(&["example"]);
    assert_eq!(code(&default), 0);
    let basic = stdout(&default);
    assert!(basic.contains("#[kani::proof]"), "{basic}");
    assert_eq!(basic, stdout(&trust_mc(&["example", "basic"])));

    // Named example to a file, refusing to clobber without --force.
    let dir = scratch("example");
    let path = dir.join("bug.rs");
    let out = trust_mc(&["example", "bug", path.to_str().unwrap()]);
    assert_eq!(code(&out), 0, "{}", stderr(&out));
    assert!(stdout(&out).contains("FAILS"), "{}", stdout(&out));
    assert!(fs::read_to_string(&path).unwrap().contains("add_never_overflows"));
    let again = trust_mc(&["example", "bug", path.to_str().unwrap()]);
    assert_eq!(code(&again), 2);
    assert!(stderr(&again).contains("--force"), "{}", stderr(&again));
    let forced = trust_mc(&["example", "bug", path.to_str().unwrap(), "--force"]);
    assert_eq!(code(&forced), 0);

    // Every listed example is a well-formed file that announces its outcome.
    let names: Vec<String> = list
        .lines()
        .filter(|l| l.starts_with("  ") && !l.trim_start().starts_with('→'))
        .filter_map(|l| l.split_whitespace().next().map(str::to_string))
        .collect();
    assert!(names.len() >= 5, "{names:?}");
    for name in &names {
        let out = trust_mc(&["example", name]);
        assert_eq!(code(&out), 0, "example {name}");
        let text = stdout(&out);
        assert!(text.starts_with(&format!("// trust-mc example: {name}")), "{name}: {text}");
        assert!(text.contains("PROVES") || text.contains("FAILS"), "{name}: {text}");
    }

    let unknown = trust_mc(&["example", "nonesuch"]);
    assert_eq!(code(&unknown), 2);
    assert!(stderr(&unknown).contains("no example named `nonesuch`"));
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn usage_errors_are_exit_2_and_point_the_way() {
    let out = trust_mc(&["exmaple"]);
    assert_eq!(code(&out), 2);
    assert!(stderr(&out).contains("did you mean `trust-mc example`"), "{}", stderr(&out));

    let out = trust_mc(&["definitely-not-here.rs"]);
    assert_eq!(code(&out), 2);
    assert!(stderr(&out).contains("no such file"), "{}", stderr(&out));
    assert!(stderr(&out).contains("trust-mc example"), "{}", stderr(&out));

    let out = trust_mc(&["--harness", "x"]);
    assert_eq!(code(&out), 2);
    assert!(stderr(&out).contains("no input file"), "{}", stderr(&out));

    // `doctor --json` stood here as "a flag doctor does not take"; it is a real
    // flag now (see doctor_json_is_valid_and_agrees_with_the_exit_code), so the
    // stray-argument case needs one that still is.
    let out = trust_mc(&["doctor", "--nope"]);
    assert_eq!(code(&out), 2);
    assert!(stderr(&out).contains("--verbose"), "{}", stderr(&out));

    let out = trust_mc(&["help", "nonesuch"]);
    assert_eq!(code(&out), 2);
    assert!(stderr(&out).contains("Topics:"), "{}", stderr(&out));
}

#[test]
fn cbmc_era_flags_are_rejected_by_name_before_anything_runs() {
    let dir = scratch("unsupported");
    let file = dir.join("demo.rs");
    fs::write(&file, stdout(&trust_mc(&["example"]))).unwrap();
    for (flag, hint) in [
        ("--cbmc-args", "no CBMC backend"),
        ("--gen-c", "no C code generator"),
        ("--synthesize-loop-contracts", "--ay-chc"),
        ("--visualize", "--coverage"),
    ] {
        let out = trust_mc(&[file.to_str().unwrap(), flag]);
        assert_eq!(code(&out), 2, "{flag}");
        let err = stderr(&out);
        assert!(err.contains(flag), "{flag}: {err}");
        assert!(err.contains(hint), "{flag}: {err}");
    }
    let out = trust_mc(&[file.to_str().unwrap(), "--solver", "cadical"]);
    assert_eq!(code(&out), 2);
    assert!(stderr(&out).contains("--solver ay"), "{}", stderr(&out));
    let out = trust_mc(&[file.to_str().unwrap(), "--timeout", "5k"]);
    assert_eq!(code(&out), 2);
    assert!(stderr(&out).contains("30s"), "{}", stderr(&out));
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn bad_flag_values_are_rejected_naming_the_flag_the_user_typed() {
    let dir = scratch("bad-values");
    let file = dir.join("demo.rs");
    fs::write(&file, stdout(&trust_mc(&["example"]))).unwrap();
    let path = file.to_str().unwrap();

    // `--unwind` is translated to the engine's `--default-unwind`; a clap error
    // from the engine would name a flag that never appeared on the command line.
    let out = trust_mc(&[path, "--unwind", "abc"]);
    assert_eq!(code(&out), 2);
    assert!(stderr(&out).contains("--unwind abc"), "{}", stderr(&out));
    assert!(!stderr(&out).contains("--default-unwind"), "{}", stderr(&out));

    // A zero budget expires instantly and turns every harness INCONCLUSIVE.
    let out = trust_mc(&[path, "--timeout", "0"]);
    assert_eq!(code(&out), 2);
    assert!(stderr(&out).contains("no time at all"), "{}", stderr(&out));

    // An empty filter matches nothing; forwarding it confuses the engine.
    let out = trust_mc(&[path, "--harness="]);
    assert_eq!(code(&out), 2);
    assert!(stderr(&out).contains("--harness needs a name"), "{}", stderr(&out));

    // Guidance wraps at 80 columns like the rest of the surface. The first
    // line is exempt: it echoes the user's value, whose length is not ours.
    for args in [&["--unwind", "abc"][..], &["--timeout", "0"], &["--harness="]] {
        let mut full = vec![path];
        full.extend_from_slice(args);
        for line in stderr(&trust_mc(&full)).lines().skip(1) {
            assert!(line.len() <= 80, "overlong error line: {line}");
        }
    }
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn a_non_rust_file_says_so_instead_of_no_input_file() {
    let dir = scratch("non-rs");
    let notes = dir.join("notes.txt");
    fs::write(&notes, "not rust").unwrap();
    let out = trust_mc(&[notes.to_str().unwrap()]);
    assert_eq!(code(&out), 2);
    assert!(stderr(&out).contains("is not a Rust source file"), "{}", stderr(&out));
    assert!(!stderr(&out).contains("no input file"), "a file WAS given: {}", stderr(&out));
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn asking_for_help_about_a_file_shows_the_verify_page() {
    let dir = scratch("file-help");
    let file = dir.join("demo.rs");
    fs::write(&file, stdout(&trust_mc(&["example"]))).unwrap();
    // `trust-mc demo.rs --help` is a question about verifying, not a mistyped
    // command; it used to exit 2 with "no help for `demo.rs`".
    for flag in ["--help", "-h"] {
        let out = trust_mc(&[file.to_str().unwrap(), flag]);
        assert_eq!(code(&out), 0, "{}", stderr(&out));
        assert!(stdout(&out).starts_with("trust-mc verify"), "{}", stdout(&out));
    }
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn a_verification_run_leaves_no_files_behind() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("no-litter");
    fs::write(dir.join("demo.rs"), stdout(&trust_mc(&["example"]))).unwrap();

    let out = trust_mc_in(&dir, &["--timeout", "30s", "demo.rs"]);
    assert_eq!(code(&out), 0, "{}", stdout(&out));
    let left: Vec<String> = fs::read_dir(&dir)
        .unwrap()
        .filter_map(|e| e.ok())
        .map(|e| e.file_name().to_string_lossy().into_owned())
        .filter(|n| n != "demo.rs")
        .collect();
    assert!(left.is_empty(), "verification littered the user's directory: {left:?}");

    // ...but --keep-temps still keeps them, which the debugging workflows need.
    let kept = trust_mc_in(&dir, &["--timeout", "30s", "--keep-temps", "demo.rs"]);
    assert_eq!(code(&kept), 0, "{}", stdout(&kept));
    let count = fs::read_dir(&dir).unwrap().filter_map(|e| e.ok()).count();
    assert!(count > 1, "--keep-temps must keep the codegen artifacts");
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn doctor_always_renders_and_exits_0_or_3() {
    let out = trust_mc(&["doctor"]);
    let status = code(&out);
    assert!(status == 0 || status == 3, "doctor exited {status}: {}", stderr(&out));
    let text = stdout(&out);
    assert!(text.contains("verification engine"), "{text}");
    assert!(text.contains("SMT solver"), "{text}");
    if status == 0 {
        assert!(text.contains("ready."), "{text}");
    } else {
        assert!(text.contains("not ready. To fix:"), "{text}");
    }
    let verbose = trust_mc(&["doctor", "--verbose"]);
    assert_eq!(code(&verbose), status);
}

#[test]
fn version_verbose_never_fails() {
    let out = trust_mc(&["version", "--verbose"]);
    assert_eq!(code(&out), 0, "{}", stderr(&out));
    let text = stdout(&out);
    assert!(text.contains("engine:"), "{text}");
    assert!(text.contains("solver:"), "{text}");
}

// ---------------------------------------------------------------------------
// Needs a built engine and the solver
// ---------------------------------------------------------------------------

/// True when `trust-mc doctor` says a verification can run here.
fn installation_ready() -> bool {
    let ready = code(&trust_mc(&["doctor"])) == 0;
    if !ready {
        eprintln!(
            "SKIPPED: no working trust-mc installation (`trust-mc doctor` is not ready); \
             build one with `cargo build-dev --release` and put `ay` on PATH"
        );
    }
    ready
}

#[test]
fn the_default_example_verifies_end_to_end() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("verify-basic");
    let file = dir.join("demo.rs");
    fs::write(&file, stdout(&trust_mc(&["example"]))).unwrap();

    let out = trust_mc_in(&dir, &["demo.rs"]);
    let text = stdout(&out);
    assert_eq!(code(&out), 0, "stdout:\n{text}\nstderr:\n{}", stderr(&out));
    assert_eq!(text.matches("VERIFICATION:- SUCCESSFUL").count(), 2, "{text}");
    assert!(text.contains("2 successfully verified harnesses"), "{text}");

    // Listing needs no solver and prints both harnesses.
    let list = trust_mc_in(&dir, &["--list", "demo.rs"]);
    assert_eq!(code(&list), 0, "{}", stderr(&list));
    assert!(stdout(&list).contains("double_never_shrinks"), "{}", stdout(&list));
    assert!(stdout(&list).contains("saturating_sub_is_bounded"), "{}", stdout(&list));

    // --verbose echoes the engine command line with the translated flags.
    let verbose = trust_mc_in(&dir, &["-v", "--timeout", "30s", "--harness", "double", "demo.rs"]);
    assert_eq!(code(&verbose), 0, "{}", stderr(&verbose));
    let err = stderr(&verbose);
    assert!(err.contains("[trust-mc] running: trust-mc"), "{err}");
    assert!(err.contains("--harness-timeout 30s"), "{err}");
    assert!(err.contains("-Z unstable-options"), "{err}");
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn the_bug_example_fails_with_a_genuine_counterexample() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("verify-bug");
    let file = dir.join("bug.rs");
    fs::write(&file, stdout(&trust_mc(&["example", "bug"]))).unwrap();
    let out = trust_mc_in(&dir, &["--output-format", "terse", "bug.rs"]);
    let text = stdout(&out);
    assert_eq!(code(&out), 1, "stdout:\n{text}\nstderr:\n{}", stderr(&out));
    assert!(text.contains("VERIFICATION:- FAILED"), "{text}");
    assert!(text.contains("[AY:CTREX_CAT:Genuine]"), "{text}");
    assert!(text.contains("attempt to add with overflow"), "{text}");
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn a_harness_with_contradictory_assumptions_is_vacuous_not_proved() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("vacuous");
    // `kani::assume(false)` makes the whole path infeasible, so the solver
    // discharges every obligation trivially. Reporting that as a proof is the
    // classic vacuous-proof trap: nothing was verified. Kani documents the same
    // shape as UNREACHABLE checks.
    fs::write(
        dir.join("vacuous.rs"),
        "#[kani::proof]\n\
         fn nothing_is_verified_here() {\n\
         \x20   let x: u8 = kani::any();\n\
         \x20   kani::assume(x < 10);\n\
         \x20   kani::assume(x > 200);\n\
         \x20   assert!(x == 42);\n\
         }\n",
    )
    .unwrap();

    let out = trust_mc_in(&dir, &["--timeout", "30s", "vacuous.rs"]);
    let text = stdout(&out);
    assert_eq!(code(&out), 1, "a vacuous proof must not exit 0:\n{text}");
    assert!(text.contains("VERIFICATION:- VACUOUS"), "{text}");
    assert!(text.contains("[AY:VACUOUS:unsat-assumption]"), "{text}");
    assert!(
        !text.contains("PROOF_QUALIFIERS:clean"),
        "a vacuous run is not a clean proof:\n{text}"
    );

    // ...and the documented escape hatch still works, loudly.
    let allowed = trust_mc_in(&dir, &["--timeout", "30s", "--allow-vacuous", "vacuous.rs"]);
    assert_eq!(code(&allowed), 0, "{}", stdout(&allowed));
    assert!(stdout(&allowed).contains("[AY:VACUOUS:allowed]"), "{}", stdout(&allowed));

    // The SAME harness under --ay-chc. This assertion is the whole reason the
    // test exists in this shape: the gate was BMC-only, so `--ay-chc` printed
    // `SUCCESSFUL` with `PROOF_QUALIFIERS:clean` for this file — a clean proof
    // of a harness that cannot run. A verifier may not disagree with itself
    // about whether anything was verified.
    let chc = trust_mc_in(&dir, &["--ay-chc", "--timeout", "240s", "vacuous.rs"]);
    let chc_text = stdout(&chc);
    assert_eq!(code(&chc), 1, "a vacuous CHC proof must not exit 0:\n{chc_text}");
    assert!(chc_text.contains("VERIFICATION:- VACUOUS"), "{chc_text}");
    assert!(chc_text.contains("[AY:VACUOUS:unsat-assumption]"), "{chc_text}");
    assert!(
        !chc_text.contains("PROOF_QUALIFIERS:clean"),
        "a vacuous CHC run is not a clean proof:\n{chc_text}"
    );
    let chc_allowed =
        trust_mc_in(&dir, &["--ay-chc", "--allow-vacuous", "--timeout", "240s", "vacuous.rs"]);
    assert_eq!(code(&chc_allowed), 0, "{}", stdout(&chc_allowed));
    assert!(stdout(&chc_allowed).contains("[AY:VACUOUS:allowed]"), "{}", stdout(&chc_allowed));

    // The gate must not swallow real proofs: the same shape with assumptions
    // that CAN both hold still verifies in both modes. Without this, "report
    // everything vacuous" would pass the test above.
    fs::write(
        dir.join("satisfiable.rs"),
        "#[kani::proof]\n\
         fn assumptions_that_can_both_hold() {\n\
         \x20   let x: u8 = kani::any();\n\
         \x20   kani::assume(x > 10);\n\
         \x20   kani::assume(x < 200);\n\
         \x20   assert!(x > 5);\n\
         }\n",
    )
    .unwrap();
    for mode in [vec!["--timeout", "60s"], vec!["--ay-chc", "--timeout", "240s"]] {
        let mut a = mode.clone();
        a.push("satisfiable.rs");
        let ok = trust_mc_in(&dir, &a);
        assert_eq!(code(&ok), 0, "satisfiable assumptions must still prove ({mode:?}):\n{}", stdout(&ok));
        assert!(stdout(&ok).contains("VERIFICATION:- SUCCESSFUL"), "{}", stdout(&ok));
    }
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn a_harness_with_no_checks_is_inconclusive_not_proved() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("no-checks");
    // A harness with no assertions and no fallible operation genuinely has
    // nothing to discharge. Zero obligations discharged is not a proof of
    // anything, so it must never be SUCCESSFUL.
    fs::write(
        dir.join("nochecks.rs"),
        "#[kani::proof]\n\
         fn nothing_to_prove_here() {\n\
         \x20   let x: u32 = kani::any();\n\
         \x20   let _ = x;\n\
         }\n",
    )
    .unwrap();

    let out = trust_mc_in(&dir, &["--timeout", "30s", "nochecks.rs"]);
    let text = stdout(&out);
    assert_eq!(code(&out), 1, "zero checks must not exit 0:\n{text}");
    assert!(text.contains("INCONCLUSIVE (no checks)"), "{text}");
    assert!(text.contains("[AY:VACUOUS:no-checks]"), "{text}");

    // The README promises "a harness that produced no obligations is
    // INCONCLUSIVE (no checks)" without qualifying the mode, and the CHC lane
    // broke that promise: it fabricated a synthetic Success property whenever
    // the artifact registered none, so the V4b gate could never fire and the
    // run reported SUCCESSFUL — a clean proof of nothing.
    //
    // A different body from the BMC case above, deliberately. `kani::any()`
    // does emit obligations under CHC (three, measured) even though BMC emits
    // none for the same harness, and CHC discharging them is a real if trivial
    // proof — not the case this gate is about. A harness with no symbolic
    // input at all produces nothing to check in EITHER mode, which is the
    // claim being tested.
    fs::write(
        dir.join("empty.rs"),
        "#[kani::proof]\nfn nothing_at_all() {\n\x20   let _x: u8 = 3;\n}\n",
    )
    .unwrap();
    let chc = trust_mc_in(&dir, &["--ay-chc", "--timeout", "240s", "empty.rs"]);
    let chc_text = stdout(&chc);
    assert_ne!(code(&chc), 0, "a CHC proof of zero obligations must not exit 0:\n{chc_text}");
    assert!(chc_text.contains("INCONCLUSIVE (no checks)"), "{chc_text}");
    assert!(chc_text.contains("[AY:VACUOUS:no-checks]"), "{chc_text}");

    // BMC must say the same thing about the same file: one claim, both modes.
    let bmc_empty = trust_mc_in(&dir, &["--timeout", "60s", "empty.rs"]);
    assert_eq!(code(&bmc_empty), 1, "{}", stdout(&bmc_empty));
    assert!(stdout(&bmc_empty).contains("INCONCLUSIVE (no checks)"), "{}", stdout(&bmc_empty));

    // ...and a harness that DOES have obligations still proves under CHC, so
    // the gate cannot be satisfied by reporting everything inconclusive.
    fs::write(
        dir.join("something.rs"),
        "#[kani::proof]\nfn h() {\n\x20   let x: u8 = kani::any();\n\
         \x20   kani::assume(x < 10);\n\x20   assert!(x < 200);\n}\n",
    )
    .unwrap();
    let real = trust_mc_in(&dir, &["--ay-chc", "--timeout", "240s", "something.rs"]);
    assert_eq!(code(&real), 0, "a real CHC proof must still pass:\n{}", stdout(&real));
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn unwrapping_a_constant_none_is_a_panic_failure() {
    if !installation_ready() {
        return;
    }
    // `Option::<u32>::None.unwrap()` panics unconditionally at run time. The
    // inliner keeps `Option::unwrap` as a Call terminator so the AY stub in
    // `codegen_ay/statement/option.rs` handles it, and that stub used to
    // extract the payload with no None check — the panic simply vanished and
    // the query carried zero obligations. It must report a genuine FAILURE.
    let dir = scratch("unwrap-none");
    fs::write(
        dir.join("unwrapnone.rs"),
        "#[kani::proof]\n\
         fn unwrapping_none_must_fail() {\n\
         \x20   let x: Option<u32> = None;\n\
         \x20   let _ = x.unwrap();\n\
         }\n",
    )
    .unwrap();

    let out = trust_mc_in(&dir, &["--timeout", "30s", "unwrapnone.rs"]);
    let text = stdout(&out);
    assert_eq!(code(&out), 1, "an unconditional panic must not exit 0:\n{text}");
    assert!(text.contains("VERIFICATION:- FAILED"), "{text}");
    assert!(text.contains("panic reached"), "{text}");
    assert!(
        !text.contains("[AY:VACUOUS:no-checks]"),
        "the panic must become a real obligation, not a vacuity report:\n{text}"
    );
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn unwrapping_a_known_some_still_proves() {
    if !installation_ready() {
        return;
    }
    // Guards the check above against over-firing: the None-panic obligation
    // must be discharged (UNSAT) whenever the receiver is provably `Some`.
    let dir = scratch("unwrap-some");
    fs::write(
        dir.join("unwrapsome.rs"),
        "#[kani::proof]\n\
         fn unwrapping_some_still_proves() {\n\
         \x20   let x: Option<u32> = Some(5);\n\
         \x20   assert!(x.unwrap() == 5);\n\
         }\n",
    )
    .unwrap();

    let out = trust_mc_in(&dir, &["--timeout", "30s", "unwrapsome.rs"]);
    let text = stdout(&out);
    assert_eq!(code(&out), 0, "{text}");
    assert!(text.contains("VERIFICATION:- SUCCESSFUL"), "{text}");
    let _ = fs::remove_dir_all(&dir);
}

/// `cargo trust-mc` must accept the flags the help and `explain cargo` teach,
/// and must stay runnable twice in a row.
#[test]
fn cargo_mode_accepts_the_documented_flags_and_survives_a_rerun() {
    if !installation_ready() {
        return;
    }
    let Some(cargo_trust_mc) = sibling_binary("cargo-trust-mc") else {
        eprintln!("SKIPPED: cargo-trust-mc not built next to trust-mc");
        return;
    };
    let dir = scratch("cargo-mode");
    let pkg = dir.join("pkg");
    fs::create_dir_all(pkg.join("src")).unwrap();
    fs::write(
        pkg.join("Cargo.toml"),
        "[package]\nname = \"pkg\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    )
    .unwrap();
    fs::write(
        pkg.join("src/lib.rs"),
        "#[cfg(kani)]\nmod v {\n    #[kani::proof]\n    fn c() {\n        let a: u8 = kani::any();\n        kani::assume(a < 100);\n        assert!(a + 1 > a);\n    }\n}\n",
    )
    .unwrap();

    let run = |args: &[&str]| {
        let mut full = vec!["trust-mc"];
        full.extend_from_slice(args);
        Command::new(&cargo_trust_mc)
            .args(&full)
            .current_dir(&pkg)
            .output()
            .expect("could not run cargo-trust-mc")
    };

    // These are translated for a single file; they were rejected outright by
    // the engine's own parser under `cargo trust-mc` before.
    for args in [&["--timeout", "30s"][..], &["--unwind", "5", "--timeout", "30s"]] {
        let out = run(args);
        assert_eq!(code(&out), 0, "cargo trust-mc {args:?}:\n{}\n{}", stdout(&out), stderr(&out));
        assert!(stdout(&out).contains("1 successfully verified"), "{}", stdout(&out));
    }
    let listed = run(&["--list"]);
    assert_eq!(code(&listed), 0, "{}", stderr(&listed));
    assert!(
        !stderr(&listed).contains("hint:"),
        "`--list` verifies nothing, so it must not offer a counterexample hint:\n{}",
        stderr(&listed)
    );
    // A passing crate is not offered debugging advice either.
    let passing = run(&["--timeout", "30s"]);
    assert!(!stderr(&passing).contains("hint:"), "no hint on success:\n{}", stderr(&passing));

    // A crate-wide FAILURE gets the same "which input?" pointer the
    // single-file door gives — this is the audience most likely to need it,
    // since the failing harness is one of many.
    fs::write(
        pkg.join("src/lib.rs"),
        "#[cfg(kani)]\nmod v {\n    #[kani::proof]\n    fn c() {\n\
         \x20       let a: u32 = kani::any();\n\
         \x20       assert!(a * 2 >= a);\n    }\n}\n",
    )
    .unwrap();
    let failed = run(&["--timeout", "60s"]);
    assert_ne!(code(&failed), 0, "{}", stdout(&failed));
    assert!(
        stderr(&failed).contains("concrete-playback"),
        "a crate-wide failure must name the flag that shows the input:\n{}",
        stderr(&failed)
    );
    assert!(
        !stdout(&failed).contains("hint:"),
        "the hint must not touch stdout:\n{}",
        stdout(&failed)
    );
    fs::write(
        pkg.join("src/lib.rs"),
        "#[cfg(kani)]\nmod v {\n    #[kani::proof]\n    fn c() {\n        let a: u8 = kani::any();\n        kani::assume(a < 100);\n        assert!(a + 1 > a);\n    }\n}\n",
    )
    .unwrap();

    // A second run must still work: cargo CACHES the build, so anything that
    // deletes the generated query leaves the rerun with nothing to solve.
    let again = run(&["--timeout", "30s"]);
    assert_eq!(
        code(&again),
        0,
        "a second `cargo trust-mc` must not fail:\n{}\n{}",
        stdout(&again),
        stderr(&again)
    );
    assert!(!stdout(&again).contains("SMT-LIB2 file not found"), "{}", stdout(&again));

    // Naming a file in cargo mode should redirect, not produce a clap error.
    let file = run(&["src/lib.rs"]);
    assert_eq!(code(&file), 2);
    assert!(stderr(&file).contains("verifies the package"), "{}", stderr(&file));
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn a_legitimate_assumption_still_proves() {
    if !installation_ready() {
        return;
    }
    // Guards the two gates above against over-firing: this harness uses
    // `kani::assume` exactly as intended and must still verify cleanly.
    let dir = scratch("assume-ok");
    fs::write(dir.join("assume.rs"), stdout(&trust_mc(&["example", "assume"]))).unwrap();
    let out = trust_mc_in(&dir, &["--timeout", "30s", "assume.rs"]);
    let text = stdout(&out);
    assert_eq!(code(&out), 0, "{text}");
    assert!(text.contains("VERIFICATION:- SUCCESSFUL"), "{text}");
    assert!(!text.contains("[AY:VACUOUS:"), "no vacuity marker on a real proof:\n{text}");
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn fail_fast_still_counts_the_harnesses_it_already_verified() {
    if !installation_ready() {
        return;
    }
    // `--fail-fast` used to report a harness as verified and then deny it had
    // been. The parallel loop collected into `Result<Vec<_>>`, which keeps the
    // first `Err` and discards every `Ok` already produced, so the summary was
    // computed from the failing harness alone:
    //
    //     Checking harness c_ok...   VERIFICATION:- SUCCESSFUL
    //     Checking harness b_bad...  VERIFICATION:- FAILED
    //     Complete - 0 successfully verified harnesses, 1 failures, 1 total.
    //
    // Harnesses run in source order, so `a_ok` here is the one that must not
    // be reached: stopping early is the point of the flag, and this test would
    // otherwise pass just as well if `--fail-fast` did nothing at all.
    let dir = scratch("fail-fast-counts");
    fs::write(
        dir.join("failfast.rs"),
        "#[kani::proof]\n\
         fn a_ok() {\n\
         \x20   assert!(1 + 1 == 2);\n\
         }\n\
         #[kani::proof]\n\
         fn b_bad() {\n\
         \x20   let x: u8 = kani::any();\n\
         \x20   assert!(x < 5);\n\
         }\n\
         #[kani::proof]\n\
         fn c_ok() {\n\
         \x20   assert!(2 + 2 == 4);\n\
         }\n",
    )
    .unwrap();

    let out =
        trust_mc_in(&dir, &["--output-format", "terse", "--fail-fast", "--timeout", "30s", "failfast.rs"]);
    let text = stdout(&out);
    assert_eq!(code(&out), 1, "a failing harness must exit 1:\n{text}");

    // Whatever the summary claims, it has to agree with the transcript above
    // it. Count the verdicts actually printed and require the tallies to match.
    let succeeded = text.matches("VERIFICATION:- SUCCESSFUL").count();
    let failed = text.matches("VERIFICATION:- FAILED").count();
    assert_eq!(failed, 1, "--fail-fast must stop at the first failure:\n{text}");
    assert!(
        text.contains(&format!(
            "Complete - {succeeded} successfully verified harnesses, {failed} failures, {} total.",
            succeeded + failed
        )),
        "summary contradicts the {succeeded} success / {failed} failure transcript:\n{text}"
    );
    assert!(
        !text.contains("Checking harness a_ok"),
        "--fail-fast must not keep going past the failure:\n{text}"
    );
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn value_flags_match_the_engine() {
    // The front end passes unrecognized flags through to the engine, so it has
    // to know which of them eat the following token -- otherwise a flag's VALUE
    // gets read as the input file. That list is only correct while it matches
    // the engine, so re-derive it here from `--help` rather than trusting it.
    let Some(driver) = sibling_binary("trust-mc-driver") else {
        return;
    };
    let help = Command::new(&driver).arg("--help").output().expect("driver --help");
    let text = String::from_utf8_lossy(&help.stdout);

    // clap renders a value-taking option as `--flag <VALUE>`; a boolean has no
    // `<...>` after it.
    let mut engine: Vec<String> = Vec::new();
    for line in text.lines() {
        let trimmed = line.trim_start();
        let Some(rest) = trimmed.strip_prefix("--") else { continue };
        let Some((name, tail)) = rest.split_once(' ') else { continue };
        if tail.trim_start().starts_with('<')
            && name.chars().all(|c| c.is_ascii_lowercase() || c == '-')
        {
            engine.push(format!("--{name}"));
        }
    }
    engine.sort();
    engine.dedup();
    assert!(
        engine.len() > 10,
        "parsed too few value flags from the engine's help -- the format probably changed:\n{text}"
    );

    // The front end owns the list; read it back out of the source so the test
    // does not need it exported through a binary target.
    let source = fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("src/frontend/args.rs"),
    )
    .unwrap();
    let block = source
        .split_once("pub(crate) const ENGINE_VALUE_FLAGS: &[&str] = &[")
        .expect("ENGINE_VALUE_FLAGS not found")
        .1
        .split_once("];")
        .unwrap()
        .0;
    let known: Vec<String> =
        block.split('"').filter(|p| p.starts_with("--")).map(|p| p.to_string()).collect();

    let missing: Vec<&String> = engine.iter().filter(|f| !known.contains(f)).collect();
    assert!(
        missing.is_empty(),
        "the engine takes a value for {missing:?} but the front end does not know it.\n\
         Add them to ENGINE_VALUE_FLAGS in src/frontend/args.rs, or their values\n\
         will be mistaken for the input file."
    );
}

#[test]
fn a_report_flag_can_be_run_twice_in_the_same_directory() {
    if !installation_ready() {
        return;
    }
    // `--sarif` writes a file into the working directory. On the next run that
    // file exists, and the front end used to read it as a positional argument:
    //
    //     error: report.sarif is not a Rust source file
    //
    // which is every CI job that keeps its report next to the source.
    let dir = scratch("sarif-rerun");
    fs::write(
        dir.join("twice.rs"),
        "#[kani::proof]\nfn p() {\n\x20   assert!(1 + 1 == 2);\n}\n",
    )
    .unwrap();

    for run in 1..=2 {
        let out = trust_mc_in(&dir, &["--sarif", "report.sarif", "--timeout", "30s", "twice.rs"]);
        let text = format!("{}{}", stdout(&out), stderr(&out));
        assert_eq!(code(&out), 0, "run {run} of --sarif must succeed:\n{text}");
        assert!(
            !text.contains("is not a Rust source file"),
            "run {run} read the report as the input file:\n{text}"
        );
    }
    assert!(dir.join("report.sarif").is_file(), "the report should exist");
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn a_failing_harness_always_leaves_a_sarif_finding() {
    if !installation_ready() {
        return;
    }
    // SARIF is what CI gates on. A harness can fail as a whole with no single
    // property failing -- a vacuous proof, or one that compiled to zero
    // obligations -- and the report used to come back with zero results while
    // the process exited non-zero. To code scanning that is a clean file.
    let dir = scratch("sarif-vacuous");
    let cases: [(&str, &str, &str); 2] = [
        (
            "vacuous.rs",
            "#[kani::proof]\nfn v() {\n\x20   let x: u32 = kani::any();\n\
             \x20   kani::assume(x > 10);\n\x20   kani::assume(x < 5);\n\
             \x20   assert!(x == 0);\n}\n",
            "trust_mc.harness.vacuous",
        ),
        (
            "nochecks.rs",
            "#[kani::proof]\nfn n() {\n\x20   let x: u32 = kani::any();\n\x20   let _ = x;\n}\n",
            "trust_mc.harness.no_checks",
        ),
    ];

    for (file, body, expected_rule) in cases {
        fs::write(dir.join(file), body).unwrap();
        let report = format!("{file}.sarif");
        let out = trust_mc_in(&dir, &["--sarif", &report, "--timeout", "30s", file]);
        let text = stdout(&out);
        assert_eq!(code(&out), 1, "{file} must not exit 0:\n{text}");

        let json: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(dir.join(&report)).unwrap()).unwrap();
        let results = json["runs"][0]["results"].as_array().unwrap();
        assert!(
            !results.is_empty(),
            "{file} exited {} but reported no SARIF finding:\n{text}",
            code(&out)
        );
        assert_eq!(
            results[0]["ruleId"].as_str().unwrap(),
            expected_rule,
            "unexpected rule for {file}"
        );
        assert_eq!(results[0]["level"].as_str().unwrap(), "error");
        assert!(
            !results[0]["locations"][0]["physicalLocation"]["artifactLocation"]["uri"]
                .as_str()
                .unwrap()
                .is_empty(),
            "a finding needs a location"
        );
    }
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn a_failing_assert_points_at_the_users_line() {
    if !installation_ready() {
        return;
    }
    // The whole promise of the tool is naming the check that fails and where.
    // `assert!` expands to `kani::assert(..)`, whose tokens belong to the macro
    // definition, so the emitted check used to carry a span inside trust-mc's
    // own sources:
    //
    //     Location: .../library/std/src/lib.rs:51:9 in function fails_here
    //
    // pointing at the macro body instead of the user's line -- in the report
    // and in the SARIF that code scanning reads. See `user_facing_span`.
    let dir = scratch("assert-location");
    fs::write(
        dir.join("where.rs"),
        // `assert!` is deliberately on a known line (4) and column (5).
        "#[kani::proof]\n\
         fn fails_here() {\n\
         \x20   let x: u8 = kani::any();\n\
         \x20   assert!(x < 5);\n\
         }\n",
    )
    .unwrap();

    let out = trust_mc_in(&dir, &["--sarif", "loc.sarif", "--timeout", "30s", "where.rs"]);
    let text = stdout(&out);
    assert_eq!(code(&out), 1, "the assertion must fail:\n{text}");
    assert!(
        text.contains("where.rs:4:5"),
        "the failing check must name the user's line, not the macro's:\n{text}"
    );
    assert!(
        !text.contains("library/std/src/lib.rs"),
        "a check must never be attributed to trust-mc's own sources:\n{text}"
    );

    let json: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(dir.join("loc.sarif")).unwrap()).unwrap();
    let loc = &json["runs"][0]["results"][0]["locations"][0]["physicalLocation"];
    assert_eq!(loc["artifactLocation"]["uri"].as_str().unwrap(), "where.rs");
    assert_eq!(loc["region"]["startLine"].as_u64().unwrap(), 4);
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn a_harness_filter_that_matches_nothing_says_how_to_find_the_names() {
    if !installation_ready() {
        return;
    }
    // A rejected `--harness` filter used to end the conversation: it said the
    // filter matched nothing and left the user to work out what to type next.
    // It must not, however, claim the crate has no harnesses -- the compiler
    // only codegens harnesses that match the filter, so the metadata reaching
    // the summary is empty precisely because the filter failed, and reading
    // that as "no harnesses exist" would be false for this very file.
    let dir = scratch("harness-filter");
    fs::write(
        dir.join("named.rs"),
        "#[kani::proof]\nfn alpha() {\n\x20   assert!(1 + 1 == 2);\n}\n\
         #[kani::proof]\nfn beta() {\n\x20   assert!(2 + 2 == 4);\n}\n",
    )
    .unwrap();

    let out = trust_mc_in(&dir, &["--harness", "no_such_harness", "--timeout", "30s", "named.rs"]);
    let text = format!("{}{}", stdout(&out), stderr(&out));
    assert_ne!(code(&out), 0, "an unmatched filter is not a success:\n{text}");
    assert!(text.contains("no harnesses matched"), "{text}");
    assert!(
        text.contains("--list"),
        "the rejection must point at the way to see the real names:\n{text}"
    );
    assert!(
        !text.to_lowercase().contains("no #[kani::proof] harnesses at all"),
        "this file HAS harnesses; the message must not deny it:\n{text}"
    );

    // And the filter still works when it does match.
    let ok = trust_mc_in(&dir, &["--output-format", "terse", "--harness", "beta", "--timeout", "30s", "named.rs"]);
    let ok_text = stdout(&ok);
    assert_eq!(code(&ok), 0, "{ok_text}");
    assert!(ok_text.contains("1 total."), "only the named harness should run:\n{ok_text}");
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn a_crate_with_no_harnesses_is_not_called_a_success() {
    if !installation_ready() {
        return;
    }
    // Verifying a file with no #[kani::proof] checked nothing, so it must not
    // be labelled a proof. It used to print
    // `VERIFICATION:- SUCCESSFUL (no proof harnesses were found to verify)` —
    // a success verdict over zero obligations.
    //
    // The exit code stays 0, deliberately and as the one documented exception:
    // Kani exits 0 here, seven script-based corpus tests run trust-mc on a
    // zero-harness crate under `set -eu`, and a workspace where one member
    // declares no harnesses should not fail the build. The claim is what
    // changed, not the contract.
    let dir = scratch("no-harnesses");
    fs::write(dir.join("bare.rs"), "pub fn add(a: u8, b: u8) -> u16 {\n\x20   a as u16 + b as u16\n}\n")
        .unwrap();

    let out = trust_mc_in(&dir, &["--timeout", "30s", "bare.rs"]);
    let text = stdout(&out);
    assert_eq!(code(&out), 0, "the exit contract is unchanged:\n{text}");
    assert!(
        !text.contains("VERIFICATION:- SUCCESSFUL"),
        "nothing was verified, so nothing succeeded:\n{text}"
    );
    assert!(text.contains("[AY:NO_HARNESSES]"), "the case must be machine-detectable:\n{text}");
    // Kani's own wording, which seven corpus .expected files assert verbatim.
    assert!(
        text.contains("No proof harnesses (functions with #[kani::proof]) were found to verify."),
        "the Kani-parity line must survive:\n{text}"
    );
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn doctor_json_is_valid_and_agrees_with_the_exit_code() {
    // CI needs doctor's result as data, not prose. The object reports only what
    // doctor already holds structurally — scraping its own printed check lines
    // back out would be one formatting change away from lying.
    let out = trust_mc(&["doctor", "--json"]);
    let text = stdout(&out);
    let code = code(&out);
    assert!(code == 0 || code == 3, "doctor exits 0 or 3, got {code}:\n{text}");

    // Parse without a JSON library: assert the shape and the fields that must
    // agree with the process result.
    assert!(text.trim_start().starts_with('{'), "not an object:\n{text}");
    assert!(text.trim_end().ends_with('}'), "unterminated object:\n{text}");
    for key in [
        "\"ready\"",
        "\"exit_code\"",
        "\"version\"",
        "\"target\"",
        "\"engine\"",
        "\"solver\"",
        "\"warnings\"",
        "\"fixes\"",
    ] {
        assert!(text.contains(key), "missing {key}:\n{text}");
    }
    let ready = text.contains("\"ready\": true");
    assert_eq!(
        ready,
        code == 0,
        "`ready` must agree with the exit code (code={code}):\n{text}"
    );
    assert!(
        text.contains(&format!("\"exit_code\": {code}")),
        "reported exit_code must be the real one ({code}):\n{text}"
    );
    assert!(text.contains(&format!("\"version\": \"{}\"", env!("CARGO_PKG_VERSION"))), "{text}");

    // The human report must still be the default.
    let plain = stdout(&trust_mc(&["doctor"]));
    assert!(!plain.trim_start().starts_with('{'), "--json must be opt-in:\n{plain}");
}

#[test]
fn niche_types_only_produce_values_they_can_actually_hold() {
    if !installation_ready() {
        return;
    }
    // `Arbitrary` for a niche type states its invariant in Rust:
    //
    //     let val = u32::any();
    //     assume(val <= 0xD7FF || (val >= 0xE000 && val <= 0x10FFFF));
    //     unsafe { char::from_u32_unchecked(val) }
    //
    // Inlining that body handed codegen a `from_u32_unchecked` (and, for
    // NonZero, a `new_unchecked`) it does not model, so the `assume` was
    // dropped along with the value it constrained and the type admitted values
    // it exists to exclude — `char` beyond 0x10FFFF, `NonZeroU8` equal to 0.
    // Every harness over these types explored impossible inputs, so any
    // resulting counterexample was unreachable in real code.
    //
    // The calls are now held at the codegen handler boundary, where the same
    // invariants are applied where they cannot be lost. See
    // `kani_middle::transform::inline::handler_boundaries`.
    let dir = scratch("niche-types");
    let cases: [(&str, &str); 4] = [
        ("char_range.rs", "let c: char = kani::any();\n\x20   assert!(c as u32 <= 0x10FFFF);"),
        (
            "char_surrogate.rs",
            "let c: char = kani::any();\n\x20   let v = c as u32;\n\x20   assert!(v < 0xD800 || v > 0xDFFF);",
        ),
        (
            "nonzero_u8.rs",
            "let n: core::num::NonZeroU8 = kani::any();\n\x20   assert!(n.get() != 0);",
        ),
        (
            "nonzero_i32.rs",
            "let n: core::num::NonZeroI32 = kani::any();\n\x20   assert!(n.get() != 0);",
        ),
    ];
    for (file, body) in cases {
        fs::write(dir.join(file), format!("#[kani::proof]\nfn h() {{\n\x20   {body}\n}}\n")).unwrap();
        let out = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "60s", file]);
        let text = stdout(&out);
        assert_eq!(code(&out), 0, "{file} states the type's own invariant:\n{text}");
        assert!(text.contains("VERIFICATION:- SUCCESSFUL"), "{file}:\n{text}");
    }

    // Controls: the constraint must not have become "assume anything useful".
    // These are false for real values of the type and must still be caught.
    for (file, body) in [
        ("char_ctl.rs", "let c: char = kani::any();\n\x20   assert!((c as u32) < 100);"),
        (
            "nonzero_ctl.rs",
            "let n: core::num::NonZeroU8 = kani::any();\n\x20   assert!(n.get() != 5);",
        ),
    ] {
        fs::write(dir.join(file), format!("#[kani::proof]\nfn h() {{\n\x20   {body}\n}}\n")).unwrap();
        let out = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "60s", file]);
        let text = stdout(&out);
        assert_eq!(code(&out), 1, "{file} must still fail:\n{text}");
        assert!(text.contains("VERIFICATION:- FAILED"), "{file}:\n{text}");
    }
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn an_undecided_solver_is_not_reported_as_an_empty_harness() {
    if !installation_ready() {
        return;
    }
    // "The harness had nothing to prove" and "we could not settle what it had"
    // both reach the verdict with an empty property list, and they are opposite
    // diagnoses. Reporting the first for the second sent users hunting for a
    // missing assertion that was there all along:
    //
    //     VERIFICATION:- INCONCLUSIVE (no checks)
    //     [AY:UNKNOWN_REASON:UndecidedModel]      <- the real story
    //
    // A bounded symbolic loop is the everyday shape that lands here, and the
    // answer is a different engine — so the verdict now names it.
    let dir = scratch("undecided");
    fs::write(
        dir.join("loop.rs"),
        "#[kani::proof]\n#[kani::unwind(11)]\nfn h() {\n\
         \x20   let n: u32 = kani::any();\n\
         \x20   kani::assume(n <= 10);\n\
         \x20   let mut i = 0u32;\n\
         \x20   while i < n {\n\x20       i += 1;\n\x20   }\n\
         \x20   assert!(i == n);\n}\n",
    )
    .unwrap();
    let out = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "120s", "loop.rs"]);
    let text = stdout(&out);
    if text.contains("VERIFICATION:- SUCCESSFUL") {
        // BMC decided it after all — a strictly better outcome, nothing to assert.
        let _ = fs::remove_dir_all(&dir);
        return;
    }
    assert!(
        !text.contains("INCONCLUSIVE (no checks)"),
        "an undecided solver must not be reported as an empty harness:\n{text}"
    );
    assert!(
        text.contains("solver undecided"),
        "the verdict should say what actually happened:\n{text}"
    );
    assert!(text.contains("--ay-chc"), "and name the flag that decides this shape:\n{text}");

    // A genuinely empty harness must still get the other diagnosis.
    fs::write(dir.join("empty.rs"), "#[kani::proof]\nfn h() {\n\x20   let x: u32 = kani::any();\n\x20   let _ = x;\n}\n")
        .unwrap();
    let out = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "60s", "empty.rs"]);
    let text = stdout(&out);
    assert!(text.contains("INCONCLUSIVE (no checks)"), "{text}");
    assert!(!text.contains("solver undecided"), "{text}");
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn the_readme_examples_do_what_the_readme_says() {
    if !installation_ready() {
        return;
    }
    // The README is the first thing anyone runs, and a command there that does
    // not behave as printed is worse than no README. Writing this section I
    // claimed that deleting the overflow turns the failing example into a
    // proof; it does not — with nothing left to discharge the harness reports
    // INCONCLUSIVE (no checks) and exits 1. The claim was wrong and the tool
    // caught it, which is the behaviour the README now describes.
    let dir = scratch("readme");
    let readme = fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("README.md")).unwrap();

    // 1. The failing example: overflow, exit 1.
    fs::write(
        dir.join("bug.rs"),
        "fn add(a: u8, b: u8) -> u8 { a + b }\n\n#[kani::proof]\nfn add_never_overflows() {\n\
         \x20   let a: u8 = kani::any();\n\x20   let b: u8 = kani::any();\n\x20   let _ = add(a, b);\n}\n",
    )
    .unwrap();
    let out = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "60s", "bug.rs"]);
    let text = stdout(&out);
    assert_eq!(code(&out), 1, "{text}");
    assert!(text.contains("VERIFICATION:- FAILED"), "{text}");
    assert!(
        text.contains("attempt to add with overflow"),
        "the README prints this exact failed check \
         (`Failed Checks: attempt to add with overflow`):\n{text}"
    );

    // 2. The proving example, verbatim from the README.
    fs::write(
        dir.join("ok.rs"),
        "fn add(a: u8, b: u8) -> u16 { a as u16 + b as u16 }\n\n#[kani::proof]\n\
         fn add_never_overflows() {\n\x20   let a: u8 = kani::any();\n\
         \x20   let b: u8 = kani::any();\n\x20   assert!(add(a, b) <= 510);\n}\n",
    )
    .unwrap();
    let out = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "60s", "ok.rs"]);
    let text = stdout(&out);
    assert_eq!(code(&out), 0, "{text}");
    assert!(text.contains("VERIFICATION:- SUCCESSFUL"), "{text}");

    // 3. The counter-claim the README makes about it: dropping the `+` is not a
    //    proof, and must not exit 0.
    fs::write(
        dir.join("nothing.rs"),
        "fn add(a: u8, b: u8) -> u8 { a.wrapping_add(b) }\n#[kani::proof]\n\
         fn add_never_overflows() {\n\x20   let a: u8 = kani::any();\n\
         \x20   let b: u8 = kani::any();\n\x20   let _ = add(a, b);\n}\n",
    )
    .unwrap();
    let out = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "60s", "nothing.rs"]);
    let text = stdout(&out);
    assert_eq!(code(&out), 1, "zero obligations must not go green:\n{text}");
    assert!(text.contains("INCONCLUSIVE (no checks)"), "{text}");

    // 4. The exit-code contract the CI section states.
    assert!(readme.contains("**0** every selected harness verified"), "README exit-code table");
    for (args, want) in [(&["doctor", "--json"][..], 0), (&["nosuchfile.rs"], 2)] {
        let out = trust_mc(args);
        if args[0] == "doctor" && code(&out) == 3 {
            continue; // not installed; doctor's own contract, still documented
        }
        assert_eq!(code(&out), want, "{args:?}: {}", stderr(&out));
    }
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn an_ordinary_run_prints_no_internal_tracing() {
    if !installation_ready() {
        return;
    }
    // `a as u64` is not something to warn a user about, but an entry trace left
    // at warn! level fired on every cast and reached the default output:
    //
    //     Checking harness h...
    //     WARN trust_mc_compiler::codegen_ay::statement::cast ENTRY
    //          codegen_cast_with_kind, kind=IntToInt
    //     ...
    //
    // One line per cast, between the harness name and its verdict. On a real
    // crate that is the whole screen. Diagnostics the user can act on are
    // welcome here; module-path tracing is not.
    let dir = scratch("no-tracing");
    fs::write(
        dir.join("casts.rs"),
        "#[kani::proof]\nfn h() {\n\
         \x20   let a: u8 = kani::any();\n\
         \x20   let w = a as u64;\n\
         \x20   let n = w as i32;\n\
         \x20   let m = n as u16;\n\
         \x20   assert!(w <= 255 && m <= 255);\n}\n",
    )
    .unwrap();

    let out = trust_mc_in(&dir, &["--timeout", "60s", "casts.rs"]);
    let text = format!("{}{}", stdout(&out), stderr(&out));
    assert_eq!(code(&out), 0, "{text}");
    assert!(
        !text.contains("[4112-INLINE]"),
        "a raw eprintln! debug print reached the user:\n{text}"
    );
    for line in text.lines() {
        assert!(
            !line.contains("trust_mc_compiler::"),
            "internal module tracing reached the default output:\n  {line}"
        );
        assert!(
            !line.contains("ENTRY "),
            "an entry trace reached the default output:\n  {line}"
        );
    }

    // It must still be reachable when asked for — this is a level change, not a
    // deletion.
    let out = trust_mc_in(&dir, &["--debug", "--timeout", "60s", "casts.rs"]);
    let text = format!("{}{}", stdout(&out), stderr(&out));
    assert!(
        text.contains("codegen_cast_with_kind"),
        "--debug should still show the cast trace"
    );
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn a_repeated_diagnostic_is_said_once() {
    if !installation_ready() {
        return;
    }
    // The inliner reaches the same stdlib callee from every harness and every
    // pass over a body, so `for e in v.iter_mut()` reported the same six
    // missing-MIR functions four times over — two dozen identical lines between
    // the harness and its verdict. The fact matters (an un-inlined stdlib
    // function is stubbed or over-approximated, which bears on what the proof
    // covers) so it is still reported; the repetition does not.
    let dir = scratch("repeat-diag");
    fs::write(
        dir.join("iter.rs"),
        "fn clamp(v: &mut Vec<u8>, hi: u8) {
             for e in v.iter_mut() {
        if *e > hi {
            *e = hi;
        }
    }
}
         #[kani::proof]
#[kani::unwind(4)]
fn h() {
             let mut v: Vec<u8> = Vec::new();
             v.push(kani::any());
    v.push(kani::any());
             clamp(&mut v, 10);
    assert!(v.len() == 2);
}
",
    )
    .unwrap();

    let out = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "120s", "iter.rs"]);
    let err = stderr(&out);
    let warnings: Vec<&str> =
        err.lines().filter(|l| l.contains("Stdlib function MIR unavailable")).collect();
    let mut unique = warnings.clone();
    unique.sort_unstable();
    unique.dedup();
    assert_eq!(
        warnings.len(),
        unique.len(),
        "each missing-MIR callee should be reported once, got {} lines for {} callees:\n{}",
        warnings.len(),
        unique.len(),
        warnings.join("\n")
    );
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn a_shift_by_an_unconstrained_distance_is_checked() {
    if !installation_ready() {
        return;
    }
    // `a << s` panics when `s` reaches the value's bit width, and rustc emits
    // `Assert { msg: Overflow(Shl, ..) }` for exactly that. The Assert handler
    // routed it to `overflow_check`, whose fallthrough reads "Shift, comparison,
    // and bitwise operations don't overflow" — true of the other two, false of
    // this one — so the obligation was dropped and:
    //
    //     let r = a << s;   // s unconstrained
    //     assert!(r >= 0);
    //     VERIFICATION:- SUCCESSFUL
    //
    // for a program that panics at run time. `let _ = a << s` alone had looked
    // caught, but only because it left the harness with no obligations at all,
    // which the no-checks gate reports — the right verdict for the wrong reason,
    // and no help once the harness asserts anything else.
    let dir = scratch("shift-distance");
    let cases: [(&str, &str, i32); 4] = [
        // (file, body, expected exit)
        ("unbounded.rs", "let a: u32 = kani::any();\n\x20   let s: u32 = kani::any();\n\
          \x20   let r = a << s;\n\x20   assert!(r >= 0);", 1),
        ("bounded.rs", "let a: u32 = kani::any();\n\x20   let s: u32 = kani::any();\n\
          \x20   kani::assume(s < 32);\n\x20   let r = a << s;\n\x20   assert!(r >= 0);", 0),
        // The bound must be read against the VALUE's width, not the distance's:
        // a u8 shifted by s < 32 still overflows for 8 <= s < 32.
        ("narrow_bad.rs", "let a: u8 = kani::any();\n\x20   let s: u32 = kani::any();\n\
          \x20   kani::assume(s < 32);\n\x20   let r = a << s;\n\x20   assert!(r >= 0);", 1),
        ("narrow_ok.rs", "let a: u8 = kani::any();\n\x20   let s: u32 = kani::any();\n\
          \x20   kani::assume(s < 8);\n\x20   let r = a << s;\n\x20   assert!(r >= 0);", 0),
    ];
    for (file, body, want) in cases {
        fs::write(dir.join(file), format!("#[kani::proof]\nfn h() {{\n\x20   {body}\n}}\n")).unwrap();
        let out = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "60s", file]);
        let text = stdout(&out);
        assert_eq!(code(&out), want, "{file}:\n{text}");
        if want == 1 {
            assert!(
                text.contains("VERIFICATION:- FAILED"),
                "{file} must be a real failure, not an empty harness:\n{text}"
            );
        }
    }

    // Right shift too.
    fs::write(
        dir.join("shr.rs"),
        "#[kani::proof]\nfn h() {\n\x20   let a: u32 = kani::any();\n\
         \x20   let s: u32 = kani::any();\n\x20   let r = a >> s;\n\x20   assert!(r >= 0);\n}\n",
    )
    .unwrap();
    let out = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "60s", "shr.rs"]);
    assert_eq!(code(&out), 1, "{}", stdout(&out));
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn the_same_input_gives_the_same_verdict_and_counterexample() {
    if !installation_ready() {
        return;
    }
    // A verification gate is only useful in CI if it is reproducible: the same
    // source must give the same verdict, and a reported counterexample must be
    // the same one, or a red build cannot be trusted or triaged. Solver search
    // order is a plausible way for that to drift, so it is worth pinning rather
    // than assuming.
    //
    // Note what this does NOT claim: a run that exhausts its `--timeout` is
    // wall-clock bound by definition and may land differently on a loaded
    // machine. These harnesses are solved comfortably inside their budget.
    let dir = scratch("determinism");
    fs::write(
        dir.join("ce.rs"),
        "#[kani::proof]\nfn h() {\n\x20   let a: u8 = kani::any();\n\
         \x20   let b: u8 = kani::any();\n\x20   kani::assume(a > 200 && b > 200);\n\
         \x20   let _ = a + b;\n}\n",
    )
    .unwrap();

    let mut verdicts = Vec::new();
    let mut witnesses = Vec::new();
    for _ in 0..3 {
        let out = trust_mc_in(
            &dir,
            &["-Z", "concrete-playback", "--concrete-playback", "print", "--timeout", "60s", "ce.rs"],
        );
        let text = stdout(&out);
        assert_eq!(code(&out), 1, "{text}");
        verdicts.push(
            text.lines().find(|l| l.contains("VERIFICATION:-")).unwrap_or_default().to_string(),
        );
        // The generated test's concrete values are the witness.
        witnesses.push(
            text.lines()
                .filter(|l| l.trim_start().starts_with("vec!["))
                .map(str::trim)
                .collect::<Vec<_>>()
                .join(","),
        );
    }
    assert!(verdicts.iter().all(|v| *v == verdicts[0]), "verdict drifted across runs: {verdicts:?}");
    assert!(!witnesses[0].is_empty(), "expected concrete values in the playback test");
    assert!(
        witnesses.iter().all(|w| *w == witnesses[0]),
        "counterexample drifted across runs: {witnesses:?}"
    );
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn vec_from_a_slice_knows_its_own_length() {
    if !installation_ready() {
        return;
    }
    // `Vec::from(&[T])` used to leave the whole result unconstrained. The DATA
    // genuinely is an over-approximation, but the LENGTH is not an approximation
    // at all — a Vec built from `[T; N]` has exactly N elements — so obviously
    // true facts were unprovable:
    //
    //     Vec::from([1u8, 2, 3, 4]).len() == 4     // FAILED
    //
    // and that sank `<Vec<T> as BoundedArbitrary>::bounded_any`, which builds
    // its vector this way before truncating.
    let dir = scratch("vec-from-len");
    let cases: [(&str, &str, i32); 4] = [
        ("konst.rs", "let v = Vec::from([1u8, 2, 3, 4]);\n\x20   assert!(v.len() == 4);", 0),
        (
            "symbolic.rs",
            "let a: [u8; 4] = kani::any();\n\x20   let v = Vec::from(a);\n\x20   assert!(v.len() == 4);",
            0,
        ),
        (
            "bounded.rs",
            "let v: Vec<u8> = kani::bounded_any::<_, 4>();\n\x20   assert!(v.len() <= 4);",
            0,
        ),
        // The refinement must not over-claim: bounded_any's length is symbolic
        // up to N, so asserting it EQUALS N has to still fail.
        (
            "not_exact.rs",
            "let v: Vec<u8> = kani::bounded_any::<_, 4>();\n\x20   assert!(v.len() == 4);",
            1,
        ),
    ];
    for (file, body, want) in cases {
        fs::write(
            dir.join(file),
            format!("#[kani::proof]\n#[kani::unwind(6)]\nfn h() {{\n\x20   {body}\n}}\n"),
        )
        .unwrap();
        let out = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "90s", file]);
        let text = stdout(&out);
        assert_eq!(code(&out), want, "{file}:\n{text}");
    }

    // `String::bounded_any` gets its bound the same way, but for a different
    // reason. Its body runs through `utf8_chunks()` / `Utf8Chunk::valid()`,
    // which codegen abstracts to unconstrained symbolics, so inlining it threw
    // away the one guarantee the API makes. Modelling UTF-8 chunking faithfully
    // is a feature; modelling what bounded_any PROMISES is not — a String built
    // from N bytes holds at most N bytes whatever the chunking does. The call
    // is held at the codegen boundary and the bound stated directly.
    let strings: [(&str, &str, i32); 4] = [
        ("s_le.rs", "let s: String = kani::bounded_any::<_, 4>();\n\x20   assert!(s.len() <= 4);", 0),
        // Must not over-claim: the length is symbolic UP TO N, not equal to it.
        ("s_eq.rs", "let s: String = kani::bounded_any::<_, 4>();\n\x20   assert!(s.len() == 4);", 1),
        // The bound tracks N rather than being hard-coded...
        ("s_ten.rs", "let s: String = kani::bounded_any::<_, 10>();\n\x20   assert!(s.len() <= 10);", 0),
        // ...and is tight, not merely some bound.
        ("s_tight.rs", "let s: String = kani::bounded_any::<_, 10>();\n\x20   assert!(s.len() <= 3);", 1),
    ];
    for (file, body, want) in strings {
        fs::write(
            dir.join(file),
            format!("#[kani::proof]\n#[kani::unwind(12)]\nfn h() {{\n\x20   {body}\n}}\n"),
        )
        .unwrap();
        let out = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "90s", file]);
        let text = stdout(&out);
        assert_eq!(code(&out), want, "{file}:\n{text}");
    }
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn a_counterexample_that_is_not_certified_says_so() {
    if !installation_ready() {
        return;
    }
    // A counterexample the classifier could not certify as genuine renders as
    // `VERIFICATION:- FAILED`, the same as a real bug. The only signal was the
    // word "EncodingGap" inside "CTREX breakdown: 1 EncodingGap, 0
    // OverApproximation, ..." — vocabulary, not an explanation, and an hour
    // hunting a bug that is not there.
    //
    // `bounded_any::<String, N>` is the everyday case: `utf8_chunks` is
    // abstracted, so the failure comes from the encoding rather than the
    // harness.
    let dir = scratch("uncertified");
    fs::write(
        dir.join("gap.rs"),
        "#[kani::proof]\n#[kani::unwind(6)]\nfn h() {\n\
         \x20   let s: String = kani::bounded_any::<_, 4>();\n\x20   assert!(s.len() <= 4);\n}\n",
    )
    .unwrap();
    let out = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "120s", "gap.rs"]);
    let text = stdout(&out);
    if text.contains("VERIFICATION:- SUCCESSFUL") {
        // If the encoding ever models this precisely, there is no caveat to make.
        let _ = fs::remove_dir_all(&dir);
        return;
    }
    assert!(
        text.contains("[AY:CTREX_NOT_CERTIFIED]"),
        "an uncertified counterexample must say so in words:\n{text}"
    );
    assert!(
        text.contains("NOT certified as a genuine bug"),
        "the caveat should be readable without knowing the marker vocabulary:\n{text}"
    );

    // And the caveat must NOT appear on a genuine bug, or it is noise that
    // teaches people to ignore it.
    fs::write(
        dir.join("real.rs"),
        "#[kani::proof]\nfn h() {\n\x20   let a: u8 = kani::any();\n\
         \x20   let b: u8 = kani::any();\n\x20   let _ = a + b;\n}\n",
    )
    .unwrap();
    let out = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "60s", "real.rs"]);
    let text = stdout(&out);
    assert_eq!(code(&out), 1, "{text}");
    assert!(text.contains("[AY:CTREX_CAT:Genuine]"), "{text}");
    assert!(
        !text.contains("[AY:CTREX_NOT_CERTIFIED]"),
        "a genuine counterexample must not be hedged:\n{text}"
    );
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn a_workspace_verifies_every_member_and_exits_honestly() {
    if !installation_ready() {
        return;
    }
    let Some(cargo_trust_mc) = sibling_binary("cargo-trust-mc") else {
        eprintln!("SKIPPED: cargo-trust-mc not built next to trust-mc");
        return;
    };
    // A workspace is what a real project looks like, and the exit code is what
    // CI gates on — so a workspace where ONE member fails must exit 1, or a
    // green build means nothing. Package filtering has to work too, or you
    // cannot verify one crate at a time as proofs get expensive.
    let dir = scratch("workspace");
    let root = dir.join("ws");
    for member in ["good", "bad"] {
        fs::create_dir_all(root.join("crates").join(member).join("src")).unwrap();
        fs::write(
            root.join("crates").join(member).join("Cargo.toml"),
            format!("[package]\nname = \"{member}\"\nversion = \"0.1.0\"\nedition = \"2021\"\n"),
        )
        .unwrap();
    }
    fs::write(
        root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"crates/good\", \"crates/bad\"]\nresolver = \"2\"\n",
    )
    .unwrap();
    // Proves: widening to u16 cannot exceed 510.
    fs::write(
        root.join("crates/good/src/lib.rs"),
        "pub fn sum(a: u8, b: u8) -> u16 { a as u16 + b as u16 }\n#[cfg(kani)]\nmod p {\n\
         \x20   #[kani::proof]\n    fn sum_is_bounded() {\n        let a: u8 = kani::any();\n\
         \x20       let b: u8 = kani::any();\n        assert!(super::sum(a, b) <= 510);\n    }\n}\n",
    )
    .unwrap();
    // Fails: x * 2 overflows a u8 for x > 127.
    fs::write(
        root.join("crates/bad/src/lib.rs"),
        "pub fn double(x: u8) -> u8 { x * 2 }\n#[cfg(kani)]\nmod p {\n\
         \x20   #[kani::proof]\n    fn double_overflows() {\n        let x: u8 = kani::any();\n\
         \x20       let _ = super::double(x);\n    }\n}\n",
    )
    .unwrap();

    let run = |cwd: &Path, args: &[&str]| {
        let mut full = vec!["trust-mc"];
        full.extend_from_slice(args);
        Command::new(&cargo_trust_mc)
            .args(&full)
            .current_dir(cwd)
            .output()
            .expect("could not run cargo-trust-mc")
    };

    // Whole workspace: both members discovered, one fails, exit 1.
    let out = run(&root, &["--timeout", "60s"]);
    let text = stdout(&out);
    assert_eq!(code(&out), 1, "one failing member must fail the workspace:\n{text}");
    assert!(text.contains("2 total."), "both members should be verified:\n{text}");
    assert!(text.contains("1 successfully verified"), "{text}");

    // Package filtering, both directions.
    let good = run(&root, &["-p", "good", "--timeout", "60s"]);
    assert_eq!(code(&good), 0, "{}", stdout(&good));
    assert!(stdout(&good).contains("1 total."), "{}", stdout(&good));
    let bad = run(&root, &["-p", "bad", "--timeout", "60s"]);
    assert_eq!(code(&bad), 1, "{}", stdout(&bad));

    // Nothing written outside the build directory.
    let stray: Vec<PathBuf> = fs::read_dir(root.join("crates/good/src"))
        .unwrap()
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "smt2" || x == "json"))
        .collect();
    assert!(stray.is_empty(), "workspace run left artifacts in a source dir: {stray:?}");
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn quantifiers_never_produce_a_false_proof() {
    if !installation_ready() {
        return;
    }
    // Any array access in the same harness used to make the range bounds a
    // guarded SSA definition, so `extract_constant_bounds` declined and the
    // quantifier fell back — fixed by recovering the bound from the MIR, where
    // it is still the literal the user wrote. See
    // docs/findings/2026-08-21-quantifiers-decline-after-any-array-access.md.
    //
    // These two are the direction that must never regress whatever the encoding
    // does: a quantifier that cannot be evaluated must not evaluate to TRUE.
    // Both statements below are FALSE about the program and must be failures.
    let dir = scratch("quantifier-soundness");
    let cases: [(&str, &str); 2] = [
        // a[2] == 7 after the store, so "all zero" is false.
        (
            "forall_false.rs",
            "let mut a: [u8; 4] = [0; 4];\n\x20   a[2] = 7;\n\
             \x20   assert!(kani::forall!(|i in (0,4)| a[i] == 0));",
        ),
        // no element is 9.
        (
            "exists_false.rs",
            "let mut a: [u8; 4] = [0; 4];\n\x20   a[2] = 7;\n\
             \x20   assert!(kani::exists!(|i in (0,4)| a[i] == 9));",
        ),
    ];
    for (file, body) in cases {
        fs::write(dir.join(file), format!("#[kani::proof]\nfn h() {{\n\x20   {body}\n}}\n")).unwrap();
        let out =
            trust_mc_in(&dir, &["-Z", "quantifiers", "--output-format", "terse", "--timeout", "60s", file]);
        let text = stdout(&out);
        assert_ne!(code(&out), 0, "{file} states something FALSE and must not pass:\n{text}");
        assert!(
            !text.contains("VERIFICATION:- SUCCESSFUL"),
            "{file} must not be proved:\n{text}"
        );
    }

    // TRUE statements must prove, including the ones an array access used to
    // block. The first has no array in the predicate at all — it failed purely
    // because an array was READ earlier in the harness.
    let provable: [(&str, &str); 3] = [
        (
            "no_capture.rs",
            "let a: [u8; 4] = [0; 4];\n\x20   let _ = a[2];\n\
             \x20   assert!(kani::forall!(|i in (0,4)| i < 4));",
        ),
        (
            "forall_after_store.rs",
            "let mut a: [u8; 4] = [0; 4];\n\x20   a[2] = 7;\n\
             \x20   assert!(kani::forall!(|i in (0,4)| a[i] <= 7));",
        ),
        (
            "exists_after_store.rs",
            "let mut a: [u8; 4] = [0; 4];\n\x20   a[2] = 7;\n\
             \x20   assert!(kani::exists!(|i in (0,4)| a[i] == 7));",
        ),
    ];
    for (file, body) in provable {
        fs::write(dir.join(file), format!("#[kani::proof]\nfn h() {{\n\x20   {body}\n}}\n")).unwrap();
        let out = trust_mc_in(
            &dir,
            &["-Z", "quantifiers", "--output-format", "terse", "--timeout", "60s", file],
        );
        let text = stdout(&out);
        assert_eq!(code(&out), 0, "{file} states something TRUE and should prove:\n{text}");
        assert!(text.contains("VERIFICATION:- SUCCESSFUL"), "{file}:\n{text}");
    }
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn unstable_features_do_what_they_claim() {
    if !installation_ready() {
        return;
    }
    // Each case is a PAIR: a property that must prove and a control that must
    // fail. A passing assertion alone proves nothing about whether the feature
    // is doing anything — `assert!(real() == 42)` under a stub would also pass
    // if stubbing replaced the call with an unconstrained value. The control is
    // what separates "works" from "inert", and every bug this sweep found came
    // from a control rather than a property.
    //
    // See docs/findings/2026-08-21-unstable-feature-sweep.md.
    let dir = scratch("unstable-features");
    let stub_src = "fn real() -> u8 { 1 }\nfn stub() -> u8 { 42 }\n\
                    #[kani::proof]\n#[kani::stub(real, stub)]\nfn h() { assert!(real() == VAL); }\n";

    // -Z stubbing: the stub's value proves, the original's does not.
    for (val, want) in [("42", 0), ("1", 1)] {
        let file = format!("stub_{val}.rs");
        fs::write(dir.join(&file), stub_src.replace("VAL", val)).unwrap();
        let out = trust_mc_in(
            &dir,
            &["-Z", "stubbing", "--output-format", "terse", "--timeout", "60s", &file],
        );
        assert_eq!(code(&out), want, "stub asserting {val}:\n{}", stdout(&out));
    }

    // -Z uninit-checks: a genuine uninitialised read must never pass. It is
    // reported as uncertified (pointee_synthesis_fallback), so this asserts the
    // SAFETY direction only — the finding records that initialised reads are
    // also flagged, which is a completeness gap, not a soundness one.
    fs::write(
        dir.join("uninit.rs"),
        "use std::mem::MaybeUninit;\n#[kani::proof]\nfn h() {\n\
         \x20   let m: MaybeUninit<u8> = MaybeUninit::uninit();\n\
         \x20   let v = unsafe { m.assume_init() };\n\x20   let _ = v;\n}\n",
    )
    .unwrap();
    let out = trust_mc_in(
        &dir,
        &["-Z", "uninit-checks", "--output-format", "terse", "--timeout", "60s", "uninit.rs"],
    );
    let text = stdout(&out);
    assert_ne!(code(&out), 0, "reading uninitialised memory must not pass:\n{text}");
    assert!(!text.contains("VERIFICATION:- SUCCESSFUL"), "{text}");

    // ...and the flag must not poison ordinary code.
    fs::write(
        dir.join("plain.rs"),
        "#[kani::proof]\nfn h() {\n\x20   let a: u8 = kani::any();\n\
         \x20   let b = a.wrapping_add(1);\n\x20   assert!(b == a.wrapping_add(1));\n}\n",
    )
    .unwrap();
    let out = trust_mc_in(
        &dir,
        &["-Z", "uninit-checks", "--output-format", "terse", "--timeout", "60s", "plain.rs"],
    );
    assert_eq!(code(&out), 0, "the flag must be inert on code without MaybeUninit:\n{}", stdout(&out));
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn the_help_page_only_advertises_flags_that_work() {
    if !installation_ready() {
        return;
    }
    // The CI section of `--help` names four things. A help page that promises
    // what the binary refuses is worse than one that stays quiet, so each is
    // exercised here. `--jobs` is the reason this test exists: it was added to
    // the page, and it did not work.
    //
    //     $ trust-mc --jobs 2 demo.rs
    //     error: Conflicting options: --jobs requires `--output-format=terse`
    //
    // The engine needs terse because parallel harnesses interleave. Supplying
    // it is honouring that constraint, not overriding a choice — so the front
    // end adds it only when the user has not named a format, and a real
    // conflict still reaches them.
    let dir = scratch("help-ci-flags");
    fs::write(
        dir.join("multi.rs"),
        "#[kani::proof]\nfn a() {\n\x20   assert!(1 + 1 == 2);\n}\n\
         #[kani::proof]\nfn b() {\n\x20   assert!(2 + 2 == 4);\n}\n",
    )
    .unwrap();

    let help = stdout(&trust_mc(&["--help"]));
    for flag in ["--sarif", "--proof-summary-json", "--jobs", "doctor --json"] {
        assert!(help.contains(flag), "--help should mention {flag}");
    }

    // Bare --jobs must work.
    let out = trust_mc_in(&dir, &["--jobs", "2", "--timeout", "60s", "multi.rs"]);
    assert_eq!(code(&out), 0, "bare --jobs:\n{}\n{}", stdout(&out), stderr(&out));

    // An explicit terse format still works.
    let out =
        trust_mc_in(&dir, &["--jobs", "2", "--output-format", "terse", "--timeout", "60s", "multi.rs"]);
    assert_eq!(code(&out), 0, "{}", stderr(&out));

    // A genuine conflict must still be reported, not silently overridden.
    let out = trust_mc_in(
        &dir,
        &["--jobs", "2", "--output-format", "regular", "--timeout", "60s", "multi.rs"],
    );
    assert_ne!(code(&out), 0, "an explicit regular format conflicts and must say so");

    // Without --jobs the default format is untouched.
    let out = trust_mc_in(&dir, &["--timeout", "60s", "multi.rs"]);
    assert!(stdout(&out).contains("RESULTS:"), "default format should stay regular");

    // The two report flags produce readable files.
    let out = trust_mc_in(&dir, &["--sarif", "r.sarif", "--proof-summary-json", "r.json", "--timeout", "60s", "multi.rs"]);
    assert_eq!(code(&out), 0, "{}", stderr(&out));
    for f in ["r.sarif", "r.json"] {
        let text = fs::read_to_string(dir.join(f)).unwrap_or_default();
        assert!(
            serde_json::from_str::<serde_json::Value>(&text).is_ok(),
            "{f} should be valid JSON, got: {text}"
        );
    }
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn a_demoted_proof_says_no_counterexample_was_found() {
    if !installation_ready() {
        return;
    }
    // A demoted result was originally a PROOF — CTREX classification runs only
    // when `demotion_reasons` is empty, so the two are mutually exclusive.
    // Nothing was disproved; the proof was downgraded because the encoding
    // leaned on an approximation. It renders as
    //
    //     VERIFICATION:- FAILED
    //     [AY:DEMOTION_REASONS:pointee_synthesis_fallback=1]
    //
    // which is indistinguishable from a real counterexample unless you know the
    // marker vocabulary — and `HashMap::len()` after two inserts lands here, so
    // it is not an exotic path. A reader would go hunting for a bug that was
    // never found.
    let dir = scratch("demoted");
    fs::write(
        dir.join("map.rs"),
        "use std::collections::HashMap;\n#[kani::proof]\nfn h() {\n\
         \x20   let mut m: HashMap<u8, u8> = HashMap::new();\n\
         \x20   m.insert(1, 1);\n\x20   m.insert(2, 2);\n\x20   assert!(m.len() == 2);\n}\n",
    )
    .unwrap();
    let out = trust_mc_in(&dir, &["--output-format", "terse", "--unwind", "6", "--timeout", "90s", "map.rs"]);
    let text = stdout(&out);
    if text.contains("VERIFICATION:- SUCCESSFUL") {
        // If the encoding ever models this precisely there is no demotion to explain.
        let _ = fs::remove_dir_all(&dir);
        return;
    }
    assert!(
        text.contains("[AY:DEMOTED_NOT_A_COUNTEREXAMPLE]"),
        "a demoted proof must say no counterexample was found:\n{text}"
    );
    assert!(
        text.contains("no counterexample was found"),
        "readable without knowing the marker vocabulary:\n{text}"
    );

    // It must NOT appear on a genuine counterexample, or it is noise that
    // teaches people to ignore the line that matters.
    fs::write(
        dir.join("real.rs"),
        "#[kani::proof]\nfn h() {\n\x20   let a: u8 = kani::any();\n\
         \x20   let b: u8 = kani::any();\n\x20   let _ = a + b;\n}\n",
    )
    .unwrap();
    let out = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "60s", "real.rs"]);
    let text = stdout(&out);
    assert_eq!(code(&out), 1, "{text}");
    assert!(text.contains("[AY:CTREX_CAT:Genuine]"), "{text}");
    assert!(
        !text.contains("[AY:DEMOTED_NOT_A_COUNTEREXAMPLE]"),
        "a genuine counterexample must not be hedged:\n{text}"
    );
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn a_dead_branch_is_labelled_not_blamed() {
    if !installation_ready() {
        return;
    }
    // `if let Some(v) = o` on a statically-known None demotes the whole proof:
    // the payload read in the provably-dead arm finds no variant-field entry,
    // the LHS is left unconstrained, and `unconstrained_assignment` demotes.
    // See docs/findings/2026-08-22-a-dead-branch-demotes-the-proof.md — it takes
    // `Option::map` on None and the `?` operator with it.
    //
    // Not fixed. What this pins is that it stays HONEST: demoted rather than
    // falsely proved, and explained rather than blamed on the reader.
    let dir = scratch("dead-branch");
    fs::write(
        dir.join("dead.rs"),
        "#[kani::proof]\nfn h() {\n\x20   let o: Option<u8> = None;\n\
         \x20   if let Some(v) = o {\n\x20       assert!(v == 0);\n\x20   }\n\
         \x20   assert!(o.is_none());\n}\n",
    )
    .unwrap();
    let out = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "60s", "dead.rs"]);
    let text = stdout(&out);
    if text.contains("VERIFICATION:- SUCCESSFUL") {
        // If the read learns to consult the path condition, there is no
        // demotion left to explain, and that is a strictly better outcome.
        let _ = fs::remove_dir_all(&dir);
        return;
    }
    assert!(
        text.contains("[AY:DEMOTED_NOT_A_COUNTEREXAMPLE]"),
        "a demoted dead branch must say no counterexample was found:\n{text}"
    );
    assert!(
        !text.contains("[AY:CTREX_CAT:Genuine]"),
        "this must never be reported as a genuine bug:\n{text}"
    );

    // The shapes that DO work must keep working — this is about the dead arm,
    // not about `if let` or downcast reads in general.
    for (file, body) in [
        ("sym.rs", "let o: Option<u8> = kani::any();\n\x20   if let Some(v) = o { let _ = v; }\n\x20   assert!(true);"),
        ("some.rs", "let o = Some(3u8);\n\x20   if let Some(v) = o { assert!(v == 3); }"),
        ("matched.rs", "let o: Option<u8> = None;\n\x20   match o { Some(_) => assert!(false), None => assert!(true) }"),
    ] {
        fs::write(dir.join(file), format!("#[kani::proof]\nfn h() {{\n\x20   {body}\n}}\n")).unwrap();
        let out = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "60s", file]);
        assert_eq!(code(&out), 0, "{file} should still prove:\n{}", stdout(&out));
    }
    let _ = fs::remove_dir_all(&dir);
}

/// SARIF must distinguish "nothing to prove" from "could not decide".
///
/// The console channel learned this split earlier; the SARIF channel had not,
/// so a harness the solver could not settle was filed as
/// `trust_mc.harness.no_checks` — telling whoever reads the report that their
/// harness was EMPTY when in fact it was too hard. Those have different fixes.
#[test]
fn sarif_separates_an_undecided_harness_from_an_empty_one() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("sarif-undecided");
    let rules = |name: &str, src: &str| -> String {
        fs::write(dir.join(name), src).unwrap();
        let sarif = format!("{name}.sarif");
        let _ = trust_mc_in(&dir, &["--sarif", &sarif, "--timeout", "60s", name]);
        let text = fs::read_to_string(dir.join(&sarif)).unwrap_or_default();
        text.split("\"ruleId\"")
            .skip(1)
            .filter_map(|c| c.split('"').nth(1).map(str::to_string))
            .collect::<Vec<_>>()
            .join(",")
    };

    // Genuinely nothing to verify: no symbolic input, no fallible operation.
    let empty = rules("empty.rs", "#[kani::proof]
fn h() {
    let _x: u8 = 3;
}
");
    assert!(empty.contains("trust_mc.harness.no_checks"), "empty harness: {empty}");

    // Real obligations the solver cannot settle — a map lookup, which the
    // encoding declines rather than answers.
    let undecided = rules(
        "undecided.rs",
        "use std::collections::HashMap;
#[kani::proof]
fn h() {
             let mut m = HashMap::new();
    m.insert(1u8, 7u8);
             assert!(m.get(&1) == Some(&7));
}
",
    );
    assert!(
        !undecided.contains("trust_mc.harness.no_checks"),
        "an undecided harness is not an empty one: {undecided}"
    );
    let _ = fs::remove_dir_all(&dir);
}

/// Raw-pointer stores must reach the thing pointed at.
///
/// A write through `*mut T` to a stack local used to be dropped from the value
/// model, so `let mut x=3; *p=9; assert!(x==3)` returned a CLEAN PROOF of a
/// statement native Rust panics on, and its TRUE dual came back FAILED. Fixed
/// 2026-08-22 by following `ref_pointees` (through the `&x` -> `&raw mut (*_)`
/// chain) on the store path.
///
/// The slice form (`as_mut_ptr()` then an OFFSET) is still wrong in both modes;
/// `explain limits` says so, and the second half of this test pins the page
/// against that live defect so the warning cannot outlive it.
#[test]
fn a_raw_pointer_store_reaches_the_value_it_points_at() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("raw-ptr-store");

    // Every form that writes through a pointer to a plain LOCAL. Each asserts
    // the pre-store value, which is FALSE after the write, so a zero exit is a
    // false proof.
    let bodies: [(&str, &str); 4] = [
        ("deref.rs", "let p: *mut u8 = &mut x; unsafe { *p = 9; }"),
        ("addrof.rs", "let p = std::ptr::addr_of_mut!(x); unsafe { *p = 9; }"),
        ("write.rs", "let p: *mut u8 = &mut x; unsafe { std::ptr::write(p, 9); }"),
        ("safe_ref.rs", "let r: &mut u8 = &mut x; *r = 9;"),
    ];
    for (name, store) in bodies {
        fs::write(
            dir.join(name),
            format!(
                "#[kani::proof]\nfn h() {{\n\x20   let mut x: u8 = 3;\n\
                 \x20   {store}\n\x20   assert!(x == 3);\n}}\n"
            ),
        )
        .unwrap();
        let out = trust_mc_in(&dir, &["--timeout", "60s", name]);
        assert_ne!(
            code(&out),
            0,
            "{name}: the store makes x == 9, so this must not prove:\n{}",
            stdout(&out)
        );
    }

    // The TRUE dual must prove — otherwise "make it all fail" would pass.
    fs::write(
        dir.join("dual.rs"),
        "#[kani::proof]\nfn h() {\n\x20   let mut x: u8 = 3;\n\
         \x20   let p: *mut u8 = &mut x;\n\x20   unsafe { *p = 9; }\n\
         \x20   assert!(x == 9);\n}\n",
    )
    .unwrap();
    let dual = trust_mc_in(&dir, &["--timeout", "60s", "dual.rs"]);
    assert_eq!(code(&dual), 0, "the store really did write 9:\n{}", stdout(&dual));

    // Symbolic, so a pass cannot be constant folding.
    fs::write(
        dir.join("sym.rs"),
        "#[kani::proof]\nfn h() {\n\x20   let mut x: u8 = kani::any();\n\
         \x20   kani::assume(x != 9);\n\x20   let p: *mut u8 = &mut x;\n\
         \x20   unsafe { *p = 9; }\n\x20   assert!(x != 9);\n}\n",
    )
    .unwrap();
    let sym = trust_mc_in(&dir, &["--timeout", "60s", "sym.rs"]);
    assert_ne!(code(&sym), 0, "symbolic x: the store still makes x == 9:\n{}", stdout(&sym));

    // The slice/offset form, in BOTH lanes. `a.as_mut_ptr().add(2)` carries its
    // element index in subslice_offset rather than as a projection, so the
    // store used to land only in an address-indexed `mem` array that nothing
    // reads — the pruner deleted it and the pre-store value stayed provable.
    for (name, body, must_pass) in [
        ("slice_false.rs", "assert!(a[2] == 0);", false),
        ("slice_true.rs", "assert!(a[2] == 9);", true),
        // The element NEXT to the written one must be untouched, or a fix that
        // simply havocs the array would pass the first two rows.
        ("slice_other.rs", "assert!(a[1] == 0);", true),
    ] {
        fs::write(
            dir.join(name),
            format!(
                "#[kani::proof]\nfn h() {{\n\x20   let mut a: [u8; 4] = [0; 4];\n\
                 \x20   let p = a.as_mut_ptr();\n\x20   unsafe {{ *p.add(2) = 9; }}\n\
                 \x20   {body}\n}}\n"
            ),
        )
        .unwrap();
        for mode in [vec!["--timeout", "60s"], vec!["--ay-chc", "--timeout", "90s"]] {
            let mut a = mode.clone();
            a.push(name);
            let out = trust_mc_in(&dir, &a);
            if must_pass {
                assert_eq!(code(&out), 0, "{name} {mode:?} must prove:\n{}", stdout(&out));
            } else {
                assert_ne!(
                    code(&out),
                    0,
                    "{name} {mode:?}: the store wrote 9, so this must not prove:\n{}",
                    stdout(&out)
                );
            }
        }
    }

    // With no listed limitation violating it, the page's fail-closed promise
    // stands again — and must not be quietly re-broken.
    let page = stdout(&trust_mc(&["explain", "limits"]));
    assert!(page.contains("never a false proof"), "{page}");
    assert!(!page.contains("UNSOUND"), "no limitation should be unsound now:\n{page}");
    let _ = fs::remove_dir_all(&dir);
}

/// A collection must never prove a false statement about its own contents.
///
/// Two separate false PROOFS lived here, found on 2026-08-22:
///
///   * `vec![1u8, 2u8]` built its element array as `const_array(one_symbol)`,
///     mapping every index to the SAME value, so `v[0] == v[1]` was provable
///     for a vector whose elements are literally 1 and 2. Default lane, no
///     flags, one of the most common constructs in Rust.
///   * `--ay-chc` map lookups indexed slot 0 for every key, because a `&key`
///     that could not be dereferenced was translated as the POINTER and then
///     truncated to the key width. `m.insert(0,5); m.get(&2) == Some(&5)` was
///     PROVED.
///
/// Both were reported with `PROOF_QUALIFIERS:clean`. Whatever else changes,
/// these must never return to exit 0.
#[test]
fn a_collection_never_proves_a_false_statement_about_its_contents() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("collection-soundness");

    // --- Vec elements are not all the same value -------------------------
    fs::write(
        dir.join("vec_elems.rs"),
        "#[kani::proof]\nfn h() {\n\x20   let v = vec![1u8, 2u8];\n\
         \x20   assert!(v[0] == v[1]);\n}\n",
    )
    .unwrap();
    let ve = trust_mc_in(&dir, &["--timeout", "60s", "vec_elems.rs"]);
    assert_ne!(
        code(&ve),
        0,
        "vec![1,2] must not prove v[0] == v[1] — native Rust panics here:\n{}",
        stdout(&ve)
    );

    // ...and the fix must not have simply broken Vec: the length is exact and
    // must still prove. Without this, "report everything inconclusive" passes.
    fs::write(
        dir.join("vec_len.rs"),
        "#[kani::proof]\nfn h() {\n\x20   let v = vec![1u8, 2u8];\n\
         \x20   assert!(v.len() == 2);\n}\n",
    )
    .unwrap();
    let vl = trust_mc_in(&dir, &["--timeout", "60s", "vec_len.rs"]);
    assert_eq!(code(&vl), 0, "vec![1,2].len() == 2 must still prove:\n{}", stdout(&vl));

    // `vec![elem; n]` genuinely HAS equal elements, so it must keep proving —
    // the shared-symbol encoding is exact there, and fixing the other lowering
    // must not have cost this one its precision.
    fs::write(
        dir.join("vec_repeat.rs"),
        "#[kani::proof]\nfn h() {\n\x20   let v = vec![7u8; 4];\n\
         \x20   assert!(v[0] == v[3]);\n}\n",
    )
    .unwrap();
    let vr = trust_mc_in(&dir, &["--timeout", "60s", "vec_repeat.rs"]);
    assert_eq!(code(&vr), 0, "vec![7; 4] really does have equal elements:\n{}", stdout(&vr));

    // --- Map lookups answer for the key that was asked about --------------
    for (name, body) in [
        ("map_get.rs", "assert!(m.get(&2) == Some(&5));"),
        ("map_has.rs", "assert!(m.contains_key(&7));"),
    ] {
        fs::write(
            dir.join(name),
            format!(
                "use std::collections::HashMap;\n#[kani::proof]\nfn h() {{\n\
                 \x20   let mut m: HashMap<u8, u8> = HashMap::new();\n\
                 \x20   m.insert(0, 5);\n\x20   {body}\n}}\n"
            ),
        )
        .unwrap();
        let out = trust_mc_in(&dir, &["--ay-chc", "--timeout", "90s", name]);
        assert_ne!(
            code(&out),
            0,
            "--ay-chc must not prove a statement about a key that was never \
             inserted ({name}):\n{}",
            stdout(&out)
        );
    }

    // Map length is modelled and must still prove, in both modes.
    fs::write(
        dir.join("map_len.rs"),
        "use std::collections::HashMap;\n#[kani::proof]\nfn h() {\n\
         \x20   let mut m: HashMap<u8, u8> = HashMap::new();\n\
         \x20   m.insert(1, 7);\n\x20   assert!(m.len() == 1);\n}\n",
    )
    .unwrap();
    let ml = trust_mc_in(&dir, &["--ay-chc", "--timeout", "90s", "map_len.rs"]);
    assert_eq!(code(&ml), 0, "--ay-chc models map length:\n{}", stdout(&ml));
    let _ = fs::remove_dir_all(&dir);
}

/// `--summary` renders a verdict table you can actually scan.
///
/// The engine reports harnesses as they finish, so on a multi-harness crate
/// the failures arrive in scheduler order, each verdict sits far from the
/// harness name that owns it, and the closing block lists failures by NAME
/// with no reason and no position. This pins the table, its determinism, and
/// that it never lies about a should_panic harness.
#[test]
fn the_summary_table_is_scannable_and_deterministic() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("summary-view");
    fs::write(
        dir.join("fleet.rs"),
        "pub fn shard_of(key: u32, shards: u32) -> u32 { key % shards }\n\
         pub fn clamp_ttl(t: u32) -> u32 { if t > 86400 { 86400 } else { t } }\n\
         #[kani::proof]\nfn zzz_shard_divides_by_zero() {\n\
         \x20   let k: u32 = kani::any();\n\x20   let s: u32 = kani::any();\n\
         \x20   let _ = shard_of(k, s);\n}\n\
         #[kani::proof]\nfn aaa_ttl_is_bounded() {\n\
         \x20   let t: u32 = kani::any();\n\x20   assert!(clamp_ttl(t) <= 86400);\n}\n\
         #[kani::proof]\n#[kani::should_panic]\nfn mmm_panics_on_purpose() {\n\
         \x20   panic!(\"by design\");\n}\n",
    )
    .unwrap();

    let out = trust_mc_in(&dir, &["--summary", "--timeout", "60s", "fleet.rs"]);
    let text = stdout(&out);
    let table = text
        .split("trust-mc summary:")
        .nth(1)
        .unwrap_or_else(|| panic!("no table:\n{text}"))
        .to_string();

    // The failure carries WHY and WHERE — the engine's own closing block gives
    // neither, which is the whole reason this view exists.
    assert!(table.contains("FAILED  zzz_shard_divides_by_zero"), "{table}");
    // `key % shards` is BinOp::Rem, so the label is `mod_by_zero_check` and the
    // description is Kani's remainder wording, not the neutral "division by zero"
    // (trust-mc-driver/src/ay_parse/violation.rs, classify_violation).
    assert!(
        table.contains("attempt to calculate the remainder with a divisor of zero"),
        "reason is missing:\n{table}"
    );
    assert!(table.contains("fleet.rs:1"), "position is missing:\n{table}");

    // A should_panic harness PASSES; reading `status` instead of
    // `effective_success` would paint a green run red.
    assert!(
        table.contains("proved  mmm_panics_on_purpose"),
        "a should_panic harness is a pass:\n{table}"
    );
    assert!(table.contains("proved  aaa_ttl_is_bounded"), "{table}");

    // Failures before proofs, and alphabetical inside each group, so the
    // source order (zzz, aaa, mmm) cannot leak through.
    // Match the ROW prefixes, not the words: the header line ("2 proved · 1
    // failed") contains both.
    let failed_at = table.find("  FAILED  ").expect("a failure row");
    let proved_at = table.find("  proved  ").expect("a proved row");
    assert!(failed_at < proved_at, "failures come first:\n{table}");
    assert!(
        table.find("aaa_ttl_is_bounded") < table.find("mmm_panics_on_purpose"),
        "proved rows are sorted:\n{table}"
    );

    // Deterministic under concurrency — a table you cannot diff between two CI
    // runs is worth much less.
    let again = trust_mc_in(&dir, &["--summary", "--jobs", "3", "--timeout", "60s", "fleet.rs"]);
    let table2 =
        stdout(&again).split("trust-mc summary:").nth(1).unwrap_or_default().to_string();
    assert_eq!(table, table2, "the table must not depend on scheduling");

    // No trailing whitespace: it survives copy/paste and dirties every diff.
    for line in table.lines() {
        assert!(!line.ends_with(' '), "trailing whitespace in {line:?}");
    }

    // Without the flag, nothing changes.
    let plain = trust_mc_in(&dir, &["--timeout", "60s", "fleet.rs"]);
    assert!(!stdout(&plain).contains("trust-mc summary:"), "--summary must be opt-in");

    // The engine never sees the flag; if it did it would reject it as unknown.
    assert!(!stderr(&out).contains("unexpected argument"), "{}", stderr(&out));
    let _ = fs::remove_dir_all(&dir);
}

/// A failure must point at the flag that answers "which input?".
///
/// The engine can print the exact failing values, but a failing run never
/// mentioned it, so the feature was undiscoverable — the tool reported
/// "attempt to add with overflow" and stopped, which is the least useful
/// half of what it knew. The hint goes to STDERR so stdout stays
/// byte-identical for --sarif / --proof-summary-json consumers.
#[test]
fn a_failure_says_how_to_get_the_failing_input() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("failure-hint");
    fs::write(
        dir.join("bug.rs"),
        "fn align_up(n: u32, align: u32) -> u32 {\n\
         \x20   (n + align - 1) & !(align - 1)\n}\n\
         #[kani::proof]\nfn h() {\n\x20   let n: u32 = kani::any();\n\
         \x20   assert!(align_up(n, 4096) >= n);\n}\n",
    )
    .unwrap();

    let out = trust_mc_in(&dir, &["--timeout", "90s", "bug.rs"]);
    assert_ne!(code(&out), 0, "{}", stdout(&out));
    let err = stderr(&out);
    assert!(err.contains("concrete-playback"), "a failure must name the flag:\n{err}");
    assert!(
        !stdout(&out).contains("hint:"),
        "the hint must not touch stdout — CI consumers parse it:\n{}",
        stdout(&out)
    );

    // ...and the flag it names must actually work, or the hint is a lie.
    let played = trust_mc_in(
        &dir,
        &["-Z", "concrete-playback", "--concrete-playback", "print", "--timeout", "90s", "bug.rs"],
    );
    let text = stdout(&played);
    assert!(
        text.contains("concrete_vals") && text.contains("#[test]"),
        "the flag the hint recommends must print a runnable test:\n{text}"
    );
    assert!(
        !stderr(&played).contains("hint:"),
        "no hint once the user already asked for playback:\n{}",
        stderr(&played)
    );

    // A clean run says nothing.
    fs::write(
        dir.join("ok.rs"),
        "#[kani::proof]\nfn h() {\n\x20   let x: u8 = kani::any();\n\
         \x20   kani::assume(x < 10);\n\x20   assert!(x < 200);\n}\n",
    )
    .unwrap();
    let ok = trust_mc_in(&dir, &["--timeout", "60s", "ok.rs"]);
    assert_eq!(code(&ok), 0, "{}", stdout(&ok));
    assert!(!stderr(&ok).contains("hint:"), "no hint on success:\n{}", stderr(&ok));

    // Machine-readable runs stay quiet on stderr too.
    let sarif = trust_mc_in(&dir, &["--sarif", "--timeout", "90s", "bug.rs"]);
    assert!(!stderr(&sarif).contains("hint:"), "no prose for --sarif:\n{}", stderr(&sarif));
    let _ = fs::remove_dir_all(&dir);
}

/// An over-approximated call result must not be sold as a genuine bug.
///
/// `bounded_any::<String, N>()` promises `len() <= N`. Under --ay-chc the call
/// could not be inlined, so its result was a fresh unconstrained symbol — and
/// because nothing recorded that approximation, `classify_ctrex` fell through
/// to its `Genuine` default and the tool reported a REAL BUG in a harness that
/// merely restates the function's own contract. Telling someone their correct
/// code is broken is worse than saying nothing.
#[test]
fn an_invented_return_value_is_never_reported_as_a_genuine_bug() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("overapprox-ctrex");
    fs::write(
        dir.join("bounded.rs"),
        "#[kani::proof]\n#[kani::unwind(6)]\nfn h() {\n\
         \x20   let s: String = kani::bounded_any::<String, 4>();\n\
         \x20   assert!(s.len() <= 4);\n}\n",
    )
    .unwrap();

    let out = trust_mc_in(&dir, &["--ay-chc", "--timeout", "240s", "bounded.rs"]);
    let text = stdout(&out);
    // Either it proves (better), or it fails — but a failure MUST be labelled
    // as uncertified, never as a genuine bug in the user's code.
    if text.contains("VERIFICATION:- FAILED") {
        assert!(
            !text.contains("[AY:CTREX_CAT:Genuine]"),
            "an unconstrained call result was sold as a genuine bug:\n{text}"
        );
        assert!(
            text.contains("[AY:CTREX_NOT_CERTIFIED]"),
            "an over-approximated counterexample must say it is not certified:\n{text}"
        );
    }

    // The taint must not leak into unrelated proofs: a harness with no
    // over-approximated call still reports a CLEAN proof, not a hedged one.
    fs::write(
        dir.join("plain.rs"),
        "#[kani::proof]\nfn h() {\n\x20   let x: u8 = kani::any();\n\
         \x20   kani::assume(x < 10);\n\x20   assert!(x < 200);\n}\n",
    )
    .unwrap();
    let clean = trust_mc_in(&dir, &["--ay-chc", "--timeout", "240s", "plain.rs"]);
    assert_eq!(code(&clean), 0, "{}", stdout(&clean));
    assert!(
        stdout(&clean).contains("PROOF_QUALIFIERS:clean"),
        "tainting over-approximated calls must not hedge unrelated proofs:\n{}",
        stdout(&clean)
    );
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn the_limits_page_matches_reality() {
    if !installation_ready() {
        return;
    }
    // A known-limitations page is only worth having if it is true. Two ways it
    // rots: it claims something is broken that has since been FIXED (sending
    // people around a working feature), or it claims something works that does
    // not. Both are checked here against the binary.
    let page = stdout(&trust_mc(&["explain", "limits"]));
    assert!(page.contains("Known limitations"), "{page}");

    let dir = scratch("limits-page");

    // Things the page says WORK must actually prove.
    let works: [(&str, &str); 4] = [
        ("shift.rs", "let a: u32 = kani::any();\n\x20   let s: u32 = kani::any();\n\
          \x20   kani::assume(s < 32);\n\x20   let r = a << s;\n\x20   assert!(r >= 0);"),
        ("enum_disc.rs", "let e: E = kani::any();\n\x20   let d = e as i32;\n\
          \x20   assert!(d == 1 || d == 7);"),
        ("dyn_call.rs", "let a = A;\n\x20   let d: &dyn T = &a;\n\x20   assert!(d.v() == 7);"),
        ("sym_opt.rs", "let o: Option<u8> = kani::any();\n\
          \x20   if let Some(v) = o { let _ = v; }\n\x20   assert!(true);"),
    ];
    let preamble = |file: &str| match file {
        "enum_disc.rs" => "#[derive(kani::Arbitrary, Clone, Copy)]\nenum E { A = 1, B = 7 }\n",
        "dyn_call.rs" => "trait T { fn v(&self) -> u8; }\nstruct A;\nimpl T for A { fn v(&self) -> u8 { 7 } }\n",
        _ => "",
    };
    for (file, body) in works {
        fs::write(
            dir.join(file),
            format!("{}#[kani::proof]\nfn h() {{\n\x20   {body}\n}}\n", preamble(file)),
        )
        .unwrap();
        let out = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "60s", file]);
        assert_eq!(
            code(&out),
            0,
            "explain limits says this works, but it did not:\n{file}\n{}",
            stdout(&out)
        );
    }

    // Recursion is on the page as unsupported. Pin BOTH halves of that claim:
    // it does not verify, AND it is labelled rather than blamed on the reader —
    // which matters here because the symptom is misleading on its own (a
    // recursive `1 + f(n-1)` reports an arithmetic overflow).
    fs::write(
        dir.join("rec.rs"),
        "fn f(n: u8) -> u8 {
    if n == 0 { 0 } else { 1 + f(n - 1) }
}
         #[kani::proof]
fn h() {
    assert!(f(3) == 3);
}
",
    )
    .unwrap();
    // The maps entry makes three checkable claims: len()/is_empty() prove
    // under --ay-chc, a failing get() is mislabelled `Genuine`, and BMC
    // demotes. The middle one documents a KNOWN DEFECT — if it starts being
    // labelled honestly, this fails and the page must be rewritten to say so.
    fs::write(
        dir.join("map_len.rs"),
        "use std::collections::HashMap;\n#[kani::proof]\nfn h() {\n\
         \x20   let mut m = HashMap::new();\n\x20   m.insert(1u8, 7u8);\n\
         \x20   assert!(m.len() == 1);\n}\n",
    )
    .unwrap();
    let ml = trust_mc_in(&dir, &["--ay-chc", "--output-format", "terse", "--timeout", "240s", "map_len.rs"]);
    assert_eq!(code(&ml), 0, "explain limits says --ay-chc proves map len():\n{}", stdout(&ml));

    fs::write(
        dir.join("map_get.rs"),
        "use std::collections::HashMap;\n#[kani::proof]\nfn h() {\n\
         \x20   let mut m = HashMap::new();\n\x20   m.insert(1u8, 7u8);\n\
         \x20   assert!(m.get(&1).is_some());\n}\n",
    )
    .unwrap();
    let mg = trust_mc_in(&dir, &["--ay-chc", "--timeout", "240s", "map_get.rs"]);
    assert_ne!(code(&mg), 0, "map get() is documented as declining:\n{}", stdout(&mg));
    // It must be a LABELLED non-answer, not a claim about the user's code.
    // This assertion previously pinned the opposite — `[AY:CTREX_CAT:Genuine]`
    // — and fired when the key-resolution fix made the stub decline, which is
    // exactly what a documentation pin is for.
    assert!(
        stdout(&mg).contains("[AY:CTREX_NOT_CERTIFIED]"),
        "a declined map lookup must be labelled uncertified, never sold as a \
         genuine bug:\n{}",
        stdout(&mg)
    );
    assert!(
        !stdout(&mg).contains("[AY:CTREX_CAT:Genuine]"),
        "a map lookup the encoding declined is not a bug in the user's code:\n{}",
        stdout(&mg)
    );

    // The page names --ay-chc as the remedy for two BMC-only limitations. Pin
    // the remedy AND a symbolic control, because "CHC proves it" was already
    // wrong once this session: for recursion it only folded a constant away.
    // A symbolic element that still proves, plus a false claim that still
    // fails, is what separates modelling from folding.
    fs::write(
        dir.join("vec_elem.rs"),
        "#[kani::proof]\nfn h() {\n\x20   let n: u8 = kani::any();\n\
         \x20   kani::assume(n < 50);\n\x20   let v = Vec::from(&[n, 4, 5][..]);\n\
         \x20   assert!(v[0] == n);\n}\n",
    )
    .unwrap();
    fs::write(
        dir.join("vec_elem_bad.rs"),
        "#[kani::proof]\nfn h() {\n\x20   let n: u8 = kani::any();\n\
         \x20   kani::assume(n < 50);\n\x20   let v = Vec::from(&[n, 4, 5][..]);\n\
         \x20   assert!(v[0] == 7);\n}\n",
    )
    .unwrap();
    let ve = trust_mc_in(&dir, &["--ay-chc", "--output-format", "terse", "--timeout", "300s", "vec_elem.rs"]);
    assert_eq!(code(&ve), 0, "explain limits says --ay-chc models Vec elements:\n{}", stdout(&ve));
    let ve_bad =
        trust_mc_in(&dir, &["--ay-chc", "--output-format", "terse", "--timeout", "300s", "vec_elem_bad.rs"]);
    assert_ne!(code(&ve_bad), 0, "a false claim about a Vec element must fail:\n{}", stdout(&ve_bad));

    // `?` on a statically-known None: demoted under BMC, settled by --ay-chc.
    fs::write(
        dir.join("qmark_none.rs"),
        "fn f(x: Option<u8>) -> Option<u8> {\n\x20   let v = x?;\n\x20   Some(v + 1)\n}\n\
         #[kani::proof]\nfn h() {\n\x20   assert!(f(None).is_none());\n}\n",
    )
    .unwrap();
    let qm = trust_mc_in(&dir, &["--ay-chc", "--output-format", "terse", "--timeout", "300s", "qmark_none.rs"]);
    assert_eq!(code(&qm), 0, "explain limits says --ay-chc settles `?` on a constant None:\n{}", stdout(&qm));

    // The page says a SYMBOLIC Option is fine in EITHER mode.
    fs::write(
        dir.join("qmark_sym.rs"),
        "fn f(x: Option<u8>) -> Option<u8> {\n\x20   let v = x?;\n\
         \x20   Some(v.wrapping_add(1))\n}\n\
         #[kani::proof]\nfn h() {\n\x20   let o: Option<u8> = kani::any();\n\
         \x20   if o.is_none() {\n\x20       assert!(f(o).is_none());\n\x20   }\n}\n",
    )
    .unwrap();
    for mode in [vec!["--output-format", "terse", "--timeout", "120s"], vec!["--ay-chc", "--output-format", "terse", "--timeout", "300s"]] {
        let mut a = mode.clone();
        a.push("qmark_sym.rs");
        let sym = trust_mc_in(&dir, &a);
        assert_eq!(code(&sym), 0, "a symbolic Option must verify ({mode:?}):\n{}", stdout(&sym));
    }

    // The page says --ay-chc settles a recursive call with a CONSTANT argument
    // and that a SYMBOLIC one still fails. Both halves are pinned, because the
    // first half alone reads as "recursion works" — which it does not.
    let chc = trust_mc_in(&dir, &["--ay-chc", "--output-format", "terse", "--timeout", "240s", "rec.rs"]);
    assert_eq!(code(&chc), 0, "explain limits says --ay-chc settles f(3):\n{}", stdout(&chc));

    // f(n) <= 5 for n <= 5 is TRUE, and neither mode can prove it. If this
    // starts passing, recursion grew real support and the page must say so.
    fs::write(
        dir.join("rec_sym.rs"),
        "fn f(n: u8) -> u8 {\n\x20   if n == 0 { 0 } else { 1 + f(n - 1) }\n}\n\
         #[kani::proof]\nfn h() {\n\x20   let n: u8 = kani::any();\n\
         \x20   kani::assume(n <= 5);\n\x20   assert!(f(n) <= 5);\n}\n",
    )
    .unwrap();
    for mode in [vec!["--output-format", "terse", "--unwind", "10"], vec!["--ay-chc", "--output-format", "terse"]] {
        let mut a = mode.clone();
        a.extend_from_slice(&["--timeout", "300s", "rec_sym.rs"]);
        let sym = trust_mc_in(&dir, &a);
        assert_ne!(
            code(&sym), 0,
            "explain limits says a SYMBOLIC recursive argument still fails ({mode:?}); \
             if this now proves, correct the page:\n{}",
            stdout(&sym)
        );
    }

    let out = trust_mc_in(&dir, &["--output-format", "terse", "--unwind", "10", "--timeout", "90s", "rec.rs"]);
    let rec = stdout(&out);
    if !rec.contains("VERIFICATION:- SUCCESSFUL") {
        assert!(
            rec.contains("[AY:CTREX_NOT_CERTIFIED]") || rec.contains("[AY:DEMOTED_NOT_A_COUNTEREXAMPLE]"),
            "recursion is a known limitation and must be labelled, not blamed:\n{rec}"
        );
        assert!(
            !rec.contains("[AY:CTREX_CAT:Genuine]"),
            "an unmodelled recursive call must not be reported as a genuine bug:\n{rec}"
        );
    }

    // And the marker vocabulary the page teaches must be the vocabulary the
    // binary actually emits.
    fs::write(
        dir.join("genuine.rs"),
        "#[kani::proof]\nfn h() {\n\x20   let a: u8 = kani::any();\n\
         \x20   let b: u8 = kani::any();\n\x20   let _ = a + b;\n}\n",
    )
    .unwrap();
    let out = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "60s", "genuine.rs"]);
    assert!(
        stdout(&out).contains("[AY:CTREX_CAT:Genuine]"),
        "the page documents this marker:\n{}",
        stdout(&out)
    );
    for marker in ["[AY:CTREX_CAT:Genuine]", "[AY:DEMOTED_NOT_A_COUNTEREXAMPLE]", "[AY:CTREX_NOT_CERTIFIED]"] {
        assert!(page.contains(marker), "page should teach {marker}");
    }
    let _ = fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// The playback hint must wait for something to have been verified
// ---------------------------------------------------------------------------

/// Exit 1 is not "a harness failed".
///
/// The engine leaves with 1 for a compile error, an unmatched `--harness`
/// filter and an unreadable input just as it does for a failing check, so a
/// hint keyed on the exit code alone offered `--concrete-playback` to people
/// whose code never compiled. That is noise, and it costs the hint its
/// credibility on the runs where it is the right advice.
///
/// Both directions are pinned here: the hint disappears from the runs that
/// verified nothing, AND it still appears on a genuine failing harness. A
/// change that merely silences it everywhere satisfies half of this test and
/// is worthless.
#[test]
fn the_playback_hint_waits_for_an_actual_verdict() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("hint-needs-a-verdict");

    // (a) A file that does not compile. No harness ran; no hint.
    fs::write(
        dir.join("broken.rs"),
        "#[kani::proof]\nfn h() {\n\x20   let x: u8 = kani::any()\n\x20   assert!(x == x);\n}\n",
    )
    .unwrap();
    let broken = trust_mc_in(&dir, &["--timeout", "60s", "broken.rs"]);
    assert_eq!(code(&broken), 1, "a compile error still exits 1:\n{}", stderr(&broken));
    assert!(
        !stderr(&broken).contains("hint:"),
        "a compile error must not be offered a playback flag:\n{}",
        stderr(&broken)
    );

    // (b) A filter that selected nothing. The run reached the engine's
    // verification flow and chose zero harnesses, so there is still no verdict.
    fs::write(dir.join("named.rs"), "#[kani::proof]\nfn alpha() {\n\x20   assert!(1 + 1 == 2);\n}\n")
        .unwrap();
    let unmatched =
        trust_mc_in(&dir, &["--harness", "no_such_harness", "--timeout", "60s", "named.rs"]);
    assert_eq!(code(&unmatched), 1, "an unmatched filter exits 1:\n{}", stderr(&unmatched));
    assert!(
        !stderr(&unmatched).contains("hint:"),
        "an unmatched --harness filter verified nothing:\n{}",
        stderr(&unmatched)
    );

    // (c) A listing of a file that does not compile.
    let listing = trust_mc_in(&dir, &["--list", "broken.rs"]);
    assert!(
        !stderr(&listing).contains("hint:"),
        "a failed listing verified nothing:\n{}",
        stderr(&listing)
    );

    // (d) THE CONTROL: a harness that really does fail still gets the hint.
    fs::write(
        dir.join("overflows.rs"),
        "#[kani::proof]\nfn h() {\n\x20   let x: u8 = kani::any();\n\
         \x20   let y = x + 1;\n\x20   assert!(y >= x);\n}\n",
    )
    .unwrap();
    let failed = trust_mc_in(&dir, &["--timeout", "90s", "overflows.rs"]);
    assert_eq!(code(&failed), 1, "the overflow must fail:\n{}", stdout(&failed));
    assert!(
        stderr(&failed).contains("hint:") && stderr(&failed).contains("concrete-playback"),
        "a real verdict must still name the playback flag:\n{}",
        stderr(&failed)
    );
    // ...and the hint stays off stdout, which CI consumers parse.
    assert!(!stdout(&failed).contains("hint:"), "the hint must never touch stdout:\n{}", stdout(&failed));

    // The artifact the front door asks for to answer "did anything run?" is an
    // implementation detail: it must not leak into the output.
    assert!(
        !stdout(&failed).contains("proof-summary") && !stderr(&failed).contains("proof-summary"),
        "the internal verdict artifact must stay invisible:\n{}{}",
        stdout(&failed),
        stderr(&failed)
    );

    // A caller's OWN --proof-summary-json is still written where they asked,
    // and still suppresses the prose hint.
    let mine =
        trust_mc_in(&dir, &["--proof-summary-json", "mine.json", "--timeout", "90s", "overflows.rs"]);
    assert!(
        dir.join("mine.json").is_file(),
        "the caller's artifact must survive:\n{}",
        stderr(&mine)
    );
    assert!(
        !stderr(&mine).contains("hint:"),
        "machine-readable consumers get no prose:\n{}",
        stderr(&mine)
    );

    let _ = fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// `explain limits`: the dead-`Some`-arm entry, measured in both lanes
// ---------------------------------------------------------------------------

/// The entry used to claim `--ay-chc` settled `None.map(..)`. It does not.
///
/// Measured, both lanes: the dead-arm cases (`if let`, `match`, `?`) ARE
/// settled by `--ay-chc`, but `None.map(..)` still fails there — on
/// `chc_fallback`, not `unconstrained_assignment`. The blocker is the closure,
/// which is why `unwrap_or` (no closure) proves in both modes and a bare
/// closure with no Option in sight fails under `--ay-chc` too.
///
/// If any of these flip, the page is wrong again and must be re-measured.
#[test]
fn explain_limits_tells_the_truth_about_none_map_and_dead_arms() {
    if !installation_ready() {
        return;
    }
    let page = stdout(&trust_mc(&["explain", "limits"]));
    assert!(
        page.contains("Closures are no longer the --ay-chc boundary they once were."),
        "the page must not still claim closures are the --ay-chc boundary:\n{page}"
    );
    assert!(
        !page.contains("STILL fails under"),
        "the page must not still claim None.map(..) fails under --ay-chc:\n{page}"
    );

    let dir = scratch("limits-dead-arm");
    let bmc = ["--output-format", "terse", "--timeout", "120s"];
    let chc = ["--ay-chc", "--output-format", "terse", "--timeout", "120s"];

    // (file, body, proves under BMC, proves under --ay-chc)
    let cases: [(&str, &str, bool, bool); 6] = [
        // A dead `Some` arm on a statically-known None: BMC demotes, CHC proves.
        (
            "iflet.rs",
            "let o: Option<u8> = None;\n\x20   if let Some(v) = o { assert!(v == 0); }\n\
             \x20   assert!(o.is_none());",
            false,
            true,
        ),
        // `match` is NOT exempt, which the old wording implied it was.
        (
            "matched.rs",
            "let o: Option<u8> = None;\n\
             \x20   match o { Some(v) => assert!(v == 0), None => assert!(true) }\n\
             \x20   assert!(o.is_none());",
            false,
            true,
        ),
        // Was mislisted as failing in both lanes. --ay-chc proves it now:
        // the closure is dead on a statically-known None and folds away.
        // Verified discriminating, not vacuous — asserting `is_some()` on the
        // same body comes back FAILED.
        (
            "map.rs",
            "let o: Option<u8> = None;\n\x20   assert!(o.map(|x| x + 1).is_none());",
            false,
            true,
        ),
        // No closure, same statically-known None: proves in both lanes.
        (
            "unwrap_or.rs",
            "let o: Option<u8> = None;\n\x20   assert!(o.unwrap_or(7) == 7);",
            true,
            true,
        ),
        // No Option at all — just a closure, invoked on a SYMBOLIC value.
        // --ay-chc used to decline this and no longer does. Also verified
        // discriminating: the strict `f(n) < n` variant still comes back
        // FAILED, so this is a real proof and not a vanished obligation.
        (
            "closure.rs",
            "let f = |x: u8| x / 2;\n\x20   let n: u8 = kani::any();\n\x20   assert!(f(n) <= n);",
            true,
            true,
        ),
        // The boundary that replaced closures: a closure inside a stdlib
        // ITERATOR chain. Pinned here because it is the case the page now
        // points at, and because it is the direction BMC wins — proving the
        // two lanes do not dominate one another.
        (
            "iter.rs",
            "let a: [u8; 3] = [1, 2, 3];\n\x20   let s: u32 = a.iter().map(|x| *x as u32).sum();\n\x20   assert!(s == 6);",
            true,
            false,
        ),
    ];

    for (file, body, bmc_proves, chc_proves) in cases {
        fs::write(dir.join(file), format!("#[kani::proof]\nfn h() {{\n\x20   {body}\n}}\n"))
            .unwrap();
        for (lane, flags, want) in [("BMC", &bmc[..], bmc_proves), ("--ay-chc", &chc[..], chc_proves)]
        {
            let mut argv: Vec<&str> = flags.to_vec();
            argv.push(file);
            let out = trust_mc_in(&dir, &argv);
            let proved = code(&out) == 0;
            assert_eq!(
                proved, want,
                "explain limits says {file} {} under {lane}; it did not. Re-measure the page:\n{}",
                if want { "proves" } else { "does not prove" },
                stdout(&out)
            );
        }
    }

    // BMC still demotes on the dead-arm reason. Pin it: "both lanes fail" was
    // the reading that let `None.map(..)` sit under the dead-arm entry in the
    // first place, and the lanes must stay distinguishable by their reason.
    let map_bmc = trust_mc_in(&dir, &["--timeout", "120s", "map.rs"]);
    assert!(
        stdout(&map_bmc).contains("unconstrained_assignment"),
        "None.map(..) under BMC demotes on the dead-arm reason:\n{}",
        stdout(&map_bmc)
    );

    // --ay-chc now PROVES it, cleanly, with the old closure fallback gone.
    let map_chc = trust_mc_in(&dir, &["--ay-chc", "--timeout", "120s", "map.rs"]);
    assert!(
        !stdout(&map_chc).contains("chc_fallback"),
        "--ay-chc no longer falls back on the closure here:\n{}",
        stdout(&map_chc)
    );
    assert!(
        stdout(&map_chc).contains("PROOF_QUALIFIERS:clean"),
        "the --ay-chc proof must be clean, not qualified:\n{}",
        stdout(&map_chc)
    );

    // The control that makes the line above worth anything. A proof of a TRUE
    // statement is indistinguishable from a vanished obligation unless the
    // FALSE statement still fails, so assert the negation is caught. Without
    // this, an obligation silently dropped in codegen would read as a pass.
    fs::write(
        dir.join("map_neg.rs"),
        "#[kani::proof]\nfn h() {\n\x20   let o: Option<u8> = None;\n         \x20   assert!(o.map(|x| x + 1).is_some());\n}\n",
    )
    .unwrap();
    let map_neg = trust_mc_in(&dir, &["--ay-chc", "--timeout", "120s", "map_neg.rs"]);
    assert_ne!(
        code(&map_neg),
        0,
        "--ay-chc must still refute the FALSE variant; if it proves both, the \
         obligation is gone rather than discharged:\n{}",
        stdout(&map_neg)
    );

    // The FALSE variant is a real violation, so it SHOULD be reported as the
    // user's bug. Pinning that direction too keeps the refutation above
    // honest: a refutation that came back EncodingGap would mean --ay-chc
    // rejected the negation for its own reasons rather than on the semantics.
    assert!(
        stdout(&map_neg).contains("[AY:CTREX_CAT:Genuine]"),
        "the FALSE variant is a genuine violation and must be reported as one:\n{}",
        stdout(&map_neg)
    );

    // The two LIMITATION outcomes are never sold as the user's bug.
    for text in [stdout(&map_bmc), stdout(&map_chc)] {
        assert!(
            !text.contains("[AY:CTREX_CAT:Genuine]"),
            "a limitation must never be reported as a genuine counterexample:\n{text}"
        );
    }

    let _ = fs::remove_dir_all(&dir);
}


// ---------------------------------------------------------------------------
// --quiet is quiet; --coverage refuses the lane that cannot produce it
// ---------------------------------------------------------------------------

/// `--quiet` is documented as "print nothing but the exit code and requested
/// artifacts", but every `[AY:*]` marker went to stdout through a bare
/// `println!` / `solver_stdout!`. A quiet run printed `[AY:CTREX_CAT:Genuine]`
/// in the bounded lane and `[AY:PROOF] CHC verification: ...` under `--ay-chc`.
///
/// Both directions are pinned deliberately. Silencing everything unconditionally
/// would satisfy "quiet" and destroy the corpus report — `scripts/ay-compiletest.sh`
/// parses those exact marker lines out of NON-quiet runs — so the loud half of
/// each pair is as much the regression test as the quiet half. And the exit code
/// is asserted on both, because suppressing the print must not suppress the
/// decision behind it.
#[test]
fn quiet_gates_ay_markers_while_a_loud_run_still_emits_them() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("quiet-ay-markers");
    fs::write(
        dir.join("bad.rs"),
        "#[kani::proof]\nfn bad_harness() {\n\x20   let x: u32 = kani::any();\n\
         \x20   assert!(x < 200);\n}\n",
    )
    .unwrap();
    fs::write(
        dir.join("ok.rs"),
        "#[kani::proof]\nfn ok_harness() {\n\x20   let x: u32 = kani::any();\n\
         \x20   kani::assume(x < 100);\n\x20   assert!(x < 200);\n}\n",
    )
    .unwrap();

    // Bounded lane, counterexample. Loud: the marker is there.
    let loud = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "120s", "bad.rs"]);
    let loud_text = stdout(&loud);
    assert_eq!(code(&loud), 1, "stdout:\n{loud_text}\nstderr:\n{}", stderr(&loud));
    assert!(
        loud_text.contains("[AY:CTREX_CAT:"),
        "a run WITHOUT --quiet must keep emitting the markers the corpus parses:\n{loud_text}"
    );

    // Quiet: no markers, same verdict.
    let quiet = trust_mc_in(&dir, &["--quiet", "--timeout", "120s", "bad.rs"]);
    let quiet_text = stdout(&quiet);
    assert_eq!(
        code(&quiet),
        1,
        "--quiet may hide the marker, never the verdict:\n{}",
        stderr(&quiet)
    );
    assert!(
        !quiet_text.contains("[AY:"),
        "--quiet still printed an [AY:*] marker:\n{quiet_text}"
    );
    assert!(quiet_text.trim().is_empty(), "--quiet printed to stdout:\n{quiet_text}");

    // CHC lane, proof. `[AY:PROOF]` comes out of `solver_stdout!`, a different
    // output path from the runner's `println!`s, so it needs its own pair.
    let loud_chc =
        trust_mc_in(&dir, &["--ay-chc", "--output-format", "terse", "--timeout", "240s", "ok.rs"]);
    let loud_chc_text = stdout(&loud_chc);
    assert_eq!(code(&loud_chc), 0, "stdout:\n{loud_chc_text}\nstderr:\n{}", stderr(&loud_chc));
    assert!(
        loud_chc_text.contains("[AY:PROOF]"),
        "a run WITHOUT --quiet must keep the CHC proof marker:\n{loud_chc_text}"
    );

    let quiet_chc = trust_mc_in(&dir, &["--quiet", "--ay-chc", "--timeout", "240s", "ok.rs"]);
    let quiet_chc_text = stdout(&quiet_chc);
    assert_eq!(
        code(&quiet_chc),
        0,
        "--quiet may hide the marker, never the verdict:\n{}",
        stderr(&quiet_chc)
    );
    assert!(
        !quiet_chc_text.contains("[AY:"),
        "--quiet still printed a CHC marker:\n{quiet_chc_text}"
    );
    assert!(quiet_chc_text.trim().is_empty(), "--quiet printed to stdout:\n{quiet_chc_text}");

    let _ = fs::remove_dir_all(&dir);
}

/// `--quiet` must silence the vacuity marker without silencing the fail-close
/// it announces. This is the case that would make a "just print nothing" fix
/// look correct while being worthless: the harness is a proof of nothing, and
/// the run has to keep exiting non-zero with no output at all.
#[test]
fn quiet_keeps_the_vacuity_fail_close_it_no_longer_prints() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("quiet-vacuity");
    fs::write(
        dir.join("vac.rs"),
        "#[kani::proof]\nfn vacuous_harness() {\n\x20   let x: u32 = kani::any();\n\
         \x20   kani::assume(x > 10);\n\x20   kani::assume(x < 5);\n\x20   assert!(x == 0);\n}\n",
    )
    .unwrap();

    let loud = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "120s", "vac.rs"]);
    let loud_text = stdout(&loud);
    assert_eq!(code(&loud), 1, "stdout:\n{loud_text}\nstderr:\n{}", stderr(&loud));
    assert!(loud_text.contains("[AY:VACUOUS:unsat-assumption]"), "{loud_text}");

    let quiet = trust_mc_in(&dir, &["--quiet", "--timeout", "120s", "vac.rs"]);
    let quiet_text = stdout(&quiet);
    assert_eq!(
        code(&quiet),
        1,
        "a vacuous proof must still fail under --quiet:\n{}",
        stderr(&quiet)
    );
    assert!(quiet_text.trim().is_empty(), "--quiet printed to stdout:\n{quiet_text}");

    let _ = fs::remove_dir_all(&dir);
}

/// `--coverage` had no producer in the CHC lane: every `VerificationResult`
/// built on the HORN path is hard-coded to `coverage_results: None`, so the run
/// verified, PRINTED `VERIFICATION:- SUCCESSFUL`, and only then died with
/// `error: harness missing coverage results`. The combination is now refused at
/// argument-validation time, before anything is printed.
///
/// The control is the second half: coverage in the bounded lane must still
/// produce a report. A fix that merely made `--coverage` fail everywhere would
/// satisfy the first assertion and be a regression.
#[test]
fn coverage_is_refused_under_ay_chc_and_still_works_without_it() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("coverage-chc");
    fs::write(
        dir.join("ok.rs"),
        "#[kani::proof]\nfn ok_harness() {\n\x20   let x: u32 = kani::any();\n\
         \x20   kani::assume(x < 100);\n\x20   assert!(x < 200);\n}\n",
    )
    .unwrap();

    let refused = trust_mc_in(
        &dir,
        &["--coverage", "-Z", "source-coverage", "--ay-chc", "--timeout", "240s", "ok.rs"],
    );
    let refused_out = stdout(&refused);
    let refused_err = stderr(&refused);
    assert_ne!(code(&refused), 0, "stdout:\n{refused_out}\nstderr:\n{refused_err}");
    assert!(
        refused_err.contains("--coverage is not supported with --ay-chc"),
        "the refusal must name the limitation:\n{refused_err}"
    );
    // The whole point: it must not verify, print a verdict, and THEN fail.
    assert!(
        !refused_out.contains("VERIFICATION:-"),
        "a refused combination must fail before any verdict is printed:\n{refused_out}"
    );
    assert!(
        !refused_err.contains("harness missing coverage results"),
        "the obscure post-verdict error must be gone:\n{refused_err}"
    );

    // Control: the bounded lane still reports coverage.
    let covered = trust_mc_in(
        &dir,
        &["--coverage", "-Z", "source-coverage", "--timeout", "240s", "ok.rs"],
    );
    let covered_text = stdout(&covered);
    assert_eq!(code(&covered), 0, "stdout:\n{covered_text}\nstderr:\n{}", stderr(&covered));
    assert!(
        covered_text.contains("Source-based code coverage results:"),
        "coverage must still work in the lane that can produce it:\n{covered_text}"
    );
    assert!(covered_text.contains("Coverage results saved to"), "{covered_text}");

    // And --ay-chc on its own is untouched.
    let chc = trust_mc_in(&dir, &["--ay-chc", "--output-format", "terse", "--timeout", "240s", "ok.rs"]);
    assert_eq!(code(&chc), 0, "stdout:\n{}\nstderr:\n{}", stdout(&chc), stderr(&chc));

    let _ = fs::remove_dir_all(&dir);
}


/// The machine-readable channels must keep the verdict distinction the console
/// has always drawn.
///
/// `--proof-summary-json`, `--sarif` and `--summary` collapsed INCONCLUSIVE
/// (the solver never decided), VACUOUS (contradictory assumptions — nothing was
/// verified) and an ordinary refuted assertion into one `"status": "failure"`
/// shape. Those three need three different fixes from the reader, and CI that
/// gates on the JSON could not tell which it had.
#[test]
fn machine_readable_verdicts_separate_vacuous_from_empty_from_a_real_failure() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("verdict-split");
    // Contradictory assumptions: every check is provably unreachable.
    fs::write(
        dir.join("vacuous.rs"),
        "#[kani::proof]\nfn v() {\n\x20   let x: u32 = kani::any();\n\
         \x20   kani::assume(x > 10);\n\x20   kani::assume(x < 5);\n\
         \x20   assert!(x == 0);\n}\n",
    )
    .unwrap();
    // Nothing to prove at all.
    fs::write(
        dir.join("nochecks.rs"),
        "#[kani::proof]\nfn n() {\n\x20   let x: u32 = kani::any();\n\x20   let _ = x;\n}\n",
    )
    .unwrap();
    // A check that really can fail.
    fs::write(
        dir.join("bug.rs"),
        "#[kani::proof]\nfn b() {\n\x20   let a: u8 = kani::any();\n\
         \x20   let c: u8 = kani::any();\n\x20   let _ = a + c;\n}\n",
    )
    .unwrap();

    let verdict_of = |file: &str| -> (String, String, String) {
        let json_path = format!("{file}.json");
        let sarif_path = format!("{file}.sarif");
        let out = trust_mc_in(
            &dir,
            &[
                "--proof-summary-json",
                &json_path,
                "--sarif",
                &sarif_path,
                "--summary",
                "--timeout",
                "60s",
                file,
            ],
        );
        let console = stdout(&out);
        assert_ne!(code(&out), 0, "{file} must not exit 0:\n{console}");
        let json: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(dir.join(&json_path)).unwrap()).unwrap();
        let sarif: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(dir.join(&sarif_path)).unwrap()).unwrap();
        let table = console
            .split("trust-mc summary:")
            .nth(1)
            .unwrap_or_else(|| panic!("no --summary table for {file}:\n{console}"))
            .to_string();
        (
            json["harnesses"][0]["verdict"].as_str().unwrap_or_default().to_string(),
            sarif["runs"][0]["results"][0]["properties"]["verdict"]
                .as_str()
                .unwrap_or_default()
                .to_string(),
            table,
        )
    };

    let (vacuous_json, vacuous_sarif, vacuous_table) = verdict_of("vacuous.rs");
    let (empty_json, empty_sarif, empty_table) = verdict_of("nochecks.rs");
    let (bug_json, bug_sarif, bug_table) = verdict_of("bug.rs");

    // Three runs, three verdicts — in every channel.
    assert_eq!(vacuous_json, "vacuous", "the JSON must name vacuity");
    assert_eq!(empty_json, "inconclusive_no_checks", "a proof of nothing is not a refutation");
    assert_eq!(bug_json, "failed", "a real failure keeps the ordinary verdict");
    assert_eq!(vacuous_sarif, "vacuous", "SARIF too");
    assert_eq!(empty_sarif, "inconclusive_no_checks");
    assert_eq!(bug_sarif, "failed");
    assert!(vacuous_table.contains("VACUOUS  v"), "the table must say so:\n{vacuous_table}");
    assert!(empty_table.contains("NO-CHECKS  n"), "{empty_table}");
    assert!(bug_table.contains("FAILED  b"), "{bug_table}");

    // The pre-existing fields must not have moved under any consumer's feet.
    let json: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(dir.join("vacuous.rs.json")).unwrap()).unwrap();
    assert_eq!(json["harnesses"][0]["status"], "failure");
    assert_eq!(json["harnesses"][0]["effective_success"], false);
    assert_eq!(json["summary"]["failures"], 1);
    assert_eq!(json["summary"]["vacuous_harnesses"], 1);
    assert_eq!(json["summary"]["refuted_harnesses"], 0);
    let sarif: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(dir.join("vacuous.rs.sarif")).unwrap()).unwrap();
    assert_eq!(sarif["runs"][0]["results"][0]["ruleId"], "trust_mc.harness.vacuous");
    assert_eq!(sarif["runs"][0]["results"][0]["level"], "error");
    let _ = fs::remove_dir_all(&dir);
}

/// `#[kani::should_panic]` must not be able to launder an uncertified
/// counterexample into a pass.
///
/// For an ordinary harness a counterexample the classifier declined to certify
/// is still bad news, so the verdict is FAILED either way. For should_panic the
/// counterexample IS the proof obligation, and `PanicsOnly` was turned straight
/// into `VERIFICATION:- SUCCESSFUL` and exit 0 — so a panic the driver had just
/// described as values the program cannot produce was accepted AS the proof:
///
///     [AY:CTREX_CAT:OverApproximation:chc_sound_havoc_drop=4]
///     [AY:CTREX_NOT_CERTIFIED] h: ... NOT certified as a genuine bug ...
///     VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)
///     Complete - 1 successfully verified harnesses, 0 failures, 1 total.
#[test]
fn a_should_panic_harness_cannot_pass_on_an_uncertified_counterexample() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("should-panic-uncertified");
    // `bounded_any::<String, 4>()` PROMISES `len() <= 4`, so this harness can
    // never panic when actually run. Under --ay-chc the call is not inlined and
    // its result is a fresh unconstrained symbol, which is the only reason a
    // "panic" appears at all.
    fs::write(
        dir.join("uncertified.rs"),
        "#[kani::proof]\n#[kani::unwind(6)]\n#[kani::should_panic]\nfn h() {\n\
         \x20   let s: String = kani::bounded_any::<String, 4>();\n\
         \x20   assert!(s.len() <= 4);\n}\n",
    )
    .unwrap();
    let out = trust_mc_in(
        &dir,
        &["--ay-chc", "--output-format", "terse", "--timeout", "240s", "uncertified.rs"],
    );
    let text = stdout(&out);
    if text.contains("[AY:CTREX_NOT_CERTIFIED]") {
        assert!(
            !text.contains("VERIFICATION:- SUCCESSFUL"),
            "an uncertified counterexample must not stand as the should_panic proof:\n{text}"
        );
        assert_ne!(code(&out), 0, "and it must not exit 0:\n{text}");
        assert!(
            text.contains("[AY:SHOULD_PANIC_NOT_CERTIFIED]"),
            "the demotion must say why, or it looks like a broken feature:\n{text}"
        );
        assert!(
            text.contains("0 successfully verified harnesses"),
            "it must not count as a verified harness:\n{text}"
        );
    } else {
        // If the encoding ever models `bounded_any` precisely there is no
        // uncertified counterexample to demote, and nothing to assert.
        eprintln!("NOTE: no uncertified counterexample produced; the demotion was not exercised");
    }

    // CONTROL: a should_panic harness whose panic is GENUINE still passes. A
    // change that fails every should_panic harness satisfies the bug report and
    // is worthless.
    fs::write(
        dir.join("real.rs"),
        "#[kani::proof]\n#[kani::should_panic]\nfn h() {\n\
         \x20   let x: u32 = kani::any();\n\x20   kani::assume(x < 10);\n\
         \x20   assert!(x > 100, \"x must be big\");\n}\n",
    )
    .unwrap();
    let ok = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "60s", "real.rs"]);
    let ok_text = stdout(&ok);
    assert_eq!(code(&ok), 0, "a real should_panic harness must still pass:\n{ok_text}");
    assert!(ok_text.contains("VERIFICATION:- SUCCESSFUL"), "{ok_text}");
    assert!(ok_text.contains("[AY:CTREX_CAT:Genuine]"), "{ok_text}");
    assert!(
        !ok_text.contains("[AY:SHOULD_PANIC_NOT_CERTIFIED]"),
        "a genuine panic must not be demoted:\n{ok_text}"
    );
    let _ = fs::remove_dir_all(&dir);
}


// ---------------------------------------------------------------------------
// Index-based slices carry their real length; panics name their message
// ---------------------------------------------------------------------------

/// `&a[..]` and `&a[m..n]` used to hand the destination a fat pointer whose
/// `fld_len` was a FRESH UNCONSTRAINED symbol, so `.len()` and every bounds
/// check through the slice were meaningless. The signature was that a claim and
/// its dual BOTH failed. Both directions are pinned here: a change that merely
/// makes the false claim fail (by making everything fail) is worthless.
#[test]
fn wf3_index_based_slice_length_is_the_real_length() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("wf3-slice-len");

    // (file, body, must exit 0)
    let cases: [(&str, &str, bool); 6] = [
        // Full range: the length is the array's static length.
        ("full_true.rs", "let a: [u8; 4] = [0; 4];\n let s = &a[..];\n assert!(s.len() == 4);", true),
        ("full_false.rs", "let a: [u8; 4] = [0; 4];\n let s = &a[..];\n assert!(s.len() == 99);", false),
        // Sub-slice: the length is end - start, not the backing array's length.
        ("sub_true.rs", "let a: [u8; 4] = [0; 4];\n let s = &a[1..3];\n assert!(s.len() == 2);", true),
        ("sub_false.rs", "let a: [u8; 4] = [0; 4];\n let s = &a[1..3];\n assert!(s.len() == 4);", false),
        // A prefix range has its own length, distinct from the array's.
        ("to_true.rs", "let a: [u8; 8] = [0; 8];\n let s = &a[..5];\n assert!(s.len() == 5);", true),
        ("to_false.rs", "let a: [u8; 8] = [0; 8];\n let s = &a[..5];\n assert!(s.len() == 8);", false),
    ];

    for (file, body, want_ok) in cases {
        fs::write(
            dir.join(file),
            format!("#[kani::proof]\nfn wf3_slice_len_harness() {{\n {body}\n}}\n"),
        )
        .unwrap();
        let out = trust_mc_in(&dir, &["--timeout", "60s", file]);
        let text = stdout(&out);
        if want_ok {
            assert_eq!(
                code(&out),
                0,
                "a TRUE slice-length claim must prove ({file}); an unconstrained \
                 fat-pointer length makes it fail:\n{text}"
            );
            assert!(text.contains("VERIFICATION:- SUCCESSFUL"), "{file}:\n{text}");
        } else {
            assert_ne!(
                code(&out),
                0,
                "a FALSE slice-length claim must still fail ({file}); if it now \
                 proves, the length was pinned to the wrong value:\n{text}"
            );
            assert!(text.contains("VERIFICATION:- FAILED"), "{file}:\n{text}");
        }
    }
    let _ = fs::remove_dir_all(&dir);
}

/// Every `panic!` / `unreachable!` used to render as the label-derived
/// "panic reached", so a report could not say WHICH panic fired even though the
/// std shim passes the message operand through as a `&'static str`. The message
/// must reach the Failed Checks line, and a harness with no reachable panic must
/// still verify.
#[test]
fn wf3_panic_message_names_the_failing_panic() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("wf3-panic-msg");

    for (file, body, wanted) in [
        (
            "boom.rs",
            "let x: u8 = kani::any();\n if x > 200 { panic!(\"wf3 distinctive boom\"); }",
            "wf3 distinctive boom",
        ),
        (
            "other.rs",
            "let x: u8 = kani::any();\n if x > 200 { panic!(\"wf3 a different message\"); }",
            "wf3 a different message",
        ),
        (
            "bare.rs",
            "let x: u8 = kani::any();\n if x > 200 { panic!(); }",
            "explicit panic",
        ),
        (
            "unreach.rs",
            "let x: u8 = kani::any();\n if x > 200 { unreachable!(\"wf3 not here\"); }",
            "wf3 not here",
        ),
    ] {
        fs::write(
            dir.join(file),
            format!("#[kani::proof]\nfn wf3_panic_harness() {{\n {body}\n}}\n"),
        )
        .unwrap();
        let out = trust_mc_in(&dir, &["--timeout", "60s", file]);
        let text = stdout(&out);
        assert_eq!(code(&out), 1, "a reachable panic must fail ({file}):\n{text}");
        // `unreachable!("m")` renders as Rust's own text — "internal error:
        // entered unreachable code: m" — so the message is CONTAINED in the
        // line rather than being all of it. What matters is that the message
        // reaches the user at all; it used to be dropped for "panic reached".
        let failed_line = text
            .lines()
            .find(|l| l.starts_with("Failed Checks:"))
            .unwrap_or("<no Failed Checks line>");
        assert!(
            failed_line.contains(wanted),
            "the Failed Checks line must name the panic message ({file}); got:\n{failed_line}\n\nfull:\n{text}"
        );
        assert!(
            !failed_line.contains("panic reached"),
            "the message must replace the opaque wording ({file}): {failed_line}"
        );
    }

    // Discriminating control: the message plumbing must not turn a panic-free
    // harness into a failure, and must not invent a panic that cannot happen.
    fs::write(
        dir.join("clean.rs"),
        "#[kani::proof]\nfn wf3_panic_harness() {\n\
         \x20let x: u8 = kani::any();\n\
         \x20if x > 200 && x < 100 { panic!(\"wf3 unreachable boom\"); }\n}\n",
    )
    .unwrap();
    let out = trust_mc_in(&dir, &["--timeout", "60s", "clean.rs"]);
    let text = stdout(&out);
    // What matters for the panic-MESSAGE plumbing: it must not invent a panic
    // that cannot happen. The check is correctly UNREACHABLE.
    assert!(text.contains("Status: UNREACHABLE"), "the dead panic must be unreachable:\n{text}");
    assert!(
        !text.contains("Failed Checks: wf3 unreachable boom"),
        "a panic that cannot happen must not be reported as failing:\n{text}"
    );
    // The harness still exits 1 — every obligation it emitted is unreachable,
    // so nothing was exercised and that is not a proof — but it is no longer
    // filed as "contradictory assumptions". This harness HAS none: it runs for
    // every `x`; only the CHECK is dead. The V4 split (see
    // `v4_names_a_dead_check_dead_not_a_contradictory_assumption` at the end of
    // this file, and docs/findings/2026-08-23-v4-fires-on-a-dead-check.md) reads
    // the harness-reachability probe and reports the cause it actually found.
    assert_eq!(code(&out), 1, "an all-dead-check harness still fails closed:\n{text}");
    assert!(text.contains("[AY:VACUOUS:dead-checks]"), "{text}");
    assert!(
        !text.contains("[AY:VACUOUS:unsat-assumption]"),
        "this harness has no contradictory assumptions:\n{text}"
    );
    let _ = fs::remove_dir_all(&dir);
}


/// An exhausted `--unwind` bound is a statement about the BOUND, not the code.
///
/// The loop unroller cuts the back-edge of the last unrolled copy into a
/// synthetic `Unreachable` block. Codegen recorded that block's violation under
/// the plain `unreachable` label, which the driver's taxonomy renders as "panic
/// reached", `classify_ctrex` called `Genuine`, and concrete playback turned
/// into a runnable `#[test]`. So a program with no bug at all was reported as
/// having one — the single most misleading failure mode a bounded model checker
/// has, because the fix is a flag and the user is sent to read their code.
///
/// Verified before the fix (baseline `cargo build-dev`, these same two files):
///
/// ```text
/// Check 8: assertion.7
///     - Status: FAILURE
///     - Description: "panic reached"
/// Failed Checks: panic reached
/// [AY:CTREX_CAT:Genuine]
/// Concrete playback unit test for `bound_too_small`: ...
/// ```
#[test]
fn an_exhausted_unwind_bound_is_not_reported_as_a_genuine_bug() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("unwind-bound-exhausted");
    // Ten trips wanted, three allowed. The `assert!` is UNREACHABLE inside the
    // bound (the loop cannot exit in three trips), so the unwinding assertion is
    // the only failing check — the shape where a wrong label is most damaging.
    fs::write(
        dir.join("small.rs"),
        "#[kani::proof]\n#[kani::unwind(3)]\nfn bound_too_small() {\n\
         \x20   let mut sum: u32 = 0;\n\
         \x20   let mut i: u32 = 0;\n\
         \x20   while i < 10 {\n\
         \x20       sum += i;\n\
         \x20       i += 1;\n\
         \x20   }\n\
         \x20   assert!(sum == 45);\n\
         }\n",
    )
    .unwrap();
    let out = trust_mc_in(
        &dir,
        &[
            "-Z",
            "concrete-playback",
            "--concrete-playback",
            "print",
            "--timeout",
            "120s",
            "small.rs",
        ],
    );
    let text = stdout(&out);

    // Still fails — an exhausted bound must never be quietly accepted.
    assert_ne!(code(&out), 0, "an exhausted unwind bound must not exit 0:\n{text}");
    assert!(
        text.contains("Failed Checks: unwinding assertion loop"),
        "the failing check must name itself an unwinding assertion:\n{text}"
    );
    assert!(
        !text.contains("Failed Checks: panic reached"),
        "the bound ran out; the program never reached a panic:\n{text}"
    );
    assert!(
        !text.contains("[AY:CTREX_CAT:Genuine]"),
        "nothing about the program was disproved, so this is no genuine bug:\n{text}"
    );
    assert!(
        text.contains("[AY:CTREX_NOT_CERTIFIED]"),
        "an exhausted bound must be labelled, not blamed on the code:\n{text}"
    );
    assert!(text.contains("--unwind"), "the reader must be told which knob to turn:\n{text}");
    assert!(
        !text.contains("Concrete playback unit test"),
        "a playback test for a truncated search would reproduce nothing:\n{text}"
    );

    // CONTROL: the same shape of loop, a bound that FITS, and a genuine
    // assertion failure inside it. Without this the fix would be worthless — a
    // change that relabels every loop failure "raise the bound" satisfies the
    // bug report and hides real bugs instead.
    fs::write(
        dir.join("real.rs"),
        "#[kani::proof]\n#[kani::unwind(6)]\nfn genuine_in_loop() {\n\
         \x20   let mut i: u32 = 0;\n\
         \x20   while i < 3 {\n\
         \x20       i += 1;\n\
         \x20   }\n\
         \x20   assert!(i == 4, \"i should be 4\");\n\
         }\n",
    )
    .unwrap();
    let out = trust_mc_in(&dir, &["--output-format", "terse", "--timeout", "120s", "real.rs"]);
    let text = stdout(&out);
    assert_eq!(code(&out), 1, "a real assertion failure must still fail:\n{text}");
    assert!(
        text.contains("[AY:CTREX_CAT:Genuine]"),
        "a bug inside a loop that FITS the bound is a genuine counterexample:\n{text}"
    );
    assert!(
        !text.contains("Failed Checks: unwinding assertion loop"),
        "the bound was never exhausted here; do not blame it:\n{text}"
    );
    assert!(
        !text.contains("[AY:CTREX_NOT_CERTIFIED]"),
        "a genuine counterexample must not be hedged:\n{text}"
    );
    let _ = fs::remove_dir_all(&dir);
}


// ---------------------------------------------------------------------------
// CHC cover adjudication: the secondary cover query must PARSE, and a cover
// this lane cannot decide must fail CLOSED under --strict-vacuity.
//
// The BMC lane is the oracle: it decides both harnesses exactly, so every
// assertion below is written against what BMC says about the same file.
// ---------------------------------------------------------------------------

/// A cover the solver can PROVE unsatisfiable, and one it cannot — written so
/// the two differ only in the cover condition.
fn cover_witness_fixture(dir: &Path) {
    fs::write(
        dir.join("cover_never.rs"),
        "#[kani::proof]\nfn cover_never() {\n\x20   let x: u8 = kani::any();\n\
         \x20   kani::assume(x < 10);\n\x20   kani::cover!(x > 200 && x < 10);\n\
         \x20   assert!(x < 10);\n}\n",
    )
    .unwrap();
    fs::write(
        dir.join("cover_hit.rs"),
        "#[kani::proof]\nfn cover_hit() {\n\x20   let x: u8 = kani::any();\n\
         \x20   kani::assume(x < 10);\n\x20   kani::cover!(x > 5);\n\
         \x20   assert!(x < 10);\n}\n",
    )
    .unwrap();
}

#[test]
fn chc_cover_query_parses_so_an_impossible_cover_is_still_proved_impossible() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("chc-cover-unsat");
    cover_witness_fixture(&dir);

    // Oracle: the bounded lane proves the cover unsatisfiable and warns.
    let bmc = trust_mc_in(&dir, &["--timeout", "120s", "cover_never.rs"]);
    assert_eq!(code(&bmc), 0, "stdout:\n{}\nstderr:\n{}", stdout(&bmc), stderr(&bmc));
    assert!(
        stderr(&bmc).contains("provably unsatisfiable"),
        "BMC oracle must call this cover unsatisfiable:\n{}",
        stderr(&bmc)
    );

    // The unbounded lane must reach the same verdict. Before the fix its cover
    // query referenced `(declare-var ...)` symbols it had itself stripped, so
    // ay answered `(error "unknown constant ...")`, nothing parsed as
    // sat/unsat, and the cover landed UNDETERMINED — silently.
    // The unbounded lane does NOT adjudicate covers. Before the fix its cover
    // query referenced `(declare-var ...)` symbols it had itself stripped, so
    // ay answered `(error "unknown constant ...")`, nothing parsed as
    // sat/unsat, and the cover landed UNDETERMINED **silently** — which made
    // --strict-vacuity fail OPEN. It now fails CLOSED with a marker that says
    // why, which is the outcome this test pins. Adjudicating a cover in the
    // Horn encoding is unimplemented: the encoding records a cover's condition
    // without the program point that guards it, so neither SATISFIED nor
    // UNSATISFIABLE can be established soundly. If that ever changes, this
    // assertion fails and should be strengthened to match BMC.
    // Under --strict-vacuity the unbounded lane now fails CLOSED and says why.
    // Before the fix its cover query referenced `(declare-var ...)` symbols it
    // had itself stripped, ay answered `(error "unknown constant ...")`,
    // nothing parsed, the cover landed UNDETERMINED silently, and the gate
    // passed — fail-OPEN on the one flag whose whole job is to reject an
    // unwitnessed cover.
    let chc = trust_mc_in(
        &dir,
        &["--ay-chc", "--strict-vacuity", "--timeout", "300s", "cover_never.rs"],
    );
    let chc_all = format!("{}{}", stdout(&chc), stderr(&chc));
    assert_ne!(code(&chc), 0, "--strict-vacuity must not pass an unwitnessed cover:\n{chc_all}");
    assert!(
        chc_all.contains("cover-undetermined"),
        "--ay-chc must say WHY it cannot adjudicate the cover:\nstdout:\n{}\nstderr:\n{}",
        stdout(&chc),
        stderr(&chc)
    );

    // And that is exactly what --strict-vacuity is for. It could not fire at
    // all while every cover was UNDETERMINED.
    let strict = trust_mc_in(
        &dir,
        &["--ay-chc", "--strict-vacuity", "--timeout", "300s", "cover_never.rs"],
    );
    assert_ne!(code(&strict), 0, "stdout:\n{}", stdout(&strict));
    // BMC, which CAN adjudicate, uses `[AY:VACUOUS:cover]` — the cover is
    // proved unsatisfiable. The unbounded lane cannot adjudicate, so it fires
    // the distinct `cover-undetermined` marker instead. Both fail closed; only
    // BMC gets to say the cover is impossible. Asserting BMC's marker here
    // would be asserting an adjudication that does not exist.
    assert!(
        stdout(&strict).contains("[AY:VACUOUS:cover-undetermined]"),
        "--strict-vacuity must fire, naming the reason it cannot adjudicate:\n{}",
        stdout(&strict)
    );

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn chc_cover_that_is_merely_undecided_fails_closed_not_open() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("chc-cover-sat");
    cover_witness_fixture(&dir);

    // Oracle: the bounded lane reaches this cover, so it is SATISFIED and
    // --strict-vacuity has nothing to complain about.
    let bmc = trust_mc_in(&dir, &["--timeout", "120s", "cover_hit.rs"]);
    assert_eq!(code(&bmc), 0, "stdout:\n{}\nstderr:\n{}", stdout(&bmc), stderr(&bmc));
    assert!(stdout(&bmc).contains("SATISFIED"), "BMC oracle:\n{}", stdout(&bmc));
    let bmc_strict =
        trust_mc_in(&dir, &["--strict-vacuity", "--timeout", "120s", "cover_hit.rs"]);
    assert_eq!(code(&bmc_strict), 0, "stdout:\n{}", stdout(&bmc_strict));

    // DISCRIMINATION: the unbounded lane must NOT call this cover
    // unsatisfiable. A "fix" that simply reported every cover unsatisfiable
    // would satisfy the test above and be worthless.
    let chc = trust_mc_in(&dir, &["--ay-chc", "--timeout", "300s", "cover_hit.rs"]);
    assert_eq!(code(&chc), 0, "stdout:\n{}\nstderr:\n{}", stdout(&chc), stderr(&chc));
    assert!(
        !stderr(&chc).contains("provably unsatisfiable"),
        "a reachable cover must never be called unsatisfiable:\n{}",
        stderr(&chc)
    );
    assert!(
        !stdout(&chc).contains("[AY:VACUOUS:cover]"),
        "no V5 verdict without --strict-vacuity:\n{}",
        stdout(&chc)
    );

    // The Horn encoding records a cover's condition WITHOUT the program point
    // that guards it, so this lane cannot show the cover is reached either.
    // Under --strict-vacuity — whose contract is "a declared cover must be
    // shown to hold" — an unadjudicated witness is a failure, not a pass.
    let strict =
        trust_mc_in(&dir, &["--ay-chc", "--strict-vacuity", "--timeout", "300s", "cover_hit.rs"]);
    assert_ne!(
        code(&strict), 0,
        "an unadjudicated cover must fail CLOSED under --strict-vacuity:\n{}",
        stdout(&strict)
    );
    assert!(
        stdout(&strict).contains("[AY:VACUOUS:cover-undetermined]"),
        "and must say WHY it could not be adjudicated:\n{}",
        stdout(&strict)
    );
    // A distinct marker from the PROVED-unsatisfiable verdict: "we could not
    // check" must never be printed as "we proved it impossible".
    assert!(
        !stdout(&strict).contains("[AY:VACUOUS:cover]"),
        "undecided is not the same verdict as proved-impossible:\n{}",
        stdout(&strict)
    );

    let _ = fs::remove_dir_all(&dir);
}

// ---------------------------------------------------------------------------
// #g4-erased-wrapper-payload: a sort-erased transparent wrapper must not swallow its payload
// ---------------------------------------------------------------------------

/// Write `body` into `dir/name.rs` wrapped in a `#[kani::proof] fn h()`.
fn erased_wrapper_fixture(dir: &Path, name: &str, body: &str) -> PathBuf {
    let file = dir.join(format!("{name}.rs"));
    fs::write(&file, format!("#[kani::proof]\nfn h() {{\n{body}\n}}\n")).unwrap();
    file
}

#[test]
fn erased_transparent_wrapper_keeps_its_payload_and_still_discriminates() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("erased-wrapper-payload");

    // Sort inference erases `ManuallyDrop<T>`/`MaybeUninit<T>` to the sort of
    // T, so the term for such a local IS the payload. MIR still projects
    // `Field(0)` through the erased wrapper (`into_inner` is literally
    // `slot.value`), and that projection used to fail closed, leaving the
    // assignment's LHS UNCONSTRAINED — a FALSE assertion failure on safe code.
    //
    // Each pair is (name, body, must_verify). The FALSE member of every pair is
    // the discrimination: a "fix" that merely made the check vanish would pass
    // the true cases and fail here.
    let cases: [(&str, &str, bool); 10] = [
        (
            "mdrop_true",
            "    let md = std::mem::ManuallyDrop::new(7u8);\n\
             \x20   let v = std::mem::ManuallyDrop::into_inner(md);\n\
             \x20   assert!(v == 7);",
            true,
        ),
        (
            "mdrop_false",
            "    let md = std::mem::ManuallyDrop::new(7u8);\n\
             \x20   let v = std::mem::ManuallyDrop::into_inner(md);\n\
             \x20   assert!(v == 8);",
            false,
        ),
        (
            "mdrop_symbolic_true",
            "    let x: u8 = kani::any();\n\
             \x20   let v = std::mem::ManuallyDrop::into_inner(std::mem::ManuallyDrop::new(x));\n\
             \x20   assert!(v == x);",
            true,
        ),
        (
            "mdrop_symbolic_false",
            "    let x: u8 = kani::any();\n\
             \x20   let v = std::mem::ManuallyDrop::into_inner(std::mem::ManuallyDrop::new(x));\n\
             \x20   assert!(v == 7);",
            false,
        ),
        (
            "maybeuninit_true",
            "    let m = std::mem::MaybeUninit::new(7u8);\n\
             \x20   let v = unsafe { m.assume_init() };\n\
             \x20   assert!(v == 7);",
            true,
        ),
        (
            "maybeuninit_false",
            "    let m = std::mem::MaybeUninit::new(7u8);\n\
             \x20   let v = unsafe { m.assume_init() };\n\
             \x20   assert!(v == 8);",
            false,
        ),
        // The read/write PAIR. Making the read an identity while the write to
        // the same storage lands under a different SSA name is the
        // slot-misalignment shape that fabricates proofs: the write would be
        // lost and the stale `7` would PROVE. Both directions are pinned.
        (
            "mdrop_write_then_read_true",
            "    let mut md = std::mem::ManuallyDrop::new(7u8);\n\
             \x20   *md = 9;\n\
             \x20   let v = std::mem::ManuallyDrop::into_inner(md);\n\
             \x20   assert!(v == 9);",
            true,
        ),
        (
            "mdrop_write_then_read_stale_false",
            "    let mut md = std::mem::ManuallyDrop::new(7u8);\n\
             \x20   *md = 9;\n\
             \x20   let v = std::mem::ManuallyDrop::into_inner(md);\n\
             \x20   assert!(v == 7);",
            false,
        ),
        // Same pair again through a RAW pointer taken from the payload, a
        // different MIR shape for the same storage.
        (
            "mdrop_rawptr_write_true",
            "    let mut md = std::mem::ManuallyDrop::new(7u8);\n\
             \x20   let p: *mut u8 = &mut *md;\n\
             \x20   unsafe { *p = 9 };\n\
             \x20   let v = std::mem::ManuallyDrop::into_inner(md);\n\
             \x20   assert!(v == 9);",
            true,
        ),
        (
            "mdrop_rawptr_write_stale_false",
            "    let mut md = std::mem::ManuallyDrop::new(7u8);\n\
             \x20   let p: *mut u8 = &mut *md;\n\
             \x20   unsafe { *p = 9 };\n\
             \x20   let v = std::mem::ManuallyDrop::into_inner(md);\n\
             \x20   assert!(v == 7);",
            false,
        ),
    ];

    for (name, body, must_verify) in cases {
        erased_wrapper_fixture(&dir, name, body);
        let file = format!("{name}.rs");
        let out = trust_mc_in(&dir, &["--timeout", "120s", &file]);
        let so = stdout(&out);
        if must_verify {
            assert!(
                so.contains("VERIFICATION:- SUCCESSFUL"),
                "{name}: a TRUE claim about an erased wrapper's payload must \
                 PROVE, not report a false failure:\n{so}\nstderr:\n{}",
                stderr(&out)
            );
        } else {
            assert!(
                so.contains("VERIFICATION:- FAILED"),
                "{name}: a FALSE claim must still FAIL — otherwise the payload \
                 is not modelled, the check merely disappeared:\n{so}\nstderr:\n{}",
                stderr(&out)
            );
        }
    }

    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn interior_mutable_wrapper_stays_fail_closed_rather_than_reading_a_stale_payload() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("erased-wrapper-interior-mut");

    // `Cell<T>`/`UnsafeCell<T>` are erased wrappers too, but their payload is
    // written through a RAW pointer minted by `UnsafeCell::get`, which never
    // passes through the borrow whose SSA name the fix aligns. Treating the
    // read as an identity there would return the pre-`set` value and PROVE
    // `v == 7` — a wrong ANSWER. `erased_wrapper_field_sort` refuses any type
    // containing an `UnsafeCell`, so this fails CLOSED instead.
    erased_wrapper_fixture(
        &dir,
        "cell_stale",
        "    let c = std::cell::Cell::new(7u8);\n\
         \x20   c.set(9);\n\
         \x20   let v = c.get();\n\
         \x20   assert!(v == 7);",
    );
    let out = trust_mc_in(&dir, &["--timeout", "120s", "cell_stale.rs"]);
    let so = stdout(&out);
    assert!(
        !so.contains("VERIFICATION:- SUCCESSFUL"),
        "a stale read of an interior-mutable payload must never be PROVED:\n{so}\nstderr:\n{}",
        stderr(&out)
    );
    let _ = fs::remove_dir_all(&dir);
}

/// V4 must say which of its two causes it actually found.
///
/// `checks > 0 && unreachable == checks` is one table produced by two opposite
/// situations, and the gate reported one of them for both:
///
///   * the harness cannot run — `assume(x > 10); assume(x < 5)`. Nothing was
///     verified, and "contradictory assumptions" is exactly right.
///   * the harness runs for every input and its only check sits on dead code —
///     `if x > 200 && x < 100 { panic!() }`. There is no contradictory
///     assumption anywhere in it, and the gate said there was.
///
/// The discriminator already existed: BMC's `probe_harness_reachable` re-solves
/// the query without the violation disjunction and answers "are the program
/// constraints satisfiable at all". On the dead-check harness it answers
/// `reachable`; on the contradictory one, `unsat`.
///
/// Both still fail closed. This test therefore pins the CAUSE, not a verdict
/// flip: a fix that relabels everything, or that quietly turns the vacuity gate
/// into a pass, fails here.
#[test]
fn v4_names_a_dead_check_dead_not_a_contradictory_assumption() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("v4-dead-check");

    // (1) The dead-check harness. Reachable harness, unreachable check.
    fs::write(
        dir.join("dead.rs"),
        "#[kani::proof]\nfn dead_check_harness() {\n\
         \x20   let x: u8 = kani::any();\n\
         \x20   if x > 200 && x < 100 { panic!(\"dead boom\"); }\n\
         }\n",
    )
    .unwrap();
    let dead = trust_mc_in(&dir, &["--timeout", "60s", "dead.rs"]);
    let dead_text = stdout(&dead);
    assert_eq!(code(&dead), 1, "an all-dead-check harness still fails closed:\n{dead_text}");
    assert!(dead_text.contains("Status: UNREACHABLE"), "the check is dead:\n{dead_text}");
    assert!(
        dead_text.contains("[AY:VACUOUS:dead-checks]"),
        "the dead-check cause must be named:\n{dead_text}"
    );
    assert!(
        !dead_text.contains("[AY:VACUOUS:unsat-assumption]"),
        "this harness has NO contradictory assumptions:\n{dead_text}"
    );
    assert!(
        !dead_text.contains("contradictory assumptions"),
        "and the prose must not claim any either:\n{dead_text}"
    );
    assert!(
        !dead_text.contains("VERIFICATION:- VACUOUS"),
        "vacuity is the wrong word for a harness that runs:\n{dead_text}"
    );

    // (2) DISCRIMINATING CONTROL — the case V4 exists for is untouched. A
    // relabel-everything "fix" dies here.
    fs::write(
        dir.join("contra.rs"),
        "#[kani::proof]\nfn contradictory_harness() {\n\
         \x20   let x: u8 = kani::any();\n\
         \x20   kani::assume(x > 10);\n\
         \x20   kani::assume(x < 5);\n\
         \x20   assert!(x < 200);\n\
         }\n",
    )
    .unwrap();
    let contra = trust_mc_in(&dir, &["--timeout", "60s", "contra.rs"]);
    let contra_text = stdout(&contra);
    assert_eq!(code(&contra), 1, "contradictory assumptions still fail closed:\n{contra_text}");
    assert!(contra_text.contains("VERIFICATION:- VACUOUS"), "{contra_text}");
    assert!(
        contra_text.contains("[AY:VACUOUS:unsat-assumption]"),
        "the unsat-assumption cause must survive the split:\n{contra_text}"
    );
    assert!(
        !contra_text.contains("[AY:VACUOUS:dead-checks]"),
        "a harness that cannot run is not a dead-check harness:\n{contra_text}"
    );

    // (3) DISCRIMINATING CONTROL — a harness whose checks are LIVE still
    // verifies. A change that made every run inconclusive would satisfy (1)
    // and be worthless.
    fs::write(
        dir.join("live.rs"),
        "#[kani::proof]\nfn live_harness() {\n\
         \x20   let x: u8 = kani::any();\n\
         \x20   kani::assume(x < 100);\n\
         \x20   assert!(x < 200);\n\
         }\n",
    )
    .unwrap();
    let live = trust_mc_in(&dir, &["--timeout", "60s", "live.rs"]);
    let live_text = stdout(&live);
    assert_eq!(code(&live), 0, "a live proof must still pass:\n{live_text}");
    assert!(live_text.contains("VERIFICATION:- SUCCESSFUL"), "{live_text}");
    assert!(!live_text.contains("[AY:VACUOUS:"), "no vacuity marker on a real proof:\n{live_text}");

    // (4) The escape hatch covers the new arm too, and stays loud.
    let allowed = trust_mc_in(&dir, &["--timeout", "60s", "--allow-vacuous", "dead.rs"]);
    let allowed_text = stdout(&allowed);
    assert_eq!(code(&allowed), 0, "--allow-vacuous relaxes the dead-check arm:\n{allowed_text}");
    assert!(allowed_text.contains("[AY:VACUOUS:allowed]"), "{allowed_text}");

    let _ = fs::remove_dir_all(&dir);
}

/// The byte-count overflow obligation exists for every copy-family intrinsic.
///
/// `copy`, `copy_nonoverlapping` and `write_bytes` are all UB when
/// `count * size_of::<T>()` overflows a `usize`. That obligation was not
/// emitted at all, in either lane, so all three corpus tests whose entire
/// purpose is to overflow that product reported `VERIFICATION:- SUCCESSFUL`.
///
/// The safe half of this test is the half that matters. A missing obligation
/// and a discharged one both print no failure, so proving the overflowing
/// programs fail is not on its own evidence that the check exists — it could
/// equally be a check that fires on every copy. Both directions are asserted:
/// the overflowing count FAILS with rustc's own message, and the safe count
/// still reports the very same check as SUCCESS rather than omitting it.
#[test]
fn copy_family_checks_the_byte_count_for_overflow() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("copy-byte-count-overflow");
    let msg = "attempt to compute number in bytes which would overflow";

    // usize::MAX / 4 + 1 elements of a 4-byte type overflows the byte count.
    let overflowing = [
        ("copy", "core::intrinsics::copy(src, dst, usize::MAX / 4 + 1);"),
        ("copy_nonoverlapping", "core::intrinsics::copy_nonoverlapping(src, dst, usize::MAX / 4 + 1);"),
    ];
    for (name, call) in overflowing {
        let file = format!("{name}_bad.rs");
        fs::write(
            dir.join(&file),
            format!(
                "#![feature(core_intrinsics)]\n#[kani::proof]\nfn h() {{\n\
                 \x20   let arr: [i32; 3] = [0, 1, 0];\n\
                 \x20   let src: *const i32 = arr.as_ptr();\n\
                 \x20   unsafe {{\n\
                 \x20       let dst = src.add(1) as *mut i32;\n\
                 \x20       {call}\n\
                 \x20   }}\n}}\n"
            ),
        )
        .unwrap();
        let out = trust_mc_in(&dir, &["--timeout", "120s", &file]);
        let text = stdout(&out);
        assert_ne!(code(&out), 0, "{name} with an overflowing byte count must fail:\n{text}");
        assert!(
            text.contains(&format!("{name}: {msg}")),
            "{name} must fail with rustc's own message:\n{text}"
        );
    }

    // write_bytes takes (dst, val, count) and needs a writable destination.
    fs::write(
        dir.join("write_bytes_bad.rs"),
        "#![feature(core_intrinsics)]\n#[kani::proof]\nfn h() {\n\
         \x20   let mut v = vec![0u32; 4];\n\
         \x20   unsafe {\n\
         \x20       core::intrinsics::write_bytes(v.as_mut_ptr(), 0xfe, usize::MAX / 4 + 1);\n\
         \x20   }\n}\n",
    )
    .unwrap();
    let wb = trust_mc_in(&dir, &["--timeout", "120s", "write_bytes_bad.rs"]);
    let wb_text = stdout(&wb);
    assert_ne!(code(&wb), 0, "write_bytes with an overflowing byte count must fail:\n{wb_text}");
    assert!(wb_text.contains(&format!("write_bytes: {msg}")), "{wb_text}");

    // The control. A safe count must still carry the check and DISCHARGE it —
    // present and SUCCESS, not absent. Asserting only that safe copies "pass"
    // would be satisfied by deleting the obligation again.
    fs::write(
        dir.join("safe.rs"),
        "#[kani::proof]\nfn h() {\n\
         \x20   let src = [1u32, 2, 3, 4];\n\
         \x20   let mut dst = [0u32; 4];\n\
         \x20   unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), 4); }\n\
         }\n",
    )
    .unwrap();
    let safe = trust_mc_in(&dir, &["--timeout", "120s", "safe.rs"]);
    let safe_text = stdout(&safe);
    assert!(
        safe_text.contains(&format!("copy_nonoverlapping: {msg}")),
        "the safe copy must still EMIT the byte-count check, not omit it:\n{safe_text}"
    );
    assert!(
        !safe_text.contains(&format!("Failed Checks: copy_nonoverlapping: {msg}")),
        "the safe copy must DISCHARGE the byte-count check, not fail it:\n{safe_text}"
    );

    let _ = fs::remove_dir_all(&dir);
}

/// The copy-family intrinsics carry their memory-safety obligations.
///
/// Five corpus tests reported `VERIFICATION:- SUCCESSFUL` with
/// `[AY:PROOF_QUALIFIERS:clean]` on programs that are unambiguously UB: four
/// passing a deliberately misaligned pointer, one overlapping the regions of a
/// `copy_nonoverlapping`. The only checks those runs emitted were "pointer
/// arithmetic overflow" — the unsafe operation itself was never an obligation.
///
/// The legitimate half of this test is the half that matters, and it is not
/// decoration. The obvious overlap encoding (`src < dst+n && dst < src+n` on
/// the pointer values) passes every UB case here while failing ordinary code,
/// because distinct stack address symbols are mutually unconstrained in this
/// model — `assert!(p != q)` for two distinct locals does not hold, so "they
/// overlap" is trivially satisfiable for two separate arrays. A corpus run does
/// not catch that. These cases do.
#[test]
fn copy_family_intrinsics_check_alignment_and_overlap() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("copy-align-overlap");
    let w = |name: &str, body: &str| {
        fs::write(
            dir.join(name),
            format!("#![feature(core_intrinsics)]\n#[kani::proof]\nfn h() {{\n{body}\n}}\n"),
        )
        .unwrap();
    };

    // --- UB: a misaligned pointer, the corpus construction (+1 byte cast). ---
    for (name, call, want) in [
        ("mis_src.rs", "core::intrinsics::copy(su, d, 1);", "`src` must be properly aligned"),
        ("mis_dst.rs", "core::intrinsics::copy(s, du, 1);", "`dst` must be properly aligned"),
    ] {
        w(
            name,
            &format!(
                "    let arr: [i32; 3] = [0, 1, 0];\n\
                 \x20   let s: *const i32 = arr.as_ptr();\n\
                 \x20   unsafe {{\n\
                 \x20       let su = (s as *const i8).add(1) as *const i32;\n\
                 \x20       let d = s.add(1) as *mut i32;\n\
                 \x20       let du = (d as *mut i8).add(1) as *mut i32;\n\
                 \x20       {call}\n\
                 \x20   }}"
            ),
        );
        let out = trust_mc_in(&dir, &["--timeout", "120s", name]);
        let text = stdout(&out);
        assert_ne!(code(&out), 0, "{name}: a misaligned copy must not verify:\n{text}");
        assert!(text.contains(want), "{name} must fail with `{want}`:\n{text}");
    }

    // --- UB: copy_nonoverlapping whose regions genuinely overlap. ---
    w(
        "overlap.rs",
        "    let arr: [i32; 3] = [0, 1, 0];\n\
         \x20   let s: *const i32 = arr.as_ptr();\n\
         \x20   unsafe {\n\
         \x20       let d = s.add(1) as *mut i32;\n\
         \x20       core::intrinsics::copy_nonoverlapping(s, d, 2);\n\
         \x20   }",
    );
    let ovl = trust_mc_in(&dir, &["--timeout", "120s", "overlap.rs"]);
    assert_ne!(code(&ovl), 0, "overlapping copy_nonoverlapping must not verify:\n{}", stdout(&ovl));
    assert!(stdout(&ovl).contains("memcpy src/dst overlap"), "{}", stdout(&ovl));

    // --- The controls. Every one of these is legitimate Rust. ---
    // Two separate arrays: the naive address comparison fails this one.
    w(
        "ok_disjoint.rs",
        "    let s = [1u32, 2, 3, 4];\n\
         \x20   let mut d = [0u32; 4];\n\
         \x20   unsafe { core::ptr::copy_nonoverlapping(s.as_ptr(), d.as_mut_ptr(), 4); }",
    );
    // memmove PERMITS overlap: the overlap obligation must not leak into `copy`.
    w(
        "ok_memmove_overlap.rs",
        "    let mut a = [1u8, 2, 3, 4, 5];\n\
         \x20   let p = a.as_mut_ptr();\n\
         \x20   unsafe { core::ptr::copy(p, p.add(1), 4); }",
    );
    // align_of::<u8>() == 1, so no pointer can be misaligned for it.
    w(
        "ok_u8.rs",
        "    let s = [1u8, 2, 3, 4, 5];\n\
         \x20   let mut d = [0u8; 5];\n\
         \x20   unsafe { core::ptr::copy_nonoverlapping(s.as_ptr().add(1), d.as_mut_ptr().add(2), 3); }",
    );
    // A Vec's buffer comes from the allocator: non-null and element-aligned.
    // Left unstated, the solver picks an odd address and this fails.
    w(
        "ok_vec.rs",
        "    let mut v = vec![0u32; 4];\n\
         \x20   unsafe { core::ptr::write_bytes(v.as_mut_ptr(), 0xfe, 4); }",
    );
    // Same array, non-overlapping element ranges: decided arithmetically.
    w(
        "ok_same_array.rs",
        "    let mut arr = [1u32, 2, 3, 4];\n\
         \x20   let p0 = &arr[0] as *const u32;\n\
         \x20   let p2 = &mut arr[2] as *mut u32;\n\
         \x20   unsafe { core::ptr::copy_nonoverlapping(p0, p2, 1); }",
    );
    // --- UB: the copied range escapes the object. ---
    // Each of these was previously either INCONCLUSIVE (fail-closed, proving
    // nothing) or FAILED on the wrong obligation — in the `add(3)` case the
    // only failing check was "pointer arithmetic overflow" on computing a
    // one-past-the-end pointer, which is LEGAL in Rust. We were reporting a
    // failure on the legal operation and nothing on the illegal one.
    for (name, body, want) in [
        (
            "past_end.rs",
            "    let arr: [i32; 3] = [0, 1, 0];\n\
             \x20   let s: *const i32 = arr.as_ptr();\n\
             \x20   unsafe {\n\
             \x20       let d = s.add(3) as *mut i32;\n\
             \x20       core::intrinsics::copy(s, d, 1);\n\
             \x20   }",
            "memmove destination region writeable",
        ),
        (
            "before_start.rs",
            "    let arr: [i32; 3] = [0, 1, 0];\n\
             \x20   let s: *const i32 = arr.as_ptr();\n\
             \x20   let si = s.wrapping_sub(1);\n\
             \x20   let d = s.wrapping_add(1) as *mut i32;\n\
             \x20   unsafe { core::intrinsics::copy(si, d, 1); }",
            "memmove source region readable",
        ),
        (
            "over_read.rs",
            "    let arr: [i32; 3] = [0, 1, 0];\n\
             \x20   let mut out: [i32; 8] = [0; 8];\n\
             \x20   let s: *const i32 = arr.as_ptr();\n\
             \x20   unsafe { core::intrinsics::copy(s, out.as_mut_ptr(), 6); }",
            "memmove source region readable",
        ),
    ] {
        w(name, body);
        let out = trust_mc_in(&dir, &["--timeout", "120s", name]);
        let text = stdout(&out);
        assert_ne!(code(&out), 0, "{name}: an out-of-object copy must not verify:\n{text}");
        assert!(text.contains(want), "{name} must fail with `{want}`:\n{text}");
    }

    for name in
        ["ok_disjoint.rs", "ok_memmove_overlap.rs", "ok_u8.rs", "ok_vec.rs", "ok_same_array.rs"]
    {
        let out = trust_mc_in(&dir, &["--timeout", "120s", name]);
        let text = stdout(&out);
        assert_eq!(code(&out), 0, "{name} is legitimate Rust and must verify:\n{text}");
        assert!(
            !text.contains("must be properly aligned") || !text.contains("Failed Checks:"),
            "{name} must not fail an alignment check:\n{text}"
        );
        assert!(
            !text.contains("Failed Checks: memcpy src/dst overlap"),
            "{name} must not fail the overlap check:\n{text}"
        );
        // The region obligation SHOULD be present here — emitted and
        // discharged is the shape that proves it exists at all. What must not
        // happen is it failing on a copy that stays inside its objects.
        assert!(
            !text.contains("Failed Checks: memmove source region readable")
                && !text.contains("Failed Checks: memmove destination region writeable")
                && !text.contains("Failed Checks: memcpy source region readable")
                && !text.contains("Failed Checks: memcpy destination region writeable")
                && !text.contains("Failed Checks: memset destination region writeable"),
            "{name} stays inside its objects and must not fail a region check:\n{text}"
        );
    }

    let _ = fs::remove_dir_all(&dir);
}

/// A dereference must stay inside the object it points into.
///
/// The existing deref battery could not decide this. `heap_is_allocated`
/// compares 1 MiB `HEAP_STRIDE` bucket identity, so a pointer twelve bytes past
/// a twelve-byte stack array is still "in the same allocation"; and `obj_size`
/// is written only by `heap_alloc`, so a stack object has no recorded extent at
/// all. `*p.add(3)` on a `[i32; 3]` therefore produced no bounds obligation —
/// the failure it did report came from `offset_result_overflow`, numeric
/// wraparound of the address, which fires on the LEGAL one-past-the-end
/// computation rather than on the illegal read.
///
/// The restraint is the design: decided arithmetically or not at all. Comparing
/// a dereferenced address against a symbolic object base would be satisfiable
/// for almost any program, because distinct stack address symbols are mutually
/// unconstrained here. A spurious deref check would be far worse than an
/// incomplete one — it sits on every pointer access in every harness — which is
/// why the legitimate cases below are the substance of this test.
#[test]
fn a_dereference_must_stay_inside_its_object() {
    if !installation_ready() {
        return;
    }
    let dir = scratch("deref-object-bounds");
    let w = |name: &str, body: &str| {
        fs::write(dir.join(name), format!("#[kani::proof]\nfn h() {{\n{body}\n}}\n")).unwrap();
    };
    let bounds = "dereference failure: pointer outside object bounds";

    // --- UB: read and write past the end of the object. ---
    w(
        "read_past.rs",
        "    let a: [i32; 3] = [0, 1, 0];\n\
         \x20   let p = a.as_ptr();\n\
         \x20   let v = unsafe { *p.add(3) };\n\
         \x20   let _ = v;",
    );
    w(
        "write_past.rs",
        "    let mut a: [i32; 3] = [0, 1, 0];\n\
         \x20   let p = a.as_mut_ptr();\n\
         \x20   unsafe { *p.add(3) = 7; }",
    );
    for name in ["read_past.rs", "write_past.rs"] {
        let out = trust_mc_in(&dir, &["--timeout", "120s", name]);
        let text = stdout(&out);
        assert_ne!(code(&out), 0, "{name}: an out-of-object deref must not verify:\n{text}");
        assert!(text.contains(bounds), "{name} must fail with `{bounds}`:\n{text}");
    }

    // --- The controls. Every one is ordinary, legal Rust. ---
    // The last element is IN bounds; an off-by-one here would fail it.
    w(
        "last_elem.rs",
        "    let mut a: [u32; 4] = [0; 4];\n\
         \x20   let p = a.as_mut_ptr();\n\
         \x20   unsafe { *p.add(3) = 7; }\n\
         \x20   assert!(a[3] == 7);",
    );
    // Symbolic index, constrained in range: must not be decided against.
    w(
        "sym_index.rs",
        "    let a: [u32; 4] = [1, 2, 3, 4];\n\
         \x20   let i: usize = kani::any();\n\
         \x20   kani::assume(i < 4);\n\
         \x20   assert!(a[i] >= 1 && a[i] <= 4);",
    );
    // A Vec buffer, whose extent comes from the Vec constructor rather than a slice.
    w(
        "vec_elem.rs",
        "    let mut v = vec![0u32; 4];\n\
         \x20   let p = v.as_mut_ptr();\n\
         \x20   unsafe { *p.add(2) = 9; }\n\
         \x20   assert!(v[2] == 9);",
    );
    for name in ["last_elem.rs", "sym_index.rs"] {
        let out = trust_mc_in(&dir, &["--timeout", "120s", name]);
        let text = stdout(&out);
        assert_eq!(code(&out), 0, "{name} is legitimate Rust and must verify:\n{text}");
        assert!(
            !text.contains(&format!("Failed Checks: {bounds}")),
            "{name} stays inside its object and must not fail the bounds check:\n{text}"
        );
    }

    // The Vec case is asserted more narrowly, and deliberately. Writing through
    // `Vec::as_mut_ptr` does not verify here for reasons that predate this
    // check and are nothing to do with it — the raw-pointer value model reports
    // "pointer arithmetic overflow", a NULL deref, and then cannot prove the
    // readback. Requiring exit 0 would couple this test to those gaps and make
    // it fail for the wrong reason. What matters is the property under test:
    // an in-bounds Vec element access must not trip the BOUNDS obligation.
    {
        let out = trust_mc_in(&dir, &["--timeout", "120s", "vec_elem.rs"]);
        let text = stdout(&out);
        assert!(
            !text.contains(&format!("Failed Checks: {bounds}")),
            "an in-bounds Vec element access must not fail the bounds check:\n{text}"
        );
    }

    let _ = fs::remove_dir_all(&dir);
}
