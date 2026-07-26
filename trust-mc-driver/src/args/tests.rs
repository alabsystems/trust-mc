// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Tests for trust-mc CLI argument parsing and validation.

use std::path::PathBuf;

use clap::Parser;
use clap::error::{Error, ErrorKind};

use super::*;

/// Ensure users can pass multiple harnesses options and that the value is accumulated.
#[test]
fn check_multiple_harnesses() {
    let args =
        StandaloneArgs::try_parse_from("kani input.rs --harness a --harness b".split(" ")).unwrap();
    assert!(!args.list_harnesses);
    assert_eq!(args.verify_opts.harnesses, vec!["a".to_owned(), "b".to_owned()]);
}

#[test]
fn check_multiple_harnesses_without_flag_fail() {
    let result =
        StandaloneArgs::try_parse_from("kani input.rs --harness harness_1 harness_2".split(" "));
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().kind(), ErrorKind::ArgumentConflict);
}

#[test]
fn check_standalone_harnesses_flag_parses_as_listing_request() {
    let file = tempfile::NamedTempFile::new().unwrap();
    let path = file.path().to_str().unwrap();
    let args = StandaloneArgs::try_parse_from(["kani", path, "--harnesses"]).unwrap();

    assert!(args.list_harnesses);
    assert!(args.command.is_none());
    assert!(args.verify_opts.harnesses.is_empty());
    assert!(args.validate().is_ok());
}

#[test]
fn check_cargo_harnesses_flag_parses_as_listing_request() {
    let args = CargoKaniArgs::try_parse_from(["cargo-trust-mc", "--harnesses"]).unwrap();

    assert!(args.list_harnesses);
    assert!(args.command.is_none());
    assert!(args.verify_opts.harnesses.is_empty());
    assert!(args.validate().is_ok());
}

#[test]
fn check_harnesses_flag_rejects_quiet_pretty_listing() {
    let err = CargoKaniArgs::try_parse_from(["cargo-trust-mc", "--harnesses", "--quiet"])
        .unwrap()
        .validate()
        .unwrap_err();

    assert_eq!(err.kind(), ErrorKind::ArgumentConflict);
}

#[test]
fn check_harnesses_flag_rejects_subcommands() {
    let err = CargoKaniArgs::try_parse_from(["cargo-trust-mc", "--harnesses", "list"])
        .unwrap()
        .validate()
        .unwrap_err();

    assert_eq!(err.kind(), ErrorKind::ArgumentConflict);
}

#[test]
fn check_cargo_list_subcommand_still_parses() {
    let args = CargoKaniArgs::try_parse_from(["cargo-trust-mc", "list"]).unwrap();

    assert!(!args.list_harnesses);
    assert!(matches!(args.command, Some(CargoKaniSubcommand::List(..))));
}

#[test]
fn check_proof_summary_json_flag_parses() {
    let args =
        CargoKaniArgs::try_parse_from(["cargo-trust-mc", "--proof-summary-json", "summary.json"])
            .unwrap();

    assert_eq!(args.verify_opts.proof_summary_json.unwrap(), PathBuf::from("summary.json"));
}

#[test]
fn check_proof_summary_json_rejects_existing_directory() {
    let dir = tempfile::tempdir().unwrap();
    let err = CargoKaniArgs::try_parse_from([
        "cargo-trust-mc",
        "--proof-summary-json",
        dir.path().to_str().unwrap(),
    ])
    .unwrap()
    .validate()
    .unwrap_err();

    assert_eq!(err.kind(), ErrorKind::InvalidValue);
}

#[test]
fn check_multiple_packages() {
    // accepts repeated:
    let a = CargoKaniArgs::try_parse_from(vec!["cargo-kani", "-p", "a", "-p", "b"]).unwrap();
    assert_eq!(a.verify_opts.cargo.package, vec!["a".to_owned(), "b".to_owned()]);
    let b = CargoKaniArgs::try_parse_from(vec![
        "cargo-kani",
        "-p",
        "a", // no -p
        "b",
    ]);
    // BUG: should not accept sequential:
    // Related: https://github.com/model-checking/kani/issues/2025
    // This assert should ideally return an error, and the assertion should instead be assert!(b.is_err())
    assert!(b.is_ok());
}

#[test]
fn check_dry_run_fails() {
    // We don't support --dry-run anymore but we print a friendly reminder for now.
    let args = vec!["kani", "file.rs", "--dry-run"];
    let err = StandaloneArgs::try_parse_from(&args).unwrap().verify_opts.validate().unwrap_err();
    assert_eq!(err.kind(), ErrorKind::ValueValidation);
}

/// trust-mc should fail if the argument given is not a file.
#[test]
fn check_invalid_input_fails() {
    let args = vec!["kani", "."];
    let err = StandaloneArgs::try_parse_from(&args).unwrap().validate().unwrap_err();
    assert_eq!(err.kind(), ErrorKind::InvalidValue);
}

#[test]
fn standalone_accepts_trust_vc_bundle_without_input() {
    let args = StandaloneArgs::try_parse_from(
        "kani --trust-vc-bundle /tmp/fixture.json".split_whitespace(),
    )
    .unwrap();
    assert_eq!(args.input, None);
    assert_eq!(args.verify_opts.trust_vc_bundle, Some(PathBuf::from("/tmp/fixture.json")));
    assert!(matches!(args.validate(), Ok(())));
}

#[test]
fn standalone_rejects_input_with_trust_vc_bundle() {
    let args = StandaloneArgs::try_parse_from(
        "kani input.rs --trust-vc-bundle /tmp/fixture.json".split_whitespace(),
    )
    .unwrap();
    let err = args.validate().unwrap_err();
    assert_eq!(err.kind(), ErrorKind::ArgumentConflict);
}

#[test]
fn cargo_accepts_trust_vc_bundle() {
    let args = CargoKaniArgs::try_parse_from(
        "cargo-trust-mc --trust-vc-bundle /tmp/fixture.json".split_whitespace(),
    )
    .unwrap();
    assert_eq!(args.verify_opts.trust_vc_bundle, Some(PathBuf::from("/tmp/fixture.json")));
    assert!(matches!(args.validate(), Ok(())));
}

#[test]
fn check_unwind_conflicts() {
    // --unwind cannot be called without --harness
    let args = vec!["kani", "file.rs", "--unwind", "3"];
    let err = StandaloneArgs::try_parse_from(args).unwrap_err();
    assert_eq!(err.kind(), ErrorKind::MissingRequiredArgument);
}

fn parse_unstable_disabled(args: &str) -> Result<StandaloneArgs, Error> {
    let args = format!("kani file.rs {args}");
    let parse_res = StandaloneArgs::try_parse_from(args.split(' '))?;
    parse_res.verify_opts.validate()?;
    Ok(parse_res)
}

fn parse_unstable_enabled(args: &str, unstable: UnstableFeature) -> Result<StandaloneArgs, Error> {
    let args = format!("kani -Z {unstable} file.rs {args}");
    let parse_res = StandaloneArgs::try_parse_from(args.split(' '))?;
    parse_res.verify_opts.validate()?;
    Ok(parse_res)
}

#[test]
fn check_restrict_vtable_unstable() {
    let res =
        parse_unstable_enabled("--output-format=terse", UnstableFeature::RestrictVtable).unwrap();
    assert!(res.verify_opts.restrict_vtable());

    let res =
        parse_unstable_enabled("--no-restrict-vtable", UnstableFeature::RestrictVtable).unwrap();
    assert!(!res.verify_opts.restrict_vtable());
}

#[test]
fn check_concrete_playback_unstable() {
    let check = |input: &str| {
        let args = input.split_whitespace();
        let result = StandaloneArgs::try_parse_from(args).unwrap().validate();
        assert!(result.is_err());

        let kind = result.unwrap_err().kind();
        assert!(matches!(kind, ErrorKind::MissingRequiredArgument), "Found {kind:?}");
    };

    check("kani file.rs --concrete-playback=inplace");
    check("kani file.rs --concrete-playback=print");
}

/// Check if parsing the given argument string results in the given error.
fn expect_validation_error(arg: &str, err: ErrorKind) {
    let args = StandaloneArgs::try_parse_from(arg.split_whitespace()).unwrap();
    assert_eq!(args.verify_opts.validate().unwrap_err().kind(), err);
}

#[test]
fn check_concrete_playback_conflicts() {
    expect_validation_error(
        "kani --concrete-playback=print --quiet -Z concrete-playback test.rs",
        ErrorKind::ArgumentConflict,
    );
    expect_validation_error(
        "kani --concrete-playback=inplace --output-format=old -Z concrete-playback test.rs",
        ErrorKind::ArgumentConflict,
    );
}

#[test]
fn check_enable_stubbing() {
    let res = parse_unstable_disabled("--harness foo").unwrap();
    assert!(!res.verify_opts.is_stubbing_enabled());

    let res = parse_unstable_disabled("--harness foo -Z stubbing").unwrap();
    assert!(res.verify_opts.is_stubbing_enabled());

    // `-Z stubbing` can now be called with concrete playback.
    let res = parse_unstable_disabled(
        "--harness foo --concrete-playback=print -Z concrete-playback -Z stubbing",
    )
    .unwrap();
    // Note that `res.validate()` fails because input file does not exist.
    assert!(matches!(res.verify_opts.validate(), Ok(())));
}

#[test]
fn check_check_disabling_flags_parse() {
    let args = StandaloneArgs::try_parse_from(
        "kani file.rs --no-memory-safety-checks --no-overflow-checks --no-undefined-function-checks"
            .split_whitespace(),
    )
    .unwrap();
    assert!(args.verify_opts.checks.no_memory_safety_checks);
    assert!(args.verify_opts.checks.no_overflow_checks);
    assert!(args.verify_opts.checks.no_undefined_function_checks);
}

#[test]
fn check_backend_default_is_auto() {
    let args = StandaloneArgs::try_parse_from("kani file.rs".split_whitespace()).unwrap();
    assert_eq!(args.verify_opts.backend, Backend::Auto);
}

#[test]
fn check_fail_on_unvalidated_success_defaults_to_false() {
    let args = StandaloneArgs::try_parse_from("kani file.rs".split_whitespace()).unwrap();
    assert!(!args.verify_opts.fail_on_unvalidated_success);
}

#[test]
fn check_fail_on_unvalidated_success_parses_for_standalone_and_cargo() {
    let args = StandaloneArgs::try_parse_from(
        "kani file.rs --fail-on-unvalidated-success".split_whitespace(),
    )
    .unwrap();
    assert!(args.verify_opts.fail_on_unvalidated_success);

    let args = CargoKaniArgs::try_parse_from(
        "cargo-trust-mc --fail-on-unvalidated-success".split_whitespace(),
    )
    .unwrap();
    assert!(args.verify_opts.fail_on_unvalidated_success);
}

#[test]
fn check_backend_resolve_ay_explicit() {
    // Explicit AY backend resolves to itself when ay is available
    if which::which("ay").is_ok() {
        let resolved = Backend::AY.resolve(AYSolver::Auto).unwrap();
        assert_eq!(resolved, Backend::AY);
    }
}

#[cfg(feature = "ay-direct")]
#[test]
fn check_backend_resolve_ay_with_direct_solver() {
    // Direct linking does not require the ay binary
    let resolved = Backend::AY.resolve(AYSolver::Direct).unwrap();
    assert_eq!(resolved, Backend::AY);
}

#[cfg(feature = "ay-direct")]
#[test]
fn check_backend_resolve_auto_with_direct_solver() {
    // Auto should pick AY backend when direct linking is explicitly selected
    let resolved = Backend::Auto.resolve(AYSolver::Direct).unwrap();
    assert_eq!(resolved, Backend::AY);
}

#[test]
fn check_ay_solver_requires_ay_binary() {
    // Auto and AY require the ay binary
    assert!(AYSolver::Auto.requires_ay_binary());
    assert!(AYSolver::AY.requires_ay_binary());
}

#[cfg(feature = "ay-direct")]
#[test]
fn check_ay_solver_direct_does_not_require_ay_binary() {
    assert!(!AYSolver::Direct.requires_ay_binary());
}

#[test]
fn check_backend_resolve_returns_concrete() {
    // resolve() should never return Auto
    let resolved = Backend::Auto.resolve(AYSolver::Auto);
    match resolved {
        Ok(backend) => assert!(!backend.is_auto()),
        Err(_) => { /* No solvers available - that's fine for this test */ }
    }
}

#[test]
fn check_features_parsing() {
    fn parse(args: &[&str]) -> Vec<String> {
        CargoKaniArgs::try_parse_from(args).unwrap().verify_opts.cargo.features()
    }

    // spaces, commas, multiple repeated args, all ok
    assert_eq!(parse(&["kani", "--features", "a b c"]), ["a", "b", "c"]);
    assert_eq!(parse(&["kani", "--features", "a,b,c"]), ["a", "b", "c"]);
    assert_eq!(parse(&["kani", "--features", "a", "--features", "b,c"]), ["a", "b", "c"]);
    assert_eq!(parse(&["kani", "--features", "a b", "-Fc"]), ["a", "b", "c"]);
}

#[test]
fn check_kani_playback() {
    let input = "kani playback file.rs -- dummy".split_whitespace();
    let args = StandaloneArgs::try_parse_from(input).unwrap();
    assert_eq!(args.input, None);
    assert!(matches!(args.command, Some(StandaloneSubcommand::Playback(..))));
}

#[test]
fn check_standalone_does_not_accept_cargo_opts() {
    fn check_invalid_args<'a, I>(args: I)
    where
        I: IntoIterator<Item = &'a str>,
    {
        let err = StandaloneArgs::try_parse_from(args).unwrap().validate().unwrap_err();
        assert_eq!(err.kind(), ErrorKind::UnknownArgument)
    }

    check_invalid_args("kani input.rs --all-targets".split_whitespace());
    check_invalid_args("kani input.rs --bench Speed".split_whitespace());
    check_invalid_args("kani input.rs --benches".split_whitespace());
    check_invalid_args("kani input.rs --bins".split_whitespace());
    check_invalid_args("kani input.rs --bin Binary".split_whitespace());
    check_invalid_args("kani input.rs --lib".split_whitespace());
    check_invalid_args("kani input.rs --example Demo".split_whitespace());
    check_invalid_args("kani input.rs --examples".split_whitespace());
    check_invalid_args("kani input.rs --test Integration".split_whitespace());

    check_invalid_args("kani input.rs --all-features".split_whitespace());
    check_invalid_args("kani input.rs --no-default-features".split_whitespace());
    check_invalid_args("kani input.rs --features feat".split_whitespace());
    check_invalid_args("kani input.rs --manifest-path pkg/Cargo.toml".split_whitespace());
    check_invalid_args("kani input.rs --workspace".split_whitespace());
    check_invalid_args("kani input.rs --package foo".split_whitespace());
    check_invalid_args("kani input.rs --exclude bar --workspace".split_whitespace());
}

#[test]
fn check_no_assert_contracts() {
    let args = "kani input.rs --no-assert-contracts".split_whitespace();
    let err = StandaloneArgs::try_parse_from(args).unwrap().validate().unwrap_err();
    assert_eq!(err.kind(), ErrorKind::MissingRequiredArgument);
}

#[test]
fn check_gen_c_is_cbmc_only_error() {
    let args = StandaloneArgs::try_parse_from("kani input.rs --gen-c".split_whitespace()).unwrap();
    let err = args.verify_opts.validate().unwrap_err();
    assert_eq!(err.kind(), ErrorKind::InvalidValue);
    assert!(
        err.to_string().contains("--gen-c is CBMC-only"),
        "expected --gen-c CBMC-only message, got: {err}"
    );
}

#[test]
fn check_cbmc_args_is_warning_not_error() {
    let _capture = crate::util::warning_test_capture_start();
    let args = StandaloneArgs::try_parse_from(
        "kani input.rs --cbmc-args --object-bits 10".split_whitespace(),
    )
    .unwrap();
    assert!(args.verify_opts.validate().is_ok(), "--cbmc-args should warn, not error");
    assert_eq!(args.verify_opts.cbmc_args, vec!["--object-bits".to_string(), "10".to_string()]);
    let messages = crate::util::warning_test_messages_take();
    assert!(
        messages.iter().any(|m| m.contains("--cbmc-args is CBMC-only")),
        "expected --cbmc-args warning, captured: {messages:?}"
    );
}

#[test]
fn check_solver_is_warning_not_error_for_kani_solver_names() {
    for solver in ["bitwuzla", "cadical", "cvc5", "kissat", "minisat", "z3", "bin=kissat"] {
        let _capture = crate::util::warning_test_capture_start();
        let args = StandaloneArgs::try_parse_from(
            format!("kani input.rs --solver {solver}").split_whitespace(),
        )
        .unwrap();
        assert!(args.verify_opts.validate().is_ok(), "--solver {solver} should warn, not error");
        assert_eq!(args.verify_opts.solver.as_deref(), Some(solver));
        let messages = crate::util::warning_test_messages_take();
        assert!(
            messages.iter().any(|m| m.contains("--solver")),
            "expected --solver warning for {solver}, captured: {messages:?}"
        );
    }
}

#[test]
fn check_solver_rejects_invalid_kani_solver_value() {
    let err = StandaloneArgs::try_parse_from("kani input.rs --solver foo=bar".split_whitespace())
        .unwrap_err();
    assert_eq!(err.kind(), ErrorKind::ValueValidation);
    assert!(
        err.to_string().contains("expected one of"),
        "expected invalid --solver message, got: {err}"
    );
}

#[test]
fn test_synthesize_loop_contracts_warns_non_fatal() {
    let _capture = crate::util::warning_test_capture_start();
    let args = StandaloneArgs::try_parse_from(
        "kani input.rs --synthesize-loop-contracts".split_whitespace(),
    )
    .unwrap();
    assert!(
        args.verify_opts.validate().is_ok(),
        "--synthesize-loop-contracts should warn, not error"
    );
    assert!(args.verify_opts.synthesize_loop_contracts);
    let messages = crate::util::warning_test_messages_take();
    assert!(
        messages.iter().any(|m| m.contains("--synthesize-loop-contracts is a no-op in trust-mc")),
        "expected --synthesize-loop-contracts warning, captured: {messages:?}"
    );
}

#[test]
fn test_print_llbc_errors() {
    let args =
        StandaloneArgs::try_parse_from("kani input.rs --print-llbc".split_whitespace()).unwrap();
    let err = args.verify_opts.validate().unwrap_err();
    assert_eq!(err.kind(), ErrorKind::InvalidValue);
    assert!(
        err.to_string().contains("--print-llbc is not supported: Lean backend not in trust-mc"),
        "expected --print-llbc Lean-backend message, got: {err}"
    );
}

#[test]
fn check_cbmc_debug_flags_warn_or_error() {
    for flag in ["--no-slice-formula", "--run-sanity-checks"] {
        let _capture = crate::util::warning_test_capture_start();
        let args =
            StandaloneArgs::try_parse_from(format!("kani input.rs {flag}").split_whitespace())
                .unwrap();
        assert!(args.verify_opts.validate().is_ok(), "{flag} should warn, not error");
        let messages = crate::util::warning_test_messages_take();
        assert!(
            messages.iter().any(|m| m.contains(flag)),
            "expected {flag} warning, captured: {messages:?}"
        );
    }

    let args =
        StandaloneArgs::try_parse_from("kani input.rs --write-json-symtab".split_whitespace())
            .unwrap();
    let err = args.verify_opts.validate().unwrap_err();
    assert_eq!(err.kind(), ErrorKind::ValueValidation);
    assert!(
        err.to_string().contains("--write-json-symtab is obsolete"),
        "expected --write-json-symtab obsolete message, got: {err}"
    );
}
