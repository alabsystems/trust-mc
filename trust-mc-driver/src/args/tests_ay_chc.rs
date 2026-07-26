// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Tests for AY/CHC-specific CLI argument parsing and validation.
//!
//! Split from `tests.rs` to keep each test module under 500 lines.
//! Covers: ay-chc-verify, ay-chc-skip-verify, ay-wide-mem,
//! ay-chc-auto-invariants, ay-chc-proof-core, ay-chc-transforms,
//! ay-chc-engine, ay-chc-no-retry, ay-chc-bounded-unroll, export-chc-comp.

use clap::Parser;
use clap::error::ErrorKind;

use super::*;

/// Reusable helper: parse standalone args and run validation, expecting a specific error.
fn expect_validation_error(arg: &str, err: ErrorKind) {
    let args = StandaloneArgs::try_parse_from(arg.split_whitespace()).unwrap();
    assert_eq!(args.verify_opts.validate().unwrap_err().kind(), err);
}

#[test]
fn check_ay_chc_verify_rejected_as_unknown() {
    // --ay-chc-verify was removed; clap should reject it as an unknown argument.
    let result = StandaloneArgs::try_parse_from("kani test.rs --ay-chc-verify".split_whitespace());
    assert!(result.is_err());
    assert_eq!(result.unwrap_err().kind(), ErrorKind::UnknownArgument);
}

#[test]
fn check_ay_chc_skip_verify_requires_ay_chc() {
    // ay-chc-skip-verify without ay-chc should fail
    expect_validation_error("kani test.rs --ay-chc-skip-verify", ErrorKind::ArgumentConflict);

    // ay-chc-skip-verify with ay-chc should succeed
    let args = StandaloneArgs::try_parse_from(
        "kani file.rs --ay-chc --ay-chc-skip-verify".split_whitespace(),
    )
    .unwrap();
    assert!(matches!(args.verify_opts.validate(), Ok(())));
    assert!(args.verify_opts.ay_chc_skip_verify);
}

#[test]
fn check_ay_chc_verify_default_on() {
    // When --ay-chc is used alone, verification should be default-on:
    // ay_chc_skip_verify must be false (so !skip_verify == true == verify).
    let args = StandaloneArgs::try_parse_from("kani file.rs --ay-chc".split_whitespace()).unwrap();
    assert!(matches!(args.verify_opts.validate(), Ok(())));
    assert!(!args.verify_opts.ay_chc_skip_verify, "verification should be on by default");
}

#[test]
fn check_ay_wide_mem_requires_ay_chc() {
    // ay-wide-mem without ay-chc should fail
    expect_validation_error("kani test.rs --ay-wide-mem", ErrorKind::ArgumentConflict);
    // wide-mem alias without ay-chc should fail
    expect_validation_error("kani test.rs --wide-mem", ErrorKind::ArgumentConflict);

    // ay-wide-mem with ay-chc should succeed
    let args =
        StandaloneArgs::try_parse_from("kani file.rs --ay-chc --ay-wide-mem".split_whitespace())
            .unwrap();
    assert!(matches!(args.verify_opts.validate(), Ok(())));
    assert!(args.verify_opts.ay_wide_mem);

    // wide-mem alias with ay-chc should succeed
    let args =
        StandaloneArgs::try_parse_from("kani file.rs --ay-chc --wide-mem".split_whitespace())
            .unwrap();
    assert!(matches!(args.verify_opts.validate(), Ok(())));
    assert!(args.verify_opts.ay_wide_mem);
}

#[test]
fn check_ay_chc_auto_invariants_off_without_chc() {
    let args = StandaloneArgs::try_parse_from("kani file.rs".split_whitespace()).unwrap();
    assert_eq!(args.verify_opts.ay_chc_auto_invariants, AYChcAutoInvariantsMode::Off);
    assert!(matches!(args.verify_opts.validate(), Ok(())));
}

#[test]
fn check_ay_chc_auto_invariants_range_requires_ay_chc() {
    expect_validation_error(
        "kani test.rs --ay-chc-auto-invariants=range",
        ErrorKind::ArgumentConflict,
    );
}

#[test]
fn check_ay_chc_auto_invariants_houdini_requires_ay_chc() {
    expect_validation_error(
        "kani test.rs --ay-chc-auto-invariants=houdini",
        ErrorKind::ArgumentConflict,
    );
}

#[test]
#[cfg(feature = "ay-chc-native")]
fn check_ay_chc_auto_invariants_houdini_with_ay_chc() {
    let args = StandaloneArgs::try_parse_from(
        "kani file.rs --ay-chc --ay-chc-auto-invariants=houdini".split_whitespace(),
    )
    .unwrap();
    assert!(matches!(args.verify_opts.validate(), Ok(())));
    assert_eq!(args.verify_opts.ay_chc_auto_invariants, AYChcAutoInvariantsMode::Houdini);
}

#[test]
#[cfg(not(feature = "ay-chc-native"))]
fn check_ay_chc_auto_invariants_range_requires_native() {
    expect_validation_error(
        "kani test.rs --ay-chc --ay-chc-auto-invariants=range",
        ErrorKind::ArgumentConflict,
    );
}

#[test]
#[cfg(not(feature = "ay-chc-native"))]
fn check_ay_chc_auto_invariants_houdini_requires_native() {
    expect_validation_error(
        "kani test.rs --ay-chc --ay-chc-auto-invariants=houdini",
        ErrorKind::ArgumentConflict,
    );
}

#[test]
fn check_ay_chc_auto_invariants_invalid_value() {
    let result = StandaloneArgs::try_parse_from(
        "kani file.rs --ay-chc --ay-chc-auto-invariants=unknown".split_whitespace(),
    );
    assert!(result.is_err());
}

#[test]
fn check_ay_chc_proof_core_off_without_chc() {
    // Default (off) should be accepted without --ay-chc
    let args = StandaloneArgs::try_parse_from("kani file.rs".split_whitespace()).unwrap();
    assert_eq!(args.verify_opts.ay_chc_proof_core, AYChcProofCoreMode::Off);
    assert!(matches!(args.verify_opts.validate(), Ok(())));
}

#[test]
fn check_ay_chc_proof_core_range_requires_ay_chc() {
    expect_validation_error("kani test.rs --ay-chc-proof-core=range", ErrorKind::ArgumentConflict);
}

#[test]
fn check_ay_chc_proof_core_range_with_ay_chc() {
    let args = StandaloneArgs::try_parse_from(
        "kani file.rs --ay-chc --ay-chc-proof-core=range".split_whitespace(),
    )
    .unwrap();
    assert!(matches!(args.verify_opts.validate(), Ok(())));
    assert_eq!(args.verify_opts.ay_chc_proof_core, AYChcProofCoreMode::Range);
}

#[test]
fn check_ay_chc_proof_core_invalid_value() {
    let result = StandaloneArgs::try_parse_from(
        "kani file.rs --ay-chc --ay-chc-proof-core=invalid".split_whitespace(),
    );
    assert!(result.is_err());
}

#[test]
fn check_ay_chc_transforms_reject_array_instantiation() {
    expect_validation_error(
        "kani test.rs --ay-chc --ay-chc-transform --ay-chc-transforms array-instantiation",
        ErrorKind::InvalidValue,
    );
}

#[test]
fn check_ay_chc_transforms_accept_inline_and_all() {
    let inline_only = StandaloneArgs::try_parse_from(
        "kani test.rs --ay-chc --ay-chc-transform --ay-chc-transforms inline".split_whitespace(),
    )
    .unwrap();
    assert!(matches!(inline_only.verify_opts.validate(), Ok(())));

    let all = StandaloneArgs::try_parse_from(
        "kani test.rs --ay-chc --ay-chc-transform --ay-chc-transforms all".split_whitespace(),
    )
    .unwrap();
    assert!(matches!(all.verify_opts.validate(), Ok(())));
}

#[test]
fn check_ay_chc_engine_auto_without_chc() {
    let args = StandaloneArgs::try_parse_from("kani file.rs".split_whitespace()).unwrap();
    assert_eq!(args.verify_opts.ay_chc_engine, AYChcEngine::Auto);
    assert!(matches!(args.verify_opts.validate(), Ok(())));
}

#[test]
fn check_ay_chc_engine_bmc_requires_ay_chc() {
    expect_validation_error("kani test.rs --ay-chc-engine bmc", ErrorKind::ArgumentConflict);
}

#[test]
fn check_ay_chc_engine_bmc_with_ay_chc() {
    let args = StandaloneArgs::try_parse_from(
        "kani file.rs --ay-chc --ay-chc-engine bmc".split_whitespace(),
    )
    .unwrap();
    assert!(matches!(args.verify_opts.validate(), Ok(())));
    assert_eq!(args.verify_opts.ay_chc_engine, AYChcEngine::Bmc);
}

#[test]
fn check_ay_chc_no_retry_requires_ay_chc() {
    expect_validation_error("kani test.rs --ay-chc-no-retry", ErrorKind::ArgumentConflict);
}

#[test]
fn check_ay_chc_no_retry_with_ay_chc() {
    let args = StandaloneArgs::try_parse_from(
        "kani file.rs --ay-chc --ay-chc-no-retry".split_whitespace(),
    )
    .unwrap();
    assert!(matches!(args.verify_opts.validate(), Ok(())));
    assert!(args.verify_opts.ay_chc_no_retry);
}

#[test]
fn check_ay_chc_bounded_unroll_requires_ay_chc() {
    expect_validation_error("kani test.rs --ay-chc-bounded-unroll", ErrorKind::ArgumentConflict);
}

#[test]
fn check_ay_chc_bounded_unroll_with_ay_chc() {
    let args = StandaloneArgs::try_parse_from(
        "kani file.rs --ay-chc --ay-chc-bounded-unroll".split_whitespace(),
    )
    .unwrap();
    assert!(matches!(args.verify_opts.validate(), Ok(())));
    assert!(args.verify_opts.ay_chc_bounded_unroll);
}

#[test]
fn check_export_chc_comp_rejected_without_ay_chc() {
    expect_validation_error(
        "kani test.rs --export-chc-comp /tmp/out.smt2",
        ErrorKind::ArgumentConflict,
    );
}

#[test]
fn check_export_chc_comp_with_ay_chc() {
    let args = StandaloneArgs::try_parse_from(
        "kani file.rs --ay-chc --export-chc-comp /tmp/out.smt2".split_whitespace(),
    )
    .unwrap();
    assert!(matches!(args.verify_opts.validate(), Ok(())));
    assert_eq!(
        args.verify_opts.export_chc_comp.as_deref(),
        Some(std::path::Path::new("/tmp/out.smt2"))
    );
}
