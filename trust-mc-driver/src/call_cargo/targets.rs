// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::args::VerificationArgs;
use cargo_metadata::{Package, Target, TargetKind};
use std::fmt::{self, Display};
use std::io::Write;
use tracing::debug;

/// Possible verification targets.
#[derive(Debug)]
pub(super) enum VerificationTarget {
    Bench(Target),
    Bin(Target),
    Example(Target),
    Lib(Target),
    Test(Target),
}

impl VerificationTarget {
    /// Convert to cargo argument that select the specific target.
    pub(super) fn to_args(&self) -> Vec<String> {
        match self {
            VerificationTarget::Bench(target) => vec![String::from("--bench"), target.name.clone()],
            VerificationTarget::Test(target) => vec![String::from("--test"), target.name.clone()],
            VerificationTarget::Bin(target) => vec![String::from("--bin"), target.name.clone()],
            VerificationTarget::Example(target) => {
                vec![String::from("--example"), target.name.clone()]
            }
            VerificationTarget::Lib(_) => vec![String::from("--lib")],
        }
    }

    pub(super) fn target(&self) -> &Target {
        match self {
            VerificationTarget::Bench(target)
            | VerificationTarget::Example(target)
            | VerificationTarget::Test(target)
            | VerificationTarget::Bin(target)
            | VerificationTarget::Lib(target) => target,
        }
    }
}

impl Display for VerificationTarget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VerificationTarget::Bench(target) => write!(f, "benchmark `{}`", target.name),
            VerificationTarget::Test(target) => write!(f, "test `{}`", target.name),
            VerificationTarget::Bin(target) => write!(f, "binary `{}`", target.name),
            VerificationTarget::Example(target) => write!(f, "example `{}`", target.name),
            VerificationTarget::Lib(target) => write!(f, "lib `{}`", target.name),
        }
    }
}

/// Extract the targets inside a package.
///
/// If `--tests` is given, the list of targets will include any integration tests.
///
/// We use the `target.kind` as documented here. Note that `kind` for library will
/// match the `crate-type`, despite them not being explicitly listed in the documentation:
/// <https://docs.rs/cargo_metadata/0.15.0/cargo_metadata/struct.Target.html#structfield.kind>
///
/// The documentation for `crate-type` explicitly states that the only time `kind` and
/// `crate-type` differs is for examples.
/// <https://docs.rs/cargo_metadata/0.15.0/cargo_metadata/struct.Target.html#structfield.crate_types>
pub(super) fn package_targets(
    args: &VerificationArgs,
    package: &Package,
) -> Vec<VerificationTarget> {
    let mut ignored_tests = vec![];
    let mut ignored_unsupported = vec![];
    let mut verification_targets = vec![];
    for target in &package.targets {
        debug!(name=?package.name, target=?target.name, kind=?target.kind, crate_type=?target
                .crate_types,
                "package_targets");
        let (mut supported_lib, mut unsupported_lib) = (false, false);
        for kind in &target.kind {
            collect_package_target_kind(
                args,
                target,
                kind,
                &mut verification_targets,
                &mut ignored_tests,
                &mut ignored_unsupported,
                &mut supported_lib,
                &mut unsupported_lib,
            );
        }
        match (supported_lib, unsupported_lib) {
            (true, true) => crate::util::warning(&format_args!(
                "Skipped verification of `{}` due to unsupported crate-type: `proc-macro`.",
                target.name
            )),
            (true, false) => verification_targets.push(VerificationTarget::Lib(target.clone())),
            (_, _) => {}
        }
    }

    if args.common_args.verbose {
        // Print targets that were skipped only on verbose mode.
        if !ignored_tests.is_empty() {
            let _ = writeln!(
                std::io::stdout(),
                "Skipped the following test targets: '{}'.",
                ignored_tests.join("', '")
            );
            let _ = writeln!(
                std::io::stdout(),
                "    -> Use '--tests' to verify harnesses inside a 'test' crate."
            );
        }
        if !ignored_unsupported.is_empty() {
            let _ = writeln!(
                std::io::stdout(),
                "Skipped verification of the following unsupported targets: '{}'.",
                ignored_unsupported.join("', '")
            );
        }
    }
    verification_targets
}

fn collect_package_target_kind<'a>(
    args: &VerificationArgs,
    target: &'a Target,
    kind: &TargetKind,
    verification_targets: &mut Vec<VerificationTarget>,
    ignored_tests: &mut Vec<&'a str>,
    ignored_unsupported: &mut Vec<&'a str>,
    supported_lib: &mut bool,
    unsupported_lib: &mut bool,
) {
    match kind {
        TargetKind::Bench if args.target.include_bench(&target.name) => {
            verification_targets.push(VerificationTarget::Bench(target.clone()));
        }
        TargetKind::Bin if args.target.include_bin(&target.name) => {
            verification_targets.push(VerificationTarget::Bin(target.clone()));
        }
        TargetKind::Example if args.target.include_example(&target.name) => {
            verification_targets.push(VerificationTarget::Example(target.clone()));
        }
        TargetKind::Lib
        | TargetKind::RLib
        | TargetKind::CDyLib
        | TargetKind::DyLib
        | TargetKind::StaticLib => {
            if args.target.include_lib() {
                *supported_lib = true;
            }
        }
        TargetKind::ProcMacro => {
            if args.target.include_lib() {
                *unsupported_lib = true;
                ignored_unsupported.push(target.name.as_str());
            }
        }
        TargetKind::Test if args.target.include_test(&target.name) => {
            if args.tests || args.target.explicitly_selects_test_targets() {
                verification_targets.push(VerificationTarget::Test(target.clone()));
            } else {
                ignored_tests.push(target.name.as_str());
            }
        }
        TargetKind::Bench | TargetKind::Bin | TargetKind::Example | TargetKind::Test => {}
        _ => ignored_unsupported.push(target.name.as_str()),
    }
}

/// Filter the requested features to only include those declared by the given package.
///
/// This matches cargo's behavior for `cargo test --workspace --features <feature>` where
/// features are applied only to packages that declare them, and silently skipped for
/// packages that don't.
pub(super) fn filter_features_for_package(
    requested_features: &[String],
    package: &Package,
) -> Vec<String> {
    requested_features
        .iter()
        .filter(|feature| package.features.contains_key(*feature))
        .cloned()
        .collect()
}
