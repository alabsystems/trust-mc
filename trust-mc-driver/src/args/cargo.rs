// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Module that define parsers that mimic Cargo options.

use crate::args::ValidateArgs;
use crate::util::args::CargoArg;
use clap::error::Error;
use std::path::PathBuf;

/// Arguments that trust-mc pass down into Cargo essentially uninterpreted.
/// These generally have to do with selection of packages or activation of features.
/// These do not (currently) include cargo args that trust-mc pays special attention to:
/// for instance, we keep `--tests` and `--target-dir` elsewhere.
#[derive(Debug, Default, clap::Args)]
#[clap(next_help_heading = "Cargo Common Options")]
pub(crate) struct CargoCommonArgs {
    /// Activate all package features
    #[arg(long)]
    pub all_features: bool,

    /// Exclude the specified packages
    #[arg(long, short, requires("workspace"), conflicts_with("package"), num_args(1..))]
    pub exclude: Vec<String>,

    // This tolerates spaces too, but we say "comma" only because this is the least error-prone approach...
    /// Comma separated list of package features to activate
    #[arg(short = 'F', long)]
    features: Vec<String>,

    /// Path to Cargo.toml
    #[arg(long, name = "PATH")]
    pub manifest_path: Option<PathBuf>,

    /// Do not activate the `default` feature
    #[arg(long)]
    pub no_default_features: bool,

    /// Run trust-mc on the specified packages (see `cargo help pkgid` for the accepted format)
    #[arg(long, short, conflicts_with("workspace"), num_args(1..))]
    pub package: Vec<String>,

    /// Build all packages in the workspace
    #[arg(long)]
    pub workspace: bool,
}

impl CargoCommonArgs {
    /// Parse the string we're given into a list of feature names
    ///
    /// clap can't do this for us because it accepts multiple different delimeters
    pub(crate) fn features(&self) -> Vec<String> {
        let mut result = Vec::new();

        for s in &self.features {
            for piece in s.split(&[' ', ',']) {
                result.push(piece.to_owned());
            }
        }
        result
    }

    /// Convert the arguments back to a format that cargo can understand.
    /// Note that the `exclude` option requires special processing and it's not included here.
    fn to_cargo_args(&self) -> Vec<CargoArg> {
        let mut cargo_args: Vec<CargoArg> = vec![];
        if self.all_features {
            cargo_args.push("--all-features".into());
        }

        if self.no_default_features {
            cargo_args.push("--no-default-features".into());
        }

        let features = self.features();
        if !features.is_empty() {
            cargo_args.push(format!("--features={}", features.join(",")).into());
        }

        if let Some(path) = &self.manifest_path {
            cargo_args.push("--manifest-path".into());
            cargo_args.push(path.into());
        }
        if self.workspace {
            cargo_args.push("--workspace".into())
        }

        cargo_args.extend(self.package.iter().map(|pkg| format!("-p={pkg}").into()));
        cargo_args
    }
}

/// Leave it for Cargo to validate these for now.
impl ValidateArgs for CargoCommonArgs {
    fn validate(&self) -> Result<(), Error> {
        Ok(())
    }
}

/// Arguments that cargo-trust-mc supports to select build / verification / test target.
/// See <https://doc.rust-lang.org/cargo/commands/cargo-test.html#target-selection> for more
/// details.
#[derive(Debug, Default, clap::Args)]
#[clap(next_help_heading = "Cargo Target Options")]
pub(crate) struct CargoTargetArgs {
    /// Check all targets.
    #[arg(long)]
    pub all_targets: bool,

    /// Check only the specified benchmark target.
    #[arg(long)]
    pub bench: Vec<String>,

    /// Check all benchmarks.
    #[arg(long)]
    pub benches: bool,

    /// Check only the specified binary target.
    #[arg(long)]
    pub bin: Vec<String>,

    /// Check all binaries.
    #[arg(long)]
    pub bins: bool,

    /// Check only the specified example target.
    #[arg(long)]
    pub example: Vec<String>,

    /// Check all examples.
    #[arg(long)]
    pub examples: bool,

    /// Check only the package's library unit tests.
    #[arg(long)]
    pub lib: bool,

    /// Check only the specified test target.
    #[arg(long)]
    pub test: Vec<String>,
}

impl CargoTargetArgs {
    /// Convert the arguments back to a format that cargo can understand.
    fn to_cargo_args(&self) -> Vec<CargoArg> {
        let mut cargo_args = Vec::new();

        if self.all_targets {
            cargo_args.push("--all-targets".into());
        }

        cargo_args.extend(self.bench.iter().map(|benchmark| format!("--bench={benchmark}").into()));

        if self.benches {
            cargo_args.push("--benches".into());
        }

        cargo_args.extend(self.bin.iter().map(|binary| format!("--bin={binary}").into()));

        if self.bins {
            cargo_args.push("--bins".into());
        }

        cargo_args.extend(self.example.iter().map(|example| format!("--example={example}").into()));

        if self.examples {
            cargo_args.push("--examples".into());
        }

        if self.lib {
            cargo_args.push("--lib".into());
        }

        cargo_args.extend(self.test.iter().map(|test| format!("--test={test}").into()));

        cargo_args
    }

    fn has_explicit_selector(&self) -> bool {
        self.all_targets
            || self.benches
            || self.bins
            || self.examples
            || self.lib
            || !self.bench.is_empty()
            || !self.bin.is_empty()
            || !self.example.is_empty()
            || !self.test.is_empty()
    }

    pub(crate) fn include_bench(&self, name: &str) -> bool {
        self.all_targets || self.benches || self.bench.iter().any(|b| b == name)
    }

    pub(crate) fn include_bin(&self, name: &str) -> bool {
        self.all_targets
            || self.bins
            || (!self.has_explicit_selector())
            || self.bin.iter().any(|b| b == name)
    }

    pub(crate) fn include_example(&self, name: &str) -> bool {
        self.all_targets || self.examples || self.example.iter().any(|e| e == name)
    }

    pub(crate) fn include_lib(&self) -> bool {
        self.all_targets || self.lib || !self.has_explicit_selector()
    }

    pub(crate) fn include_test(&self, name: &str) -> bool {
        self.all_targets || !self.has_explicit_selector() || self.test.iter().any(|t| t == name)
    }

    pub(crate) fn explicitly_selects_test_targets(&self) -> bool {
        self.all_targets || !self.test.is_empty()
    }
}

impl ValidateArgs for CargoTargetArgs {
    fn validate(&self) -> Result<(), Error> {
        Ok(())
    }
}

/// Arguments that trust-mc pass down into Cargo test essentially uninterpreted.
#[derive(Debug, Default, clap::Args)]
pub(crate) struct CargoTestArgs {
    /// Arguments to pass down to Cargo
    #[command(flatten)]
    pub common: CargoCommonArgs,

    /// Arguments used to select Cargo target.
    #[command(flatten)]
    pub target: CargoTargetArgs,
}

impl CargoTestArgs {
    /// Convert the arguments back to a format that cargo can understand.
    pub(crate) fn to_cargo_args(&self) -> Vec<CargoArg> {
        let mut cargo_args = self.common.to_cargo_args();
        cargo_args.append(&mut self.target.to_cargo_args());
        cargo_args
    }
}

impl ValidateArgs for CargoTestArgs {
    fn validate(&self) -> Result<(), Error> {
        self.common.validate()?;
        self.target.validate()
    }
}

#[cfg(test)]
mod tests {
    use clap::Parser;

    use crate::args::CargoKaniArgs;

    #[test]
    fn parses_cargo_target_selectors() {
        let args = CargoKaniArgs::try_parse_from([
            "cargo-trust-mc",
            "--all-targets",
            "--example",
            "demo",
            "--examples",
            "--test",
            "integ",
            "--bench",
            "speed",
            "--benches",
        ])
        .unwrap();

        let target = args.verify_opts.target;
        assert!(target.all_targets);
        assert_eq!(target.example, ["demo"]);
        assert!(target.examples);
        assert_eq!(target.test, ["integ"]);
        assert_eq!(target.bench, ["speed"]);
        assert!(target.benches);
    }

    #[test]
    fn explicit_example_does_not_select_default_lib_or_bin() {
        let target =
            super::CargoTargetArgs { example: vec!["demo".to_string()], ..Default::default() };

        assert!(target.include_example("demo"));
        assert!(!target.include_example("other"));
        assert!(!target.include_lib());
        assert!(!target.include_bin("bin"));
    }

    #[test]
    fn all_targets_selects_every_supported_target_kind() {
        let target = super::CargoTargetArgs { all_targets: true, ..Default::default() };

        assert!(target.include_lib());
        assert!(target.include_bin("bin"));
        assert!(target.include_example("demo"));
        assert!(target.include_test("integ"));
        assert!(target.include_bench("speed"));
    }
}
