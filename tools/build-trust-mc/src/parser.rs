// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This file contains a small parser for our build script.
use clap::{Args, Parser, Subcommand};

#[derive(Parser)]
#[clap(name = "build-trust-mc")]
#[clap(about = "Builds trust-mc either for development or release.", long_about = None)]
pub(crate) struct ArgParser {
    #[clap(subcommand)]
    pub(crate) subcommand: Commands,
}

#[derive(Args, Debug, Eq, PartialEq)]
pub(crate) struct BuildDevParser {
    /// Arguments to be passed down to cargo when building cargo binaries.
    #[clap(value_name = "ARG", allow_hyphen_values = true)]
    pub(crate) args: Vec<String>,
    /// Do not re-build trust-mc libraries. Only use this if you know there has been no changes to trust-mc
    /// libraries or the underlying Rust compiler.
    #[clap(long)]
    pub(crate) skip_libs: bool,
}

#[derive(Args, Debug, Eq, PartialEq)]
pub(crate) struct BundleParser {
    /// String version
    #[clap(value_name = "VERSION", default_value(env!("CARGO_PKG_VERSION")))]
    pub(crate) version: String,
}

#[derive(Eq, PartialEq, Subcommand)]
pub(crate) enum Commands {
    /// Build trust-mc binaries and sysroot for development.
    BuildDev(BuildDevParser),
    /// Build trust-mc's release bundle.
    Bundle(BundleParser),
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::*;
    use clap::CommandFactory;

    #[test]
    fn test_parser_valid() {
        // Verify that the CLI spec is valid
        ArgParser::command().debug_assert();
    }

    #[test]
    fn test_build_dev_default() {
        let parser = BuildDevParser { args: vec![], skip_libs: false };
        assert!(!parser.skip_libs);
        assert!(parser.args.is_empty());
    }

    #[test]
    fn test_build_dev_skip_libs() {
        let parser = BuildDevParser { args: vec![], skip_libs: true };
        assert!(parser.skip_libs);
    }

    #[test]
    fn test_build_dev_with_args() {
        let args = vec!["--release".to_string(), "-j4".to_string()];
        let parser = BuildDevParser { args: args.clone(), skip_libs: false };
        assert_eq!(parser.args, args);
    }

    #[test]
    fn test_bundle_default_version() {
        let parser = BundleParser { version: env!("CARGO_PKG_VERSION").to_string() };
        assert!(!parser.version.is_empty());
    }

    #[test]
    fn test_bundle_custom_version() {
        let parser = BundleParser { version: "1.2.3".to_string() };
        assert_eq!(parser.version, "1.2.3");
    }

    // Actual CLI parsing tests using try_parse_from
    #[test]
    fn test_parse_build_dev_minimal() {
        let args = ArgParser::try_parse_from(["build-trust-mc", "build-dev"]).unwrap();
        match args.subcommand {
            Commands::BuildDev(p) => {
                assert!(!p.skip_libs);
                assert!(p.args.is_empty());
            }
            _ => panic!("expected BuildDev subcommand"),
        }
    }

    #[test]
    fn test_parse_build_dev_with_skip_libs() {
        let args =
            ArgParser::try_parse_from(["build-trust-mc", "build-dev", "--skip-libs"]).unwrap();
        match args.subcommand {
            Commands::BuildDev(p) => {
                assert!(p.skip_libs);
            }
            _ => panic!("expected BuildDev subcommand"),
        }
    }

    #[test]
    fn test_parse_build_dev_with_cargo_args() {
        let args =
            ArgParser::try_parse_from(["build-trust-mc", "build-dev", "--release", "-j4"]).unwrap();
        match args.subcommand {
            Commands::BuildDev(p) => {
                assert_eq!(p.args, vec!["--release", "-j4"]);
            }
            _ => panic!("expected BuildDev subcommand"),
        }
    }

    #[test]
    fn test_parse_bundle_with_version() {
        let args = ArgParser::try_parse_from(["build-trust-mc", "bundle", "2.0.0"]).unwrap();
        match args.subcommand {
            Commands::Bundle(p) => {
                assert_eq!(p.version, "2.0.0");
            }
            _ => panic!("expected Bundle subcommand"),
        }
    }

    #[test]
    fn test_parse_invalid_subcommand() {
        let result = ArgParser::try_parse_from(["build-trust-mc", "invalid"]);
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_bundle_default_version() {
        // Bundle without explicit version should use CARGO_PKG_VERSION default
        let args = ArgParser::try_parse_from(["build-trust-mc", "bundle"]).unwrap();
        match args.subcommand {
            Commands::Bundle(p) => {
                assert_eq!(p.version, env!("CARGO_PKG_VERSION"));
            }
            _ => panic!("expected Bundle subcommand"),
        }
    }

    #[test]
    fn test_parse_build_dev_combined_flags() {
        // Build-dev with both --skip-libs and cargo args
        let args = ArgParser::try_parse_from([
            "build-trust-mc",
            "build-dev",
            "--skip-libs",
            "--release",
            "-j4",
        ])
        .unwrap();
        match args.subcommand {
            Commands::BuildDev(p) => {
                assert!(p.skip_libs);
                assert_eq!(p.args, vec!["--release", "-j4"]);
            }
            _ => panic!("expected BuildDev subcommand"),
        }
    }
}
