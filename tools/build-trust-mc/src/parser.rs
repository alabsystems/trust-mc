// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This file contains a small parser for our build script.
use clap::{Args, Parser, Subcommand, ValueEnum};
use std::path::PathBuf;

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
    /// Trust git checkout containing the compiler's commit, for a toolchain that
    /// ships no standard-library sources (the Trust seal ships none): `-Z build-std`
    /// then reads `library/` extracted from it at that exact commit. Also
    /// `TRUST_MC_TRUST_CHECKOUT`; without either, the sysroot's own sources, then
    /// the trust superproject of this checkout. Like `--skip-libs`, it must come
    /// before the cargo arguments.
    #[clap(long, value_name = "PATH")]
    pub(crate) trust_checkout: Option<PathBuf>,
}

#[derive(Args, Debug, Eq, PartialEq)]
pub(crate) struct BundleParser {
    /// The bundle version. Default: trust-mc's own `[package] version` (the
    /// version `trust-mc setup` installs), never this tool's.
    #[clap(value_name = "VERSION")]
    pub(crate) version: Option<String>,
}

/// Which std a keyed Kani library is built against.
#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
pub(crate) enum StdMode {
    /// Rebuild std with -Zbuild-std from the compiler commit's library sources.
    /// Parity grade: the only mode whose rows count (T1-D5).
    BuildStd,
    /// Link the compiler's prebuilt dist std. Smoke grade: rows never count.
    Prebuilt,
}

#[derive(Args, Debug, Eq, PartialEq)]
pub(crate) struct BuildKeyedParser {
    /// Trust compiler that builds the library and whose identity keys it. cargo is
    /// taken from this compiler's sysroot, never from PATH.
    #[clap(long, value_name = "PATH")]
    pub(crate) trustc: PathBuf,
    /// Top level of a trust git checkout containing the compiler's reported_commit.
    #[clap(
        long,
        value_name = "PATH",
        required_unless_present_any = ["print_key", "trust_src"],
        conflicts_with = "trust_src"
    )]
    pub(crate) trust_checkout: Option<PathBuf>,
    /// Take the library sources from the trust-src component inside --trustc's own
    /// sysroot (lib/rustlib/src/rust) instead of a trust git checkout.
    #[clap(long)]
    pub(crate) trust_src: bool,
    /// `build-std` (parity) or `prebuilt` (smoke).
    #[clap(long, value_enum, value_name = "MODE", required_unless_present = "print_key")]
    pub(crate) std: Option<StdMode>,
    /// Codegen-backend dylib to install as <KEY>/codegen-backends/librustc_codegen_trust_mc.
    #[clap(long, value_name = "DYLIB")]
    pub(crate) backend: Option<PathBuf>,
    /// Print the KEY and KEY directory for --trustc, then exit without building.
    #[clap(long)]
    pub(crate) print_key: bool,
}

#[derive(Eq, PartialEq, Subcommand)]
pub(crate) enum Commands {
    /// Build trust-mc binaries and sysroot for development.
    BuildDev(BuildDevParser),
    /// Build trust-mc's release bundle.
    Bundle(BundleParser),
    /// Build the Kani library with one Trust compiler into target/trust-mc/keyed/<KEY>.
    BuildKeyed(BuildKeyedParser),
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
        let parser = BuildDevParser { args: vec![], skip_libs: false, trust_checkout: None };
        assert!(!parser.skip_libs);
        assert!(parser.args.is_empty());
    }

    #[test]
    fn test_build_dev_skip_libs() {
        let parser = BuildDevParser { args: vec![], skip_libs: true, trust_checkout: None };
        assert!(parser.skip_libs);
    }

    #[test]
    fn test_build_dev_with_args() {
        let args = vec!["--release".to_string(), "-j4".to_string()];
        let parser = BuildDevParser { args: args.clone(), skip_libs: false, trust_checkout: None };
        assert_eq!(parser.args, args);
    }

    #[test]
    fn test_bundle_default_version() {
        let parser = BundleParser { version: None };
        assert!(parser.version.is_none());
    }

    #[test]
    fn test_bundle_custom_version() {
        let parser = BundleParser { version: Some("1.2.3".to_string()) };
        assert_eq!(parser.version.as_deref(), Some("1.2.3"));
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
                assert_eq!(p.version.as_deref(), Some("2.0.0"));
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
        // Without an explicit version, `bundle` reads trust-mc's own version
        // (`main.rs`, `bundle_version`), not this tool's CARGO_PKG_VERSION.
        let args = ArgParser::try_parse_from(["build-trust-mc", "bundle"]).unwrap();
        match args.subcommand {
            Commands::Bundle(p) => {
                assert_eq!(p.version, None);
            }
            _ => panic!("expected Bundle subcommand"),
        }
    }

    #[test]
    fn test_parse_build_keyed() {
        let args = ArgParser::try_parse_from([
            "build-trust-mc",
            "build-keyed",
            "--trustc",
            "/s/bin/trustc",
            "--trust-checkout",
            "$HOME/trust",
            "--std",
            "build-std",
        ])
        .unwrap();
        match args.subcommand {
            Commands::BuildKeyed(p) => {
                assert_eq!(p.trustc, PathBuf::from("/s/bin/trustc"));
                assert_eq!(p.trust_checkout, Some(PathBuf::from("$HOME/trust")));
                assert_eq!(p.std, Some(StdMode::BuildStd));
                assert!(p.backend.is_none() && !p.print_key && !p.trust_src);
            }
            _ => panic!("expected BuildKeyed subcommand"),
        }
        let prebuilt = ArgParser::try_parse_from([
            "build-trust-mc",
            "build-keyed",
            "--trustc",
            "t",
            "--trust-checkout",
            "c",
            "--std",
            "prebuilt",
            "--backend",
            "b.dylib",
        ])
        .unwrap();
        match prebuilt.subcommand {
            Commands::BuildKeyed(p) => {
                assert_eq!(p.std, Some(StdMode::Prebuilt));
                assert_eq!(p.backend, Some(PathBuf::from("b.dylib")));
            }
            _ => panic!("expected BuildKeyed subcommand"),
        }
    }

    #[test]
    fn test_parse_build_keyed_requires_checkout_and_std_unless_print_key() {
        let base = ["build-trust-mc", "build-keyed", "--trustc", "t"];
        assert!(ArgParser::try_parse_from(base).is_err());
        assert!(ArgParser::try_parse_from(base.iter().chain(&["--std", "build-std"])).is_err());
        assert!(
            ArgParser::try_parse_from(base.iter().chain(&[
                "--trust-checkout",
                "c",
                "--std",
                "nightly"
            ]))
            .is_err()
        );
        assert!(ArgParser::try_parse_from(base.iter().chain(&["--print-key"])).is_ok());
        // The seal's own trust-src component replaces the checkout; naming both is refused.
        let seal =
            ArgParser::try_parse_from(base.iter().chain(&["--trust-src", "--std", "build-std"]))
                .unwrap();
        match seal.subcommand {
            Commands::BuildKeyed(p) => assert!(p.trust_src && p.trust_checkout.is_none()),
            _ => panic!("expected BuildKeyed subcommand"),
        }
        assert!(
            ArgParser::try_parse_from(base.iter().chain(&[
                "--trust-src",
                "--trust-checkout",
                "c",
                "--std",
                "build-std"
            ]))
            .is_err()
        );
        assert!(
            ArgParser::try_parse_from(["build-trust-mc", "build-keyed", "--print-key"]).is_err()
        );
    }

    #[test]
    fn test_parse_build_dev_trust_checkout() {
        let args = ArgParser::try_parse_from([
            "build-trust-mc",
            "build-dev",
            "--trust-checkout",
            "/t",
            "--release",
        ])
        .unwrap();
        match args.subcommand {
            Commands::BuildDev(p) => {
                assert_eq!(p.trust_checkout, Some(PathBuf::from("/t")));
                assert_eq!(p.args, vec!["--release"]);
            }
            _ => panic!("expected BuildDev subcommand"),
        }
        // Like --skip-libs, it precedes the cargo arguments; after them it is one
        // of them, and cargo refuses it loudly.
        let args = ArgParser::try_parse_from([
            "build-trust-mc",
            "build-dev",
            "--release",
            "--trust-checkout",
            "/t",
        ])
        .unwrap();
        match args.subcommand {
            Commands::BuildDev(p) => {
                assert_eq!(p.trust_checkout, None);
                assert_eq!(p.args, vec!["--release", "--trust-checkout", "/t"]);
            }
            _ => panic!("expected BuildDev subcommand"),
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
