// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `--compiler-route` and the inputs of the Trustc route (T1-D1).

use crate::args::ValidateArgs;
use clap::error::{Error, ErrorKind};
use std::path::PathBuf;

/// Which compiler builds the crates under verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, clap::ValueEnum)]
pub(crate) enum CompilerRouteKind {
    /// `trust-mc-compiler --kani-compiler` from the trust-mc install.
    #[default]
    DevCli,
    /// Canonical trustc loading the trust-mc codegen-backend dylib.
    Trustc,
}

/// Compiler-route arguments shared by verification and playback.
#[derive(Debug, Clone, clap::Args)]
#[clap(next_help_heading = "Compiler Route Options")]
pub(crate) struct CompilerRouteArgs {
    /// Which compiler builds the crates under verification. `dev-cli` runs
    /// trust-mc-compiler. `trustc` runs canonical trustc with
    /// `-Zcodegen-backend=<--backend-dylib>` and `-Ztrust-verify=off`, against
    /// the Kani library of the KEY directory that TRUST_MC_SYSROOT names; the
    /// KEY, the dylib and trustc must all come from one librustc_driver.
    #[arg(long, value_enum, default_value_t = CompilerRouteKind::DevCli, value_name = "ROUTE")]
    pub compiler_route: CompilerRouteKind,

    /// The canonical trustc for `--compiler-route trustc`. Defaults to TRUST_MC_TRUSTC.
    #[arg(long, value_name = "PATH")]
    pub trustc: Option<PathBuf>,

    /// The trust-mc codegen-backend dylib for `--compiler-route trustc`.
    /// Defaults to TRUST_MC_BACKEND_DYLIB.
    #[arg(long, value_name = "PATH")]
    pub backend_dylib: Option<PathBuf>,
}

impl CompilerRouteArgs {
    pub(crate) fn is_trustc(&self) -> bool {
        self.compiler_route == CompilerRouteKind::Trustc
    }
}

impl ValidateArgs for CompilerRouteArgs {
    fn validate(&self) -> Result<(), Error> {
        if !self.is_trustc() && (self.trustc.is_some() || self.backend_dylib.is_some()) {
            return Err(Error::raw(
                ErrorKind::ArgumentConflict,
                "Invalid argument: `--trustc` and `--backend-dylib` only apply with \
                 `--compiler-route trustc`",
            ));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::args::{StandaloneArgs, StandaloneSubcommand};
    use clap::Parser;

    #[test]
    fn compiler_route_flag_defaults_to_dev_cli() {
        let args = StandaloneArgs::try_parse_from(["trust-mc", "pass.rs"]).unwrap();
        assert_eq!(args.verify_opts.compiler_route.compiler_route, CompilerRouteKind::DevCli);
        assert!(args.verify_opts.compiler_route.trustc.is_none());
        args.verify_opts.validate().unwrap();
    }

    #[test]
    fn compiler_route_flag_selects_trustc_with_its_inputs() {
        let args = StandaloneArgs::try_parse_from([
            "trust-mc",
            "pass.rs",
            "--compiler-route",
            "trustc",
            "--trustc",
            "/s/Application Support/bin/trustc",
            "--backend-dylib",
            "/k/codegen-backends/librustc_codegen_trust_mc.dylib",
        ])
        .unwrap();
        let route = &args.verify_opts.compiler_route;
        assert!(route.is_trustc());
        assert_eq!(
            route.trustc.as_deref(),
            Some(std::path::Path::new("/s/Application Support/bin/trustc"))
        );
        args.verify_opts.validate().unwrap();
    }

    #[test]
    fn compiler_route_refuses_no_codegen_on_trustc_only() {
        let parse = |route: &str| {
            StandaloneArgs::try_parse_from([
                "trust-mc",
                "pass.rs",
                "--compiler-route",
                route,
                "--no-codegen",
                "-Z",
                "unstable-options",
            ])
            .unwrap()
        };
        let error = parse("trustc").verify_opts.validate().unwrap_err().to_string();
        assert!(error.contains("--no-codegen") && error.contains("trustc"), "{error}");
        parse("dev-cli").verify_opts.validate().unwrap();
    }

    #[test]
    fn compiler_route_refuses_trustc_inputs_on_dev_cli() {
        let args =
            StandaloneArgs::try_parse_from(["trust-mc", "pass.rs", "--trustc", "/t"]).unwrap();
        let error = args.verify_opts.validate().unwrap_err().to_string();
        assert!(error.contains("--compiler-route trustc"), "{error}");
    }

    #[test]
    fn compiler_route_flags_reach_playback() {
        let args = StandaloneArgs::try_parse_from([
            "trust-mc",
            "playback",
            "-Z",
            "concrete-playback",
            "--compiler-route",
            "trustc",
            "pass.rs",
        ])
        .unwrap();
        let Some(StandaloneSubcommand::Playback(playback)) = args.command else {
            panic!("expected the playback subcommand");
        };
        assert!(playback.playback.compiler_route.is_trustc());
    }

    #[test]
    fn compiler_route_playback_refuses_a_backend_it_never_loads() {
        let parse = |extra: &[&str]| {
            let mut argv = vec![
                "trust-mc",
                "playback",
                "-Z",
                "concrete-playback",
                "--compiler-route",
                "trustc",
            ];
            argv.extend_from_slice(extra);
            argv.push("Cargo.toml");
            let args = StandaloneArgs::try_parse_from(argv).unwrap();
            let Some(StandaloneSubcommand::Playback(playback)) = args.command else {
                panic!("expected the playback subcommand");
            };
            playback.playback.validate()
        };
        let error =
            parse(&["--backend-dylib", "/k/codegen-backends/x.dylib"]).unwrap_err().to_string();
        assert!(error.contains("--backend-dylib") && error.contains("playback"), "{error}");
        parse(&["--trustc", "/s/bin/trustc"]).unwrap();
    }
}
