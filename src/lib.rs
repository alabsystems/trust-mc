// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! trust_mc (Model Checking) — Software Model Checker for Rust
//!
//! trust_mc is a bit-precise software model checker for Rust. The **mc** suffix
//! stands for **Model Checking**, the process of exhaustively verifying whether
//! a system meets its specification by exploring its state space.
//!
//! This crate includes proxy binaries and support for the trust_mc verifier.

mod cmd;
mod frontend;
mod os_hacks;
mod setup;

pub use frontend::front_door;

use std::ffi::{OsStr, OsString};
#[cfg(unix)]
use std::os::unix::prelude::CommandExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;
use std::{env, fs};

use anyhow::{Context, Result, bail};

/// Effectively the entry point (i.e. `main` function) for both our proxy binaries.
/// `bin` should be either `trust-mc` or `cargo-trust-mc` — the only installed
/// proxy names since R2 deletion D-C retired the legacy `kani` / `cargo-kani`
/// [[bin]] targets. The kani-spelled invocation identities remain recognized
/// internally (argv parsing here and in trust-mc-driver) so Kani-corpus
/// semantics keep working for tool-internal callers like kani-domination.
pub fn proxy(bin: &str) -> Result<()> {
    match parse_args(env::args_os().collect()) {
        ArgsResult::ExplicitSetup { use_local_bundle, use_local_toolchain } => {
            setup::setup(use_local_bundle, use_local_toolchain)
        }
        ArgsResult::Default => {
            fail_if_in_dev_environment()?;
            if !setup::appears_setup() {
                setup::setup(None, None)?;
            } else {
                // This handles cases where the setup was left incomplete due to an interrupt
                // For example - https://github.com/model-checking/kani/issues/1545
                if let Some(path_to_bundle) = setup::appears_incomplete() {
                    setup::setup(Some(path_to_bundle.clone().into_os_string()), None)?;
                    // Suppress warning with unused assignment
                    // and remove the bundle if it still exists
                    let _ = fs::remove_file(path_to_bundle);
                }
            }
            exec(bin)
        }
    }
}

/// Minimalist argument parsing result type
#[derive(PartialEq, Eq, Debug)]
enum ArgsResult {
    ExplicitSetup { use_local_bundle: Option<OsString>, use_local_toolchain: Option<OsString> },
    Default,
}

/// Parse `args` and decide what to do.
fn parse_args(args: Vec<OsString>) -> ArgsResult {
    // In an effort to keep our dependencies minimal, we do the bare minimum argument parsing manually.
    // `args_ez` makes it easy to do crude arg parsing with match.
    let args_ez: Vec<Option<&str>> = args.iter().map(|x| x.to_str()).collect();
    let setup_index = match &args_ez[..] {
        // "cargo trust-mc setup" comes in as "cargo-trust-mc trust-mc setup".
        // "cargo-trust-mc setup" comes in as "cargo-trust-mc setup".
        [_, Some("setup"), ..] => Some(1),
        [_, Some(command), Some("setup"), ..] if is_proxy_command(command) => Some(2),
        _ => None,
    };

    if let Some(setup_index) = setup_index {
        parse_setup_args(&args, &args_ez, setup_index)
    } else {
        ArgsResult::Default
    }
}

fn is_proxy_command(command: &str) -> bool {
    matches!(command, "trust-mc" | "kani")
}

fn parse_setup_args(args: &[OsString], args_ez: &[Option<&str>], setup_index: usize) -> ArgsResult {
    let value_index = |offset: usize| setup_index + offset;

    match args_ez[setup_index + 1..] {
        [Some("--use-local-bundle"), _, Some("--use-local-toolchain"), _] => {
            ArgsResult::ExplicitSetup {
                use_local_bundle: Some(args[value_index(2)].clone()),
                use_local_toolchain: Some(args[value_index(4)].clone()),
            }
        }
        [Some("--use-local-bundle"), _] => ArgsResult::ExplicitSetup {
            use_local_bundle: Some(args[value_index(2)].clone()),
            use_local_toolchain: None,
        },
        [Some("--use-local-toolchain"), _] => ArgsResult::ExplicitSetup {
            use_local_bundle: None,
            use_local_toolchain: Some(args[value_index(2)].clone()),
        },
        [] => ArgsResult::ExplicitSetup { use_local_bundle: None, use_local_toolchain: None },
        _ => ArgsResult::Default,
    }
}

/// In dev environments, this proxy shouldn't be used.
/// But accidentally using it (with the test suite) can fire off
/// hundreds of HTTP requests trying to download a non-existent release bundle.
/// So if we positively detect a dev environment, raise an error early.
fn fail_if_in_dev_environment() -> Result<()> {
    // Don't collapse if as let_chains have only been stabilized in 1.88, which the target host
    // installing Kani need not have just yet.
    #[allow(clippy::collapsible_if)]
    if let Ok(exe) = std::env::current_exe() {
        if let Some(path) = exe.parent() {
            if path.ends_with("target/debug") || path.ends_with("target/release") {
                // exe succeeded from current_exe(), so file_name() always exists
                let name = exe.file_name().unwrap_or_default().to_string_lossy();
                bail!(
                    "Running a release-only executable, {name}, from a development environment. This is usually caused by PATH including 'target/release' erroneously.",
                )
            }
        }
    }

    Ok(())
}

/// Executes `trust-mc-driver` in `bin` mode (trust_mc or cargo-trust-mc)
/// augmenting environment variables to accomodate our release environment
fn exec(bin: &str) -> Result<()> {
    let kani_dir = setup::kani_dir()?;
    let program = kani_dir.join("bin").join("trust-mc-driver");
    let pyroot = kani_dir.join("pyroot");
    let bin_kani = kani_dir.join("bin");
    let bin_pyroot = pyroot.join("bin");

    // Allow python scripts to find dependencies under our pyroot
    let pythonpath = prepend_search_path(&[pyroot], env::var_os("PYTHONPATH"))?;
    // Add: trust_mc binaries and our rust toolchain directly to our PATH
    let path = prepend_search_path(&[bin_kani, bin_pyroot], env::var_os("PATH"))?;

    // Ensure our environment variables for linker search paths won't cause failures, before we execute:
    fixup_dynamic_linking_environment();
    // Override our `RUSTUP_TOOLCHAIN` with the version Kani links against
    set_kani_rust_toolchain(&kani_dir)?;

    let mut cmd = Command::new(program);
    cmd.args(env::args_os().skip(1)).env("PYTHONPATH", pythonpath).env("PATH", path);
    // Set argv[0] so trust-mc-driver can determine its invocation identity
    // (trust-mc / cargo-trust-mc / legacy kani) from the name it was invoked as.
    // Windows has no argv[0] override in std::process::Command; there the driver
    // falls back to its default identity (`cargo trust-mc` invocations still pass
    // the identity as the first argument, which takes precedence over argv[0]).
    #[cfg(unix)]
    cmd.arg0(bin);
    #[cfg(not(unix))]
    let _ = bin;

    let result = cmd.status().context("Failed to invoke trust_mc driver")?;

    std::process::exit(result.code().expect("No exit code?"));
}

/// Prepend paths to an environment variable search string like PATH
pub(crate) fn prepend_search_path(
    paths: &[PathBuf],
    original: Option<OsString>,
) -> Result<OsString> {
    match original {
        None => Ok(env::join_paths(paths)?),
        Some(original) => {
            let orig = env::split_paths(&original);
            let new_iter = paths.iter().cloned().chain(orig);
            Ok(env::join_paths(new_iter)?)
        }
    }
}

/// `rustup` sets dynamic linker paths when it proxies to the target Rust toolchain. It's not fully
/// clear why. `rustup run` exists, which may aid in running Rust binaries that dynamically link to
/// the Rust standard library with `-C prefer-dynamic`. This might be why. All toolchain binaries
/// have `RUNPATH` set, so it's not needed by e.g. rustc. (Same for Kani)
///
/// However, this causes problems for us when the default Rust toolchain is nightly. Then
/// `LD_LIBRARY_PATH` is set to a nightly `lib` that may contain a different version of
/// `librustc_driver-*.so` that might have the same name. This takes priority over the `RUNPATH` of
/// `trust-mc-compiler` and causes the linker to use a slightly different version of rustc than trust_mc
/// was built against. This manifests in errors like:
/// `trust-mc-compiler: symbol lookup error: ... undefined symbol`
///
/// Consequently, let's remove from our linking environment anything that looks like a toolchain
/// path that rustup set. Then we can safely invoke our binaries. Note also that we update
/// `PATH` in [`exec`] to include our favored Rust toolchain, so we won't re-drive `rustup` when
/// `trust-mc-driver` later invokes `cargo`.
/// THE single blessed env-mutation choke point for this crate: performs the
/// raw process-global `set_var` under a process-wide lock. Both CLI-startup
/// callers below — `LOADER_PATH` in [`fixup_dynamic_linking_environment`] and
/// `RUSTUP_TOOLCHAIN` in [`set_kani_rust_toolchain`] — mutate the environment
/// intentionally and permanently: the values must persist into the `exec`'d
/// `trust-mc-driver` child, so there is nothing to restore. The lock serializes
/// both mutation entrypoints; both callers run during single-threaded startup,
/// before any concurrent environment readers exist. This is the crate's one
/// item-level `env_mutation` allow; `unknown_lints` keeps the stock-rustc build
/// green (the lint is defined only by the Trust toolchain).
#[allow(unknown_lints, env_mutation)]
pub(crate) fn set_process_env_var(key: impl AsRef<OsStr>, value: impl AsRef<OsStr>) {
    static ENV_LOCK: Mutex<()> = Mutex::new(());
    let _guard = ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    // SAFETY: serialized by ENV_LOCK; single-threaded CLI startup with no
    // concurrent env readers in this process before we exec the driver child.
    unsafe {
        env::set_var(key, value);
    }
}

pub(crate) fn fixup_dynamic_linking_environment() {
    #[cfg(not(target_os = "macos"))]
    const LOADER_PATH: &str = "LD_LIBRARY_PATH";
    #[cfg(target_os = "macos")]
    const LOADER_PATH: &str = "DYLD_FALLBACK_LIBRARY_PATH";

    if let Some(paths) = env::var_os(LOADER_PATH) {
        // Filtering existing paths never introduces invalid characters
        #[expect(clippy::unwrap_used, reason = "filtering valid paths cannot produce invalid join")]
        let new_val =
            env::join_paths(env::split_paths(&paths).filter(unlike_toolchain_path)).unwrap();
        set_process_env_var(LOADER_PATH, new_val);
    }
}

/// Determines if a path looks unlike a toolchain library path. These often looks like:
/// `/home/user/.rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib`
// Ignore this lint (recommending Path instead of PathBuf),
// we want to take the right argument type for use in `filter` above.
#[allow(clippy::ptr_arg)]
fn unlike_toolchain_path(path: &PathBuf) -> bool {
    let mut components = path.iter().rev();

    // effectively matching `*/toolchains/*/lib`
    !(components.next() == Some(std::ffi::OsStr::new("lib"))
        && components.next().is_some()
        && components.next() == Some(std::ffi::OsStr::new("toolchains")))
}

/// We should currently see a `RUSTUP_TOOLCHAIN` that was set by whatever default
/// toolchain the user has. We override our own environment variable (that is passed
/// down to children) with the toolchain Kani uses instead.
fn set_kani_rust_toolchain(kani_dir: &Path) -> Result<()> {
    let toolchain_verison = setup::get_rust_toolchain_version(kani_dir)?;
    set_process_env_var("RUSTUP_TOOLCHAIN", toolchain_verison);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_unlike_toolchain_path() {
        fn trial(s: &str) -> bool {
            unlike_toolchain_path(&PathBuf::from(s))
        }
        // filter these out:
        assert!(!trial("/home/user/.rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib"));
        assert!(!trial("/home/user/.rustup/toolchains/nightly-x86_64-unknown-linux-gnu/lib/"));
        assert!(!trial("/home/user/.rustup/toolchains/nightly/lib"));
        assert!(!trial("/home/user/.rustup/toolchains/stable/lib"));
        // minimally:
        assert!(!trial("toolchains/nightly/lib"));
        // keep these:
        assert!(trial("/home/user/.rustup/toolchains"));
        assert!(trial("/usr/lib"));
        assert!(trial("/home/user/lib/toolchains"));
        // don't error on these:
        assert!(trial(""));
        assert!(trial("/"));
    }

    #[test]
    fn check_arg_parsing() {
        fn trial(args: &[&str]) -> ArgsResult {
            parse_args(args.iter().map(OsString::from).collect())
        }
        {
            let e = ArgsResult::Default;
            assert_eq!(e, trial(&["cargo-kani", "kani"]));
            assert_eq!(e, trial(&[]));
        }
        {
            let e = ArgsResult::ExplicitSetup { use_local_bundle: None, use_local_toolchain: None };
            assert_eq!(e, trial(&["cargo-kani", "kani", "setup"]));
            assert_eq!(e, trial(&["cargo", "kani", "setup"]));
            assert_eq!(e, trial(&["cargo-kani", "setup"]));
            assert_eq!(e, trial(&["cargo-trust-mc", "trust-mc", "setup"]));
            assert_eq!(e, trial(&["cargo", "trust-mc", "setup"]));
            assert_eq!(e, trial(&["cargo-trust-mc", "setup"]));
        }
        {
            let e = ArgsResult::ExplicitSetup {
                use_local_bundle: Some(OsString::from("FILE")),
                use_local_toolchain: None,
            };
            assert_eq!(e, trial(&["cargo-kani", "kani", "setup", "--use-local-bundle", "FILE"]));
            assert_eq!(e, trial(&["cargo", "kani", "setup", "--use-local-bundle", "FILE"]));
            assert_eq!(e, trial(&["cargo-kani", "setup", "--use-local-bundle", "FILE"]));
            assert_eq!(
                e,
                trial(&["cargo-trust-mc", "trust-mc", "setup", "--use-local-bundle", "FILE"])
            );
            assert_eq!(e, trial(&["cargo", "trust-mc", "setup", "--use-local-bundle", "FILE"]));
            assert_eq!(e, trial(&["cargo-trust-mc", "setup", "--use-local-bundle", "FILE"]));
        }
        {
            let e = ArgsResult::ExplicitSetup {
                use_local_bundle: None,
                use_local_toolchain: Some(OsString::from("TOOLCHAIN")),
            };
            assert_eq!(
                e,
                trial(&["cargo-kani", "kani", "setup", "--use-local-toolchain", "TOOLCHAIN"])
            );
            assert_eq!(e, trial(&["cargo", "kani", "setup", "--use-local-toolchain", "TOOLCHAIN"]));
            assert_eq!(e, trial(&["cargo-kani", "setup", "--use-local-toolchain", "TOOLCHAIN"]));
            assert_eq!(
                e,
                trial(&[
                    "cargo-trust-mc",
                    "trust-mc",
                    "setup",
                    "--use-local-toolchain",
                    "TOOLCHAIN"
                ])
            );
            assert_eq!(
                e,
                trial(&["cargo", "trust-mc", "setup", "--use-local-toolchain", "TOOLCHAIN"])
            );
            assert_eq!(
                e,
                trial(&["cargo-trust-mc", "setup", "--use-local-toolchain", "TOOLCHAIN"])
            );
        }
        {
            let e = ArgsResult::ExplicitSetup {
                use_local_bundle: Some(OsString::from("FILE")),
                use_local_toolchain: Some(OsString::from("TOOLCHAIN")),
            };
            assert_eq!(
                e,
                trial(&[
                    "cargo-kani",
                    "kani",
                    "setup",
                    "--use-local-bundle",
                    "FILE",
                    "--use-local-toolchain",
                    "TOOLCHAIN"
                ])
            );
            assert_eq!(
                e,
                trial(&[
                    "cargo",
                    "kani",
                    "setup",
                    "--use-local-bundle",
                    "FILE",
                    "--use-local-toolchain",
                    "TOOLCHAIN"
                ])
            );
            assert_eq!(
                e,
                trial(&[
                    "cargo-kani",
                    "setup",
                    "--use-local-bundle",
                    "FILE",
                    "--use-local-toolchain",
                    "TOOLCHAIN"
                ])
            );
            assert_eq!(
                e,
                trial(&[
                    "cargo-trust-mc",
                    "trust-mc",
                    "setup",
                    "--use-local-bundle",
                    "FILE",
                    "--use-local-toolchain",
                    "TOOLCHAIN"
                ])
            );
            assert_eq!(
                e,
                trial(&[
                    "cargo",
                    "trust-mc",
                    "setup",
                    "--use-local-bundle",
                    "FILE",
                    "--use-local-toolchain",
                    "TOOLCHAIN"
                ])
            );
            assert_eq!(
                e,
                trial(&[
                    "cargo-trust-mc",
                    "setup",
                    "--use-local-bundle",
                    "FILE",
                    "--use-local-toolchain",
                    "TOOLCHAIN"
                ])
            );
        }
    }
}
