// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Argv-composition tests for the compile commands (`compiler_route` filter).
//!
//! The DevCli goldens below were recorded from the composition as it stood
//! BEFORE the Trustc route existed (commit "driver: make compile argv
//! composition testable"); the route must leave them byte for byte unchanged.

use super::*;
use crate::args::{Backend, CargoKaniArgs, VerificationArgs};
use crate::session::CompilerRoute;
use clap::Parser;
use std::ffi::OsStr;

pub(super) fn argv_test_args() -> VerificationArgs {
    let mut args = CargoKaniArgs::try_parse_from(["cargo-trust-mc"]).unwrap().verify_opts;
    // What `resolve_backend_for_session` leaves behind for an Auto request.
    args.backend = Backend::AY;
    args.harnesses = vec!["check_add".to_string()];
    // A path with a space: the `-Cllvm-args` whitespace hazard.
    args.c_lib = vec![PathBuf::from("/opt/Application Support/stub.o")];
    args.default_unwind = Some(3);
    args
}

pub(super) fn builder(session: &KaniSession) -> StandaloneProjectBuilder<'_> {
    StandaloneProjectBuilder {
        outdir: PathBuf::from("/w/out"),
        metadata: standalone_artifact(Path::new("/w/out"), "pass", ArtifactType::Metadata),
        input: PathBuf::from("/w/pass.rs"),
        crate_name: "pass".to_string(),
        session,
    }
}

pub(super) fn strings<'a>(args: impl Iterator<Item = &'a OsStr>) -> Vec<String> {
    args.map(|arg| arg.to_str().expect("utf-8 test argv").to_string()).collect()
}

fn assert_golden(actual: &[String], golden: &[&str], what: &str) {
    assert_eq!(
        actual, golden,
        "{what} drifted from its golden; actual argv as a literal:\n{actual:#?}"
    );
}

/// `trust-mc-compiler` argv for a standalone compile, recorded before the route.
const DEVCLI_STANDALONE_GOLDEN: &[&str] = &[
    "-Cllvm-args=--log-level=warn --assertion-reach-checks --harness check_add --c-lib /opt/Application Support/stub.o --default-unwind 3 --reachability=harnesses",
    "-C",
    "overflow-checks=on",
    "-Z",
    "unstable-options",
    "-Z",
    "trim-diagnostic-paths=no",
    "-Z",
    "human_readable_cgu_names",
    "-Z",
    "always-encode-mir",
    "--cfg=kani",
    "--cfg=trust_mc",
    "-Z",
    "crate-attr=feature(register_tool)",
    "-Z",
    "crate-attr=register_tool(kanitool)",
    "-Z",
    "crate-attr=register_tool(trust_mctool)",
    "--sysroot",
    "/k",
    "-L",
    "/k/lib",
    "--extern",
    "kani",
    "--extern",
    "noprelude:std=/k/lib/libstd.rlib",
    "-C",
    "panic=abort",
    "-C",
    "symbol-mangling-version=v0",
    "-Z",
    "panic_abort_tests=yes",
    "-Z",
    "mir-enable-passes=-RemoveStorageMarkers",
    "-Z",
    "inline-mir=no",
    "--check-cfg=cfg(kani)",
    "-Clinker=echo",
    "--kani-compiler",
    "/w/pass.rs",
    "--out-dir",
    "/w/out",
    "--crate-name",
    "pass",
    "--crate-type",
    "lib",
];

/// `CARGO_ENCODED_RUSTFLAGS` elements for a cargo compile, recorded before the route.
const DEVCLI_CARGO_ALL_CRATES_GOLDEN: &[&str] = &[
    "-C",
    "overflow-checks=on",
    "-Z",
    "unstable-options",
    "-Z",
    "trim-diagnostic-paths=no",
    "-Z",
    "human_readable_cgu_names",
    "-Z",
    "always-encode-mir",
    "--cfg=kani",
    "--cfg=trust_mc",
    "-Z",
    "crate-attr=feature(register_tool)",
    "-Z",
    "crate-attr=register_tool(kanitool)",
    "-Z",
    "crate-attr=register_tool(trust_mctool)",
    "--sysroot",
    "/k",
    "-L",
    "/k/lib",
    "--extern",
    "kani",
    "--extern",
    "noprelude:std=/k/lib/libstd.rlib",
    "-C",
    "panic=abort",
    "-C",
    "symbol-mangling-version=v0",
    "-Z",
    "panic_abort_tests=yes",
    "-Z",
    "mir-enable-passes=-RemoveStorageMarkers",
    "-Z",
    "inline-mir=no",
    "--check-cfg=cfg(kani)",
    "-Clinker=echo",
    "--kani-compiler",
    "-Cllvm-args=--check-version=0.6.0",
];

/// The package-local `-Cllvm-args` for a cargo compile, recorded before the route.
const DEVCLI_CARGO_LOCAL_GOLDEN: &str = "-Cllvm-args=--reachability=harnesses --log-level=warn \
     --assertion-reach-checks --harness check_add --c-lib /opt/Application Support/stub.o \
     --default-unwind 3";

#[test]
fn compiler_route_devcli_standalone_argv_matches_pre_route_golden() {
    let session = KaniSession::for_argv_tests(argv_test_args());
    let cmd = builder(&session)
        .compile_command(Path::new("/i/bin/trust-mc-compiler"), PathBuf::from("/k/lib"), None)
        .unwrap();
    assert_eq!(cmd.get_program(), "/i/bin/trust-mc-compiler");
    assert_golden(&strings(cmd.get_args()), DEVCLI_STANDALONE_GOLDEN, "DevCli standalone argv");
}

#[test]
fn compiler_route_devcli_cargo_rustflags_match_pre_route_golden() {
    let session = KaniSession::for_argv_tests(argv_test_args());
    let all = session.cargo_build_rustc_args(PathBuf::from("/k/lib"), None).unwrap();
    let mut cmd = Command::new("cargo");
    cmd.pass_rustc_args(&all, PassTo::AllCrates);
    let encoded = cmd
        .get_envs()
        .find(|(key, _)| *key == "CARGO_ENCODED_RUSTFLAGS")
        .and_then(|(_, value)| value)
        .expect("CARGO_ENCODED_RUSTFLAGS is set")
        .to_str()
        .unwrap()
        .split('\x1f')
        .map(str::to_string)
        .collect::<Vec<_>>();
    assert_golden(&encoded, DEVCLI_CARGO_ALL_CRATES_GOLDEN, "DevCli cargo all-crates flags");

    let mut local = Command::new("cargo");
    local.pass_rustc_arg(session.cargo_build_local_kani_arg(), PassTo::OnlyLocalCrate);
    let local = strings(local.get_args());
    assert_eq!(local, [DEVCLI_CARGO_LOCAL_GOLDEN], "DevCli cargo local arg drifted:\n{local:#?}");
}

/// A Trustc route over fake files whose paths contain "Application Support".
fn trustc_route(tmp: &tempfile::TempDir) -> CompilerRoute {
    let sysroot_bin = tmp.path().join("Application Support/aterm/pkg/store/trust/8571/bin");
    let key_dir = tmp.path().join("keyed/driver-948b36c62eacc5d1");
    std::fs::create_dir_all(&sysroot_bin).unwrap();
    std::fs::create_dir_all(key_dir.join("codegen-backends")).unwrap();
    let trustc = sysroot_bin.join("trustc");
    let backend = key_dir.join("codegen-backends/librustc_codegen_trust_mc.dylib");
    std::fs::write(&trustc, "").unwrap();
    std::fs::write(&backend, b"fake dylib").unwrap();
    std::fs::write(
        key_dir.join("KEY.json"),
        r#"{"driver_sha256": "948b36c62eacc5d19ae9308d2cdcffe55535a4519f3d4bdb2d4f5ae54a973055"}"#,
    )
    .unwrap();
    CompilerRoute::Trustc {
        trustc: trustc.canonicalize().unwrap(),
        backend: backend.canonicalize().unwrap(),
        key_dir: key_dir.canonicalize().unwrap(),
    }
}

fn backend_of(route: &CompilerRoute) -> &Path {
    match route {
        CompilerRoute::Trustc { backend, .. } => backend,
        CompilerRoute::DevCli => panic!("not a trustc route"),
    }
}

#[test]
fn compiler_route_trustc_session_refuses_a_backend_changed_by_a_compile() {
    let tmp = tempfile::TempDir::new().unwrap();
    let route = trustc_route(&tmp);
    let CompilerRoute::Trustc { trustc, backend, key_dir } = route.clone() else { unreachable!() };
    let session = KaniSession::for_argv_tests_with_route(argv_test_args(), route);
    // No preflight yet: nothing was loaded, nothing to re-check.
    assert_eq!(session.with_backend_recheck(|| Ok(1)).unwrap(), 1);

    let sha256 = |bytes: &[u8]| trust_mc_core::evidence::EvidenceHash::sha256_bytes(bytes).value;
    let identity = crate::session::trustc_route::TrustcIdentity {
        trustc,
        sysroot: PathBuf::from("/s"),
        commit: "45dc60873c4fef21649ae277a93cc8cc9cf39191".to_string(),
        driver_name: "librustc_driver-98fef360a4a26975.dylib".to_string(),
        driver_sha256: "948b36c62eacc5d19ae9308d2cdcffe55535a4519f3d4bdb2d4f5ae54a973055".into(),
        backend: Some(crate::session::trustc_route::BackendIdentity {
            path: backend.clone(),
            sha256: sha256(b"fake dylib"),
        }),
        key_dir: key_dir.clone(),
        key: "driver-948b36c62eacc5d1".to_string(),
        key_libraries: crate::session::trustc_route::key_library_fingerprint(&key_dir).unwrap(),
        key_sha256: sha256(b"fake key"),
    };
    let identity_key_json = key_dir.join("KEY.json");
    session.trustc_identity.set(identity).unwrap();
    assert_eq!(session.with_backend_recheck(|| Ok(2)).unwrap(), 2);

    // The compile replaces the dylib: its own result, success or failure, is discarded.
    let changed = session
        .with_backend_recheck(|| {
            std::fs::write(&backend, b"rebuilt mid-session").unwrap();
            Ok(3)
        })
        .unwrap_err();
    assert!(matches!(
        changed.downcast_ref::<crate::session::trustc_route::TrustcRouteError>(),
        Some(crate::session::trustc_route::TrustcRouteError::BackendChanged { .. })
    ));
    let failed = session
        .with_backend_recheck(|| -> Result<()> { anyhow::bail!("compile failed") })
        .unwrap_err();
    assert!(failed.to_string().contains("changed during the session"), "{failed}");

    // A compile during which an rlib appears in a KEY library folder: refused, with
    // the compile's own success discarded.
    std::fs::write(&backend, b"fake dylib").unwrap();
    assert_eq!(session.with_backend_recheck(|| Ok(5)).unwrap(), 5);
    let library = key_dir.join("lib/libkani.rlib");
    let swapped = session
        .with_backend_recheck(|| {
            std::fs::create_dir_all(library.parent().unwrap()).unwrap();
            std::fs::write(&library, b"same-driver rlib").unwrap();
            Ok(7)
        })
        .unwrap_err();
    assert!(matches!(
        swapped.downcast_ref::<crate::session::trustc_route::TrustcRouteError>(),
        Some(crate::session::trustc_route::TrustcRouteError::KeyLibraryChanged { .. })
    ));
    std::fs::remove_dir_all(key_dir.join("lib")).unwrap();
    assert_eq!(session.with_backend_recheck(|| Ok(8)).unwrap(), 8);

    // A build-keyed rebuild removes KEY.json first: that refuses too, even with the
    // backend restored.
    std::fs::remove_file(identity_key_json).unwrap();
    let rebuilt = session.with_backend_recheck(|| Ok(6)).unwrap_err();
    assert!(matches!(
        rebuilt.downcast_ref::<crate::session::trustc_route::TrustcRouteError>(),
        Some(crate::session::trustc_route::TrustcRouteError::KeyChanged { .. })
    ));

    // DevCli never re-checks anything.
    let dev_cli = KaniSession::for_argv_tests(argv_test_args());
    assert_eq!(dev_cli.with_backend_recheck(|| Ok(4)).unwrap(), 4);
}

/// What rustc's `parse_list` makes of one `-Cllvm-args=<value>` argument.
fn rustc_llvm_args(arg: &str) -> Vec<String> {
    arg.strip_prefix("-Cllvm-args=")
        .expect("an -Cllvm-args argument")
        .split_whitespace()
        .map(str::to_string)
        .collect()
}

fn engine_argv(arg: &str) -> Vec<String> {
    trust_mc_metadata::engine_args::decode_llvm_args(&rustc_llvm_args(arg)).unwrap()
}

fn count(args: &[String], predicate: impl Fn(&str) -> bool) -> usize {
    args.iter().filter(|arg| predicate(arg)).count()
}

const LOCAL_ENGINE_ARGV: &[&str] = &[
    "--log-level=warn",
    "--assertion-reach-checks",
    "--harness",
    "check_add",
    "--c-lib",
    "/opt/Application Support/stub.o",
    "--default-unwind",
    "3",
];

#[test]
fn compiler_route_devcli_engine_args_split_the_path_under_application_support() {
    // The measured hazard the Trustc route fixes: rustc splits the DevCli form.
    let split = rustc_llvm_args(DEVCLI_STANDALONE_GOLDEN[0]);
    assert!(split.contains(&"/opt/Application".to_string()), "{split:?}");
    assert!(split.contains(&"Support/stub.o".to_string()), "{split:?}");
}

#[test]
fn compiler_route_trustc_standalone_argv_selects_the_backend_and_keeps_paths_whole() {
    let tmp = tempfile::TempDir::new().unwrap();
    let route = trustc_route(&tmp);
    let backend_flag = format!("-Zcodegen-backend={}", backend_of(&route).display());
    let session = KaniSession::for_argv_tests_with_route(argv_test_args(), route);
    let cmd = builder(&session)
        .compile_command(Path::new("/s/bin/trustc"), PathBuf::from("/k/lib"), None)
        .unwrap();
    assert_eq!(cmd.get_program(), "/s/bin/trustc");
    let args = strings(cmd.get_args());

    assert_eq!(count(&args, |a| a.starts_with("-Zcodegen-backend=")), 1, "{args:#?}");
    assert_eq!(count(&args, |a| a == backend_flag), 1, "{args:#?}");
    assert_eq!(count(&args, |a| a == "-Ztrust-verify=off"), 1, "{args:#?}");
    assert_eq!(count(&args, |a| a == "--kani-compiler"), 0, "{args:#?}");
    assert_eq!(count(&args, |a| a.contains("trust-mc-compiler")), 0, "{args:#?}");
    assert_eq!(count(&args, |a| a.starts_with("-Cllvm-args=")), 1, "{args:#?}");

    // The engine receives its argv exactly, the spaced path as one token, and the
    // --check-version the trustc-hosted backend requires.
    let mut expected = vec![format!("--check-version={}", env!("CARGO_PKG_VERSION"))];
    expected.extend(LOCAL_ENGINE_ARGV.iter().map(|s| s.to_string()));
    expected.push("--reachability=harnesses".to_string());
    assert_eq!(engine_argv(&args[0]), expected);

    // Everything else is the DevCli golden with --kani-compiler replaced.
    let mut rest: Vec<String> = Vec::new();
    for arg in &DEVCLI_STANDALONE_GOLDEN[1..] {
        if *arg == "--kani-compiler" {
            rest.push(backend_flag.clone());
            rest.push("-Ztrust-verify=off".to_string());
        } else {
            rest.push((*arg).to_string());
        }
    }
    assert_eq!(&args[1..], rest.as_slice());
}

#[test]
fn compiler_route_trustc_cargo_flags_select_the_backend_once_and_keep_paths_whole() {
    let tmp = tempfile::TempDir::new().unwrap();
    let route = trustc_route(&tmp);
    let backend_flag = format!("-Zcodegen-backend={}", backend_of(&route).display());
    let session = KaniSession::for_argv_tests_with_route(argv_test_args(), route);

    let all: Vec<String> = {
        let args = session.cargo_build_rustc_args(PathBuf::from("/k/lib"), None).unwrap();
        let mut cmd = Command::new("cargo");
        cmd.pass_rustc_args(&args, PassTo::AllCrates);
        let value = cmd.get_envs().find(|(k, _)| *k == "CARGO_ENCODED_RUSTFLAGS").unwrap().1;
        value.unwrap().to_str().unwrap().split('\x1f').map(str::to_string).collect()
    };
    assert_eq!(count(&all, |a| a == backend_flag), 1, "{all:#?}");
    assert_eq!(count(&all, |a| a.starts_with("-Zcodegen-backend=")), 1, "{all:#?}");
    assert_eq!(count(&all, |a| a == "-Ztrust-verify=off"), 1, "{all:#?}");
    assert_eq!(count(&all, |a| a == "--kani-compiler"), 0, "{all:#?}");
    let dependency = all.iter().find(|a| a.starts_with("-Cllvm-args=")).unwrap();
    assert_eq!(engine_argv(dependency), [format!("--check-version={}", env!("CARGO_PKG_VERSION"))]);

    let mut local = Command::new("cargo");
    local.pass_rustc_arg(session.cargo_build_local_kani_arg(), PassTo::OnlyLocalCrate);
    let local = strings(local.get_args());
    let mut expected = vec!["--reachability=harnesses".to_string()];
    expected.extend(LOCAL_ENGINE_ARGV.iter().map(|s| s.to_string()));
    assert_eq!(engine_argv(&local[0]), expected);
}

/// `tests/trust-lane/engine-args/<name>.llvm-args`, which trust-mc-compiler's
/// `parse_llvm_args` tests parse. Keeping the driver's output equal to these files
/// is what pairs the two sides of the `pct1` channel.
fn engine_fixture(name: &str) -> Vec<String> {
    let text = match name {
        "standalone" => include_str!("../../tests/trust-lane/engine-args/standalone.llvm-args"),
        "cargo-dependency" => {
            include_str!("../../tests/trust-lane/engine-args/cargo-dependency.llvm-args")
        }
        "cargo-local" => include_str!("../../tests/trust-lane/engine-args/cargo-local.llvm-args"),
        _ => unreachable!("no fixture {name}"),
    };
    text.lines()
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| line.replace("@CARGO_PKG_VERSION@", env!("CARGO_PKG_VERSION")))
        .collect()
}

#[test]
fn compiler_route_trustc_llvm_args_match_the_engine_fixtures() {
    let tmp = tempfile::TempDir::new().unwrap();
    let session = KaniSession::for_argv_tests_with_route(argv_test_args(), trustc_route(&tmp));

    let cmd = builder(&session)
        .compile_command(Path::new("/s/bin/trustc"), PathBuf::from("/k/lib"), None)
        .unwrap();
    let args = strings(cmd.get_args());
    assert_eq!(rustc_llvm_args(&args[0]), engine_fixture("standalone"));

    let rustflags = session.cargo_build_rustc_args(PathBuf::from("/k/lib"), None).unwrap();
    let mut cargo = Command::new("cargo");
    cargo.pass_rustc_args(&rustflags, PassTo::AllCrates);
    let encoded = cargo.get_envs().find(|(k, _)| *k == "CARGO_ENCODED_RUSTFLAGS").unwrap().1;
    let encoded = encoded.unwrap().to_str().unwrap().to_string();
    let dependency = encoded.split('\x1f').find(|a| a.starts_with("-Cllvm-args=")).unwrap();
    assert_eq!(rustc_llvm_args(dependency), engine_fixture("cargo-dependency"));

    let mut local = Command::new("cargo");
    local.pass_rustc_arg(session.cargo_build_local_kani_arg(), PassTo::OnlyLocalCrate);
    let local = strings(local.get_args());
    assert_eq!(rustc_llvm_args(&local[0]), engine_fixture("cargo-local"));
}

/// The environment a child of `cmd` sees when its parent environment is `parent`.
fn child_env(
    parent: impl IntoIterator<Item = (std::ffi::OsString, std::ffi::OsString)>,
    cmd: &Command,
) -> std::collections::BTreeMap<std::ffi::OsString, std::ffi::OsString> {
    let mut child: std::collections::BTreeMap<_, _> = parent.into_iter().collect();
    for (key, value) in cmd.get_envs() {
        match value {
            Some(value) => {
                child.insert(key.to_os_string(), value.to_os_string());
            }
            None => {
                child.remove(key);
            }
        }
    }
    child
}

fn scrubbed_keys(
    child: &std::collections::BTreeMap<std::ffi::OsString, std::ffi::OsString>,
) -> Vec<String> {
    child
        .keys()
        .map(|key| key.to_string_lossy().into_owned())
        .filter(|key| key.starts_with("TRUST_MC_") || key.starts_with("AY_"))
        .collect()
}

#[test]
fn compiler_route_trustc_compile_env_holds_no_trust_mc_or_ay_variable() {
    let tmp = tempfile::TempDir::new().unwrap();
    let route = trustc_route(&tmp);
    let session = KaniSession::for_argv_tests_with_route(argv_test_args(), route.clone());
    let mut cmd = builder(&session)
        .compile_command(Path::new("/s/bin/trustc"), PathBuf::from("/k/lib"), None)
        .unwrap();

    // Whatever this test process inherited is removed from the compile command.
    let ambient = child_env(std::env::vars_os(), &cmd);
    assert!(scrubbed_keys(&ambient).is_empty(), "the trustc child would see {ambient:?}");
    assert!(ambient.contains_key(std::ffi::OsStr::new("RUSTC_BOOTSTRAP")));

    // The same scrub against a parent that certainly holds such variables, and with
    // variables set on the command itself, so this never depends on the environment
    // the tests happen to run in.
    let parent: Vec<(std::ffi::OsString, std::ffi::OsString)> = [
        ("TRUST_MC_SYSROOT", "/k"),
        ("TRUST_MC_AY_BIN", "/ay"),
        ("AY_TIMEOUT", "9"),
        ("PATH", "/usr/bin"),
    ]
    .into_iter()
    .map(|(key, value)| (key.into(), value.into()))
    .collect();
    cmd.env("TRUST_MC_SET_ON_COMMAND", "1").env("AY_SET_ON_COMMAND", "1");
    crate::session::apply_route_env_with(
        &route,
        &mut cmd,
        parent.iter().map(|(key, _)| key.clone()),
    );
    let injected = child_env(parent, &cmd);
    assert!(scrubbed_keys(&injected).is_empty(), "the trustc child would see {injected:?}");
    assert!(injected.contains_key(std::ffi::OsStr::new("PATH")), "{injected:?}");
    assert!(injected.contains_key(std::ffi::OsStr::new("RUSTC_BOOTSTRAP")), "{injected:?}");
}

#[test]
fn compiler_route_devcli_compile_env_is_untouched() {
    let session = KaniSession::for_argv_tests(argv_test_args());
    let cmd = builder(&session)
        .compile_command(Path::new("/i/bin/trust-mc-compiler"), PathBuf::from("/k/lib"), None)
        .unwrap();
    let envs: Vec<_> = cmd.get_envs().collect();
    assert!(envs.iter().all(|(_, value)| value.is_some()), "DevCli removed variables: {envs:?}");
}
