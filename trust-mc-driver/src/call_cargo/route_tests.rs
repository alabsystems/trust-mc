// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Cargo units on the Trustc route (T1 S7), `compiler_route` filter: the composed
//! cargo invocation and every refusal of the cargo launcher.

use super::targets::package_targets;
use crate::args::compiler_route::{CompilerRouteArgs, CompilerRouteKind};
use crate::args::{Backend, CargoKaniArgs, VerificationArgs};
use crate::session::trustc_route::{
    BackendIdentity, RUSTC_WRAPPER_ENV_VARS, TRUSTC_HOST_RUSTFLAGS, TrustcIdentity,
    TrustcRouteError, key_content_sha256, key_library_fingerprint,
};
use crate::session::{CompilerRoute, KaniSession};
use crate::util::args::{CargoArg, CommandWrapper as _, PassTo};
use cargo_metadata::Package;
use clap::Parser;
use std::collections::BTreeMap;
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};
use std::process::Command;

const COMMIT: &str = "45dc60873c4fef21649ae277a93cc8cc9cf39191";
const DRIVER_SHA256: &str = "948b36c62eacc5d19ae9308d2cdcffe55535a4519f3d4bdb2d4f5ae54a973055";
const PACKAGE_ID: &str = "cargo-pair-pass 0.1.0 (path+file:///w/cargo-pair/pass)";

fn verify_args() -> VerificationArgs {
    let mut args = CargoKaniArgs::try_parse_from(["cargo-trust-mc"]).unwrap().verify_opts;
    args.backend = Backend::AY;
    args
}

fn strings<'a>(args: impl Iterator<Item = &'a OsStr>) -> Vec<String> {
    args.map(|arg| arg.to_str().expect("utf-8 test argv").to_string()).collect()
}

fn cargo_arg_strings(args: &[CargoArg]) -> Vec<String> {
    let mut cmd = Command::new("cargo");
    cmd.pass_cargo_args(args);
    strings(cmd.get_args())
}

fn env_pairs(pairs: &[(&str, &str)]) -> Vec<(OsString, OsString)> {
    pairs.iter().map(|(key, value)| (OsString::from(key), OsString::from(value))).collect()
}

/// The value `cmd` sets for `key`: `Some(Some(v))` set, `Some(None)` removed,
/// `None` untouched.
fn env_edit(cmd: &Command, key: &str) -> Option<Option<String>> {
    cmd.get_envs()
        .find(|(k, _)| *k == key)
        .map(|(_, value)| value.map(|v| v.to_string_lossy().into_owned()))
}

/// The environment a child of `cmd` sees when its parent environment is `parent`.
fn child_env(parent: &[(OsString, OsString)], cmd: &Command) -> BTreeMap<String, String> {
    let mut child: BTreeMap<String, String> = parent
        .iter()
        .map(|(k, v)| (k.to_string_lossy().into_owned(), v.to_string_lossy().into_owned()))
        .collect();
    for (key, value) in cmd.get_envs() {
        let key = key.to_string_lossy().into_owned();
        match value {
            Some(value) => child.insert(key, value.to_string_lossy().into_owned()),
            None => child.remove(&key),
        };
    }
    child
}

/// A Trustc route over fake files: a seal under "Application Support" holding
/// `bin/trustc` and `bin/targo`, and a KEY with its backend dylib and KEY.json.
struct FakeRoute {
    _tmp: tempfile::TempDir,
    sysroot: PathBuf,
    trustc: PathBuf,
    backend: PathBuf,
    key_dir: PathBuf,
}

impl FakeRoute {
    fn new() -> Self {
        let tmp = tempfile::TempDir::new().unwrap();
        let sysroot = tmp.path().join("Application Support/aterm/pkg/store/trust/8571");
        let key_dir = tmp.path().join("keyed/driver-948b36c62eacc5d1");
        std::fs::create_dir_all(sysroot.join("bin")).unwrap();
        std::fs::create_dir_all(key_dir.join("codegen-backends")).unwrap();
        std::fs::write(sysroot.join("bin/trustc"), "").unwrap();
        std::fs::write(sysroot.join("bin/targo"), "").unwrap();
        let backend = key_dir.join("codegen-backends/librustc_codegen_trust_mc.dylib");
        std::fs::write(&backend, b"fake dylib").unwrap();
        std::fs::write(
            key_dir.join("KEY.json"),
            format!(r#"{{"driver_sha256": "{DRIVER_SHA256}"}}"#),
        )
        .unwrap();
        let sysroot = sysroot.canonicalize().unwrap();
        FakeRoute {
            trustc: sysroot.join("bin/trustc"),
            backend: backend.canonicalize().unwrap(),
            key_dir: key_dir.canonicalize().unwrap(),
            sysroot,
            _tmp: tmp,
        }
    }

    fn route(&self) -> CompilerRoute {
        CompilerRoute::Trustc {
            trustc: self.trustc.clone(),
            backend: self.backend.clone(),
            key_dir: self.key_dir.clone(),
        }
    }

    fn backend_sha256(&self) -> String {
        trust_mc_core::evidence::EvidenceHash::sha256_bytes(b"fake dylib").value
    }

    /// The KEY content identity the preflight would compute for this KEY.
    fn key_sha256(&self) -> String {
        key_content_sha256(
            &std::fs::read(self.key_dir.join("KEY.json")).unwrap(),
            &key_library_fingerprint(&self.key_dir).unwrap(),
        )
    }

    /// A session on this route whose identity is already established, as the
    /// preflight would have left it.
    fn session(&self) -> KaniSession {
        let session = KaniSession::for_argv_tests_with_route(verify_args(), self.route());
        let identity = TrustcIdentity {
            trustc: self.trustc.clone(),
            sysroot: self.sysroot.clone(),
            commit: COMMIT.to_string(),
            driver_name: "librustc_driver-98fef360a4a26975.dylib".to_string(),
            driver_sha256: DRIVER_SHA256.to_string(),
            backend: Some(BackendIdentity {
                path: self.backend.clone(),
                sha256: self.backend_sha256(),
            }),
            key_dir: self.key_dir.clone(),
            key: "driver-948b36c62eacc5d1".to_string(),
            key_libraries: key_library_fingerprint(&self.key_dir).unwrap(),
            key_sha256: self.key_sha256(),
        };
        session.trustc_identity.set(identity).unwrap();
        session
    }

    /// Replace the fake seal's `bin/targo` with a script: the `[env]` table probe
    /// runs it as `cargo -Zunstable-options config get env --format json-value`.
    #[cfg(unix)]
    fn fake_cargo(&self, script: &str) {
        use std::os::unix::fs::PermissionsExt;
        let cargo = self.sysroot.join("bin/targo");
        std::fs::write(&cargo, format!("#!/bin/sh\n{script}\n")).unwrap();
        std::fs::set_permissions(&cargo, std::fs::Permissions::from_mode(0o755)).unwrap();
    }
}

fn lib_package() -> Package {
    serde_json::from_value(serde_json::json!({
        "name": "cargo-pair-pass",
        "version": "0.1.0",
        "id": PACKAGE_ID,
        "source": null,
        "dependencies": [],
        "targets": [{
            "name": "cargo_pair_pass",
            "kind": ["lib"],
            "crate_types": ["lib"],
            "src_path": "/w/cargo-pair/pass/src/lib.rs",
            "edition": "2021",
            "doctest": true,
            "test": true,
            "doc": true,
        }],
        "features": {},
        "manifest_path": "/w/cargo-pair/pass/Cargo.toml",
        "edition": "2021",
    }))
    .expect("valid test Package JSON")
}

/// A parent environment holding everything the cargo launcher must not pass on.
fn hostile_parent_env() -> Vec<(OsString, OsString)> {
    env_pairs(&[
        ("PATH", "/usr/bin"),
        ("RUSTUP_TOOLCHAIN", "nightly-2025-12-03"),
        ("TRUST_MC_SYSROOT", "/k"),
        ("TRUST_MC_AY_BIN", "/ay"),
        ("AY_TIMEOUT", "9"),
        // Empty: how cargo is told to run no wrapper, so not refused.
        ("RUSTC_WRAPPER", ""),
        ("CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", ""),
    ])
}

fn assert_trustc_cargo_env(cmd: &Command, fake: &FakeRoute, parent: &[(OsString, OsString)]) {
    assert_eq!(env_edit(cmd, "RUSTC"), Some(Some(fake.trustc.display().to_string())));
    for var in RUSTC_WRAPPER_ENV_VARS {
        assert_eq!(env_edit(cmd, var), Some(Some(String::new())), "{var} must be set empty");
    }
    assert_eq!(env_edit(cmd, "RUSTUP_TOOLCHAIN"), Some(None), "RUSTUP_TOOLCHAIN must be removed");
    let child = child_env(parent, cmd);
    let leaked: Vec<&String> =
        child.keys().filter(|k| k.starts_with("TRUST_MC_") || k.starts_with("AY_")).collect();
    assert!(leaked.is_empty(), "the cargo child would see {leaked:?}");
    assert!(!child.contains_key("RUSTUP_TOOLCHAIN"), "{child:?}");
    assert_eq!(child.get("PATH").map(String::as_str), Some("/usr/bin"));
}

/// `cargo_build_args` on DevCli, written down from the composition before S7.
#[test]
fn compiler_route_devcli_cargo_build_args_match_pre_route_golden() {
    let session = KaniSession::for_argv_tests(verify_args());
    assert_eq!(
        cargo_arg_strings(&session.cargo_build_args(PathBuf::from("/t/kani"))),
        [
            "rustc",
            "--target",
            env!("TARGET"),
            "-Zhost-config",
            "-Ztarget-applies-to-host",
            "--config=host.rustflags=[\"--cfg=kani_host\"]",
            "--target-dir",
            "/t/kani",
            "--message-format",
            "json-diagnostic-rendered-ansi",
        ]
    );
    assert_eq!(
        cargo_arg_strings(&session.route_cargo_config_args()),
        cargo_arg_strings(&super::cargo_config_args())
    );
}

#[test]
fn compiler_route_trustc_cargo_config_args_give_host_units_the_posture_and_no_engine() {
    let host = "[\"--cfg=kani_host\",\"-Ztrust-verify=off\"]";
    let args = cargo_arg_strings(&super::trustc_cargo_config_args());
    assert_eq!(
        args,
        [
            "--target".to_string(),
            env!("TARGET").to_string(),
            "-Zhost-config".to_string(),
            "-Ztarget-applies-to-host".to_string(),
            format!("--config=host.rustflags={host}"),
            format!("--config=host.{}.rustflags={host}", env!("TARGET")),
        ]
    );
    assert_eq!(TRUSTC_HOST_RUSTFLAGS, ["--cfg=kani_host", "-Ztrust-verify=off"]);
    for arg in &args {
        assert!(!arg.contains("codegen-backend") && !arg.contains("llvm-args"), "{arg}");
    }
    let session = FakeRoute::new().session();
    assert_eq!(cargo_arg_strings(&session.route_cargo_config_args()), args);
}

#[test]
fn compiler_route_trustc_targo_separates_compilation_and_project_queries() {
    let fake = FakeRoute::new();
    let session = fake.session();
    let parent = hostile_parent_env();
    let query = session.trustc_cargo_command_on(parent.clone()).unwrap();
    let build = session.trustc_cargo_build_command_on(parent.clone()).unwrap();
    for command in [&query, &build] {
        assert_eq!(Path::new(command.get_program()), fake.sysroot.join("bin/targo"));
        assert_trustc_cargo_env(command, &fake, &parent);
    }
    assert!(query.get_args().next().is_none(), "project queries reject compilation lane flags");
    assert_eq!(strings(build.get_args()), ["--unverified"]);
}

#[test]
fn compiler_route_trustc_cargo_build_runs_the_seal_cargo_with_the_host_split() {
    let fake = FakeRoute::new();
    let session = fake.session();
    let parent = hostile_parent_env();

    let cargo = session.trustc_cargo_build_command_on(parent.clone()).unwrap();
    let namespace = session.kani_target_namespace().unwrap();
    assert_eq!(
        namespace,
        format!(
            "kani-trustc-{}-{}-{}",
            &COMMIT[..12],
            &fake.backend_sha256()[..12],
            &fake.key_sha256()[..12]
        )
    );
    let target_dir = PathBuf::from("/t").join(&namespace);
    let cargo_args = session.cargo_build_args(target_dir.clone());
    let rustc_args = session.cargo_build_rustc_args(fake.key_dir.join("lib"), None).unwrap();
    let package = lib_package();
    let target = package_targets(&session.args, &package).remove(0);
    let cmd = session
        .cargo_build_command(
            cargo,
            &cargo_args,
            PACKAGE_ID,
            &[],
            &target,
            &rustc_args,
            session.cargo_build_local_kani_arg(),
        )
        .unwrap();

    // The seal's own Trust frontend, never the driver's build toolchain.
    assert_eq!(Path::new(cmd.get_program()), fake.sysroot.join("bin/targo"));
    assert_trustc_cargo_env(&cmd, &fake, &parent);

    // Cargo arguments: the host split, the backend-keyed target dir, the package
    // and target; no engine selection or engine argument anywhere before `--`.
    let argv = strings(cmd.get_args());
    let split = argv.iter().position(|arg| arg == "--").expect("a `--` before the local args");
    let host = "[\"--cfg=kani_host\",\"-Ztrust-verify=off\"]";
    assert_eq!(
        &argv[..split],
        [
            "--unverified".to_string(),
            "rustc".to_string(),
            "--target".to_string(),
            env!("TARGET").to_string(),
            "-Zhost-config".to_string(),
            "-Ztarget-applies-to-host".to_string(),
            format!("--config=host.rustflags={host}"),
            format!("--config=host.{}.rustflags={host}", env!("TARGET")),
            "--target-dir".to_string(),
            target_dir.display().to_string(),
            "--message-format".to_string(),
            "json-diagnostic-rendered-ansi".to_string(),
            "-p".to_string(),
            PACKAGE_ID.to_string(),
            "--lib".to_string(),
        ]
    );
    // Only the selected target gets the package-local engine group.
    let local = &argv[split + 1..];
    assert_eq!(local.len(), 1, "{local:?}");
    assert!(local[0].starts_with("-Cllvm-args=--trust-mc-engine-args=pct1:"), "{local:?}");

    // Target units (CARGO_ENCODED_RUSTFLAGS): the backend exactly once, verification
    // off, one dependency engine group, the KEY sysroot, and no DevCli selector.
    let encoded = env_edit(&cmd, "CARGO_ENCODED_RUSTFLAGS").flatten().expect("target rustflags");
    let target_flags: Vec<&str> = encoded.split('\x1f').collect();
    let count = |pred: &dyn Fn(&str) -> bool| target_flags.iter().filter(|f| pred(f)).count();
    let backend_flag = format!("-Zcodegen-backend={}", fake.backend.display());
    assert_eq!(count(&|f| f.starts_with("-Zcodegen-backend=")), 1, "{target_flags:#?}");
    assert_eq!(count(&|f| f == backend_flag), 1, "{target_flags:#?}");
    assert_eq!(count(&|f| f == "-Ztrust-verify=off"), 1, "{target_flags:#?}");
    assert_eq!(count(&|f| f.starts_with("-Cllvm-args=--trust-mc-engine-args=pct1:")), 1);
    assert_eq!(count(&|f| f.starts_with("-Cllvm-args=")), 1, "{target_flags:#?}");
    assert_eq!(count(&|f| f == "--kani-compiler"), 0, "{target_flags:#?}");
    let sysroot = target_flags.iter().position(|f| *f == "--sysroot").expect("--sysroot");
    assert_eq!(target_flags[sysroot + 1], fake.key_dir.display().to_string());
}

#[test]
fn compiler_route_trustc_cargo_refuses_every_rustc_wrapper_variable_before_any_probe() {
    let fake = FakeRoute::new();
    for var in RUSTC_WRAPPER_ENV_VARS {
        let env = env_pairs(&[(*var, "/usr/local/bin/sccache"), ("PATH", "/usr/bin")]);
        let expect_refusal = |error: anyhow::Error| {
            match error.downcast_ref::<TrustcRouteError>() {
                Some(TrustcRouteError::RustcWrapper { vars }) => {
                    assert_eq!(vars, &[format!("{var}=/usr/local/bin/sccache")]);
                }
                other => panic!("{var}: expected a RustcWrapper refusal, got {other:?}"),
            }
            assert!(error.to_string().contains("compiler route trustc refused"), "{error}");
        };
        // No identity yet: the refusal must come before the preflight probes anything
        // (with these fake paths a probe would fail with another error).
        let session = KaniSession::for_argv_tests_with_route(verify_args(), fake.route());
        expect_refusal(session.trustc_cargo_command_on(env.clone()).unwrap_err());
        expect_refusal(session.trustc_cargo_build_command_on(env.clone()).unwrap_err());
        match session.cargo_metadata_command_on(env!("TARGET"), env.clone()) {
            Ok(_) => panic!("{var}: cargo metadata ran through a wrapper"),
            Err(error) => expect_refusal(error),
        }
        assert!(session.trustc_identity.get().is_none(), "{var}: a probe ran before the refusal");

        let route_args = CompilerRouteArgs {
            compiler_route: CompilerRouteKind::Trustc,
            trustc: Some(fake.trustc.clone()),
            backend_dylib: None,
        };
        let error =
            crate::session::install::trustc_route_locate_cargo_with(&route_args, env).unwrap_err();
        assert!(matches!(error, TrustcRouteError::RustcWrapper { .. }), "{error}");
    }

    // Set empty, a wrapper variable is how cargo is told to run none: accepted.
    let session = fake.session();
    let empty: Vec<(OsString, OsString)> =
        RUSTC_WRAPPER_ENV_VARS.iter().map(|var| (OsString::from(var), OsString::new())).collect();
    session.trustc_cargo_command_on(empty).unwrap();
}

#[test]
fn compiler_route_trustc_cargo_refuses_a_sysroot_without_its_own_cargo() {
    let fake = FakeRoute::new();
    let session = fake.session();
    let seal_cargo = fake.sysroot.join("bin/targo");
    let expect_refusal = |error: anyhow::Error, detail: &str| {
        match error.downcast_ref::<TrustcRouteError>() {
            Some(TrustcRouteError::SealCargo { sysroot, .. }) => assert_eq!(sysroot, &fake.sysroot),
            other => panic!("expected a SealCargo refusal, got {other:?}"),
        }
        assert!(error.to_string().contains(detail), "{error}");
    };

    // Even an available compatibility persona cannot replace the missing Trust frontend.
    std::fs::write(fake.sysroot.join("bin/cargo"), "compatibility persona").unwrap();
    std::fs::remove_file(&seal_cargo).unwrap();
    expect_refusal(session.trustc_cargo_command_on(Vec::new()).unwrap_err(), "bin/targo");
    expect_refusal(session.trustc_cargo_build_command_on(Vec::new()).unwrap_err(), "bin/targo");
    match session.cargo_metadata_command_on(env!("TARGET"), Vec::new()) {
        Ok(_) => panic!("cargo metadata ran without the seal's cargo"),
        Err(error) => expect_refusal(error, "bin/targo"),
    }

    // A link could follow another toolchain's frontend.
    #[cfg(unix)]
    {
        std::os::unix::fs::symlink("/usr/bin/true", &seal_cargo).unwrap();
        expect_refusal(
            session.trustc_cargo_command_on(Vec::new()).unwrap_err(),
            "is not a regular file",
        );
    }
}

#[test]
fn compiler_route_trustc_cargo_metadata_and_locate_project_run_the_seal_cargo() {
    let fake = FakeRoute::new();
    let session = fake.session();
    let parent = hostile_parent_env();

    let metadata = match session.cargo_metadata_command_on(env!("TARGET"), parent.clone()) {
        Ok(metadata) => metadata.cargo_command(),
        Err(error) => panic!("{error}"),
    };
    assert_eq!(Path::new(metadata.get_program()), fake.sysroot.join("bin/targo"));
    assert_trustc_cargo_env(&metadata, &fake, &parent);
    let argv = strings(metadata.get_args());
    assert_eq!(argv.first().map(String::as_str), Some("metadata"));
    assert!(!argv.iter().any(|arg| arg == "--unverified"), "{argv:?}");
    let platform = argv.iter().position(|a| a == "--filter-platform").expect("--filter-platform");
    assert_eq!(argv[platform + 1], env!("TARGET"));

    // `locate-project` runs before any session: the cargo next to --trustc (or
    // TRUST_MC_TRUSTC), with the same environment.
    let mut route_args = CompilerRouteArgs {
        compiler_route: CompilerRouteKind::Trustc,
        trustc: Some(fake.trustc.clone()),
        backend_dylib: None,
    };
    let locate =
        crate::session::install::trustc_route_locate_cargo_with(&route_args, parent.clone())
            .unwrap();
    assert_eq!(Path::new(locate.get_program()), fake.sysroot.join("bin/targo"));
    assert_trustc_cargo_env(&locate, &fake, &parent);
    assert!(locate.get_args().next().is_none(), "locate-project receives no compilation lane");

    route_args.trustc = None;
    let mut from_env = parent.clone();
    from_env.push((OsString::from("TRUST_MC_TRUSTC"), fake.trustc.clone().into_os_string()));
    let locate =
        crate::session::install::trustc_route_locate_cargo_with(&route_args, from_env).unwrap();
    assert_eq!(Path::new(locate.get_program()), fake.sysroot.join("bin/targo"));
}

/// The single-file route's environment refusals hold for cargo units, and come
/// before any probe: a `RUSTFLAGS` token that reaches a route-owned option (it would
/// reach every target unit through `CARGO_ENCODED_RUSTFLAGS`) and a set engine knob.
#[test]
fn compiler_route_trustc_cargo_refuses_route_owned_rustflags_and_engine_knobs_before_any_probe() {
    let fake = FakeRoute::new();
    let cases: &[(&[(&str, &str)], &str)] = &[
        (&[("RUSTFLAGS", "-Cllvm-args=--no-unwinding-checks")], "RouteOwnedRustflags"),
        (&[("RUSTFLAGS", "--cfg x -C llvm_args=--harness=other")], "RouteOwnedRustflags"),
        (&[("RUSTFLAGS", "@/k/engine-flag.args")], "RouteOwnedRustflags"),
        (&[("RUSTFLAGS", "-Zcodegen-backend=/x/other.dylib")], "RouteOwnedRustflags"),
        (&[("RUSTFLAGS", "-Ztrust-verify=on")], "RouteOwnedRustflags"),
        (&[("TRUST_MC_NO_LOOP_RULE", "1"), ("PATH", "/usr/bin")], "EngineEnvKnobs"),
        // The `[host]` tables' environment form reaches build scripts and proc-macros.
        (&[("CARGO_HOST_RUSTFLAGS", "-Cllvm-args=--no-unwinding-checks")], "HostRustflags"),
        (
            &[("CARGO_HOST_AARCH64_APPLE_DARWIN_RUSTFLAGS", "--cfg x -Zcodegen-backend=/x.dylib")],
            "HostRustflags",
        ),
        (&[("CARGO_HOST_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS", "@/k/flags")], "HostRustflags"),
    ];
    for (pairs, want) in cases {
        let env = env_pairs(pairs);
        let session = KaniSession::for_argv_tests_with_route(verify_args(), fake.route());
        let check = |error: anyhow::Error| {
            let got = match error.downcast_ref::<TrustcRouteError>() {
                Some(TrustcRouteError::RouteOwnedRustflags { .. }) => "RouteOwnedRustflags",
                Some(TrustcRouteError::EngineEnvKnobs { .. }) => "EngineEnvKnobs",
                Some(TrustcRouteError::HostRustflags { vars }) => {
                    assert_eq!(vars, &[format!("{}={}", pairs[0].0, pairs[0].1)], "{pairs:?}");
                    "HostRustflags"
                }
                other => panic!("{pairs:?}: expected {want}, got {other:?}"),
            };
            assert_eq!(got, *want, "{pairs:?}");
            assert!(error.to_string().contains("compiler route trustc refused"), "{error}");
        };
        check(session.trustc_cargo_command_on(env.clone()).unwrap_err());
        check(session.trustc_cargo_build_command_on(env.clone()).unwrap_err());
        match session.cargo_metadata_command_on(env!("TARGET"), env) {
            Ok(_) => panic!("{pairs:?}: cargo metadata ran"),
            Err(error) => check(error),
        }
        assert!(
            session.trustc_identity.get().is_none(),
            "{pairs:?}: a probe ran before the refusal"
        );
    }

    // A compile-flags header that leaves the route's options alone is accepted, and
    // reaches the target units ahead of the route's own flags (rustc: last wins);
    // so is a host flag that leaves them alone.
    let session = fake.session();
    let forwarded = "--cfg trust_mc_smoke_forwarded";
    session
        .trustc_cargo_command_on(env_pairs(&[
            ("RUSTFLAGS", forwarded),
            ("CARGO_HOST_RUSTFLAGS", "--cfg from_host_env -W unused"),
        ]))
        .unwrap();
    let rustc_args =
        session.cargo_build_rustc_args(fake.key_dir.join("lib"), Some(forwarded)).unwrap();
    let mut rendered = Command::new("trustc");
    rendered.pass_rustc_args(&rustc_args, PassTo::OnlyLocalCrate);
    let flags = strings(rendered.get_args());
    let cfg = flags.iter().position(|f| f == "trust_mc_smoke_forwarded").expect("forwarded cfg");
    let backend =
        flags.iter().position(|f| f.starts_with("-Zcodegen-backend=")).expect("backend selection");
    let posture = flags.iter().rposition(|f| f == "-Ztrust-verify=off").expect("posture");
    assert!(cfg < backend && cfg < posture, "{flags:?}");
}

/// The effective cargo `[env]` table is read with the seal's own cargo before any
/// compile: a `TRUST_MC_*` / `AY_*` key there is refused naming `NAME=value`, no
/// table at all (cargo exits 101 saying so) is accepted, any other probe failure
/// is refused, and DevCli probes nothing.
#[cfg(unix)]
#[test]
fn compiler_route_trustc_cargo_env_table_probe_refuses_scrubbed_keys_before_any_compile() {
    let fake = FakeRoute::new();
    let session = fake.session();
    let probe_args = "-Zunstable-options config get env --format json-value";

    fake.fake_cargo(&format!(
        r#"[ "$*" = "{probe_args}" ] || {{ echo "unexpected argv: $*" >&2; exit 3; }}
echo '{{"KANI_X":{{"force":true,"value":"1"}},"OTHER":"y","TRUST_MC_REACH_DEBUG":"","AY_TIMEOUT":{{"value":"9"}}}}'"#
    ));
    let error = session.refuse_cargo_env_table(None).unwrap_err();
    match error.downcast_ref::<TrustcRouteError>() {
        Some(TrustcRouteError::CargoEnvTable { vars }) => {
            assert_eq!(vars, &["AY_TIMEOUT=9".to_string(), "TRUST_MC_REACH_DEBUG=".to_string()]);
        }
        other => panic!("expected a CargoEnvTable refusal, got {other:?}"),
    }
    assert!(error.to_string().contains("compiler route trustc refused"), "{error}");

    // A table without scrubbed keys, and no table at all, are accepted.
    fake.fake_cargo(r#"echo '{"KANI_X":"1","RUSTC_BOOTSTRAP":"1"}'"#);
    session.refuse_cargo_env_table(None).unwrap();
    fake.fake_cargo(r#"echo 'error: config value `env` is not set' >&2; exit 101"#);
    session.refuse_cargo_env_table(Some(&fake.key_dir)).unwrap();

    // Any other failure of the probe is a refusal: the route cannot show the table.
    fake.fake_cargo(r#"echo 'error: something else' >&2; exit 101"#);
    let error = session.refuse_cargo_env_table(None).unwrap_err();
    assert!(
        matches!(
            error.downcast_ref::<TrustcRouteError>(),
            Some(TrustcRouteError::CargoEnvProbe { .. })
        ),
        "{error}"
    );
    fake.fake_cargo("echo 'not json'");
    let error = session.refuse_cargo_env_table(None).unwrap_err();
    assert!(
        matches!(
            error.downcast_ref::<TrustcRouteError>(),
            Some(TrustcRouteError::CargoEnvProbe { .. })
        ),
        "{error}"
    );

    // DevCli runs no probe (the fake cargo would fail it).
    fake.fake_cargo("exit 7");
    KaniSession::for_argv_tests(verify_args()).refuse_cargo_env_table(None).unwrap();
}
