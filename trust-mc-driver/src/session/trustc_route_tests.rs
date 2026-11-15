// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Preflight refusals of the Trustc route (`compiler_route` filter), against fake
//! sysroots, KEY directories and a fake backend dylib.

use super::*;
use std::collections::BTreeMap;
use std::env::consts::{DLL_PREFIX, DLL_SUFFIX};
use tempfile::TempDir;

const SHA_8571: &str = "948b36c62eacc5d19ae9308d2cdcffe55535a4519f3d4bdb2d4f5ae54a973055";
const SHA_8560: &str = "c2e8f1798de668fa8819c6c9c4b05075441f4fea84541d3b4bb10983ae8bd744";
const COMMIT_8571: &str = "45dc60873c4fef21649ae277a93cc8cc9cf39191";

fn driver(hash: &str) -> String {
    format!("{DLL_PREFIX}rustc_driver-{hash}{DLL_SUFFIX}")
}

fn driver_8571() -> String {
    driver("98fef360a4a26975")
}

fn driver_8560() -> String {
    driver("e5ab7a82643f630e")
}

fn sha256(bytes: &[u8]) -> String {
    trust_mc_core::evidence::EvidenceHash::sha256_bytes(bytes).value
}

struct Fixture {
    _tmp: TempDir,
    trustc: PathBuf,
    sysroot: PathBuf,
    backend: PathBuf,
    key_dir: PathBuf,
}

impl Fixture {
    /// A sysroot shaped like store/trust/8571 (with "Application Support" in its
    /// path) and a matching KEY directory holding a fake backend dylib.
    fn new() -> Self {
        let tmp = TempDir::new().unwrap();
        let sysroot = tmp.path().join("Application Support/aterm/pkg/store/trust/8571");
        fs::create_dir_all(sysroot.join("bin")).unwrap();
        fs::create_dir_all(sysroot.join("lib")).unwrap();
        let trustc = sysroot.join("bin/trustc");
        fs::write(&trustc, "not a compiler").unwrap();
        fs::write(sysroot.join("lib").join(driver_8571()), b"driver").unwrap();
        fs::write(
            sysroot.join(PROVENANCE_FILE),
            format!(
                "# PROVENANCE\nprovenance_class=BUILD-STAMPED-CLEAN\nreported_commit={COMMIT_8571}\n\
                 artifact_driver_name={}\nartifact_driver_sha256={SHA_8571}\n\
                 build_stamp:head={COMMIT_8571}\n",
                driver_8571()
            ),
        )
        .unwrap();
        let fixture = Fixture {
            trustc,
            backend: PathBuf::new(),
            key_dir: PathBuf::new(),
            sysroot,
            _tmp: tmp,
        };
        fixture.with_key(&format!("driver-{}", &SHA_8571[..16]), SHA_8571)
    }

    fn with_key(mut self, name: &str, driver_sha256: &str) -> Self {
        self.key_dir = self._tmp.path().join("keyed").join(name);
        fs::create_dir_all(self.key_dir.join("codegen-backends")).unwrap();
        fs::write(
            self.key_dir.join(KEY_JSON_FILE),
            serde_json::json!({ "driver_sha256": driver_sha256, "library_mode": "smoke" })
                .to_string(),
        )
        .unwrap();
        self.backend = self.key_dir.join("codegen-backends/librustc_codegen_trust_mc.dylib");
        fs::write(&self.backend, b"fake dylib").unwrap();
        self
    }

    fn host(&self) -> FakeHost {
        FakeHost {
            sysroot: self.sysroot.clone(),
            commit: Some(COMMIT_8571.to_string()),
            linked: vec![
                "librustc_codegen_trust_mc.dylib".to_string(),
                driver_8571(),
                "libSystem.B.dylib".to_string(),
            ],
            world_writable: None,
        }
    }

    fn preflight(&self, host: &FakeHost) -> Result<TrustcIdentity, TrustcRouteError> {
        preflight(&self.trustc, &self.backend, &self.key_dir, host)
    }

    /// The KEY content identity as the preflight computes it now.
    fn key_sha256(&self) -> String {
        key_content_sha256(
            &fs::read(self.key_dir.join(KEY_JSON_FILE)).unwrap(),
            &key_library_fingerprint(&self.key_dir).unwrap(),
        )
    }
}

/// Cargo fingerprints `--sysroot <KEY>` by path, so a KEY rebuilt at the same path
/// must land in a fresh target-dir namespace: the namespace follows the KEY's
/// libraries and KEY.json, and stays put while nothing changes.
#[test]
fn compiler_route_target_namespace_changes_with_the_key_libraries_and_key_json() {
    let f = Fixture::new();
    let rlib = f.key_dir.join("lib/libkani.rlib");
    fs::create_dir_all(rlib.parent().unwrap()).unwrap();
    fs::write(&rlib, b"first library").unwrap();
    let first = f.preflight(&f.host()).unwrap();
    assert_eq!(f.preflight(&f.host()).unwrap().target_namespace(), first.target_namespace());
    assert_eq!(first.target_namespace().len(), "kani-trustc-".len() + 12 + 1 + 12 + 1 + 12);

    // The rlib rewritten in place with the same length: the stamp's inode stays, its
    // times move, and so does the namespace (the review's stale-KEY attack).
    std::thread::sleep(std::time::Duration::from_millis(20));
    fs::write(&rlib, b"other library").unwrap();
    let rewritten = f.preflight(&f.host()).unwrap();
    assert_eq!(rewritten.backend, first.backend);
    assert_eq!(rewritten.commit, first.commit);
    assert_ne!(rewritten.key_sha256, first.key_sha256);
    assert_ne!(rewritten.target_namespace(), first.target_namespace());
    assert_eq!(
        rewritten.target_namespace().rsplit('-').next().unwrap(),
        &rewritten.key_sha256[..12]
    );

    // A library entry added, and KEY.json rewritten (build-keyed rewrites it on
    // every rebuild), each move it too.
    fs::write(f.key_dir.join("lib/libstd.rlib"), b"std").unwrap();
    let added = f.preflight(&f.host()).unwrap();
    assert_ne!(added.key_sha256, rewritten.key_sha256);
    fs::write(
        f.key_dir.join(KEY_JSON_FILE),
        serde_json::json!({ "driver_sha256": SHA_8571, "library_mode": "parity" }).to_string(),
    )
    .unwrap();
    let rekeyed = f.preflight(&f.host()).unwrap();
    assert_ne!(rekeyed.key_sha256, added.key_sha256);

    // The content identity is a function of the bytes and the fingerprint alone.
    let libraries = key_library_fingerprint(&f.key_dir).unwrap();
    assert_eq!(key_content_sha256(b"{}", &libraries), key_content_sha256(b"{}", &libraries));
    assert_ne!(key_content_sha256(b"{}", &libraries), key_content_sha256(b"{ }", &libraries));
}

/// The effective cargo `[env]` table (`config get env --format json-value`): any
/// `TRUST_MC_*` / `AY_*` key is refused as `NAME=value`, in both value shapes;
/// other keys are cargo's business; a non-object is a probe failure.
#[test]
fn compiler_route_cargo_env_table_json_refuses_scrubbed_keys_only() {
    let json = r#"{"KANI_X":{"force":true,"value":"1"},"RUSTC_BOOTSTRAP":"1",
        "TRUST_MC_NO_LOOP_RULE":"1","TRUST_MC_REACH_DEBUG":"","AY_TIMEOUT":{"value":"9","force":false}}"#;
    match refuse_cargo_env_table_json(json) {
        Err(TrustcRouteError::CargoEnvTable { vars }) => {
            assert_eq!(vars, ["AY_TIMEOUT=9", "TRUST_MC_NO_LOOP_RULE=1", "TRUST_MC_REACH_DEBUG="])
        }
        other => panic!("{other:?}"),
    }
    refuse_cargo_env_table_json(r#"{"KANI_X":"1","RUSTC_BOOTSTRAP":"1"}"#).unwrap();
    refuse_cargo_env_table_json("{}").unwrap();
    assert!(matches!(
        refuse_cargo_env_table_json("[1]"),
        Err(TrustcRouteError::CargoEnvProbe { .. })
    ));
    assert!(matches!(
        refuse_cargo_env_table_json("not json"),
        Err(TrustcRouteError::CargoEnvProbe { .. })
    ));
    let error = refuse_cargo_env_table_json(r#"{"TRUST_MC_SMT_NODE_BUDGET":"1"}"#).unwrap_err();
    assert!(
        error.to_string().contains("[env] table in effect here sets TRUST_MC_SMT_NODE_BUDGET=1"),
        "{error}"
    );
}

/// `CARGO_HOST_*` variables reach build scripts and proc-macros: one carrying a
/// route-owned token or an argfile is refused, naming it; a `--cfg` is forwarded.
#[test]
fn compiler_route_host_rustflags_refuse_route_owned_tokens_only() {
    let pairs = |pairs: &[(&str, &str)]| -> Vec<(String, String)> {
        pairs.iter().map(|(k, v)| ((*k).to_string(), (*v).to_string())).collect()
    };
    refuse_host_rustflags(pairs(&[
        ("CARGO_HOST_RUSTFLAGS", "--cfg from_host_env"),
        ("CARGO_HOST_AARCH64_APPLE_DARWIN_RUSTFLAGS", "-W unused --cfg x"),
        ("CARGO_BUILD_RUSTFLAGS", "-Cllvm-args=--no-unwinding-checks"),
        ("RUSTFLAGS", "-Cllvm-args=--no-unwinding-checks"),
    ]))
    .unwrap();
    match refuse_host_rustflags(pairs(&[
        ("CARGO_HOST_AARCH64_APPLE_DARWIN_RUSTFLAGS", "--cfg x -Zcodegen-backend=/x.dylib"),
        ("CARGO_HOST_RUSTFLAGS", "-C llvm_args=--harness=other"),
        ("CARGO_HOST_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS", "@/k/flags"),
        ("CARGO_HOST_LINKER", "cc"),
    ])) {
        Err(TrustcRouteError::HostRustflags { vars }) => assert_eq!(
            vars,
            [
                "CARGO_HOST_AARCH64_APPLE_DARWIN_RUSTFLAGS=--cfg x -Zcodegen-backend=/x.dylib",
                "CARGO_HOST_RUSTFLAGS=-C llvm_args=--harness=other",
                "CARGO_HOST_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS=@/k/flags",
            ]
        ),
        other => panic!("{other:?}"),
    }
    let env: Vec<(OsString, OsString)> =
        vec![(OsString::from("CARGO_HOST_RUSTFLAGS"), OsString::from("-Ztrust-verify=on"))];
    assert!(matches!(refuse_cargo_route_env(&env), Err(TrustcRouteError::HostRustflags { .. })));
}

struct FakeHost {
    sysroot: PathBuf,
    commit: Option<String>,
    linked: Vec<String>,
    world_writable: Option<(PathBuf, u32)>,
}

impl RouteHost for FakeHost {
    fn trustc_sysroot(&self, _trustc: &Path) -> Result<PathBuf, TrustcRouteError> {
        Ok(self.sysroot.clone())
    }

    fn trustc_commit_hash(&self, _trustc: &Path) -> Result<Option<String>, TrustcRouteError> {
        Ok(self.commit.clone())
    }

    fn linked_libraries(&self, _dylib: &Path) -> Result<Vec<String>, TrustcRouteError> {
        Ok(self.linked.clone())
    }

    /// Reported when the world-writable path is `path` or one of its ancestors.
    fn world_writable_ancestor(
        &self,
        path: &Path,
    ) -> Result<Option<(PathBuf, u32)>, TrustcRouteError> {
        Ok(self.world_writable.clone().filter(|(found, _)| path.starts_with(found)))
    }

    /// Reported when the world-writable path is `dir` or lies below it.
    fn world_writable_within(
        &self,
        dir: &Path,
    ) -> Result<Option<(PathBuf, u32)>, TrustcRouteError> {
        Ok(self.world_writable.clone().filter(|(found, _)| found.starts_with(dir)))
    }
}

#[test]
fn compiler_route_preflight_accepts_one_driver_identity() {
    let f = Fixture::new();
    let identity = f.preflight(&f.host()).unwrap();
    assert_eq!(identity.commit, COMMIT_8571);
    assert_eq!(identity.driver_name, driver_8571());
    assert_eq!(identity.driver_sha256, SHA_8571);
    assert_eq!(identity.key, "driver-948b36c62eacc5d1");
    let backend = identity.backend.as_ref().unwrap();
    assert_eq!(backend.path, f.backend);
    assert_eq!(backend.sha256, sha256(b"fake dylib"));
    assert_eq!(
        identity.target_namespace(),
        format!(
            "kani-trustc-45dc60873c4f-{}-{}",
            &sha256(b"fake dylib")[..12],
            &identity.key_sha256[..12]
        )
    );
    assert_eq!(identity.key_sha256, f.key_sha256());
    assert_eq!(
        identity.marker(),
        format!(
            "[AY:COMPILER_ROUTE route=trustc trustc={} commit=45dc60873c4f driver={} \
             backend_sha256={} key=driver-948b36c62eacc5d1]",
            f.trustc.display().to_string().replace(' ', "%20"),
            driver_8571(),
            sha256(b"fake dylib"),
        )
    );
    assert!(
        identity.marker().contains("Application%20Support/aterm/pkg/store/trust/8571/bin/trustc")
    );
}

#[test]
fn compiler_route_target_namespace_changes_with_the_backend_sha256_alone() {
    // Cargo does not fingerprint the dylib's bytes, so a backend rebuilt at the same
    // path under the same trustc must land in a fresh target-dir namespace.
    let f = Fixture::new();
    let identity = f.preflight(&f.host()).unwrap();
    let mut rebuilt = identity.clone();
    rebuilt.backend.as_mut().unwrap().sha256 = SHA_8560.to_string();
    assert_eq!(rebuilt.trustc, identity.trustc);
    assert_eq!(rebuilt.backend.as_ref().unwrap().path, identity.backend.as_ref().unwrap().path);
    assert_eq!(rebuilt.commit, identity.commit);
    assert_ne!(rebuilt.target_namespace(), identity.target_namespace());
    assert_eq!(
        rebuilt.target_namespace(),
        format!("kani-trustc-45dc60873c4f-c2e8f1798de6-{}", &identity.key_sha256[..12])
    );
    assert_eq!(identity.clone().target_namespace(), identity.target_namespace());

    // And the preflight really does see a rebuilt dylib at the same path.
    fs::write(&f.backend, b"rebuilt dylib").unwrap();
    let after = f.preflight(&f.host()).unwrap();
    assert_eq!(after.backend.as_ref().unwrap().path, identity.backend.as_ref().unwrap().path);
    assert_ne!(after.target_namespace(), identity.target_namespace());
}

#[test]
fn compiler_route_playback_preflight_neither_requires_nor_reports_a_backend() {
    let f = Fixture::new();
    fs::remove_dir_all(f.key_dir.join("codegen-backends")).unwrap();
    // A host whose backend answers would all refuse: playback must not consult them.
    let mut host = f.host();
    host.linked = vec![driver_8560()];
    host.world_writable = Some((f.key_dir.join("codegen-backends"), 0o1777));
    let identity = preflight_key(&f.trustc, &f.key_dir, &host).unwrap();
    assert_eq!(identity.backend, None);
    assert_eq!(identity.driver_sha256, SHA_8571);
    assert_eq!(identity.key, "driver-948b36c62eacc5d1");
    let marker = identity.marker();
    assert!(marker.contains(" backend=unused "), "{marker}");
    assert!(!marker.contains("backend_sha256"), "{marker}");

    // The KEY and driver checks still hold for playback.
    let f = Fixture::new().with_key(&format!("driver-{}", &SHA_8571[..16]), SHA_8560);
    assert!(matches!(
        preflight_key(&f.trustc, &f.key_dir, &f.host()),
        Err(TrustcRouteError::KeyDriverSha { .. })
    ));
}

#[test]
fn compiler_route_refuses_key_json_from_another_driver_naming_both_sha256s() {
    let f = Fixture::new().with_key(&format!("driver-{}", &SHA_8571[..16]), SHA_8560);
    let error = f.preflight(&f.host()).unwrap_err();
    assert!(matches!(
        &error,
        TrustcRouteError::KeyDriverSha { key_driver_sha256, sysroot_driver_sha256, .. }
            if key_driver_sha256 == SHA_8560 && sysroot_driver_sha256 == SHA_8571
    ));
    let message = error.to_string();
    assert!(message.contains(SHA_8560) && message.contains(SHA_8571), "{message}");
}

#[test]
fn compiler_route_refuses_a_trustc_outside_the_sysroot_it_reports() {
    // A shim (atpkg's pkg/bin/trustc, a rustup proxy, or a script re-pointed by a seal
    // promotion) answers `--print sysroot` for one build and may compile with another.
    let mut f = Fixture::new();
    let shim_dir = f._tmp.path().join("Application Support/aterm/pkg/bin");
    fs::create_dir_all(&shim_dir).unwrap();
    f.trustc = shim_dir.join("trustc");
    fs::write(&f.trustc, "#!/bin/sh\nexec .../store/trust/8571/bin/trustc \"$@\"\n").unwrap();
    let error = f.preflight(&f.host()).unwrap_err();
    assert_eq!(
        error,
        TrustcRouteError::TrustcOutsideSysroot {
            trustc: f.trustc.clone(),
            sysroot: f.sysroot.clone()
        }
    );
    assert!(error.to_string().contains("/bin/trustc itself"), "{error}");

    // A trustc in a sibling sysroot's bin is refused too.
    f.trustc = f.sysroot.with_file_name("8560").join("bin/trustc");
    assert!(matches!(f.preflight(&f.host()), Err(TrustcRouteError::TrustcOutsideSysroot { .. })));
}

#[test]
fn compiler_route_refuses_a_key_directory_named_for_another_driver() {
    let f = Fixture::new().with_key(&format!("driver-{}", &SHA_8560[..16]), SHA_8571);
    assert_eq!(
        f.preflight(&f.host()).unwrap_err(),
        TrustcRouteError::KeyName {
            key_dir: f.key_dir.clone(),
            key: "driver-c2e8f1798de668fa".to_string(),
            expected: "driver-948b36c62eacc5d1".to_string(),
        }
    );
}

#[test]
fn compiler_route_refuses_a_missing_or_malformed_key_json() {
    let f = Fixture::new();
    fs::remove_file(f.key_dir.join(KEY_JSON_FILE)).unwrap();
    assert!(matches!(f.preflight(&f.host()), Err(TrustcRouteError::KeyJson { .. })));

    fs::write(f.key_dir.join(KEY_JSON_FILE), r#"{"driver_sha256": "c2e8"}"#).unwrap();
    assert!(matches!(f.preflight(&f.host()), Err(TrustcRouteError::KeyJson { .. })));

    fs::write(f.key_dir.join(KEY_JSON_FILE), "not json").unwrap();
    assert!(matches!(f.preflight(&f.host()), Err(TrustcRouteError::KeyJson { .. })));
}

#[test]
fn compiler_route_refuses_a_backend_linked_to_another_driver() {
    let f = Fixture::new();
    let mut host = f.host();
    host.linked = vec![driver_8560(), "libSystem.B.dylib".to_string()];
    let error = f.preflight(&host).unwrap_err();
    assert_eq!(
        error,
        TrustcRouteError::BackendDriver {
            dylib: f.backend.clone(),
            linked: vec![driver_8560()],
            sysroot_driver: driver_8571(),
        }
    );
    let message = error.to_string();
    assert!(message.contains(&driver_8560()) && message.contains(&driver_8571()), "{message}");
}

#[test]
fn compiler_route_refuses_a_backend_linked_to_no_driver_or_two() {
    let f = Fixture::new();
    let mut host = f.host();
    host.linked = vec!["libSystem.B.dylib".to_string()];
    assert!(
        matches!(f.preflight(&host), Err(TrustcRouteError::BackendDriver { linked, .. }) if linked.is_empty())
    );
    host.linked = vec![driver_8571(), driver_8560()];
    assert!(matches!(f.preflight(&host), Err(TrustcRouteError::BackendDriver { .. })));
}

#[test]
fn compiler_route_refuses_a_backend_under_a_world_writable_directory() {
    let f = Fixture::new();
    let mut host = f.host();
    let dir = f.backend.parent().unwrap().to_path_buf();
    host.world_writable = Some((dir.clone(), 0o1777));
    assert_eq!(
        f.preflight(&host).unwrap_err(),
        TrustcRouteError::WorldWritable { dylib: f.backend.clone(), path: dir, mode: 0o1777 }
    );
}

#[test]
fn compiler_route_refuses_a_world_writable_key_directory_or_library_entry() {
    let f = Fixture::new();
    let mut host = f.host();
    // The directory holding every KEY, mode 1777.
    let keyed = f.key_dir.parent().unwrap().to_path_buf();
    host.world_writable = Some((keyed.clone(), 0o1777));
    assert_eq!(
        f.preflight(&host).unwrap_err(),
        TrustcRouteError::KeyWorldWritable {
            key_dir: f.key_dir.clone(),
            path: keyed,
            mode: 0o1777
        }
    );

    // One rlib inside a library folder, for verification and for playback alike.
    for subdir in KEY_LIBRARY_DIRS {
        let rlib = f.key_dir.join(subdir).join("libkani.rlib");
        host.world_writable = Some((rlib.clone(), 0o666));
        let expected = TrustcRouteError::KeyWorldWritable {
            key_dir: f.key_dir.clone(),
            path: rlib,
            mode: 0o666,
        };
        assert_eq!(f.preflight(&host).unwrap_err(), expected);
        assert_eq!(preflight_key(&f.trustc, &f.key_dir, &host).unwrap_err(), expected);
        assert!(expected.to_string().contains("world-writable"), "{expected}");
    }

    // KEY.json itself.
    let key_json = f.key_dir.join(KEY_JSON_FILE);
    host.world_writable = Some((key_json.clone(), 0o666));
    assert!(matches!(
        f.preflight(&host),
        Err(TrustcRouteError::KeyWorldWritable { path, .. }) if path == key_json
    ));
}

#[test]
fn compiler_route_refuses_a_backend_that_changed_after_the_preflight() {
    let f = Fixture::new();
    let identity = f.preflight(&f.host()).unwrap();
    assert_eq!(identity.recheck_backend(), Ok(()));

    fs::write(&f.backend, b"replaced dylib").unwrap();
    let error = identity.recheck_backend().unwrap_err();
    assert_eq!(
        error,
        TrustcRouteError::BackendChanged {
            dylib: f.backend.clone(),
            preflight_sha256: sha256(b"fake dylib"),
            current_sha256: sha256(b"replaced dylib"),
        }
    );
    let message = error.to_string();
    assert!(message.starts_with("compiler route trustc refused"), "{message}");
    assert!(
        message.contains(&sha256(b"fake dylib")) && message.contains(&sha256(b"replaced dylib"))
    );

    fs::remove_file(&f.backend).unwrap();
    assert!(matches!(identity.recheck_backend(), Err(TrustcRouteError::BadPath { .. })));

    // Playback loads no backend, so there is nothing to re-check.
    let playback = preflight_key(&f.trustc, &f.key_dir, &f.host()).unwrap();
    assert_eq!(playback.recheck_backend(), Ok(()));
}

#[test]
fn compiler_route_refuses_a_key_rebuilt_or_removed_after_the_preflight() {
    let f = Fixture::new();
    let identity = f.preflight(&f.host()).unwrap();
    let playback = preflight_key(&f.trustc, &f.key_dir, &f.host()).unwrap();
    let key_json = f.key_dir.join(KEY_JSON_FILE);

    // Rewritten for another driver.
    fs::write(&key_json, serde_json::json!({ "driver_sha256": SHA_8560 }).to_string()).unwrap();
    for checked in [&identity, &playback] {
        match checked.recheck_backend() {
            Err(error @ TrustcRouteError::KeyChanged { .. }) => {
                let text = error.to_string();
                assert!(text.contains(SHA_8560) && text.contains(SHA_8571), "{text}");
            }
            other => panic!("expected KeyChanged, got {other:?}"),
        }
    }

    // Removed, as build-keyed does before it rebuilds the libraries.
    fs::remove_file(&key_json).unwrap();
    assert!(matches!(identity.recheck_backend(), Err(TrustcRouteError::KeyChanged { .. })));
    assert!(matches!(playback.recheck_backend(), Err(TrustcRouteError::KeyChanged { .. })));
}

/// A temporary directory none of whose ancestors is world-writable.
///
/// `world_writable_ancestor` judges a symbolic link's target by EVERY directory
/// above it, so a fixture created under a world-writable system temp directory
/// (`/tmp` is mode 1777 on Linux) reports that directory before the fixture's
/// own permissions are ever looked at. macOS's per-user `$TMPDIR` has no such
/// ancestor, which is the only reason the fixture passed there. Take the first
/// candidate root with no world-writable ancestor, and refuse, naming every
/// candidate, rather than skip the assertions on a host that offers none.
#[cfg(unix)]
fn temp_dir_without_world_writable_ancestor() -> TempDir {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let candidates =
        [std::env::temp_dir(), manifest.join("../target/tmp"), manifest.join("target/tmp")];
    let mut rejected = Vec::new();
    for root in candidates {
        if fs::create_dir_all(&root).is_err() {
            rejected.push(format!("{}: cannot create", root.display()));
            continue;
        }
        let Ok(canonical) = root.canonicalize() else {
            rejected.push(format!("{}: cannot canonicalize", root.display()));
            continue;
        };
        match world_writable_ancestor(&canonical) {
            Ok(None) => return TempDir::new_in(&canonical).unwrap(),
            Ok(Some((path, mode))) => {
                rejected.push(format!("{}: {} is mode {mode:o}", root.display(), path.display()))
            }
            Err(error) => rejected.push(format!("{}: {error}", root.display())),
        }
    }
    panic!("no temporary root without a world-writable ancestor on this host: {rejected:?}");
}

#[cfg(unix)]
#[test]
fn compiler_route_world_writable_within_scans_a_key_library_folder() {
    use std::os::unix::fs::PermissionsExt;
    let tmp = temp_dir_without_world_writable_ancestor();
    let lib = tmp.path().join("lib");
    let rustlib = lib.join("rustlib/aarch64-apple-darwin/lib");
    fs::create_dir_all(&rustlib).unwrap();
    for dir in [&lib, &lib.join("rustlib"), &lib.join("rustlib/aarch64-apple-darwin"), &rustlib] {
        fs::set_permissions(dir, fs::Permissions::from_mode(0o755)).unwrap();
    }
    let kani = lib.join("libkani.rlib");
    let std_rlib = rustlib.join("libstd.rlib");
    for file in [&kani, &std_rlib] {
        fs::write(file, b"rlib").unwrap();
        fs::set_permissions(file, fs::Permissions::from_mode(0o644)).unwrap();
    }
    assert_eq!(world_writable_within(&lib).unwrap(), None);
    assert_eq!(world_writable_within(&tmp.path().join("absent")).unwrap(), None);

    fs::set_permissions(&std_rlib, fs::Permissions::from_mode(0o666)).unwrap();
    assert_eq!(world_writable_within(&lib).unwrap(), Some((std_rlib.clone(), 0o666)));
    fs::set_permissions(&std_rlib, fs::Permissions::from_mode(0o644)).unwrap();

    // A symbolic link is judged by its target, and not descended into.
    let outside = tmp.path().join("outside");
    fs::create_dir(&outside).unwrap();
    fs::set_permissions(&outside, fs::Permissions::from_mode(0o755)).unwrap();
    let shared = outside.join("shared.rlib");
    fs::write(&shared, b"rlib").unwrap();
    fs::set_permissions(&shared, fs::Permissions::from_mode(0o666)).unwrap();
    std::os::unix::fs::symlink(&outside, lib.join("linked")).unwrap();
    assert_eq!(world_writable_within(&lib).unwrap(), None);
    std::os::unix::fs::symlink(&shared, lib.join("libshared.rlib")).unwrap();
    assert_eq!(
        world_writable_within(&lib).unwrap().map(|(path, _)| path),
        Some(lib.join("libshared.rlib"))
    );
    fs::remove_file(lib.join("libshared.rlib")).unwrap();
    assert_eq!(world_writable_within(&lib).unwrap(), None);

    // ... and by every directory above its target: anyone could swap a file there.
    let open = tmp.path().join("open");
    let deep = open.join("rustlib/lib");
    fs::create_dir_all(&deep).unwrap();
    fs::set_permissions(&open, fs::Permissions::from_mode(0o777)).unwrap();
    std::os::unix::fs::symlink(&deep, lib.join("prebuilt-std")).unwrap();
    assert_eq!(world_writable_within(&lib).unwrap(), Some((open.canonicalize().unwrap(), 0o777)));
}

#[cfg(unix)]
#[test]
fn compiler_route_world_writable_check_finds_the_innermost_sticky_directory() {
    use std::os::unix::fs::PermissionsExt;
    let tmp = TempDir::new().unwrap();
    let sticky = tmp.path().join("shared");
    fs::create_dir(&sticky).unwrap();
    fs::set_permissions(&sticky, fs::Permissions::from_mode(0o1777)).unwrap();
    let dylib = sticky.join("librustc_codegen_trust_mc.dylib");
    fs::write(&dylib, b"fake dylib").unwrap();
    let dylib = dylib.canonicalize().unwrap();
    assert_eq!(
        world_writable_ancestor(&dylib).unwrap(),
        Some((sticky.canonicalize().unwrap(), 0o1777))
    );

    fs::set_permissions(&dylib, fs::Permissions::from_mode(0o666)).unwrap();
    assert_eq!(world_writable_ancestor(&dylib).unwrap().map(|(path, _)| path), Some(dylib));

    let private = tmp.path().join("private");
    fs::create_dir(&private).unwrap();
    fs::set_permissions(&private, fs::Permissions::from_mode(0o755)).unwrap();
    let inside = private.join("lib.dylib");
    fs::write(&inside, b"").unwrap();
    let inside = inside.canonicalize().unwrap();
    let found = world_writable_ancestor(&inside).unwrap().map(|(path, _)| path);
    assert!(
        found.as_ref().is_none_or(|path| !path.starts_with(tmp.path().canonicalize().unwrap())),
        "a private directory was reported world-writable: {found:?}"
    );
}

#[test]
fn compiler_route_refuses_a_sysroot_without_exactly_one_driver() {
    let f = Fixture::new();
    fs::write(f.sysroot.join("lib").join(driver_8560()), b"second").unwrap();
    assert!(matches!(
        f.preflight(&f.host()),
        Err(TrustcRouteError::SysrootDriver { found, .. }) if found.len() == 2
    ));
    fs::remove_file(f.sysroot.join("lib").join(driver_8560())).unwrap();
    fs::remove_file(f.sysroot.join("lib").join(driver_8571())).unwrap();
    assert!(matches!(
        f.preflight(&f.host()),
        Err(TrustcRouteError::SysrootDriver { found, .. }) if found.is_empty()
    ));
}

#[test]
fn compiler_route_refuses_provenance_naming_another_driver() {
    let f = Fixture::new();
    fs::rename(
        f.sysroot.join("lib").join(driver_8571()),
        f.sysroot.join("lib").join(driver_8560()),
    )
    .unwrap();
    assert!(matches!(
        f.preflight(&f.host()),
        Err(TrustcRouteError::ProvenanceDriverName { recorded, installed, .. })
            if recorded == driver_8571() && installed == driver_8560()
    ));
}

#[test]
fn compiler_route_refuses_conflicting_provenance_fields() {
    let f = Fixture::new();
    let path = f.sysroot.join(PROVENANCE_FILE);
    let mut text = fs::read_to_string(&path).unwrap();
    text.push_str(&format!("artifact_driver_sha256={SHA_8560}\n"));
    fs::write(&path, text).unwrap();
    assert!(matches!(f.preflight(&f.host()), Err(TrustcRouteError::Provenance { .. })));
}

#[test]
fn compiler_route_without_provenance_hashes_the_driver_and_asks_trustc_for_its_commit() {
    let f = Fixture::new();
    fs::remove_file(f.sysroot.join(PROVENANCE_FILE)).unwrap();
    let hashed = sha256(b"driver");
    let f = f.with_key(&format!("driver-{}", &hashed[..16]), &hashed);
    let mut host = f.host();
    host.commit = Some("feedfacefeedfacefeedfacefeedfacefeedface".to_string());
    let identity = f.preflight(&host).unwrap();
    assert_eq!(identity.driver_sha256, hashed);
    assert_eq!(identity.commit, "feedfacefeedfacefeedfacefeedfacefeedface");

    host.commit = None;
    assert!(matches!(f.preflight(&host), Err(TrustcRouteError::SysrootProbe { .. })));
}

#[test]
fn compiler_route_refuses_provenance_whose_commit_is_not_the_trustc_commit() {
    let f = Fixture::new();
    let mut host = f.host();
    host.commit = Some("feedfacefeedfacefeedfacefeedfacefeedface".to_string());
    let refused = |result: Result<TrustcIdentity, TrustcRouteError>| match result {
        Err(error @ TrustcRouteError::ProvenanceCommit { .. }) => error.to_string(),
        other => panic!("expected ProvenanceCommit, got {other:?}"),
    };
    let text = refused(f.preflight(&host));
    assert!(text.contains(COMMIT_8571) && text.contains("feedface"), "{text}");
    // Playback runs the same half of the preflight.
    refused(preflight_key(&f.trustc, &f.key_dir, &host));

    // A trustc that reports no commit-hash keeps PROVENANCE's record.
    host.commit = None;
    assert_eq!(f.preflight(&host).unwrap().commit, COMMIT_8571);
}

#[test]
fn compiler_route_parses_otool_and_readelf_library_lists() {
    // `otool -L` of the probe backend built by build 8571 (2026-09-12).
    let otool = "$HOME/Library/Caches/trust-mc-t1/driver-route/probe/libprobe_backend.dylib:\n\
        \t$HOME/Library/Caches/trust-mc-t1/driver-route/probe/libprobe_backend.dylib (compatibility version 0.0.0, current version 0.0.0)\n\
        \t@rpath/librustc_driver-98fef360a4a26975.dylib (compatibility version 0.0.0, current version 0.0.0)\n\
        \t/usr/lib/libSystem.B.dylib (compatibility version 1.0.0, current version 1359.0.0)\n";
    assert_eq!(
        parse_otool_libraries(otool),
        ["libprobe_backend.dylib", "librustc_driver-98fef360a4a26975.dylib", "libSystem.B.dylib"]
    );
    let readelf = " 0x0000000000000001 (NEEDED)             Shared library: [librustc_driver-98fef360a4a26975.so]\n \
                   0x0000000000000001 (NEEDED)             Shared library: [libc.so.6]\n \
                   0x000000000000000e (SONAME)             Library soname: [librustc_codegen_trust_mc.so]\n";
    assert_eq!(parse_readelf_needed(readelf), ["librustc_driver-98fef360a4a26975.so", "libc.so.6"]);
    assert_eq!(
        parse_commit_hash("rustc 1.99.0-dev\ncommit-hash: 45dc60873c4f\nhost: x\n").as_deref(),
        Some("45dc60873c4f")
    );
    assert_eq!(parse_commit_hash("rustc 1.99.0-dev\ncommit-hash: unknown\n"), None);
}

#[test]
fn compiler_route_scrub_leaves_no_trust_mc_or_ay_variable_in_the_child_env() {
    let parent: BTreeMap<OsString, OsString> = [
        ("TRUST_MC_SYSROOT", "/k"),
        ("TRUST_MC_AY_BIN", "/ay"),
        ("AY_DETERMINISTIC", "1"),
        ("HOME", "$HOME"),
        ("PATH", "/usr/bin"),
    ]
    .into_iter()
    .map(|(k, v)| (OsString::from(k), OsString::from(v)))
    .collect();
    let mut cmd = Command::new("trustc");
    cmd.env("RUSTC_BOOTSTRAP", "1").env("TRUST_MC_LOG", "debug").env("AY_BIN", "/x");
    scrub_engine_env(&mut cmd, parent.keys().cloned());

    let mut child = parent.clone();
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
    let leaked: Vec<_> = child.keys().filter(|key| is_scrubbed_env_key(key)).collect();
    assert!(leaked.is_empty(), "leaked into the trustc child: {leaked:?}");
    assert!(child.contains_key(OsStr::new("HOME")));
    assert!(child.contains_key(OsStr::new("RUSTC_BOOTSTRAP")));
}

#[test]
fn compiler_route_refuses_engine_knobs_it_would_silently_drop() {
    assert_eq!(
        refuse_engine_env_knobs(["TRUST_MC_SYSROOT", "TRUST_MC_NO_LOOP_RULE", "TRUST_MC_LOG"]),
        Err(TrustcRouteError::EngineEnvKnobs { vars: vec!["TRUST_MC_NO_LOOP_RULE".to_string()] })
    );
    assert_eq!(refuse_engine_env_knobs(["TRUST_MC_SYSROOT", "TRUST_MC_LOG", "AY_BIN"]), Ok(()));
}

#[test]
fn compiler_route_engine_env_knobs_cover_the_engine_sources() {
    let engine_src = Path::new(env!("CARGO_MANIFEST_DIR")).join("../trust-mc-compiler/src");
    if !engine_src.is_dir() {
        eprintln!("skipping: {} is not in this checkout", engine_src.display());
        return;
    }
    // Names that a single engine unit test reads for its own diagnostics, each
    // exempt only in that test's source: none changes what the engine generates.
    // The same name in any other source must still be inventoried.
    const TEST_ONLY: &[(&str, &str)] = &[
        // The directory test_static_array_addresses writes its evidence to.
        ("TRUST_MC_ARRAY_ADDRESS_EVIDENCE", "codegen_ay/chc/tests/test_static_array_addresses.rs"),
        // Turns on debug tracing of two engine modules in that test's process.
        ("TRUST_MC_CALLABLE_CONST_TRACE", "codegen_ay/chc/tests/test_boxed_callable_constants.rs"),
    ];
    let test_only: Vec<(&str, PathBuf)> =
        TEST_ONLY.iter().map(|(name, file)| (*name, engine_src.join(file))).collect();
    // Names the engine source mentions that are not generation knobs: its own
    // unit-test timeouts, build-time `env!` stamps, and the log filter.
    const NOT_KNOBS: &[&str] = &[
        "TRUST_MC_AY_TEST_TIMEOUT_SECS",
        "TRUST_MC_GIT_SHA",
        "TRUST_MC_GIT_DIRTY",
        "TRUST_MC_LOG",
    ];
    let mut found = std::collections::BTreeSet::new();
    let mut stack = vec![engine_src];
    while let Some(dir) = stack.pop() {
        for entry in fs::read_dir(&dir).unwrap().map(Result::unwrap) {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|ext| ext == "rs") {
                let text = fs::read_to_string(&path).unwrap();
                for piece in text.split("\"TRUST_MC_").skip(1) {
                    let name: String = piece
                        .chars()
                        .take_while(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || *c == '_')
                        .collect();
                    if piece[name.len()..].starts_with('"') {
                        let name = format!("TRUST_MC_{name}");
                        if test_only
                            .iter()
                            .any(|(test_name, file)| name == *test_name && path == *file)
                        {
                            continue;
                        }
                        found.insert(name);
                    }
                }
            }
        }
    }
    let knobs: std::collections::BTreeSet<String> =
        found.into_iter().filter(|name| !NOT_KNOBS.contains(&name.as_str())).collect();
    let listed: std::collections::BTreeSet<String> =
        ENGINE_ENV_KNOBS.iter().map(|name| (*name).to_string()).collect();
    assert_eq!(knobs, listed, "ENGINE_ENV_KNOBS is out of date with trust-mc-compiler/src");
}

#[test]
fn compiler_route_refuses_rustflags_that_reach_route_owned_options() {
    let refused = |rustflags: &str| match refuse_route_owned_rustflags(Some(rustflags)) {
        Err(TrustcRouteError::RouteOwnedRustflags { tokens }) => tokens,
        other => panic!("{rustflags:?}: expected a RUSTFLAGS refusal, got {other:?}"),
    };
    // The engine-argument channel, in every shape rustc accepts: attached, as a
    // separate token after -C, with `_` for `-`, the long --codegen forms, and a
    // getopts short cluster where -O is a flag and -C takes the rest of the token.
    for engine_flag in [
        "-Cllvm-args=--no-unwinding-checks",
        "-Cllvm_args=--no-overflow-checks",
        "--codegen=llvm-args=--harness=good",
        "-OCllvm-args=--no-memory-safety-checks",
        "-gCllvm_args=--ay-chc-bounded-unroll",
    ] {
        assert_eq!(refused(engine_flag), [engine_flag]);
    }
    assert_eq!(refused("-C llvm-args=--no-unwinding-checks"), ["llvm-args=--no-unwinding-checks"]);
    assert_eq!(
        refused("--codegen llvm_args=--no-default-checks"),
        ["llvm_args=--no-default-checks"]
    );
    // The backend selection and the harness posture the route sets itself.
    for owned in [
        "-Zcodegen-backend=$HOME/libother.dylib",
        "-Ztrust-verify=on",
        "-Zno-trust-verify",
        "-Ztrust_verify=on",
        "-Zno-codegen",
    ] {
        assert_eq!(refused(owned), [owned]);
    }
    assert_eq!(refused("-Z codegen_backend=llvm"), ["codegen_backend=llvm"]);
    assert_eq!(refused("-Z no_codegen"), ["no_codegen"]);
    // Argfiles are expanded by rustc before parsing, so their contents are unknown here.
    assert_eq!(refused("@$HOME/args.txt"), ["@$HOME/args.txt"]);
    assert_eq!(refused("@shell:$HOME/args.txt"), ["@shell:$HOME/args.txt"]);
    // Only the offending tokens are named, in order, among forwarded ones.
    let error = refuse_route_owned_rustflags(Some(
        "--edition 2021 -Cllvm-args=--no-unwinding-checks -Awarnings -Ztrust-verify=on",
    ))
    .unwrap_err();
    assert_eq!(
        error,
        TrustcRouteError::RouteOwnedRustflags {
            tokens: vec![
                "-Cllvm-args=--no-unwinding-checks".to_string(),
                "-Ztrust-verify=on".to_string()
            ]
        }
    );
    let message = error.to_string();
    assert!(message.starts_with("compiler route trustc refused: RUSTFLAGS token(s)"), "{message}");
    assert!(message.contains("\"-Cllvm-args=--no-unwinding-checks\""), "{message}");
    assert!(message.contains("--no-unwinding-checks") && message.contains("harnesses"));
}

#[test]
fn compiler_route_forwards_rustflags_that_leave_route_owned_options_alone() {
    // Compile-flags headers (compiletest, kani-domination) arrive through RUSTFLAGS.
    for value in [
        None,
        Some(""),
        Some("-Awarnings"),
        Some("--edition 2021"),
        Some("-Coverflow-checks=off"),
        Some("--cfg trust_mc_smoke_forwarded -Zthreads=4"),
        Some("-C opt-level=0 --cap-lints warn"),
        Some("--extern kani=$HOME/Application%20Support/libkani.rlib"),
    ] {
        assert_eq!(refuse_route_owned_rustflags(value), Ok(()), "{value:?}");
    }
    // The refusal judges the tokens compiles receive: the forwarder's own split.
    assert_eq!(
        crate::call_single_file::rustflags_tokens("--edition  2021").collect::<Vec<_>>(),
        ["--edition", "", "2021"]
    );
    assert!(
        crate::call_single_file::rustflags_tokens("-C llvm-args=x")
            .any(is_route_owned_rustflags_token)
    );
}

#[test]
fn compiler_route_establish_refuses_route_owned_rustflags_before_any_probe() {
    let f = Fixture::new();
    let host = f.host();
    let establish = |keys: &[&str], rustflags: Option<&str>, host: &FakeHost| {
        establish_identity_on(keys.iter(), rustflags, &f.trustc, &f.backend, &f.key_dir, host)
    };
    assert!(establish(&["HOME"], None, &host).is_ok());
    assert!(establish(&["HOME"], Some("--edition 2021"), &host).is_ok());
    // Every identity check passes; the engine flag alone refuses.
    assert!(matches!(
        establish(&["HOME"], Some("-Cllvm-args=--no-unwinding-checks"), &host),
        Err(TrustcRouteError::RouteOwnedRustflags { .. })
    ));
    // Before any probe: a host whose answers would all refuse still yields it.
    let mut broken = f.host();
    broken.sysroot = f.key_dir.clone();
    broken.linked = vec![driver_8560()];
    assert!(matches!(
        establish(&[], Some("-Zcodegen-backend=$HOME/libother.dylib"), &broken),
        Err(TrustcRouteError::RouteOwnedRustflags { .. })
    ));
    // Engine knobs are still refused, and first.
    assert!(matches!(
        establish(&["TRUST_MC_NO_LOOP_RULE"], Some("-Cllvm-args=x"), &host),
        Err(TrustcRouteError::EngineEnvKnobs { .. })
    ));
    // Playback forwards RUSTFLAGS too: the same tokens refuse, and otherwise its
    // preflight stays backend-free.
    assert!(matches!(
        establish_playback_identity_on(Some("-Zcodegen-backend=/x"), &f.trustc, &f.key_dir, &host),
        Err(TrustcRouteError::RouteOwnedRustflags { .. })
    ));
    let playback =
        establish_playback_identity_on(Some("--edition 2021"), &f.trustc, &f.key_dir, &host)
            .unwrap();
    assert_eq!(playback.backend, None);
}

/// The entry and detail of a `KeyLibraryChanged` refusal, or a panic naming `what`.
fn key_library_change(identity: &TrustcIdentity, what: &str) -> (String, String) {
    match identity.recheck_backend() {
        Err(error @ TrustcRouteError::KeyLibraryChanged { .. }) => {
            let message = error.to_string();
            assert!(message.starts_with("compiler route trustc refused: KEY "), "{message}");
            let TrustcRouteError::KeyLibraryChanged { entry, detail, .. } = error else {
                unreachable!()
            };
            (entry, detail)
        }
        other => panic!("{what}: expected KeyLibraryChanged, got {other:?}"),
    }
}

#[test]
fn compiler_route_refuses_a_key_library_changed_after_the_preflight() {
    use std::io::Write;
    let f = Fixture::new();
    let kani = f.key_dir.join("lib/libkani.rlib");
    let std_rlib = f.key_dir.join("lib/rustlib/aarch64-apple-darwin/lib/libstd.rlib");
    let playback_std = f.key_dir.join("playback/lib/libstd.rlib");
    for file in [&kani, &std_rlib, &playback_std] {
        fs::create_dir_all(file.parent().unwrap()).unwrap();
        fs::write(file, b"rlib v1").unwrap();
    }
    let preflight = || f.preflight(&f.host()).unwrap();
    let identity = preflight();
    let playback = preflight_key(&f.trustc, &f.key_dir, &f.host()).unwrap();
    assert_eq!(identity.key_libraries, key_library_fingerprint(&f.key_dir).unwrap());
    // Reading the libraries, as every compile does, changes nothing.
    fs::read(&kani).unwrap();
    fs::read(&playback_std).unwrap();
    assert_eq!(identity.recheck_backend(), Ok(()));
    assert_eq!(playback.recheck_backend(), Ok(()));

    // The same-driver rlib swap from the review: another rlib renamed over libkani.
    let identity = preflight();
    let staged = f.key_dir.join("lib/libkani.rlib.new");
    fs::write(&staged, b"rlib v2").unwrap();
    fs::rename(&staged, &kani).unwrap();
    let (entry, detail) = key_library_change(&identity, "rename over");
    assert_eq!(entry, "lib/libkani.rlib");
    assert!(detail.starts_with("was ["), "{detail}");

    // Written in place at the same size with the modification time put back: only
    // the status-change time moves (the pause covers coarse filesystem clocks).
    let identity = preflight();
    let modified = fs::metadata(&std_rlib).unwrap().modified().unwrap();
    std::thread::sleep(std::time::Duration::from_millis(50));
    let mut file = fs::OpenOptions::new().write(true).open(&std_rlib).unwrap();
    file.write_all(b"rlib v3").unwrap();
    file.set_modified(modified).unwrap();
    drop(file);
    assert_eq!(fs::metadata(&std_rlib).unwrap().modified().unwrap(), modified);
    #[cfg(unix)]
    assert_eq!(
        key_library_change(&identity, "in-place write").0,
        "lib/rustlib/aarch64-apple-darwin/lib/libstd.rlib"
    );

    // An rlib added to a library folder, and one removed.
    let identity = preflight();
    fs::write(f.key_dir.join("lib/libshadow.rlib"), b"rlib").unwrap();
    let (entry, detail) = key_library_change(&identity, "added");
    assert_eq!((entry.as_str(), detail.starts_with("added")), ("lib/libshadow.rlib", true));
    let identity = preflight();
    fs::remove_file(f.key_dir.join("lib/libshadow.rlib")).unwrap();
    let (entry, detail) = key_library_change(&identity, "removed");
    assert_eq!((entry.as_str(), detail.starts_with("removed")), ("lib/libshadow.rlib", true));

    // A library folder that was absent at the preflight and appears later.
    let identity = preflight();
    assert_eq!(identity.key_libraries.0.get("no_core/lib").map(String::as_str), Some("absent"));
    fs::create_dir_all(f.key_dir.join("no_core/lib")).unwrap();
    assert_eq!(key_library_change(&identity, "folder created").0, "no_core/lib");

    // Playback re-checks its libraries too.
    let playback = preflight_key(&f.trustc, &f.key_dir, &f.host()).unwrap();
    fs::write(&playback_std, b"rlib v4 longer").unwrap();
    assert_eq!(key_library_change(&playback, "playback").0, "playback/lib/libstd.rlib");
}

#[cfg(unix)]
#[test]
fn compiler_route_key_library_fingerprint_follows_linked_directories_once() {
    let f = Fixture::new();
    let lib = f.key_dir.join("lib");
    fs::create_dir_all(&lib).unwrap();
    fs::write(lib.join("libkani.rlib"), b"rlib").unwrap();
    // A linked prebuilt rustlib outside the KEY, and a link back up to the folder.
    let outside = f.key_dir.parent().unwrap().join("prebuilt-rustlib");
    fs::create_dir_all(&outside).unwrap();
    fs::write(outside.join("libcore.rlib"), b"core v1").unwrap();
    std::os::unix::fs::symlink(&outside, lib.join("prebuilt")).unwrap();
    std::os::unix::fs::symlink(&lib, lib.join("loop")).unwrap();

    let identity = f.preflight(&f.host()).unwrap();
    let names: Vec<&str> = identity.key_libraries.0.keys().map(String::as_str).collect();
    assert!(names.contains(&"lib/prebuilt/libcore.rlib"), "{names:?}");
    assert!(names.contains(&"lib/loop"), "{names:?}");
    assert!(!names.iter().any(|name| name.starts_with("lib/loop/")), "{names:?}");
    assert_eq!(identity.recheck_backend(), Ok(()));

    // A rewrite behind the link is a change of the KEY's libraries.
    fs::write(outside.join("libcore.rlib"), b"core v2 longer").unwrap();
    assert_eq!(key_library_change(&identity, "behind a link").0, "lib/prebuilt/libcore.rlib");

    // Re-pointing the link is one too.
    let identity = f.preflight(&f.host()).unwrap();
    let other = f.key_dir.parent().unwrap().join("other-rustlib");
    fs::create_dir_all(&other).unwrap();
    fs::write(other.join("libcore.rlib"), b"core v2 longer").unwrap();
    fs::remove_file(lib.join("prebuilt")).unwrap();
    std::os::unix::fs::symlink(&other, lib.join("prebuilt")).unwrap();
    assert!(key_library_change(&identity, "re-pointed link").0.starts_with("lib/prebuilt"));
}
