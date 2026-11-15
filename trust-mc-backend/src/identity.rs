// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Compiler identity handshake for `librustc_codegen_trust_mc.dylib` (plan S3).
//!
//! The dylib is only valid inside the exact `librustc_driver` it was linked
//! against. `dlopen` already refuses a driver with a different *filename*; this
//! module catches a different *build* that reuses the filename.
//!
//! Pure std so the same file serves `build.rs` (via `#[path]`) and the unit
//! tests, with no rustc_private crates in either.
//!
//! # What `artifact_driver_sha256` proves
//!
//! It is a seal LABEL: Trust packaging records it before the install-time
//! rewrite of the driver (ad-hoc re-signing), so it is not the sha256 of the
//! `librustc_driver-*.dylib` that is actually loaded. Measured 2026-09-12 on
//! seal 8571: PROVENANCE says `948b36c6…3055`, the file on disk hashes to
//! `e7a812eb…6edff`, and the driver's mtime is 9 s after PROVENANCE's (seal
//! 8560: `c2e8f179…d744` vs `5cc0b73e…48cc`). The handshake therefore proves
//! "same seal label", not "same loaded bytes". It keys on that label only and
//! never falls back to hashing the file, whose digest could never equal the
//! label for the same seal. Binding the loaded bytes needs Trust packaging to
//! record the post-install driver sha256 in PROVENANCE as well.

use std::io::ErrorKind;
use std::path::Path;

/// What `build.rs` measured about the compiler that built this dylib.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct BakedIdentity<'a> {
    /// `commit-hash:` from `$RUSTC -vV`.
    pub(crate) rustc_commit: &'a str,
    /// Basename of `<sysroot>/lib/librustc_driver-*.dylib`.
    pub(crate) driver: &'a str,
    /// `artifact_driver_sha256` from `<sysroot>/PROVENANCE`; empty when the
    /// building toolchain has no PROVENANCE (rustup nightlies).
    pub(crate) driver_sha256: &'a str,
}

/// The value of a top-level `key=value` line of a seal PROVENANCE file.
///
/// Comment lines and prefixed lines (`build_stamp:head=...`) never match, so a
/// quoted build stamp cannot shadow the seal's own artifact identity.
pub(crate) fn provenance_value<'t>(provenance: &'t str, key: &str) -> Option<&'t str> {
    provenance.lines().find_map(|line| {
        let (k, v) = line.split_once('=')?;
        (k == key).then(|| v.trim())
    })
}

/// Read a compiler's `PROVENANCE`: `Ok(None)` only when the file does not
/// exist.
///
/// Every other failure (EACCES, macOS privacy consent's "Operation not
/// permitted", a directory in its place) is an error: an unreadable file must
/// not downgrade the identity check to the weaker commit comparison.
pub(crate) fn read_provenance(path: &Path) -> Result<Option<String>, String> {
    match std::fs::read_to_string(path) {
        Ok(text) => Ok(Some(text)),
        Err(e) if e.kind() == ErrorKind::NotFound => Ok(None),
        Err(e) => Err(format!(
            "trust-mc codegen backend cannot establish the compiler identity: cannot read \
             {}: {e}",
            path.display()
        )),
    }
}

/// The commit hash rustc embeds in its version string,
/// `1.99.0-dev (45dc60873 2026-09-10)` -> `45dc60873`.
pub(crate) fn version_commit(version: &str) -> Option<&str> {
    let inner = version.split_once('(')?.1;
    let hash = inner.split_whitespace().next()?.trim_end_matches(')');
    (hash.len() >= 7 && hash.bytes().all(|b| b.is_ascii_hexdigit())).then_some(hash)
}

/// Decide whether a dylib built for `baked` may run inside the compiler whose
/// own sysroot is `sysroot` (carrying `provenance`, if the file exists) and
/// whose `rustc_interface` version string is `version`.
///
/// With PROVENANCE, identity is the driver artifact's sha256 label and nothing
/// else: two seals from one commit can differ. A backend built against a sealed
/// compiler (non-empty baked sha) requires PROVENANCE. Only a backend built
/// without one (the frozen rustup nightly) falls back to comparing the commit
/// in the version string with the baked commit. Every other case fails closed.
/// The error names both sides so the refusal is actionable.
pub(crate) fn check_identity(
    baked: &BakedIdentity<'_>,
    sysroot: &str,
    provenance: Option<&str>,
    version: Option<&str>,
) -> Result<(), String> {
    let rebuild = "rebuild trust-mc-backend with this compiler";
    if let Some(provenance) = provenance {
        let observed = provenance_value(provenance, "artifact_driver_sha256").unwrap_or("");
        if !observed.is_empty() && observed == baked.driver_sha256 {
            return Ok(());
        }
        let shown = |v: &str| if v.is_empty() { "<none>".to_owned() } else { v.to_owned() };
        return Err(format!(
            "trust-mc codegen backend was built for a different compiler: the backend was \
             built against {} with artifact_driver_sha256={}, but this compiler's \
             {sysroot}/PROVENANCE has artifact_driver_sha256={}; {rebuild}",
            baked.driver,
            shown(baked.driver_sha256),
            shown(observed),
        ));
    }
    if !baked.driver_sha256.is_empty() {
        return Err(format!(
            "trust-mc codegen backend was built for a different compiler: the backend was \
             built against a sealed compiler ({} with artifact_driver_sha256={}), but this \
             compiler has no PROVENANCE in {sysroot}; {rebuild}",
            baked.driver, baked.driver_sha256,
        ));
    }
    let observed = version.and_then(version_commit);
    match observed {
        Some(short) if !baked.rustc_commit.is_empty() && baked.rustc_commit.starts_with(short) => {
            Ok(())
        }
        _ => Err(format!(
            "trust-mc codegen backend was built for a different compiler: the backend was \
             built by rustc commit {} ({}), but this compiler (no PROVENANCE in {sysroot}) \
             reports commit {}; {rebuild}",
            if baked.rustc_commit.is_empty() { "<none>" } else { baked.rustc_commit },
            baked.driver,
            observed.unwrap_or("<none>"),
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SHA_8571: &str = "948b36c62eacc5d19ae9308d2cdcffe55535a4519f3d4bdb2d4f5ae54a973055";
    const SHA_8560: &str = "c2e8f1798de668fa8819c6c9c4b05075441f4fea84541d3b4bb10983ae8bd744";
    const BAKED_8571: BakedIdentity<'static> = BakedIdentity {
        rustc_commit: "45dc60873c4fef21649ae277a93cc8cc9cf39191",
        driver: "librustc_driver-98fef360a4a26975.dylib",
        driver_sha256: SHA_8571,
    };

    fn provenance(sha: &str) -> String {
        format!(
            "# PROVENANCE\nreported_commit=25ccaf01f102fe3b4127dabeffbeba7f55516b5a\n\
             artifact_driver_sha256={sha}\nbuild_stamp:artifact_driver_sha256=decoy\n"
        )
    }

    #[test]
    fn identity_mismatch_is_fatal_and_names_both_hashes() {
        let err = check_identity(&BAKED_8571, "/s/8560", Some(&provenance(SHA_8560)), None)
            .expect_err("a different driver build must be refused");
        assert!(err.contains(SHA_8571), "{err}");
        assert!(err.contains(SHA_8560), "{err}");
        assert!(err.contains("/s/8560/PROVENANCE"), "{err}");
    }

    #[test]
    fn identity_match_on_driver_sha_passes() {
        let ok = check_identity(&BAKED_8571, "/s/8571", Some(&provenance(SHA_8571)), None);
        assert_eq!(ok, Ok(()));
    }

    #[test]
    fn provenance_without_driver_sha_fails_closed() {
        let err = check_identity(&BAKED_8571, "/s", Some("reported_rev=45dc60873\n"), None)
            .expect_err("absent sha cannot establish identity");
        assert!(err.contains(SHA_8571) && err.contains("<none>"), "{err}");
        let unbaked = BakedIdentity { driver_sha256: "", ..BAKED_8571 };
        assert!(check_identity(&unbaked, "/s", Some(&provenance(SHA_8571)), None).is_err());
    }

    #[test]
    fn commit_fallback_without_provenance() {
        // Only a backend built by a toolchain without PROVENANCE (the frozen
        // nightly lane) may fall back to the commit.
        let unbaked = BakedIdentity { driver_sha256: "", ..BAKED_8571 };
        assert_eq!(
            check_identity(&unbaked, "/s", None, Some("1.99.0-dev (45dc60873 2026-09-10)")),
            Ok(())
        );
        let err = check_identity(&unbaked, "/s", None, Some("1.99.0-dev (25ccaf01f 2026-09-10)"))
            .expect_err("a different commit must be refused");
        assert!(
            err.contains("45dc60873c4fef21649ae277a93cc8cc9cf39191") && err.contains("25ccaf01f")
        );
        assert!(check_identity(&unbaked, "/s", None, None).is_err());
    }

    #[test]
    fn sealed_backend_without_provenance_fails_closed() {
        // Same commit, so the fallback would have accepted it.
        let err = check_identity(
            &BAKED_8571,
            "/s/clone",
            None,
            Some("1.99.0-dev (45dc60873 2026-09-10)"),
        )
        .expect_err("a sealed backend needs the loading compiler's PROVENANCE");
        assert!(err.contains(SHA_8571) && err.contains("no PROVENANCE in /s/clone"), "{err}");
    }

    /// A scratch directory unique to this test process and `name`.
    fn scratch(name: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir()
            .join(format!("trust-mc-backend-identity-{}-{name}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("create scratch dir");
        dir
    }

    #[test]
    fn unreadable_provenance_fails_closed() {
        let dir = scratch("unreadable");
        let path = dir.join("PROVENANCE");
        assert_eq!(read_provenance(&path), Ok(None), "absent is the only None");

        std::fs::write(&path, provenance(SHA_8571)).expect("write PROVENANCE");
        assert_eq!(read_provenance(&path), Ok(Some(provenance(SHA_8571))));

        // chmod 000: EACCES for anyone but root.
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o000)).unwrap();
            if std::fs::read(&path).is_err() {
                let err = read_provenance(&path).expect_err("EACCES must not read as absent");
                assert!(err.contains("cannot read") && err.contains("PROVENANCE"), "{err}");
            }
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o644)).unwrap();
        }

        // A directory in its place fails for every user.
        std::fs::remove_file(&path).unwrap();
        std::fs::create_dir(&path).unwrap();
        let err = read_provenance(&path).expect_err("an unreadable PROVENANCE must be an error");
        assert!(err.contains(&path.display().to_string()), "{err}");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn provenance_value_ignores_prefixed_and_comment_lines() {
        let text = provenance(SHA_8560);
        assert_eq!(provenance_value(&text, "artifact_driver_sha256"), Some(SHA_8560));
        assert_eq!(
            provenance_value("# artifact_driver_sha256=x\n", "artifact_driver_sha256"),
            None
        );
    }
}
