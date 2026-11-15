// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source-authoritative private AY location in a canonical release bundle.

use std::path::{Path, PathBuf};

pub(super) fn root_from_executable(executable: &Path) -> Result<&Path, String> {
    let bin = executable.parent().filter(|p| p.file_name().is_some_and(|n| n == "bin"));
    bin.and_then(Path::parent).ok_or_else(|| {
        "release driver is outside its bundle's bin directory; reinstall trust-mc".into()
    })
}

pub(super) fn locate(root: &Path) -> Result<PathBuf, String> {
    let refusal = |reason| {
        format!(
            "bundled AY helper is unavailable ({reason}); reinstall trust-mc. No PATH fallback is allowed"
        )
    };
    let root = root.canonicalize().map_err(|_| refusal("bundle root cannot be resolved"))?;
    let directory = root.join("libexec");
    let metadata = std::fs::symlink_metadata(&directory).map_err(|_| refusal("missing libexec"))?;
    if !metadata.is_dir() || metadata.file_type().is_symlink() {
        return Err(refusal("libexec must be a real directory"));
    }
    let helper = directory.join(format!("ay{}", std::env::consts::EXE_SUFFIX));
    let metadata = std::fs::symlink_metadata(&helper).map_err(|_| refusal("missing libexec/ay"))?;
    if !metadata.is_file()
        || metadata.file_type().is_symlink()
        || !super::is_executable_file(&helper)
    {
        return Err(refusal("libexec/ay must be a regular executable"));
    }
    if helper.canonicalize().map_err(|_| refusal("helper cannot be resolved"))? != helper {
        return Err(refusal("helper escaped its private directory"));
    }
    Ok(helper)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ay_binary::{
        AySource, Decision, ExternalAy, PinStatus, locate_selected, locate_with,
    };

    #[test]
    fn an_explicit_override_precedes_an_outside_bin_release_location() {
        let root = tempfile::tempdir().unwrap();
        let chosen = super::super::tests::fake_binary(root.path(), "explicit-ay");
        let outside = root.path().join("standalone-driver");
        assert_eq!(
            locate_selected(
                Some(chosen.clone().into_os_string()),
                || Ok(Some(outside.clone())),
                || panic!("explicit override must not consult PATH")
            ),
            Ok((chosen, AySource::Override))
        );
        let error = locate_selected(
            None,
            || Ok(Some(outside)),
            || panic!("invalid release must not consult PATH"),
        )
        .unwrap_err();
        assert!(error.contains("outside its bundle's bin"), "{error}");
    }

    #[test]
    fn private_helper_wins_and_missing_helper_never_consults_path() {
        let root = tempfile::tempdir().unwrap();
        let canonical = root.path().canonicalize().unwrap();
        let no_path = || panic!("release helper must not consult ambient AY");
        assert!(
            locate_with(None, Some(&canonical), no_path).unwrap_err().contains("missing libexec")
        );
        std::fs::create_dir(canonical.join("libexec")).unwrap();
        let helper = super::super::tests::fake_binary(&canonical.join("libexec"), "ay");
        assert_eq!(
            locate_with(None, Some(&canonical), no_path),
            Ok((helper.clone(), AySource::Bundled))
        );
        std::fs::remove_file(helper).unwrap();
        assert!(
            locate_with(None, Some(&canonical), no_path)
                .unwrap_err()
                .contains("missing libexec/ay")
        );
    }

    #[cfg(unix)]
    #[test]
    fn neither_a_helper_link_nor_an_intermediate_directory_link_can_escape() {
        let root = tempfile::tempdir().unwrap();
        let outside = tempfile::tempdir().unwrap();
        let helper = super::super::tests::fake_binary(outside.path(), "ay");
        std::fs::create_dir(root.path().join("libexec")).unwrap();
        std::os::unix::fs::symlink(&helper, root.path().join("libexec/ay")).unwrap();
        assert!(locate(root.path()).unwrap_err().contains("regular executable"));
        std::fs::remove_file(root.path().join("libexec/ay")).unwrap();
        std::fs::remove_dir(root.path().join("libexec")).unwrap();
        std::os::unix::fs::symlink(outside.path(), root.path().join("libexec")).unwrap();
        assert!(locate(root.path()).unwrap_err().contains("real directory"));
    }

    #[test]
    fn bundled_dirty_unstamped_and_off_pin_helpers_cannot_use_the_unpinned_escape() {
        let pin = "a".repeat(40);
        for version in [
            format!("ay 0.1.0+build.1.{}", "b".repeat(40)),
            format!("ay 0.1.0+build.1.{pin}-dirty"),
            "ay 0.1.0".into(),
        ] {
            let ay = ExternalAy::new(
                PathBuf::from("libexec/ay"),
                AySource::Bundled,
                Some(version),
                Ok(pin.clone()),
            );
            assert_ne!(ay.status, PinStatus::Matched);
            assert_eq!(ay.decision(true), Decision::Refuse);
        }
        let ay = ExternalAy::new(
            PathBuf::from("libexec/ay"),
            AySource::Bundled,
            Some(format!("ay 0.1.0+build.1.{pin}")),
            Ok(pin),
        );
        assert_eq!(ay.decision(false), Decision::Use);
    }
}
