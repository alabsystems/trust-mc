// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use anyhow::{Context, Result, bail};

use crate::InvocationType;
/// We assume this is the same as the `trust-mc-verifier` version, but we should
/// make sure it's enforced through CI:
/// <https://github.com/model-checking/kani/issues/2626>
pub(crate) const KANI_VERSION: &str = env!("CARGO_PKG_VERSION");
/// Short git commit hash, set by build.rs (#387).
const GIT_COMMIT: &str = env!("GIT_COMMIT");
/// Full (40-char) git commit hash, set by build.rs. Consumed by the
/// staleness-check shim in `scripts/cargo-trust-mc`. Falls back to `unknown-sha`
/// on tarball/non-git installs.
pub(crate) const TRUST_MC_GIT_SHA: &str = env!("TRUST_MC_GIT_SHA");
/// "1" when the working tree had uncommitted changes at build time, "0"
/// otherwise. Set by build.rs via `git diff-index --quiet HEAD --`.
pub(crate) const TRUST_MC_GIT_DIRTY: &str = env!("TRUST_MC_GIT_DIRTY");
const CARGO_LOCK: &str = include_str!("../../Cargo.lock");
const ROOT_MANIFEST: &str = include_str!("../../Cargo.toml");
const AY_GIT_URL: &str = "https://github.com/alabsystems/ay.git";
const REQUIRED_AY_WORKSPACE_DEPENDENCIES: [(&str, &str); 8] = [
    ("ay-dpll", "ay-dpll"),
    ("ay-core", "ay-core"),
    ("ay-frontend", "ay-frontend"),
    ("ay-chc", "ay-chc"),
    ("ay_bindings", "ay-bindings"),
    ("ay", "ay"),
    ("ay-sys", "ay-sys"),
    ("ay-encode", "ay-encode"),
];

/// AY solver version, fetched from the ay facade crate metadata.
/// Only available when ay-direct feature is enabled.
/// Fixes #638.
#[cfg(feature = "ay-direct")]
const AY_VERSION: &str = ay::VERSION;

/// Print trust-mc version including development version information.
///
/// Output format:
/// ```text
/// trust-mc Rust Verifier <version> (<invocation>)
///   commit: <short-hash>[-dirty]
///   ay: <version> (when ay-direct feature enabled)
/// ```
pub(crate) fn print_kani_version(invocation_type: InvocationType) {
    let is_trust_mc_identity = invocation_type.is_trust_mc_identity();
    let kani_version = kani_version_release(invocation_type);
    println!("{kani_version}");
    if is_trust_mc_identity {
        use std::io::Write as _;

        let dirty_suffix = if TRUST_MC_GIT_DIRTY == "1" { "-dirty" } else { "" };
        let mut stdout = std::io::stdout().lock();
        writeln!(stdout, "  commit: {GIT_COMMIT}{dirty_suffix}")
            .expect("write commit version to stdout");
        writeln!(stdout, "  sha: {TRUST_MC_GIT_SHA}{dirty_suffix}")
            .expect("write sha version to stdout");
        #[cfg(feature = "ay-direct")]
        writeln!(stdout, "  ay: {AY_VERSION}").expect("write ay version to stdout");
    }
}

/// Print a single machine-readable line encoding the embedded git SHA and
/// dirty flag, then exit. Consumed by `scripts/cargo-trust-mc`'s staleness check.
///
/// Output format (one line, KEY=VALUE pairs separated by spaces, terminated
/// by newline):
/// ```text
/// trust_mc-version-sha sha=<full-sha> dirty=<0|1> version=<cargo-pkg-version>
/// ```
///
/// The `trust-mc-version-sha` prefix is a stable marker so the shim can refuse
/// to proceed if an older binary produces unexpected output (defensive
/// parsing: we never silently fall back to "treat as current" on parse
/// failure).
pub(crate) fn print_machine_readable_sha() {
    println!(
        "trust_mc-version-sha sha={TRUST_MC_GIT_SHA} dirty={TRUST_MC_GIT_DIRTY} version={KANI_VERSION}"
    );
}

/// Print public version-authority evidence suitable for logs and reviewers.
///
/// Output format (one line, KEY=VALUE pairs separated by spaces, terminated
/// by newline):
/// ```text
/// trust_mc-version-authority version=<cargo-pkg-version> invocation=<standalone|cargo-plugin> trust_mc_sha=<full-sha> trust_mc_dirty=<0|1> ay_version=<version> ay_pin=<full-sha> ay_linked_sha=<full-sha> ay_linked_dirty=0 ay_authority=matched
/// ```
pub(crate) fn print_version_authority(invocation_type: InvocationType) -> Result<()> {
    use std::io::Write as _;

    let invocation = match invocation_type {
        InvocationType::CargoKani { .. } => "cargo-plugin",
        InvocationType::Standalone { .. } => "standalone",
    };
    let ay_version = ay_package_version().context("Cargo.lock has no AY package version")?;
    let ay_pin = ay_pinned_commit()?;
    let linked_revision = linked_ay_build_revision();
    let linked = validate_linked_ay_revision(&ay_pin, linked_revision)?;
    let mut stdout = std::io::stdout().lock();
    writeln!(
        stdout,
        "trust_mc-version-authority version={KANI_VERSION} invocation={invocation} \
         trust_mc_sha={TRUST_MC_GIT_SHA} trust_mc_dirty={TRUST_MC_GIT_DIRTY} \
         ay_version={ay_version} ay_pin={ay_pin} ay_linked_sha={} \
         ay_linked_dirty=0 ay_authority=matched",
        linked.sha
    )
    .context("write version authority to stdout")?;
    Ok(())
}

/// Print trust-mc release version as `trust-mc Rust Verifier <version> (<invocation>)`
/// where:
///  - `<version>` is the `trust-mc-verifier` version
///  - `<invocation>` is `cargo plugin` if trust-mc was invoked with `cargo trust-mc` or
///    `standalone` if it was invoked with `trust-mc`.
fn kani_version_release(invocation_type: InvocationType) -> String {
    let invocation_str = match invocation_type {
        InvocationType::CargoKani { .. } => "cargo plugin",
        InvocationType::Standalone { .. } => "standalone",
    };
    format!("{} {KANI_VERSION} ({invocation_str})", invocation_type.identity().verifier_name())
}

fn ay_package_version() -> Option<&'static str> {
    parse_ay_package_field(CARGO_LOCK, "version").filter(|version| !version.is_empty())
}

fn ay_pinned_commit() -> Result<String> {
    parse_uniform_ay_manifest_pin(ROOT_MANIFEST)
}

fn linked_ay_build_revision() -> &'static str {
    ay::symbolic_execution_capability_route_readiness(ay::SolverCapabilityCode::ModelBlocking)
        .current_ay_revision
}

fn parse_ay_package_field<'a>(lock: &'a str, field: &str) -> Option<&'a str> {
    let mut in_ay_package = false;
    for line in lock.lines() {
        let trimmed = line.trim();
        if trimmed == "[[package]]" {
            in_ay_package = false;
            continue;
        }
        if trimmed == "name = \"ay\"" {
            in_ay_package = true;
            continue;
        }
        if in_ay_package && let Some(value) = trimmed.strip_prefix(&format!("{field} = \"")) {
            return value.strip_suffix('"');
        }
    }
    None
}

fn parse_uniform_ay_manifest_pin(manifest: &str) -> Result<String> {
    let document = manifest
        .parse::<toml::Value>()
        .context("parse root Cargo.toml for AY version authority")?;
    let dependencies = document
        .get("workspace")
        .and_then(|workspace| workspace.get("dependencies"))
        .and_then(toml::Value::as_table)
        .context("root Cargo.toml has no [workspace.dependencies] table")?;

    for (name, specification) in dependencies {
        if REQUIRED_AY_WORKSPACE_DEPENDENCIES.iter().any(|(required, _)| name == required) {
            continue;
        }
        let Some(table) = specification.as_table() else {
            if is_ay_package_name(name) {
                bail!("unexpected non-table AY workspace dependency `{name}`");
            }
            continue;
        };
        let package = table.get("package").and_then(toml::Value::as_str);
        let git = table.get("git").and_then(toml::Value::as_str);
        if git == Some(AY_GIT_URL)
            || is_ay_package_name(name)
            || package.is_some_and(is_ay_package_name)
        {
            bail!("unexpected AY workspace dependency `{name}`");
        }
    }

    let mut uniform_pin: Option<String> = None;
    for (name, package_name) in REQUIRED_AY_WORKSPACE_DEPENDENCIES {
        let specification = dependencies
            .get(name)
            .with_context(|| format!("missing required AY workspace dependency `{name}`"))?;
        let table = specification
            .as_table()
            .with_context(|| format!("AY dependency `{name}` must use an inline table"))?;
        let git = table.get("git").and_then(toml::Value::as_str);
        if git != Some(AY_GIT_URL) {
            bail!("AY dependency `{name}` must use canonical git URL `{AY_GIT_URL}`");
        }
        if table.contains_key("branch") || table.contains_key("tag") || table.contains_key("path") {
            bail!("AY dependency `{name}` must use only an exact `rev` selector");
        }
        let declared_package = table.get("package").and_then(toml::Value::as_str);
        if name == package_name {
            if declared_package.is_some_and(|package| package != package_name) {
                bail!("AY dependency `{name}` names an unexpected package");
            }
        } else if declared_package != Some(package_name) {
            bail!("AY dependency `{name}` must name package `{package_name}`");
        }
        let rev = table
            .get("rev")
            .and_then(toml::Value::as_str)
            .with_context(|| format!("AY dependency `{name}` has no exact `rev`"))?;
        validate_full_lowercase_nonzero_sha(rev)
            .with_context(|| format!("invalid AY revision for dependency `{name}`"))?;
        match &uniform_pin {
            Some(expected) if expected != rev => {
                bail!("AY workspace dependencies have divergent revisions")
            }
            Some(_) => {}
            None => uniform_pin = Some(rev.to_string()),
        }
    }
    uniform_pin.context("AY workspace dependency inventory is empty")
}

fn is_ay_package_name(name: &str) -> bool {
    name == "ay" || name.starts_with("ay-") || name.starts_with("ay_")
}

fn validate_full_lowercase_nonzero_sha(value: &str) -> Result<()> {
    if value.len() != 40
        || !value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        || value.bytes().all(|byte| byte == b'0')
    {
        bail!("expected a nonzero 40-character lowercase hexadecimal commit")
    }
    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct LinkedAyRevision<'a> {
    sha: &'a str,
    dirty: bool,
}

fn parse_linked_ay_revision(value: &str) -> Result<LinkedAyRevision<'_>> {
    let (sha, dirty) = value.strip_suffix("-dirty").map_or((value, false), |sha| (sha, true));
    validate_full_lowercase_nonzero_sha(sha).context("invalid linked AY build revision")?;
    Ok(LinkedAyRevision { sha, dirty })
}

fn validate_linked_ay_revision<'a>(
    declared_pin: &str,
    linked_revision: &'a str,
) -> Result<LinkedAyRevision<'a>> {
    validate_full_lowercase_nonzero_sha(declared_pin).context("invalid declared AY pin")?;
    let linked = parse_linked_ay_revision(linked_revision)?;
    if linked.dirty {
        bail!("linked AY build is dirty; version authority is unavailable");
    }
    if linked.sha != declared_pin {
        bail!("linked AY build revision {} does not match declared pin {declared_pin}", linked.sha);
    }
    Ok(linked)
}

#[cfg(test)]
mod tests {
    use super::*;

    const PIN: &str = "fa63e3afed08f364ad6437b20dfb5b72fd44803a";
    const OTHER_PIN: &str = "ba63e3afed08f364ad6437b20dfb5b72fd44803a";
    const COMPLETE_MANIFEST: &str = r#"
[workspace.dependencies]
ay-dpll = { rev = "fa63e3afed08f364ad6437b20dfb5b72fd44803a", git = "https://github.com/alabsystems/ay.git" }
ay-core = { git = "https://github.com/alabsystems/ay.git", rev = "fa63e3afed08f364ad6437b20dfb5b72fd44803a" }
ay-frontend = { git = "https://github.com/alabsystems/ay.git", rev = "fa63e3afed08f364ad6437b20dfb5b72fd44803a" }
ay-chc = { git = "https://github.com/alabsystems/ay.git", rev = "fa63e3afed08f364ad6437b20dfb5b72fd44803a" }
ay_bindings = { rev = "fa63e3afed08f364ad6437b20dfb5b72fd44803a", package = "ay-bindings", git = "https://github.com/alabsystems/ay.git" }
ay = { git = "https://github.com/alabsystems/ay.git", rev = "fa63e3afed08f364ad6437b20dfb5b72fd44803a", default-features = false }
ay-sys = { git = "https://github.com/alabsystems/ay.git", rev = "fa63e3afed08f364ad6437b20dfb5b72fd44803a" }
ay-encode = { git = "https://github.com/alabsystems/ay.git", rev = "fa63e3afed08f364ad6437b20dfb5b72fd44803a" }

[patch."https://github.com/alabsystems/ay.git"]
ay = { path = "../ay/crates/ay" }
"#;

    #[test]
    fn repository_manifest_has_a_uniform_commit_pin_for_ay() {
        let declared =
            ay_pinned_commit().expect("repository AY dependency inventory must be valid");
        validate_linked_ay_revision(&declared, linked_ay_build_revision())
            .expect("linked AY build must exactly match the repository pin");
    }

    #[test]
    fn parses_ay_version_from_path_patched_lockfile() {
        let lock = r#"
[[package]]
name = "other"
version = "1.0.0"

[[package]]
name = "ay"
version = "0.10.0"
"#;

        assert_eq!(parse_ay_package_field(lock, "version"), Some("0.10.0"));
    }

    #[test]
    fn parses_complete_ay_inventory_independent_of_inline_field_order() {
        assert_eq!(parse_uniform_ay_manifest_pin(COMPLETE_MANIFEST).unwrap(), PIN);
    }

    #[test]
    fn rejects_missing_extra_or_divergent_ay_dependencies() {
        let missing = COMPLETE_MANIFEST.replace("ay-sys =", "not-ay-sys =");
        let extra = COMPLETE_MANIFEST.replace(
            "[patch.",
            "ay-extra = { git = \"https://github.com/alabsystems/ay.git\", rev = \"fa63e3afed08f364ad6437b20dfb5b72fd44803a\" }\n\n[patch.",
        );
        let extra_non_table = COMPLETE_MANIFEST.replace("[patch.", "ay-extra = \"0.1\"\n\n[patch.");
        let divergent = COMPLETE_MANIFEST.replacen(PIN, OTHER_PIN, 1);

        assert!(parse_uniform_ay_manifest_pin(&missing).is_err());
        assert!(parse_uniform_ay_manifest_pin(&extra).is_err());
        assert!(parse_uniform_ay_manifest_pin(&extra_non_table).is_err());
        assert!(parse_uniform_ay_manifest_pin(&divergent).is_err());
    }

    #[test]
    fn rejects_mixed_path_authority_for_required_ay_dependency() {
        let mixed = COMPLETE_MANIFEST
            .replace("ay-dpll = {", "ay-dpll = { path = \"../ay/crates/ay-dpll\",");
        assert!(parse_uniform_ay_manifest_pin(&mixed).is_err());
    }

    #[test]
    fn rejects_noncanonical_ay_revisions() {
        for invalid in [
            "0000000000000000000000000000000000000000",
            "FA63E3AFED08F364AD6437B20DFB5B72FD44803A",
            "main",
        ] {
            let manifest = COMPLETE_MANIFEST.replace(PIN, invalid);
            assert!(parse_uniform_ay_manifest_pin(&manifest).is_err(), "accepted {invalid}");
        }
    }

    #[test]
    fn linked_ay_revision_must_be_exact_clean_and_matched() {
        assert_eq!(
            validate_linked_ay_revision(PIN, PIN).unwrap(),
            LinkedAyRevision { sha: PIN, dirty: false }
        );
        for invalid in ["unknown", "main", "FA63E3AFED08F364AD6437B20DFB5B72FD44803A"] {
            assert!(validate_linked_ay_revision(PIN, invalid).is_err());
        }
        assert!(validate_linked_ay_revision(PIN, &format!("{PIN}-dirty")).is_err());
        assert!(validate_linked_ay_revision(PIN, OTHER_PIN).is_err());
    }
}
