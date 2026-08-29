// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::path::{Path, PathBuf};
use std::process::Command;

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
/// Workspace root, i.e. the directory `[patch]` paths are resolved against.
/// `CARGO_MANIFEST_DIR` is `<root>/trust-mc-driver`, so its parent is the root.
const WORKSPACE_ROOT: &str = env!("CARGO_MANIFEST_DIR");

/// AY solver version, fetched from the ay facade crate metadata.
/// Only available when ay-direct feature is enabled.
/// Fixes #638.
#[cfg(feature = "ay-direct")]
const AY_VERSION: &str = ay::VERSION;

/// Print trust-mc version including development version information.
///
/// Output format:
/// ```text
/// trust_mc Rust Verifier <version> (<invocation>)
/// ```
///
/// With `verbose`, the build's provenance follows:
///
/// ```text
///   commit: <short-hash>[-dirty]
///   sha: <full-hash>[-dirty]
///   ay: <version> (when ay-direct feature enabled)
/// ```
pub(crate) fn print_kani_version(invocation_type: InvocationType, verbose: bool) {
    let is_trust_mc_identity = invocation_type.is_trust_mc_identity();
    let kani_version = kani_version_release(invocation_type);
    println!("{kani_version}");
    // Build provenance is three lines of preamble in front of every single
    // run, and two of them say the same thing -- `commit:` is a prefix of
    // `sha:`. Neither is the channel anything actually reads: the staleness
    // check uses `print_machine_readable_sha`, and a proof's provenance is
    // `--version-authority`, which is digest-backed. Keep it for `--verbose`,
    // where the user asked to see the machinery.
    if is_trust_mc_identity && verbose {
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
/// trust_mc-version-authority version=<cargo-pkg-version> invocation=<standalone|cargo-plugin> trust_mc_sha=<full-sha> trust_mc_dirty=<0|1> ay_version=<version> ay_pin=<full-sha> ay_linked_sha=<full-sha> ay_linked_dirty=0 ay_authority=<matched|contains-pin>
/// ```
///
/// `ay_authority` names the lane the guarantee was established in — see
/// [`AyResolution`]. It is never printed unless the corresponding check passed.
pub(crate) fn print_version_authority(invocation_type: InvocationType) -> Result<()> {
    use std::io::Write as _;

    let invocation = match invocation_type {
        InvocationType::CargoKani { .. } => "cargo-plugin",
        InvocationType::Standalone { .. } => "standalone",
    };
    let ay_version = ay_package_version().context("Cargo.lock has no AY package version")?;
    let authority = resolve_ay_authority()?;
    let ay_pin = &authority.pin;
    let ay_authority = authority.resolution.label();
    let mut stdout = std::io::stdout().lock();
    writeln!(
        stdout,
        "trust_mc-version-authority version={KANI_VERSION} invocation={invocation} \
         trust_mc_sha={TRUST_MC_GIT_SHA} trust_mc_dirty={TRUST_MC_GIT_DIRTY} \
         ay_version={ay_version} ay_pin={ay_pin} ay_linked_sha={} \
         ay_linked_dirty=0 ay_authority={ay_authority}",
        authority.linked.sha
    )
    .context("write version authority to stdout")?;
    Ok(())
}

/// Print trust-mc release version as `trust_mc Rust Verifier <version> (<invocation>)`
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
    // toml 0.9's `FromStr for Value` parses a bare *value*, not a document, so
    // `.parse::<toml::Value>()` rejects every manifest ("expected nothing").
    // Use the document deserializer.
    let document = toml::from_str::<toml::Value>(manifest)
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

/// How Cargo actually resolves the AY packages for this build.
///
/// The two lanes support different — but both non-vacuous — guarantees, and the
/// lane is not a matter of taste: it is read out of `Cargo.lock` and the root
/// manifest, so a build cannot select the weaker lane by asserting it.
#[derive(Debug, Clone, PartialEq, Eq)]
enum AyResolution {
    /// `Cargo.lock` names the pinned git revision as AY's source. The linked
    /// build is that exact commit, so the pin is checked by strict equality.
    Pinned,
    /// The root manifest `[patch]`es the canonical AY git source to a sibling
    /// checkout and `Cargo.lock` records AY without a source, i.e. the patch was
    /// accepted. The linked commit is then whatever that checkout's HEAD was at
    /// AY build time, which trust-mc does not own and cannot hold still — a
    /// second agent working in `../ay` moves it. Equality is therefore not an
    /// enforceable property, but *ancestry* is: the linked build must CONTAIN
    /// the declared pin, so this workspace can never link an AY older than, or
    /// off the history of, the revision it claims.
    PathPatched {
        /// AY checkout path as written in `[patch]`, relative to the workspace root.
        path: String,
    },
}

impl AyResolution {
    fn label(&self) -> &'static str {
        match self {
            AyResolution::Pinned => "matched",
            AyResolution::PathPatched { .. } => "contains-pin",
        }
    }
}

/// The AY authority this binary was built against, once every lane check passed.
#[derive(Debug, Clone, PartialEq, Eq)]
struct AyAuthority {
    resolution: AyResolution,
    pin: String,
    linked: LinkedAyRevision<'static>,
}

/// Establish the AY authority, or fail with the reason.
///
/// Fails closed on: a malformed/non-uniform manifest pin, a dirty or malformed
/// linked revision, a patch Cargo silently declined, a path-resolved AY with no
/// patch behind it, a lock source that names a different revision, a missing or
/// non-canonical patch entry, and (path lane) a linked AY that does not contain
/// the declared pin or cannot be examined at all.
fn resolve_ay_authority() -> Result<AyAuthority> {
    let pin = ay_pinned_commit()?;
    let resolution = parse_ay_resolution(CARGO_LOCK, ROOT_MANIFEST, &pin)?;
    let linked = validate_linked_ay_revision(&resolution, &pin, linked_ay_build_revision())?;
    Ok(AyAuthority { resolution, pin, linked })
}

fn validate_linked_ay_revision<'a>(
    resolution: &AyResolution,
    declared_pin: &str,
    linked_revision: &'a str,
) -> Result<LinkedAyRevision<'a>> {
    validate_full_lowercase_nonzero_sha(declared_pin).context("invalid declared AY pin")?;
    let linked = parse_linked_ay_revision(linked_revision)?;
    if linked.dirty {
        bail!("linked AY build is dirty; version authority is unavailable");
    }
    match resolution {
        AyResolution::Pinned => {
            if linked.sha != declared_pin {
                bail!(
                    "linked AY build revision {} does not match declared pin {declared_pin}",
                    linked.sha
                );
            }
        }
        AyResolution::PathPatched { path } => {
            require_linked_contains_pin(&ay_checkout_directory(path), declared_pin, linked.sha)?;
        }
    }
    Ok(linked)
}

/// Resolve a `[patch]` path against the workspace root.
fn ay_checkout_directory(patch_path: &str) -> PathBuf {
    Path::new(WORKSPACE_ROOT).parent().unwrap_or_else(|| Path::new(WORKSPACE_ROOT)).join(patch_path)
}

/// Assert that the AY commit actually linked into this binary contains the
/// declared pin. Anything that prevents establishing that — no git, no
/// checkout, an unknown commit on either side, or a genuine non-ancestor — is a
/// failure. `git merge-base --is-ancestor` exits 0 only for a true ancestor;
/// 1 means "not an ancestor" and 128 means a revision could not be resolved.
fn require_linked_contains_pin(
    checkout: &Path,
    declared_pin: &str,
    linked_sha: &str,
) -> Result<()> {
    let checkout_display = checkout.display();
    let output = Command::new("git")
        .arg("-C")
        .arg(checkout)
        .args(["merge-base", "--is-ancestor", declared_pin, linked_sha])
        .output()
        .with_context(|| {
            format!("run `git merge-base --is-ancestor` in AY checkout {checkout_display}")
        })?;
    match output.status.code() {
        Some(0) => Ok(()),
        Some(1) => bail!(
            "linked AY build revision {linked_sha} does not contain declared pin {declared_pin} \
             (AY checkout {checkout_display}); the workspace is linking an AY older than, or off \
             the history of, the revision its manifest claims"
        ),
        _ => bail!(
            "cannot establish that linked AY build revision {linked_sha} contains declared pin \
             {declared_pin} in AY checkout {checkout_display}: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ),
    }
}

/// Read the resolution lane out of `Cargo.lock` plus the root manifest.
///
/// This is where the hazard recorded in
/// `docs/findings/2026-08-19-the-ay-patch-was-silently-version-rejected.md` is
/// caught: a `[patch]` whose replacement does not satisfy the dependency's
/// version requirement is DECLINED by Cargo with a warning and exit 0, and the
/// build silently resolves the git pin instead. That state is exactly
/// "manifest patches AY, lock still has a git source", and it is rejected here.
fn parse_ay_resolution(lock: &str, manifest: &str, declared_pin: &str) -> Result<AyResolution> {
    let patched_path = parse_ay_patch_path(manifest)?;
    let lock_source = parse_ay_package_field(lock, "source");
    match (lock_source, patched_path) {
        (None, Some(path)) => Ok(AyResolution::PathPatched { path }),
        (Some(source), None) => {
            let expected = format!("git+{AY_GIT_URL}?rev={declared_pin}#{declared_pin}");
            if source != expected {
                bail!("Cargo.lock resolves AY from `{source}`, not the declared `{expected}`");
            }
            Ok(AyResolution::Pinned)
        }
        (Some(source), Some(_)) => bail!(
            "the root manifest patches AY to a path but Cargo.lock still resolves it from \
             `{source}`: Cargo declined the patch (a `[patch]` must also satisfy the version \
             requirement) — see \
             docs/findings/2026-08-19-the-ay-patch-was-silently-version-rejected.md"
        ),
        (None, None) => bail!(
            "Cargo.lock records AY without a source but the root manifest declares no \
             `[patch.\"{AY_GIT_URL}\"]`; the linked AY has no declared authority"
        ),
    }
}

/// Return the `ay` checkout path if — and only if — the root manifest carries a
/// complete, canonical AY patch table. `None` means no AY patch at all.
fn parse_ay_patch_path(manifest: &str) -> Result<Option<String>> {
    let document = toml::from_str::<toml::Value>(manifest)
        .context("parse root Cargo.toml for AY patch authority")?;
    let Some(patch) = document.get("patch").and_then(toml::Value::as_table) else {
        return Ok(None);
    };
    // A `[patch]` key that is not byte-identical to the `git =` URL silently
    // stops applying. Refuse to treat a near-miss key as "no patch".
    for key in patch.keys() {
        if key != AY_GIT_URL && key.contains("alabsystems/ay") {
            bail!(
                "AY patch key `{key}` is not byte-identical to the declared git URL \
                 `{AY_GIT_URL}`; Cargo would silently ignore it"
            );
        }
    }
    let Some(entries) = patch.get(AY_GIT_URL) else {
        return Ok(None);
    };
    let entries = entries
        .as_table()
        .with_context(|| format!("`[patch.\"{AY_GIT_URL}\"]` must be a table"))?;
    for (_, package_name) in REQUIRED_AY_WORKSPACE_DEPENDENCIES {
        let entry = entries
            .get(package_name)
            .with_context(|| format!("AY patch table does not replace `{package_name}`"))?;
        let table = entry
            .as_table()
            .with_context(|| format!("AY patch entry `{package_name}` must be an inline table"))?;
        if table.contains_key("git") || table.contains_key("rev") || table.contains_key("branch") {
            bail!("AY patch entry `{package_name}` must replace the source by `path` only");
        }
        if !table.get("path").is_some_and(|path| path.as_str().is_some_and(|p| !p.is_empty())) {
            bail!("AY patch entry `{package_name}` has no `path`");
        }
    }
    let path = entries["ay"]["path"].as_str().expect("checked above").to_string();
    Ok(Some(path))
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
        let authority =
            resolve_ay_authority().expect("repository AY authority must be establishable");
        assert_eq!(
            authority.pin,
            ay_pinned_commit().expect("repository AY dependency inventory must be valid")
        );
        assert!(!authority.linked.dirty);
        // Whichever lane this checkout resolves through, the guarantee that was
        // actually established is the one reported.
        match &authority.resolution {
            AyResolution::Pinned => assert_eq!(authority.linked.sha, authority.pin),
            AyResolution::PathPatched { path } => assert!(path.contains("ay")),
        }
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
    fn linked_ay_revision_must_be_exact_clean_and_matched_in_the_pinned_lane() {
        let pinned = AyResolution::Pinned;
        assert_eq!(
            validate_linked_ay_revision(&pinned, PIN, PIN).unwrap(),
            LinkedAyRevision { sha: PIN, dirty: false }
        );
        for invalid in ["unknown", "main", "FA63E3AFED08F364AD6437B20DFB5B72FD44803A"] {
            assert!(validate_linked_ay_revision(&pinned, PIN, invalid).is_err());
        }
        assert!(validate_linked_ay_revision(&pinned, PIN, &format!("{PIN}-dirty")).is_err());
        assert!(validate_linked_ay_revision(&pinned, PIN, OTHER_PIN).is_err());
    }

    const LOCK_PATH_RESOLVED: &str = r#"
[[package]]
name = "ay"
version = "0.13.0"
"#;

    fn lock_git_resolved(rev: &str) -> String {
        format!(
            "\n[[package]]\nname = \"ay\"\nversion = \"0.13.0\"\nsource = \
             \"git+https://github.com/alabsystems/ay.git?rev={rev}#{rev}\"\n"
        )
    }

    const PATCH_TABLE: &str = r#"
[patch."https://github.com/alabsystems/ay.git"]
ay = { path = "../ay/crates/ay" }
ay-core = { path = "../ay/crates/ay-core" }
ay-dpll = { path = "../ay/crates/ay-dpll" }
ay-frontend = { path = "../ay/crates/ay-frontend" }
ay-chc = { path = "../ay/crates/ay-chc" }
ay-bindings = { path = "../ay/crates/ay-bindings" }
ay-sys = { path = "../ay/crates/ay-sys" }
ay-encode = { path = "../ay/crates/ay-encode" }
"#;

    fn manifest_with_patch() -> String {
        format!("{COMPLETE_MANIFEST_NO_PATCH}{PATCH_TABLE}")
    }

    /// `COMPLETE_MANIFEST` minus its (deliberately partial) patch table.
    const COMPLETE_MANIFEST_NO_PATCH: &str = r#"
[workspace.dependencies]
ay-dpll = { rev = "fa63e3afed08f364ad6437b20dfb5b72fd44803a", git = "https://github.com/alabsystems/ay.git" }
ay-core = { git = "https://github.com/alabsystems/ay.git", rev = "fa63e3afed08f364ad6437b20dfb5b72fd44803a" }
ay-frontend = { git = "https://github.com/alabsystems/ay.git", rev = "fa63e3afed08f364ad6437b20dfb5b72fd44803a" }
ay-chc = { git = "https://github.com/alabsystems/ay.git", rev = "fa63e3afed08f364ad6437b20dfb5b72fd44803a" }
ay_bindings = { rev = "fa63e3afed08f364ad6437b20dfb5b72fd44803a", package = "ay-bindings", git = "https://github.com/alabsystems/ay.git" }
ay = { git = "https://github.com/alabsystems/ay.git", rev = "fa63e3afed08f364ad6437b20dfb5b72fd44803a", default-features = false }
ay-sys = { git = "https://github.com/alabsystems/ay.git", rev = "fa63e3afed08f364ad6437b20dfb5b72fd44803a" }
ay-encode = { git = "https://github.com/alabsystems/ay.git", rev = "fa63e3afed08f364ad6437b20dfb5b72fd44803a" }
"#;

    #[test]
    fn accepted_patch_and_bare_git_pin_each_name_their_own_lane() {
        assert_eq!(
            parse_ay_resolution(LOCK_PATH_RESOLVED, &manifest_with_patch(), PIN).unwrap(),
            AyResolution::PathPatched { path: "../ay/crates/ay".to_string() }
        );
        assert_eq!(
            parse_ay_resolution(&lock_git_resolved(PIN), COMPLETE_MANIFEST_NO_PATCH, PIN).unwrap(),
            AyResolution::Pinned
        );
        assert_eq!(AyResolution::Pinned.label(), "matched");
        assert_eq!(AyResolution::PathPatched { path: String::new() }.label(), "contains-pin");
    }

    /// The exact failure recorded in
    /// `docs/findings/2026-08-19-the-ay-patch-was-silently-version-rejected.md`:
    /// the manifest patches AY to a path, Cargo declines the patch over a
    /// version mismatch, and the lock keeps the git source. Warning only, exit 0.
    #[test]
    fn rejects_a_patch_that_cargo_silently_declined() {
        let error = parse_ay_resolution(&lock_git_resolved(PIN), &manifest_with_patch(), PIN)
            .expect_err("a declined AY patch must not be accepted as a valid authority");
        assert!(format!("{error}").contains("declined the patch"), "{error}");
    }

    #[test]
    fn rejects_path_resolved_ay_with_no_patch_behind_it() {
        assert!(parse_ay_resolution(LOCK_PATH_RESOLVED, COMPLETE_MANIFEST_NO_PATCH, PIN).is_err());
    }

    #[test]
    fn rejects_a_lock_source_naming_a_revision_other_than_the_pin() {
        assert!(
            parse_ay_resolution(&lock_git_resolved(OTHER_PIN), COMPLETE_MANIFEST_NO_PATCH, PIN)
                .is_err()
        );
    }

    #[test]
    fn rejects_a_patch_key_that_is_not_byte_identical_to_the_git_url() {
        let near_miss = manifest_with_patch().replace(
            "[patch.\"https://github.com/alabsystems/ay.git\"]",
            "[patch.\"https://github.com/alabsystems/ay\"]",
        );
        assert!(parse_ay_patch_path(&near_miss).is_err());
    }

    #[test]
    fn rejects_an_incomplete_or_non_path_ay_patch_table() {
        let missing = manifest_with_patch().replace("ay-encode = { path", "not-ay = { path");
        let git_sourced = manifest_with_patch().replace(
            "ay-chc = { path = \"../ay/crates/ay-chc\" }",
            "ay-chc = { git = \"https://github.com/alabsystems/ay.git\", rev = \"fa63e3afed08f364ad6437b20dfb5b72fd44803a\" }",
        );
        assert!(parse_ay_patch_path(&missing).is_err());
        assert!(parse_ay_patch_path(&git_sourced).is_err());
        assert!(parse_ay_patch_path(COMPLETE_MANIFEST_NO_PATCH).unwrap().is_none());
    }

    /// A guard that cannot fail is not a guard. Build a throwaway history and
    /// prove the ancestry check accepts a descendant, rejects an ancestor-less
    /// sibling, rejects an unknown revision, and rejects a missing checkout.
    #[test]
    fn ancestry_check_accepts_descendants_and_rejects_everything_else() {
        let scratch = tempfile::tempdir().expect("create scratch checkout");
        let repo = scratch.path();
        let git = |args: &[&str]| {
            let output = Command::new("git")
                .arg("-C")
                .arg(repo)
                .args(args)
                .output()
                .expect("run git in scratch checkout");
            assert!(output.status.success(), "git {args:?}: {:?}", output);
            String::from_utf8(output.stdout).expect("git stdout is utf-8").trim().to_string()
        };
        git(&["init", "--quiet", "--initial-branch=main", "."]);
        git(&["config", "user.email", "guard@example.invalid"]);
        git(&["config", "user.name", "guard"]);
        git(&["commit", "--quiet", "--allow-empty", "-m", "pin"]);
        let pin = git(&["rev-parse", "HEAD"]);
        git(&["commit", "--quiet", "--allow-empty", "-m", "descendant"]);
        let descendant = git(&["rev-parse", "HEAD"]);
        git(&["checkout", "--quiet", "--orphan", "elsewhere"]);
        git(&["commit", "--quiet", "--allow-empty", "-m", "unrelated"]);
        let unrelated = git(&["rev-parse", "HEAD"]);

        require_linked_contains_pin(repo, &pin, &descendant)
            .expect("a descendant contains the pin");
        require_linked_contains_pin(repo, &pin, &pin).expect("a commit contains itself");

        // Linking an AY that predates the pin.
        let older = require_linked_contains_pin(repo, &descendant, &pin)
            .expect_err("an ancestor does not contain its descendant");
        assert!(format!("{older}").contains("does not contain declared pin"), "{older}");
        // Linking an AY off the declared history entirely.
        assert!(require_linked_contains_pin(repo, &pin, &unrelated).is_err());
        // A pin that the linked checkout has never heard of.
        assert!(require_linked_contains_pin(repo, OTHER_PIN, &descendant).is_err());
        // No checkout at all is a failure, never a pass.
        assert!(require_linked_contains_pin(&repo.join("absent"), &pin, &descendant).is_err());
    }
}
