// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use super::ProgressConfig;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProgressAuthority {
    pub(crate) expected_commit: ExpectedAuthority,
    pub(crate) expected_ay_pin: ExpectedAuthority,
    pub(crate) expected_tree_fingerprint: ExpectedAuthority,
    pub(crate) workspace: WorkspaceAuthority,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ExpectedAuthority {
    pub(crate) value: Option<String>,
    pub(crate) source: &'static str,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct WorkspaceAuthority {
    pub(crate) repo_root: PathBuf,
    pub(crate) git_head: Option<String>,
    pub(crate) tree_state: String,
    pub(crate) ay_pin: Option<String>,
    pub(crate) ay_pin_source: String,
    pub(crate) problems: Vec<String>,
}

pub(crate) fn resolve_progress_authority(
    config: &ProgressConfig,
) -> Result<ProgressAuthority, String> {
    let workspace = load_workspace_authority(&config.repo_root);
    let expected_commit = expected_full_hex(
        "expected commit",
        config.expected_commit.as_deref(),
        workspace.git_head.as_deref(),
        "workspace_git_head",
        40,
    )?;
    let expected_ay_pin = expected_full_hex(
        "expected ay pin",
        config.expected_ay_pin.as_deref(),
        workspace.ay_pin.as_deref(),
        "workspace_cargo_toml",
        40,
    )?;
    let expected_tree_fingerprint = expected_full_hex(
        "expected tree fingerprint",
        config.expected_tree_fingerprint.as_deref(),
        None,
        "unavailable",
        64,
    )?;

    Ok(ProgressAuthority { expected_commit, expected_ay_pin, expected_tree_fingerprint, workspace })
}

fn expected_full_hex(
    label: &str,
    explicit: Option<&str>,
    fallback: Option<&str>,
    fallback_source: &'static str,
    len: usize,
) -> Result<ExpectedAuthority, String> {
    if let Some(value) = explicit {
        if !is_hex_len(value, len) {
            return Err(format!("{label} {value:?} is not a {len}-character hex value"));
        }
        return Ok(ExpectedAuthority { value: Some(value.to_string()), source: "cli" });
    }
    Ok(ExpectedAuthority {
        value: fallback.map(str::to_string),
        source: if fallback.is_some() { fallback_source } else { "unavailable" },
    })
}

fn load_workspace_authority(repo_root_hint: &Path) -> WorkspaceAuthority {
    let mut problems = Vec::new();
    let repo_root = match git_output(repo_root_hint, ["rev-parse", "--show-toplevel"]) {
        Ok(root) => PathBuf::from(root),
        Err(err) => {
            problems.push(format!("git repo root unavailable: {err}"));
            repo_root_hint.to_path_buf()
        }
    };

    let git_head = match git_output(&repo_root, ["rev-parse", "HEAD"]) {
        Ok(head) if is_hex_len(&head, 40) => Some(head),
        Ok(head) => {
            problems.push(format!("git HEAD {head:?} is not a 40-character hex commit"));
            None
        }
        Err(err) => {
            problems.push(format!("git HEAD unavailable: {err}"));
            None
        }
    };

    let tree_state = match git_output(&repo_root, ["status", "--porcelain", "--untracked-files=no"])
    {
        Ok(status) if status.is_empty() => "clean".to_string(),
        Ok(_) => "dirty".to_string(),
        Err(err) => {
            problems.push(format!("git tree state unavailable: {err}"));
            "unavailable".to_string()
        }
    };

    let (ay_pin, ay_pin_source) = match pinned_ay_rev_from_cargo_toml(&repo_root) {
        Ok(pin) => (Some(pin), "Cargo.toml".to_string()),
        Err(err) => {
            problems.push(err.clone());
            (None, format!("unavailable:{err}"))
        }
    };

    WorkspaceAuthority { repo_root, git_head, tree_state, ay_pin, ay_pin_source, problems }
}

fn git_output<const N: usize>(repo_root: &Path, args: [&str; N]) -> Result<String, String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(repo_root)
        .args(args)
        .output()
        .map_err(|err| err.to_string())?;
    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
    } else {
        let stderr = String::from_utf8_lossy(&output.stderr).trim().to_string();
        Err(if stderr.is_empty() { output.status.to_string() } else { stderr })
    }
}

fn pinned_ay_rev_from_cargo_toml(repo_root: &Path) -> Result<String, String> {
    let path = repo_root.join("Cargo.toml");
    let text = fs::read_to_string(&path)
        .map_err(|err| format!("failed to read {}: {err}", path.display()))?;
    let mut pins = BTreeSet::new();
    for line in text.lines().filter(|line| line.contains("alabsystems/ay.git")) {
        if let Some(pin) = rev_from_dependency_line(line)
            && is_hex_len(&pin, 40)
        {
            pins.insert(pin);
        }
    }
    match pins.len() {
        1 => Ok(pins.into_iter().next().expect("one ay pin")),
        0 => Err(format!("{} has no 40-character AY git rev pins", path.display())),
        _ => Err(format!("{} has multiple AY git rev pins: {}", path.display(), pins_label(&pins))),
    }
}

fn rev_from_dependency_line(line: &str) -> Option<String> {
    let start = line.find("rev")?;
    let after_rev = &line[start..];
    let quote_start = after_rev.find('"')?;
    let after_quote = &after_rev[quote_start + 1..];
    let quote_end = after_quote.find('"')?;
    Some(after_quote[..quote_end].to_string())
}

fn pins_label(pins: &BTreeSet<String>) -> String {
    pins.iter().cloned().collect::<Vec<_>>().join(",")
}

fn is_hex_len(value: &str, len: usize) -> bool {
    value.len() == len && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}
