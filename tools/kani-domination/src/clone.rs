// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Download Kani's upstream source at a pinned revision into the cache dir.

use anyhow::{Context, Result, bail};
use std::path::Path;
use std::process::Command;

/// The default pinned Kani revision the corpus is measured against. Bump this
/// (and re-run) to track a newer Kani; record the rev in the burndown ledger.
pub const DEFAULT_KANI_REV: &str = "4c0fce8c300e1f049f2b0c6766a5111dfc9ff32e";

pub fn clone_kani(dir: &Path, rev: &str, url: &str, force: bool) -> Result<String> {
    if dir.exists() {
        if force {
            std::fs::remove_dir_all(dir).context("removing existing Kani checkout")?;
        } else {
            let cur = head_rev(dir);
            eprintln!("[kani-domination] Kani already present at {} (rev {cur})", dir.display());
            return Ok(cur);
        }
    }
    std::fs::create_dir_all(dir).context("creating Kani cache dir")?;
    eprintln!("[kani-domination] cloning {url} @ {rev} -> {}", dir.display());

    git(dir, &["init", "-q"])?;
    git(dir, &["remote", "add", "origin", url])?;

    // Try to fetch the exact pinned rev (GitHub allows SHA fetch); fall back to
    // a shallow default-branch fetch if the server refuses a by-SHA want.
    let pinned = git(dir, &["fetch", "--depth", "1", "origin", rev]).is_ok();
    if pinned {
        git(dir, &["checkout", "-q", "FETCH_HEAD"])?;
    } else {
        eprintln!("[kani-domination] by-SHA fetch refused; falling back to shallow HEAD");
        git(dir, &["fetch", "--depth", "1", "origin", "HEAD"])
            .context("shallow fetch of origin HEAD")?;
        git(dir, &["checkout", "-q", "FETCH_HEAD"])?;
    }

    let got = head_rev(dir);
    if pinned && !got.starts_with(&rev[..rev.len().min(12)]) {
        bail!("checked-out rev {got} does not match requested {rev}");
    }
    eprintln!("[kani-domination] Kani at rev {got}");
    Ok(got)
}

fn head_rev(dir: &Path) -> String {
    Command::new("git")
        .args(["rev-parse", "HEAD"])
        .current_dir(dir)
        .output()
        .ok()
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "<unknown>".into())
}

fn git(dir: &Path, args: &[&str]) -> Result<()> {
    let status = Command::new("git")
        .args(args)
        .current_dir(dir)
        .status()
        .with_context(|| format!("running git {args:?}"))?;
    if !status.success() {
        bail!("git {:?} failed", args);
    }
    Ok(())
}
