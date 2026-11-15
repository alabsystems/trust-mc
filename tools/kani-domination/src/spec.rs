// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! The generated Kani functional spec (`spec/kani/<rev>/units.jsonl`, written
//! by `tools/kani-spec`), read for ONE fact per unit: whether the spec
//! classifies it `fixme` — a unit upstream Kani's compiletest never runs.
//!
//! The spec is a second, independent source for the runner's own
//! path rule ([`crate::discover::compiletest_ignores`]): a unit is tagged
//! `upstream_ignored` when EITHER says so, never only when both do. Loading is
//! fail-closed on the file's shape (a `units.jsonl` that exists but does not
//! parse refuses to load) and open on its absence (no spec for the corpus rev
//! means the path rule alone decides, and the caller says so).

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};

/// The `fixme` units of one spec revision, keyed `<suite>/<suite-relative path>`
/// — the spec's own `id` field, which for a cargo unit already names the
/// expected file, so it matches `TestResult::file` exactly.
#[derive(Debug, Clone)]
pub struct SpecIndex {
    /// The Kani rev the spec was generated from (its directory name).
    pub kani_rev: String,
    /// The `units.jsonl` that was read.
    pub path: PathBuf,
    /// Every unit row the file holds.
    pub units: usize,
    fixme: BTreeSet<String>,
}

/// `<repo>/spec/kani/<rev>/units.jsonl`.
pub fn units_path(repo_root: &Path, kani_rev: &str) -> PathBuf {
    repo_root.join("spec").join("kani").join(kani_rev).join("units.jsonl")
}

impl SpecIndex {
    /// Load the spec for `kani_rev` from `repo_root`. `Ok(None)` when no spec
    /// exists for that rev; `Err` when one exists but is not the file this
    /// reader understands (a half-read spec would silently under-tag).
    pub fn load(repo_root: &Path, kani_rev: &str) -> Result<Option<Self>> {
        let path = units_path(repo_root, kani_rev);
        if !path.is_file() {
            return Ok(None);
        }
        let text = std::fs::read_to_string(&path)
            .with_context(|| format!("reading spec units {}", path.display()))?;
        Self::parse(&text, kani_rev, path).map(Some)
    }

    /// Parse a `units.jsonl` body. Every line must be a JSON object carrying
    /// `id`, `suite` and `classification`; `ignored` is the compiletest
    /// ignore message (`"fixme test"` / `"ignore test"`) or null.
    pub fn parse(text: &str, kani_rev: &str, path: PathBuf) -> Result<Self> {
        let mut fixme = BTreeSet::new();
        let mut units = 0usize;
        for (n, line) in text.lines().enumerate() {
            if line.trim().is_empty() {
                continue;
            }
            let row: serde_json::Value = serde_json::from_str(line)
                .with_context(|| format!("{}:{}: not a JSON object", path.display(), n + 1))?;
            let id = row.get("id").and_then(|v| v.as_str());
            let class = row.get("classification").and_then(|v| v.as_str());
            let (Some(id), Some(class)) = (id, class) else {
                bail!("{}:{}: a unit row needs string `id` and `classification`", path.display(), n + 1);
            };
            units += 1;
            let ignored = row.get("ignored").is_some_and(|v| !v.is_null());
            if class == "fixme" || ignored {
                fixme.insert(id.to_string());
            }
        }
        if units == 0 {
            bail!("{} holds no unit rows", path.display());
        }
        Ok(SpecIndex { kani_rev: kani_rev.to_string(), path, units, fixme })
    }

    /// Does the spec classify `<suite>/<rel>` as `fixme` (or mark it ignored
    /// upstream)?
    pub fn is_fixme(&self, suite: &str, rel: &str) -> bool {
        self.fixme.contains(&format!("{suite}/{rel}"))
    }

    /// Every `fixme` id, sorted.
    pub fn fixme_ids(&self) -> impl Iterator<Item = &str> {
        self.fixme.iter().map(String::as_str)
    }

    /// How many units the spec classifies `fixme`.
    pub fn fixme_count(&self) -> usize {
        self.fixme.len()
    }
}

/// Load the spec for the corpus at `kani_dir` from the trust-mc repo root, if
/// both can be found. Prints why when it cannot, so a run that tags by the
/// path rule alone says so; refuses (returns the error) when a spec exists
/// but does not parse.
pub fn load_for_corpus(kani_dir: &Path) -> Result<Option<SpecIndex>> {
    load_for_rev(&crate::env::kani_rev_of(kani_dir))
}

/// [`load_for_corpus`] for a rev already known (a results file's sidecar).
pub fn load_for_rev(rev: &str) -> Result<Option<SpecIndex>> {
    let Ok(repo) = crate::env::repo_root_lax() else {
        eprintln!("[kani-domination] no trust-mc repo root found: upstream-ignored units are tagged by compiletest's path rule alone");
        return Ok(None);
    };
    match SpecIndex::load(&repo, rev)? {
        Some(spec) => {
            eprintln!(
                "[kani-domination] spec {} ({} unit(s), {} fixme) read for the upstream-ignored cross-check",
                spec.path.display(),
                spec.units,
                spec.fixme_count()
            );
            Ok(Some(spec))
        }
        None => {
            eprintln!(
                "[kani-domination] no spec at {}: upstream-ignored units are tagged by compiletest's path rule alone",
                units_path(&repo, rev).display()
            );
            Ok(None)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ROWS: &str = r#"{"id":"expected/loop-contract/fixme_box.rs","suite":"expected","classification":"fixme","ignored":"fixme test"}
{"id":"kani/Helpers/vtable_utils_ignore.rs","suite":"kani","classification":"fixme","ignored":"ignore test"}
{"id":"kani/Plain/ok.rs","suite":"kani","classification":"verdict-spec","ignored":null}
{"id":"std-checks/core/mem.expected","suite":"std-checks","classification":"verdict-spec","ignored":null}

{"id":"kani/Odd/marked.rs","suite":"kani","classification":"verdict-spec","ignored":"ignore test"}
"#;

    /// `fixme` is the union of the spec's class and its compiletest ignore
    /// message; a plain unit is not fixme; a cargo unit's id is its expected
    /// file, the same key `TestResult::file` uses.
    #[test]
    fn fixme_is_the_union_of_class_and_ignore_message() {
        let spec = SpecIndex::parse(ROWS, "abc", PathBuf::from("/s/units.jsonl")).unwrap();
        assert_eq!(spec.units, 5);
        assert_eq!(spec.fixme_count(), 3);
        assert!(spec.is_fixme("expected", "loop-contract/fixme_box.rs"));
        assert!(spec.is_fixme("kani", "Helpers/vtable_utils_ignore.rs"));
        assert!(spec.is_fixme("kani", "Odd/marked.rs"), "an ignored unit is fixme whatever its class");
        assert!(!spec.is_fixme("kani", "Plain/ok.rs"));
        assert!(!spec.is_fixme("std-checks", "core/mem.expected"));
        assert_eq!(spec.fixme_ids().count(), 3);
    }

    /// A spec that exists but is not this shape refuses to load, and an
    /// absent spec is `None`, never an empty index that would under-tag.
    #[test]
    fn malformed_spec_refuses_and_absent_spec_is_none() {
        let err = SpecIndex::parse("{\"id\":\"x\"}\n", "r", PathBuf::from("/s/units.jsonl")).unwrap_err();
        assert!(err.to_string().contains("`classification`"), "{err}");
        assert!(SpecIndex::parse("not json\n", "r", PathBuf::from("/s/units.jsonl")).is_err());
        assert!(SpecIndex::parse("\n\n", "r", PathBuf::from("/s/units.jsonl")).is_err());

        let root = std::env::temp_dir().join(format!("kd-spec-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        std::fs::create_dir_all(&root).unwrap();
        assert!(SpecIndex::load(&root, "deadbeef").unwrap().is_none());
        let p = units_path(&root, "deadbeef");
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(&p, ROWS).unwrap();
        let spec = SpecIndex::load(&root, "deadbeef").unwrap().expect("present");
        assert_eq!(spec.kani_rev, "deadbeef");
        assert_eq!(spec.path, p);
        std::fs::write(&p, "garbage\n").unwrap();
        assert!(SpecIndex::load(&root, "deadbeef").is_err(), "a present but unreadable spec is refused");
        let _ = std::fs::remove_dir_all(&root);
    }
}
