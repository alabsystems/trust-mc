// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Entry-file discovery and the Kani **oracle**: for each harness-bearing test
//! file, derive the verdict Kani expects (success / fail) and the flags Kani
//! would forward to the verifier. Directories owned by a `Cargo.toml` become
//! *cargo units* (one per Kani `expected` / `*.expected` file), mirroring
//! Kani's own `cargo-kani` compiletest mode.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

use crate::model::Verdict;
use crate::suites::Suite;

/// How a discovered test must be executed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EntryKind {
    /// A standalone `.rs` file, run via single-file `trust-mc-driver`.
    SingleFile {
        /// `#[kani::proof…]` count in the file (outer-timeout scaling: the
        /// driver budgets `--harness-timeout` *per harness*, so the outer
        /// watchdog must scale with the number of harnesses too).
        harness_count: usize,
    },
    /// One Kani cargo test unit: `cargo trust-mc` in `manifest_dir`, output
    /// checked against the unit's expected file (Kani `run_cargo_kani_test`
    /// semantics: `--harness <stem>` unless the file is named exactly
    /// `expected`).
    CargoPackage {
        manifest_dir: PathBuf,
        /// `--harness` filter (the expected file's stem), if any.
        harness: Option<String>,
        /// `#[kani::proof…]` count across the package (outer-timeout scaling).
        harness_count: usize,
    },
}

/// A discovered test entry, ready to run.
#[derive(Debug, Clone)]
pub struct Discovered {
    pub suite: String,
    /// Suite-relative POSIX path (the `.rs` entry, or the expected file for a
    /// cargo unit).
    pub rel: String,
    pub abs: PathBuf,
    pub oracle: Verdict,
    /// `// kani-flags:` forwarded verbatim to the verifier.
    pub flags: Vec<String>,
    /// `// compile-flags:` exported via `RUSTFLAGS`.
    pub rustflags: Vec<String>,
    /// Execution lane.
    pub kind: EntryKind,
    /// The Kani expected-output file governing this test, if any (resolved
    /// per Kani's compiletest rules — used for output-match parity).
    pub expected_path: Option<PathBuf>,
    /// The test header carries a `// kani-check-fail` directive: the oracle is
    /// a **compile failure** (Kani itself fails to build the file), not a
    /// verification failure. A matching trust-mc compile error is parity.
    pub check_fail: bool,
}

/// Walk one suite directory and return every runnable test: harness-bearing
/// single `.rs` entry files plus cargo units for `Cargo.toml`-owned dirs.
pub fn discover_suite(kani_tests: &Path, suite: &Suite) -> Vec<Discovered> {
    let root = kani_tests.join(suite.name);
    let mut out = Vec::new();
    if !root.is_dir() {
        return out;
    }

    // Pass 1: find every cargo package dir (a dir containing Cargo.toml).
    let mut package_dirs: Vec<PathBuf> = Vec::new();
    for entry in WalkDir::new(&root).into_iter().filter_map(Result::ok) {
        let path = entry.path();
        if path.file_name().and_then(|n| n.to_str()) == Some("Cargo.toml")
            && !in_build_artifact_dir(path, &root)
        {
            package_dirs.push(path.parent().unwrap().to_path_buf());
        }
    }

    // Pass 2: collect single-file entries (proof-bearing .rs NOT owned by a
    // cargo package), remembering per-directory entry counts for the
    // dir-level `expected` fallback.
    struct Entry {
        path: PathBuf,
        flags: Vec<String>,
        rustflags: Vec<String>,
        header_fail: bool,
        check_fail: bool,
        harness_count: usize,
    }
    let mut entries: Vec<Entry> = Vec::new();
    let mut per_dir: HashMap<PathBuf, usize> = HashMap::new();
    for entry in WalkDir::new(&root).into_iter().filter_map(Result::ok) {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("rs") {
            continue;
        }
        if in_build_artifact_dir(path, &root)
            || package_dirs.iter().any(|p| path.starts_with(p))
        {
            continue;
        }
        let Ok(src) = std::fs::read_to_string(path) else { continue };
        if !is_proof_entry(&src) {
            continue;
        }
        let (flags, rustflags) = parse_flags(&src);
        // Paths go relative to the CHECKOUT root (`<kani>`), not the suite
        // root: the child is spawned with the checkout as its cwd, which is
        // why sibling headers spell `tests/kani/ForeignItems/lib.c`.
        let checkout_root = kani_tests.parent().unwrap_or(kani_tests);
        let flags = augment_prose_c_lib(flags, &src, path, checkout_root);
        if let Some(dir) = path.parent() {
            *per_dir.entry(dir.to_path_buf()).or_insert(0) += 1;
        }
        entries.push(Entry {
            path: path.to_path_buf(),
            flags,
            rustflags,
            header_fail: header_expects_fail(&src),
            check_fail: header_expects_check_fail(&src),
            harness_count: src.matches("#[kani::proof").count().max(1),
        });
    }

    for e in entries {
        let siblings = e.path.parent().map(|d| *per_dir.get(d).unwrap_or(&1)).unwrap_or(1);
        let expected = resolve_expected_path(&e.path, siblings == 1);
        let expected_content =
            expected.as_deref().and_then(|p| std::fs::read_to_string(p).ok());
        let expected_verdict = expected_content.as_deref().and_then(expected_file_verdict);
        // Verdict-indeterminate expected file whose content is a compile
        // diagnostic: the oracle is "compilation fails" (check_fail), same
        // machinery as the `kani-check-fail` directive.
        let compile_error_oracle = !e.header_fail
            && expected_verdict.is_none()
            && expected_content.as_deref().is_some_and(expected_is_compile_error);
        let oracle = if e.header_fail || compile_error_oracle {
            Verdict::Fail
        } else {
            expected_verdict.unwrap_or(Verdict::Success)
        };
        out.push(Discovered {
            suite: suite.name.to_string(),
            rel: rel_of(&e.path, &root),
            abs: e.path.clone(),
            oracle,
            flags: e.flags,
            rustflags: e.rustflags,
            kind: EntryKind::SingleFile { harness_count: e.harness_count },
            expected_path: expected,
            check_fail: e.check_fail || compile_error_oracle,
        });
    }

    // Pass 3: one cargo unit per expected file in each package dir (Kani
    // `cargo-kani` mode). A package without any expected file is a single
    // all-harness unit keyed by its Cargo.toml.
    for pkg in &package_dirs {
        let harness_count = count_package_harnesses(pkg);
        let mut expected_files: Vec<PathBuf> = std::fs::read_dir(pkg)
            .into_iter()
            .flatten()
            .filter_map(Result::ok)
            .map(|e| e.path())
            .filter(|p| is_expected_file(p))
            .collect();
        expected_files.sort();
        if expected_files.is_empty() {
            out.push(Discovered {
                suite: suite.name.to_string(),
                rel: rel_of(&pkg.join("Cargo.toml"), &root),
                abs: pkg.join("Cargo.toml"),
                oracle: Verdict::Success,
                flags: Vec::new(),
                rustflags: Vec::new(),
                kind: EntryKind::CargoPackage {
                    manifest_dir: pkg.clone(),
                    harness: None,
                    harness_count,
                },
                expected_path: None,
                check_fail: false,
            });
            continue;
        }
        for exp in expected_files {
            let harness = if exp.file_name().and_then(|n| n.to_str()) == Some("expected") {
                None
            } else {
                exp.file_stem().and_then(|s| s.to_str()).map(str::to_string)
            };
            let oracle = match oracle_from_expected_file(&exp) {
                Ok(v) => v,
                Err(err) => {
                    // FAIL CLOSED. This file EXISTS (enumeration just yielded it),
                    // so an unreadable one is a corpus-integrity failure, not a
                    // "test passes" signal. Defaulting it to Success would be
                    // fail-OPEN in the dangerous direction: `missed_bug` is
                    // (oracle == Fail && observed == Success), so a wrongly
                    // Success oracle can HIDE a missed bug from the hard gate.
                    // Dropping the row keeps it out of the denominator entirely,
                    // which understates coverage but cannot launder a defect.
                    eprintln!(
                        "[kani-domination] CORPUS INTEGRITY: cannot read expected file {} \
                         ({err}) — dropping the row rather than guessing oracle=Success"
                    , exp.display());
                    continue;
                }
            };
            out.push(Discovered {
                suite: suite.name.to_string(),
                rel: rel_of(&exp, &root),
                abs: exp.clone(),
                oracle,
                flags: Vec::new(),
                rustflags: Vec::new(),
                kind: EntryKind::CargoPackage {
                    manifest_dir: pkg.clone(),
                    harness,
                    harness_count,
                },
                expected_path: Some(exp),
                check_fail: false,
            });
        }
    }

    // Manifest-listed oracle corrections (see `quarantine::ORACLE_FIXUPS`):
    // per-test, evidence-quoted fixes for oracles the derivation above gets
    // provably wrong (e.g. a `fixme_` file with a planted constant-false
    // assertion whose absent expected file defaulted the oracle to Success).
    for d in &mut out {
        if let Some(fx) = crate::quarantine::oracle_fixup(&d.suite, &d.rel) {
            d.oracle = fx.oracle;
        }
    }

    out.sort_by(|a, b| a.rel.cmp(&b.rel));
    out
}

fn rel_of(path: &Path, root: &Path) -> String {
    path.strip_prefix(root).unwrap_or(path).to_string_lossy().replace('\\', "/")
}

/// Skip cargo build artifacts that a prior in-tree build may have left behind.
fn in_build_artifact_dir(path: &Path, root: &Path) -> bool {
    path.strip_prefix(root)
        .map(|r| r.components().any(|c| c.as_os_str() == "target"))
        .unwrap_or(false)
}

fn is_expected_file(p: &Path) -> bool {
    p.is_file()
        && (p.file_name().and_then(|n| n.to_str()) == Some("expected")
            || p.extension().and_then(|x| x.to_str()) == Some("expected"))
}

/// Count `#[kani::proof…]` attributes across a package's `.rs` files.
fn count_package_harnesses(pkg: &Path) -> usize {
    let mut n = 0;
    for entry in WalkDir::new(pkg).into_iter().filter_map(Result::ok) {
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("rs") {
            continue;
        }
        if let Ok(src) = std::fs::read_to_string(path) {
            n += src.matches("#[kani::proof").count();
        }
    }
    n
}

/// A file is a verdict-bearing entry if it declares at least one Kani proof
/// harness. `#[kani::proof` matches both `proof` and `proof_for_contract`;
/// the macro-expanded `kani::proof]` form is also accepted.
fn is_proof_entry(src: &str) -> bool {
    src.contains("#[kani::proof") || src.contains("kani::proof]") || src.contains("#[proof]")
}

/// Explicit fail directives in the test header win over any expected file.
///
/// `kani-expect-fail` is not in compiletest's directive set (`kani-check-fail`
/// / `kani-codegen-fail` / `kani-verify-fail`, tools/compiletest/src/header.rs
/// `parse_kani_step_fail_directive`) but appears once in the corpus
/// (`kani/DynTrait/vtable_restrictions_fail_fixme.rs`, which deliberately
/// corrupts a vtable slot and must fail) — the stale spelling was never caught
/// upstream because compiletest skips `fixme` paths. The author's fail intent
/// is unambiguous, so honor it.
fn header_expects_fail(src: &str) -> bool {
    src.lines().take(80).any(|line| {
        let l = line.trim_start_matches(['/', ' ']).trim();
        l.starts_with("kani-verify-fail")
            || l.starts_with("kani-check-fail")
            || l.starts_with("kani-expect-fail")
    })
}

/// `// kani-check-fail`: Kani's compiletest expects *compilation* of this file
/// to fail (as opposed to `kani-verify-fail`, where compilation succeeds and
/// verification finds a bug). Recorded separately so the classifier can accept
/// a matching trust-mc compile error as parity.
fn header_expects_check_fail(src: &str) -> bool {
    src.lines().take(80).any(|line| {
        let l = line.trim_start_matches(['/', ' ']).trim();
        l.starts_with("kani-check-fail")
    })
}

/// Resolve the Kani expected file for a single-file test, mirroring
/// compiletest's `run_expected_test`: `<test>.expected` next to the file
/// wins; the directory-level `expected` file applies only when the test is
/// the directory's sole entry (a shared directory `expected` cannot be
/// attributed to one of several tests). Never concatenates multiple
/// `.expected` files.
fn resolve_expected_path(path: &Path, sole_entry_in_dir: bool) -> Option<PathBuf> {
    let dot = path.with_extension("expected");
    if dot.is_file() {
        return Some(dot);
    }
    if sole_entry_in_dir {
        let dir_expected = path.parent()?.join("expected");
        if dir_expected.is_file() {
            return Some(dir_expected);
        }
    }
    None
}

/// Derive a verdict oracle from one expected file's *content*.
///
/// # Precedence
///
/// The whole-run verdict line is authoritative and is checked FIRST, because a
/// `#[kani::should_panic]` harness inverts the semantics: its expected output
/// lists `Status: FAILURE` / `Failed Checks:` lines for the panics it *expects*
/// yet ends in `VERIFICATION:- SUCCESSFUL (encountered one or more panics as
/// expected)`. Reading the per-check markers first would wrongly flip such a
/// success to a fail (e.g. `ui/should-panic-attribute/…`,
/// `expected/derive-invariant/…_fail_mut`).
///
/// # Failure markers
///
/// When there is no whole-run verdict line, the corpus records an *expected*
/// verification failure through one of Kani's per-check / per-harness markers.
/// The original heuristic only recognised the trust-mc/CBMC-style
/// `VERIFICATION:- FAILED` / `Status: FAILURE` / `Verification failed for …`
/// lines and therefore silently defaulted a large family of genuinely
/// failure-expecting tests (the `expected/reach/*/reachable_fail`,
/// `expected/intrinsics/*`, `expected/panic/*`, `expected/vec`,
/// `expected/unreachable`, `unwind_tip`, `unwind-recursion-fail`, … suites) to
/// `Success`. trust-mc then *correctly* reported the failure, but the run was
/// mislabelled a `false_positive`. We additionally recognise the standalone
/// per-check status tokens Kani prints (`FAILURE` / `UNDETERMINED`), its
/// `Failed Checks:` summary line, and the unwinding-failure banner.
///
/// Free-text mentions such as `assertion failed: …` quoted inside a SUCCESS
/// Description must still NOT flip the oracle, so bare-token matching is exact
/// (a line whose trimmed content *is* the token), not a substring scan.
/// Oracle for one `.expected` file, distinguishing "read it and it names no
/// failure" from "could not read it at all".
///
/// The first is a legitimate corpus convention — an expected file with no failure
/// markers describes a passing run — so it yields `Success`. The second is an I/O
/// failure and is returned as an error so the caller can refuse to score the row;
/// collapsing both into `unwrap_or(Verdict::Success)` is fail-OPEN, and since
/// `missed_bug` is (oracle == Fail && observed == Success) a wrongly-Success
/// oracle can hide a missed bug from the hard gate.
fn oracle_from_expected_file(path: &Path) -> std::io::Result<Verdict> {
    let content = std::fs::read_to_string(path)?;
    Ok(expected_file_verdict(&content).unwrap_or(Verdict::Success))
}

fn expected_file_verdict(content: &str) -> Option<Verdict> {
    // Whole-run verdict lines win over any per-check marker (should_panic).
    if content.contains("VERIFICATION:- FAILED") {
        return Some(Verdict::Fail);
    }
    if content.contains("VERIFICATION:- SUCCESSFUL") || content.contains("VERIFICATION SUCCESSFUL") {
        return Some(Verdict::Success);
    }
    // An unwinding-assertion failure renders every check UNDETERMINED and the
    // whole run FAILED; the corpus records it via this banner rather than a
    // `VERIFICATION:-` line.
    if content.contains("one or more unwinding failures") {
        return Some(Verdict::Fail);
    }
    // Bare Kani/CBMC UB-check descriptions: some `.expected` files carry only a
    // failing check's DESCRIPTION substring, without the `FAILURE` / `Failed
    // Checks:` / `VERIFICATION:-` banner that the markers above key on. These
    // messages appear ONLY on a failed check (a passing run never emits them),
    // so their presence means Kani's own harness fails — the oracle is Fail.
    // `memcpy src/dst overlap` is the `copy_nonoverlapping` range-disjointness
    // UB. AUDITED 2026-07-22 (user-approved): this is the SOLE such test in the
    // verification corpus — every other UB-message `.expected` (offset-*-fail,
    // arith-offset-*, copy-overflow, offset-same-object, simd-shuffle-out,
    // pointer-overflow, dead-invalid-access) already carries a FAILURE/Failed-
    // Checks marker and is already oracle=Fail, so this cannot mask a real FP.
    if content.contains("memcpy src/dst overlap") {
        return Some(Verdict::Fail);
    }
    // Kani's manual-harness / cargo summary line is the authoritative whole-run
    // verdict when there is no `VERIFICATION:-` line:
    //   `Complete - 3 successfully verified harnesses, 0 failures, 3 total.`
    // Consulted BEFORE the per-check scan (same should_panic reasoning as above)
    // so a should_panic harness's expected `Status: FAILURE` lines — present in
    // multi-harness files like `derive-invariant/…` — cannot flip the oracle.
    for l in content.lines() {
        if let Some(rest) = l.trim().strip_prefix("Complete -") {
            if let Some(failures) = rest.split(',').find_map(|seg| {
                let seg = seg.trim();
                seg.strip_suffix("failures")
                    .or_else(|| seg.strip_suffix("failure"))
                    .and_then(|n| n.trim().parse::<u64>().ok())
            }) {
                return Some(if failures == 0 { Verdict::Success } else { Verdict::Fail });
            }
        }
    }
    let mentions_fail = content.lines().any(|l| {
        let t = l.trim();
        // Exact per-check status tokens (Kani prints `SUCCESS\`, `FAILURE\`,
        // `UNDETERMINED\` — the trailing `\` is a `contains_lines` block join).
        t == "FAILURE"
            || t == "FAILURE\\"
            || t == "UNDETERMINED"
            || t == "UNDETERMINED\\"
            || t.contains("Status: FAILURE")
            || t.starts_with("Failed Checks:")
            || t.starts_with("Verification failed for")
            // Old-format per-check line: `line <N> <description>: FAILURE`
            // (assert-location pair). AUDITED 2026-07-22: a full-corpus
            // oracle-diff of this marker flips EXACTLY the two
            // assert-location expected files (None -> Fail), both of which
            // real Kani genuinely fails; no other test's oracle moves.
            || t.trim_end_matches('\\').trim_end().ends_with(": FAILURE")
    });
    if mentions_fail {
        return Some(Verdict::Fail);
    }
    // Kani's per-harness summary line `** N of M failed[ (k unreachable)]`.
    // Checked LAST (only when every marker above is indeterminate) so it can
    // never override a whole-run verdict — a `#[kani::should_panic]` expected
    // file quotes `** 2 of 2 failed` next to its SUCCESSFUL verdict line.
    // Corpus-audited blast radius: exactly two otherwise-indeterminate files,
    // `expected/reach/assert/unreachable/expected` (`** 1 of 3 failed
    // (1 unreachable)` — a failure-expecting oracle that previously defaulted
    // to Success and mislabelled trust-mc's correct FAILED a false_positive)
    // and `expected/one-assert/expected` (`** 0 of 1 failed` — Success, same
    // as the previous default).
    let mut saw_harness_summary = false;
    for l in content.lines() {
        if let Some(rest) = l.trim().strip_prefix("**") {
            if let Some((n, tail)) = rest.trim_start().split_once(" of ") {
                if tail.contains("failed") {
                    if let Ok(n) = n.trim().parse::<u64>() {
                        saw_harness_summary = true;
                        if n > 0 {
                            return Some(Verdict::Fail);
                        }
                    }
                }
            }
        }
    }
    if saw_harness_summary {
        return Some(Verdict::Success);
    }
    // Indeterminate expected file (e.g. only checks a diagnostic string);
    // fall through to the directive/default oracle.
    None
}

/// The expected file's content is a *compile-time diagnostic* transcript
/// (rustc `error[E…]` codes or rustc's `error: aborting due to` line): the
/// oracle is a **compile failure** — Kani's compiletest passes the test when
/// the diagnostic lines appear in the output; the program never runs. Only
/// consulted when [`expected_file_verdict`] is indeterminate, so an expected
/// file that quotes an error string next to a real verification verdict keeps
/// the verdict. The `expected/intrinsics/simd-*` family is the canonical
/// case: rustc itself rejects those programs at monomorphization (verified:
/// nightly-2025-12-03 emits exactly the quoted `error[E0511]`), so a
/// verification verdict of either polarity can never match this oracle.
fn expected_is_compile_error(content: &str) -> bool {
    content.contains("error: aborting due to") || content.contains("error[E")
}

/// Kani declares a test's C dependencies through two channels: the
/// `// kani-flags:` header, and — in older tests — prose only, in the form its
/// own docs use: `//! kani <test>.rs -- lib.c`. Only the header channel was
/// honored, so a prose-only test was compiled WITHOUT the C definitions it
/// calls. Every `extern` is then undefined and the run cannot succeed, so the
/// row scored as a trust-mc `false_positive` — a harness-invocation artifact,
/// not a verifier defect. The same directory's `main.rs` carries BOTH
/// spellings and reaches parity, which is what makes the omission visible.
///
/// Supply exactly what the test asks for, and nothing else:
/// - never override an explicit `--c-lib` that a header already set;
/// - only accept a `.c` file that actually exists beside the test;
/// - emit link-only flags (`-Z c-ffi --c-lib`). These SUPPLY definitions
///   rather than relax a check, so they cannot manufacture a vacuous pass —
///   a missing definition is what makes such a run unverifiable to begin with.
///   (Measured on `fixme_varadic.rs`: with the library linked the run performs
///   MORE checks, including `va_arg` bounds and C-side overflow.)
///
/// The path is emitted relative to the Kani checkout root because the child is
/// spawned with that root as its cwd (see `runner.rs`).
fn augment_prose_c_lib(
    mut flags: Vec<String>,
    src: &str,
    path: &Path,
    checkout_root: &Path,
) -> Vec<String> {
    if flags.iter().any(|f| f == "--c-lib") {
        return flags;
    }
    let Some(dir) = path.parent() else { return flags };
    for line in src.lines() {
        let t = line.trim_start();
        let Some(body) = t.strip_prefix("//!").or_else(|| t.strip_prefix("//")) else {
            continue;
        };
        let body = body.trim();
        // The documented invocation form: `kani <something> -- <lib>.c ...`.
        if !body.starts_with("kani ") {
            continue;
        }
        let Some((_, tail)) = body.split_once(" -- ") else { continue };
        for tok in tail.split_whitespace() {
            if !tok.ends_with(".c") {
                continue;
            }
            let candidate = dir.join(tok);
            if !candidate.is_file() {
                continue;
            }
            let rel = candidate.strip_prefix(checkout_root).unwrap_or(&candidate);
            if !flags.iter().any(|f| f == "c-ffi") {
                flags.push("-Z".to_string());
                flags.push("c-ffi".to_string());
            }
            flags.push("--c-lib".to_string());
            flags.push(rel.to_string_lossy().into_owned());
            return flags;
        }
    }
    flags
}

/// Parse `// kani-flags:` (→ verifier flags) and `// compile-flags:` (→
/// RUSTFLAGS) directives, mirroring `tools/compiletest` header parsing.
fn parse_flags(src: &str) -> (Vec<String>, Vec<String>) {
    let mut flags = Vec::new();
    let mut rustflags = Vec::new();
    for line in src.lines() {
        let t = line.trim_start();
        let body = t
            .strip_prefix("//")
            .or_else(|| t.strip_prefix('#'))
            .map(str::trim_start)
            .unwrap_or("");
        if let Some(v) = body.strip_prefix("kani-flags:") {
            flags.extend(v.split_whitespace().map(str::to_string));
        } else if let Some(v) = body.strip_prefix("compile-flags:") {
            rustflags.extend(v.split_whitespace().map(str::to_string));
        }
    }
    (flags, rustflags)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Verdict as V;
    use crate::suites;

    fn write(p: &Path, content: &str) {
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, content).unwrap();
    }

    fn tmpdir(tag: &str) -> PathBuf {
        let d = std::env::temp_dir()
            .join(format!("kani-domination-test-{tag}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir_all(&d).unwrap();
        d
    }

    const PROOF: &str = "#[kani::proof]\nfn check() {}\n";

    /// A prose-only C dependency (`//! kani x.rs -- lib.c`) is honored, so the
    /// test is no longer compiled without the definitions it calls.
    #[test]
    fn prose_c_lib_is_supplied_when_header_is_absent() {
        let d = tmpdir("prose-clib");
        let t = d.join("tests/kani/ForeignItems/fixme_varadic.rs");
        write(&t, "//! To run this test, do\n//! kani fixme_varadic.rs -- lib.c\n");
        write(&d.join("tests/kani/ForeignItems/lib.c"), "int my_add(int n, ...);\n");
        let src = std::fs::read_to_string(&t).unwrap();
        let got = augment_prose_c_lib(Vec::new(), &src, &t, &d);
        assert_eq!(
            got,
            vec![
                "-Z".to_string(),
                "c-ffi".to_string(),
                "--c-lib".to_string(),
                "tests/kani/ForeignItems/lib.c".to_string(),
            ]
        );
    }

    /// An explicit header wins: never override what the test already declared.
    #[test]
    fn prose_c_lib_never_overrides_an_explicit_header() {
        let d = tmpdir("prose-clib-hdr");
        let t = d.join("a.rs");
        write(&t, "//! kani a.rs -- lib.c\n");
        write(&d.join("lib.c"), "int f(void);\n");
        let src = std::fs::read_to_string(&t).unwrap();
        let declared = vec!["--c-lib".to_string(), "already/lib.c".to_string()];
        let got = augment_prose_c_lib(declared.clone(), &src, &t, &d);
        assert_eq!(got, declared);
    }

    /// A `.c` file that does not exist is NOT invented: a stale prose line must
    /// not silently change how the corpus is invoked.
    #[test]
    fn prose_c_lib_requires_the_file_to_exist() {
        let d = tmpdir("prose-clib-missing");
        let t = d.join("a.rs");
        write(&t, "//! kani a.rs -- absent.c\n");
        let src = std::fs::read_to_string(&t).unwrap();
        assert!(augment_prose_c_lib(Vec::new(), &src, &t, &d).is_empty());
    }

    /// Ordinary prose mentioning a `.c` file is not an invocation directive.
    #[test]
    fn prose_c_lib_ignores_non_invocation_prose() {
        let d = tmpdir("prose-clib-noise");
        let t = d.join("a.rs");
        write(&t, "//! see lib.c for the definitions -- it is vendored\n");
        write(&d.join("lib.c"), "int f(void);\n");
        let src = std::fs::read_to_string(&t).unwrap();
        assert!(augment_prose_c_lib(Vec::new(), &src, &t, &d).is_empty());
    }

    fn suite() -> &'static Suite {
        suites::lookup("expected").unwrap()
    }

    /// Per-test `.expected` files are matched to their own test; a directory
    /// with many `.expected` files must NEVER concatenate them into one
    /// fabricated oracle.    /// An expected file that READS but names no failure is a passing run — the
    /// corpus convention — so Success is correct there.
    #[test]
    fn readable_expected_with_no_failure_marker_is_success() {
        let dir = std::env::temp_dir().join("kd_oracle_ok_test");
        let _ = std::fs::create_dir_all(&dir);
        let f = dir.join("expected");
        std::fs::write(&f, "some check: SUCCESS\n").unwrap();
        assert_eq!(super::oracle_from_expected_file(&f).unwrap(), Verdict::Success);
        let _ = std::fs::remove_file(&f);
    }

    /// A file we CANNOT read must NOT collapse to Success. That default is
    /// fail-OPEN: `missed_bug` is (oracle == Fail && observed == Success), so a
    /// wrongly-Success oracle hides a missed bug from the hard gate.
    #[test]
    fn unreadable_expected_file_is_an_error_not_success() {
        let missing = std::env::temp_dir().join("kd_oracle_definitely_missing_9f3a/expected");
        assert!(
            super::oracle_from_expected_file(&missing).is_err(),
            "an unreadable expected file must not yield a verdict"
        );
    }

    /// A real failure marker still wins.
    #[test]
    fn readable_expected_with_failure_marker_is_fail() {
        let dir = std::env::temp_dir().join("kd_oracle_fail_test");
        let _ = std::fs::create_dir_all(&dir);
        let f = dir.join("expected");
        std::fs::write(&f, "VERIFICATION:- FAILED\n").unwrap();
        assert_eq!(super::oracle_from_expected_file(&f).unwrap(), Verdict::Fail);
        let _ = std::fs::remove_file(&f);
    }


    #[test]
    fn per_test_expected_preferred_over_directory_concat() {
        let root = tmpdir("pertest");
        let dir = root.join("expected/quant");
        write(&dir.join("pass.rs"), PROOF);
        write(&dir.join("pass.expected"), "- Status: SUCCESS\nVERIFICATION:- SUCCESSFUL\n");
        write(&dir.join("fail.rs"), PROOF);
        write(&dir.join("fail.expected"), "- Status: FAILURE\nVERIFICATION:- FAILED\n");

        let found = discover_suite(&root, suite());
        let by_rel: std::collections::HashMap<_, _> =
            found.iter().map(|d| (d.rel.as_str(), d)).collect();
        // The sibling fail.expected must not leak into pass.rs's oracle.
        assert_eq!(by_rel["quant/pass.rs"].oracle, V::Success);
        assert_eq!(by_rel["quant/fail.rs"].oracle, V::Fail);
        assert_eq!(
            by_rel["quant/pass.rs"].expected_path.as_deref(),
            Some(dir.join("pass.expected").as_path())
        );
        let _ = std::fs::remove_dir_all(&root);
    }

    /// The directory-level `expected` file only applies when the test is the
    /// directory's sole entry.
    #[test]
    fn directory_expected_only_for_sole_entry() {
        let root = tmpdir("direxp");
        // Sole entry: dir expected applies.
        let solo = root.join("expected/solo");
        write(&solo.join("main.rs"), PROOF);
        write(&solo.join("expected"), "VERIFICATION:- FAILED\n");
        // Two entries, one shared dir `expected`: attribution is ambiguous,
        // so neither may claim it.
        let multi = root.join("expected/multi");
        write(&multi.join("a.rs"), PROOF);
        write(&multi.join("b.rs"), PROOF);
        write(&multi.join("expected"), "VERIFICATION:- FAILED\n");

        let found = discover_suite(&root, suite());
        let by_rel: std::collections::HashMap<_, _> =
            found.iter().map(|d| (d.rel.as_str(), d)).collect();
        assert_eq!(by_rel["solo/main.rs"].oracle, V::Fail);
        assert!(by_rel["solo/main.rs"].expected_path.is_some());
        assert_eq!(by_rel["multi/a.rs"].oracle, V::Success);
        assert_eq!(by_rel["multi/a.rs"].expected_path, None);
        assert_eq!(by_rel["multi/b.rs"].oracle, V::Success);
        let _ = std::fs::remove_dir_all(&root);
    }

    /// `assertion failed: …` quoted inside a SUCCESS Description is NOT a
    /// failure oracle (Kani quotes the property text in success lines).
    #[test]
    fn assertion_failed_text_in_success_description_is_not_a_fail_oracle() {
        let content = "- Status: SUCCESS\n\
                       - Description: \"assertion failed: x > 0\"\n\
                       VERIFICATION:- SUCCESSFUL\n";
        assert_eq!(expected_file_verdict(content), Some(V::Success));
    }

    #[test]
    fn expected_verdict_markers() {
        assert_eq!(expected_file_verdict("VERIFICATION:- FAILED\n"), Some(V::Fail));
        assert_eq!(expected_file_verdict(" - Status: FAILURE\n"), Some(V::Fail));
        assert_eq!(
            expected_file_verdict("Verification failed for - ptr::verify::check\n"),
            Some(V::Fail)
        );
        assert_eq!(expected_file_verdict("VERIFICATION:- SUCCESSFUL\n"), Some(V::Success));
        // Diagnostic-only expected file: indeterminate.
        assert_eq!(expected_file_verdict("error: no harnesses matched\n"), None);
    }

    /// Kani's own per-check status tokens (`FAILURE` / `Failed Checks:`) mark a
    /// failure-expecting test even without a `VERIFICATION:-` line. These are the
    /// `expected/reach/*/reachable_fail`, `expected/vec`, `expected/panic/*`,
    /// `expected/intrinsics/*` families that previously defaulted to Success and
    /// were mislabelled `false_positive` when trust-mc correctly failed them.
    #[test]
    fn kani_per_check_failure_tokens_are_a_fail_oracle() {
        // `expected/reach/assert/reachable_fail/expected` shape.
        let reach = "FAILURE\\\n\
                     Description: \"assertion failed: x != 5\"\n\
                     Failed Checks: assertion failed: x != 5\n";
        assert_eq!(expected_file_verdict(reach), Some(V::Fail));
        // `expected/unreachable/expected` shape (summary line only).
        assert_eq!(
            expected_file_verdict("Failed Checks: internal error: entered unreachable code:\n"),
            Some(V::Fail)
        );
        // Mixed `SUCCESS\`/`FAILURE\` block (`expected/vec/expected`).
        let vec = "SUCCESS\\\nassertion failed: y == 10\nFAILURE\\\nassertion failed: y != 10\n";
        assert_eq!(expected_file_verdict(vec), Some(V::Fail));
    }

    /// An unwinding-assertion failure marks a Fail via `UNDETERMINED` checks and
    /// the unwinding-failure banner (`unwind_tip`, `unwind-recursion-fail`).
    #[test]
    fn unwinding_failure_is_a_fail_oracle() {
        let tip = "UNDETERMINED\n\
                   [Kani] info: Verification output shows one or more unwinding failures.\n";
        assert_eq!(expected_file_verdict(tip), Some(V::Fail));
    }

    /// A `#[kani::should_panic]` harness lists the panics as `Failed Checks:` /
    /// `Status: FAILURE` but ends in a SUCCESSFUL whole-run verdict; the verdict
    /// line must win so the oracle stays Success (regression guard for
    /// `ui/should-panic-attribute/…` and `derive-invariant/…_fail_mut`).
    #[test]
    fn should_panic_success_wins_over_failed_check_lines() {
        let should_panic = " ** 2 of 2 failed\n\
                            Failed Checks: panicked on the `if` branch!\n\
                            VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)\n";
        assert_eq!(expected_file_verdict(should_panic), Some(V::Success));
        let inv = "Check 2: check.assertion.2\\\n\
                   - Status: FAILURE\\\n\
                   VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)\n";
        assert_eq!(expected_file_verdict(inv), Some(V::Success));
    }

    /// Kani's manual-harness / cargo summary line `Complete - N … M failures …`
    /// is the authoritative whole-run verdict when no `VERIFICATION:-` line is
    /// present (multi-harness files like `derive-invariant/…`). `0 failures`
    /// wins over the should_panic harness's expected `Status: FAILURE` lines, so
    /// the oracle stays Success and trust-mc's correct proof is not mislabelled a
    /// missed_bug.
    #[test]
    fn complete_summary_line_is_the_whole_run_oracle() {
        // 2 ordinary proofs + a should_panic harness whose expected panic prints
        // `Status: FAILURE`, but the run summary reports 0 failures.
        let ok = "Check 1: check.assertion\\\n\
                  - Status: FAILURE\\\n\
                  Complete - 3 successfully verified harnesses, 0 failures, 3 total.\n";
        assert_eq!(expected_file_verdict(ok), Some(V::Success));
        // A genuine failure count flips it to Fail.
        let bad = "Complete - 2 successfully verified harnesses, 1 failures, 3 total.\n";
        assert_eq!(expected_file_verdict(bad), Some(V::Fail));
        // Singular `1 failure` phrasing is also recognised.
        let bad1 = "Complete - 0 successfully verified harnesses, 1 failure, 1 total.\n";
        assert_eq!(expected_file_verdict(bad1), Some(V::Fail));
    }

    /// Kani's per-harness `** N of M failed` summary marks a failure-expecting
    /// oracle when nothing else is determinate (`expected/reach/assert/
    /// unreachable/expected` shape: only `UNREACHABLE\` + Description +
    /// summary), while `** 0 of 1 failed` (`expected/one-assert`) stays a
    /// success oracle, and the should_panic whole-run verdict still wins over
    /// a nonzero summary.
    #[test]
    fn n_of_m_failed_summary_line_oracle() {
        let unreachable = "UNREACHABLE\\\n\
                           Description: \"assertion failed: x == 2\"\n\
                            ** 1 of 3 failed (1 unreachable)\n";
        assert_eq!(expected_file_verdict(unreachable), Some(V::Fail));
        assert_eq!(expected_file_verdict(" ** 0 of 1 failed\n"), Some(V::Success));
        // Whole-run verdict precedence unchanged (should_panic files quote a
        // nonzero summary next to their SUCCESSFUL verdict).
        let should_panic = " ** 2 of 2 failed\n\
                            VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)\n";
        assert_eq!(expected_file_verdict(should_panic), Some(V::Success));
    }

    /// An expected file that is rustc compile-error text (the
    /// `expected/intrinsics/simd-*` E0511 family) sets a compile-fail oracle:
    /// oracle=Fail AND check_fail=true, so a verification verdict of either
    /// polarity can never silently count as parity. A diagnostic-only expected
    /// file without a compile-error signature keeps the default oracle.
    #[test]
    fn compile_error_expected_file_sets_check_fail_oracle() {
        let root = tmpdir("ce-oracle");
        let simd = root.join("expected/simd");
        write(&simd.join("main.rs"), PROOF);
        write(
            &simd.join("expected"),
            "expected return type with integer elements, found `f32x2` with non-integer `f32`\n\
             error: aborting due to 1 previous error\n",
        );
        let diag = root.join("expected/diag");
        write(&diag.join("main.rs"), PROOF);
        write(&diag.join("expected"), "warning: no harnesses matched\n");

        let found = discover_suite(&root, suite());
        let by_rel: std::collections::HashMap<_, _> =
            found.iter().map(|d| (d.rel.as_str(), d)).collect();
        let simd = by_rel["simd/main.rs"];
        assert_eq!(simd.oracle, V::Fail);
        assert!(simd.check_fail, "compile-error expected file must set the check-fail oracle");
        let diag = by_rel["diag/main.rs"];
        assert_eq!(diag.oracle, V::Success);
        assert!(!diag.check_fail);
        let _ = std::fs::remove_dir_all(&root);
    }

    /// A determinate verification verdict in the expected file wins over any
    /// quoted compile-error text: the compile-fail oracle only applies to
    /// verdict-indeterminate expected files.
    #[test]
    fn verdict_wins_over_quoted_compile_error_text() {
        let root = tmpdir("ce-verdict");
        let dir = root.join("expected/mixed");
        write(&dir.join("main.rs"), PROOF);
        write(
            &dir.join("expected"),
            "Description: \"error[E0080]: quoted in a property\"\nVERIFICATION:- FAILED\n",
        );
        let found = discover_suite(&root, suite());
        assert_eq!(found[0].oracle, V::Fail);
        assert!(!found[0].check_fail, "determinate verdict must not become a check-fail oracle");
        let _ = std::fs::remove_dir_all(&root);
    }

    /// The stale-but-unambiguous `// kani-expect-fail` spelling (one corpus
    /// use: kani/DynTrait/vtable_restrictions_fail_fixme.rs, which corrupts a
    /// vtable and must fail) is a fail oracle, not a compile-fail one.
    #[test]
    fn kani_expect_fail_directive_is_fail_oracle() {
        assert!(header_expects_fail("// kani-expect-fail\n#[kani::proof]\nfn f() {}\n"));
        assert!(!header_expects_check_fail("// kani-expect-fail\n"));
        assert!(!header_expects_fail("// kani-flags: -Z restrict-vtable\n"));
    }

    /// Manifest-listed oracle fixups apply during discovery: the real corpus
    /// path `kani/Unwind-Attribute/fixme_lib.rs` (planted `assert!(1 == 2)`,
    /// no expected file, Kani skips fixme paths) flips to a fail oracle while
    /// an unlisted sibling keeps the derived default.
    #[test]
    fn oracle_fixup_manifest_applies_to_listed_test_only() {
        let root = tmpdir("fixup");
        let dir = root.join("kani/Unwind-Attribute");
        write(&dir.join("fixme_lib.rs"), "#[kani::proof]\nfn main() { assert!(1 == 2); }\n");
        write(&dir.join("other_lib.rs"), PROOF);
        let kani_suite = suites::lookup("kani").unwrap();
        let found = discover_suite(&root, kani_suite);
        let by_rel: std::collections::HashMap<_, _> =
            found.iter().map(|d| (d.rel.as_str(), d)).collect();
        assert_eq!(by_rel["Unwind-Attribute/fixme_lib.rs"].oracle, V::Fail);
        assert_eq!(by_rel["Unwind-Attribute/other_lib.rs"].oracle, V::Success);
        let _ = std::fs::remove_dir_all(&root);
    }

    /// `// kani-check-fail` (compile-fail oracle) is recorded separately from
    /// `// kani-verify-fail`, and single-file entries carry their harness
    /// count for outer-watchdog scaling.
    #[test]
    fn check_fail_directive_and_harness_count_recorded() {
        let root = tmpdir("checkfail");
        let dir = root.join("expected/cf");
        write(
            &dir.join("a.rs"),
            "// kani-check-fail\n#[kani::proof]\nfn a() {}\n#[kani::proof]\nfn b() {}\n",
        );
        write(&dir.join("b.rs"), "// kani-verify-fail\n#[kani::proof]\nfn a() {}\n");

        let found = discover_suite(&root, suite());
        let by_rel: std::collections::HashMap<_, _> =
            found.iter().map(|d| (d.rel.as_str(), d)).collect();
        let a = by_rel["cf/a.rs"];
        assert_eq!(a.oracle, V::Fail);
        assert!(a.check_fail);
        assert_eq!(a.kind, EntryKind::SingleFile { harness_count: 2 });
        let b = by_rel["cf/b.rs"];
        assert_eq!(b.oracle, V::Fail);
        assert!(!b.check_fail, "kani-verify-fail is not a compile-fail oracle");
        assert_eq!(b.kind, EntryKind::SingleFile { harness_count: 1 });
        let _ = std::fs::remove_dir_all(&root);
    }

    /// A dir owned by a Cargo.toml becomes cargo units (one per expected
    /// file), and its `.rs` files are NOT single-file entries.
    #[test]
    fn cargo_package_becomes_units_not_single_files() {
        let root = tmpdir("cargo");
        let pkg = root.join("expected/proj");
        write(&pkg.join("Cargo.toml"), "[package]\nname = \"proj\"\n");
        write(&pkg.join("src/lib.rs"), PROOF);
        write(&pkg.join("src/extra.rs"), PROOF);
        write(&pkg.join("expected"), "Complete - 2 successfully verified harnesses, 0 failures, 2 total.\n");
        write(&pkg.join("ptr.expected"), "Verification failed for - ptr::check\n");

        let found = discover_suite(&root, suite());
        let rels: Vec<&str> = found.iter().map(|d| d.rel.as_str()).collect();
        assert_eq!(rels, vec!["proj/expected", "proj/ptr.expected"]);
        let all = &found[0];
        match &all.kind {
            EntryKind::CargoPackage { harness, harness_count, .. } => {
                assert_eq!(harness, &None);
                assert_eq!(*harness_count, 2);
            }
            k => panic!("expected cargo unit, got {k:?}"),
        }
        assert_eq!(all.oracle, V::Success);
        let ptr = &found[1];
        match &ptr.kind {
            EntryKind::CargoPackage { harness, .. } => {
                assert_eq!(harness.as_deref(), Some("ptr"));
            }
            k => panic!("expected cargo unit, got {k:?}"),
        }
        assert_eq!(ptr.oracle, V::Fail);
        let _ = std::fs::remove_dir_all(&root);
    }
}
