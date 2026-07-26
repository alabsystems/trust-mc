// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! The Kani upstream test-suite registry. Each suite is mapped to a [`Scope`]
//! that determines the *layered* parity denominator.

use crate::model::Scope;

/// A Kani upstream test suite under `tests/<name>/`.
#[derive(Debug, Clone, Copy)]
pub struct Suite {
    pub name: &'static str,
    pub scope: Scope,
    /// True when tests are whole cargo projects (an `expected`/`Cargo.toml`
    /// driven directory). Informational: discovery detects `Cargo.toml`
    /// ownership per-directory and routes those tests through the
    /// `cargo trust-mc` lane in any suite.
    pub cargo_project: bool,
    /// Short note on what the suite is.
    pub about: &'static str,
}

/// The full registry, mirroring `kani/tests/`. The denominator layering is:
///   * `Verification`  -> primary parity number
///   * `Verification + Benchmark + Diagnostic` -> outer full-corpus coverage
///   * `Excluded`      -> never counted (known-failing upstream / empty / non-rust)
pub const SUITES: &[Suite] = &[
    // ---- Verification (single-verdict) — the primary denominator ----------
    Suite { name: "expected",   scope: Scope::Verification, cargo_project: false,
            about: "canonical expected-output verification suite" },
    Suite { name: "kani",       scope: Scope::Verification, cargo_project: false,
            about: "the main functional verification suite" },
    Suite { name: "slow",       scope: Scope::Verification, cargo_project: false,
            about: "verification tests with long unwind/solve budgets" },
    Suite { name: "smack",      scope: Scope::Verification, cargo_project: false,
            about: "SMACK-derived verification tests" },
    Suite { name: "prusti",     scope: Scope::Verification, cargo_project: false,
            about: "Prusti-derived verification tests" },
    Suite { name: "std-checks", scope: Scope::Verification, cargo_project: true,
            about: "contracts/harnesses over the standard library" },
    // ---- Benchmark --------------------------------------------------------
    Suite { name: "perf",       scope: Scope::Benchmark,    cargo_project: true,
            about: "performance/benchmark harnesses (verdict + wall-clock)" },
    // ---- Diagnostic / coverage / cargo lanes (coverage denominator only) --
    Suite { name: "ui",             scope: Scope::Diagnostic, cargo_project: false,
            about: "diagnostic/UI output tests" },
    Suite { name: "coverage",       scope: Scope::Diagnostic, cargo_project: false,
            about: "line/region coverage reporting tests" },
    Suite { name: "cargo-kani",     scope: Scope::Diagnostic, cargo_project: true,
            about: "cargo-driven multi-crate verification" },
    Suite { name: "cargo-ui",       scope: Scope::Diagnostic, cargo_project: true,
            about: "cargo-driven UI tests" },
    Suite { name: "cargo-coverage", scope: Scope::Diagnostic, cargo_project: true,
            about: "cargo-driven coverage tests" },
    Suite { name: "script-based-pre", scope: Scope::Diagnostic, cargo_project: true,
            about: "shell-script-driven end-to-end tests" },
    Suite { name: "firecracker",    scope: Scope::Diagnostic, cargo_project: true,
            about: "Firecracker integration smoke tests" },
    Suite { name: "kani-docs",      scope: Scope::Diagnostic, cargo_project: true,
            about: "documentation example tests" },
    Suite { name: "llbc",           scope: Scope::Diagnostic, cargo_project: false,
            about: "Charon/LLBC backend tests" },
    // ---- Excluded ---------------------------------------------------------
    Suite { name: "kani-fixme",          scope: Scope::Excluded, cargo_project: false,
            about: "known-failing-upstream tests (not part of parity)" },
    Suite { name: "remote-target-lists", scope: Scope::Excluded, cargo_project: false,
            about: "non-rust target-list fixtures" },
];

pub fn lookup(name: &str) -> Option<&'static Suite> {
    SUITES.iter().find(|s| s.name == name)
}

/// Suites selected by a comma-list of scope keywords (`verification`,
/// `benchmark`, `diagnostic`, `full`, `all`).
pub fn suites_for_scopes(scopes: &[String]) -> Vec<&'static Suite> {
    let want = |sc: Scope| -> bool {
        scopes.iter().any(|s| match s.as_str() {
            "verification" => sc == Scope::Verification,
            "benchmark" => sc == Scope::Benchmark,
            "diagnostic" => sc == Scope::Diagnostic,
            // `full`/`all` = everything except the explicitly-excluded lanes.
            "full" | "all" => sc != Scope::Excluded,
            _ => false,
        })
    };
    SUITES.iter().filter(|s| want(s.scope)).collect()
}
