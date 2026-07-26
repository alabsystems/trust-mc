// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Explicit, per-test corpus fixups — the measurement-honesty escape hatches.
//!
//! Two hand-audited manifests, each entry carrying the *verified evidence*
//! for why the corpus row (not trust-mc) is wrong:
//!
//! * [`CORPUS_INVALID`]: sources that **no verifier on the pinned toolchain
//!   can compile** (removed intrinsics/features, planted unresolvable
//!   symbols, contract syntax Kani's own macros reject). Rows that would
//!   classify `Error` are reclassified to the visible `corpus_invalid`
//!   column and excluded from the parity denominator. The quarantine never
//!   touches a run that produced a verdict — if trust-mc (or a future
//!   toolchain) *does* process the file, it scores normally.
//!
//! * [`ORACLE_FIXUPS`]: tests whose derived oracle is provably wrong from
//!   the test source itself (e.g. a planted constant-false assertion in a
//!   `fixme_` file Kani's compiletest skips, so the default-success oracle
//!   is a fabrication).
//!
//! Integrity rules (mirroring `exceeds_oracle`): membership is an explicit
//! allowlist, never a heuristic — a heuristic here would become the place
//! genuine trust-mc compile regressions hide. Every entry quotes evidence
//! reproducible from the corpus source and the pinned toolchain
//! (`rustc nightly-2025-12-03` probes, Kani `tools/compiletest` /
//! `library/kani_macros` sources).

use crate::model::{Classification, Verdict};

/// A corpus source that cannot compile on the pinned toolchain, with the
/// verified evidence. Keyed by (suite, suite-relative POSIX path).
pub struct CorpusInvalid {
    pub suite: &'static str,
    pub rel: &'static str,
    pub evidence: &'static str,
}

/// Sources verified un-compilable by probing the pinned toolchain
/// (nightly-2025-12-03) and/or by inspection of Kani's own macro sources.
/// Kani's compiletest skips every one of them (`fixme` in the path =>
/// ignored, tools/compiletest/src/header.rs:193), so no Kani verdict exists
/// either — these rows measure the corpus, not trust-mc.
pub const CORPUS_INVALID: &[CorpusInvalid] = &[
    CorpusInvalid {
        suite: "kani",
        rel: "Intrinsics/fixme_try.rs",
        evidence: "uses `std::intrinsics::r#try`, removed from rustc (renamed \
                   `catch_unwind`); probe on nightly-2025-12-03: error[E0432]: \
                   unresolved import `std::intrinsics::r#try`",
    },
    CorpusInvalid {
        suite: "kani",
        rel: "Asm/main_fixme.rs",
        evidence: "calls the pre-1.59 crate-root `asm!` macro (no \
                   `std::arch::asm` import); probe on nightly-2025-12-03: \
                   error: cannot find macro `asm` in this scope",
    },
    CorpusInvalid {
        suite: "kani",
        rel: "FunctionSymbols/fixme_main.rs",
        evidence: "harness body is `size_of_val(&h)` with no `h` defined \
                   anywhere in the file; probe on nightly-2025-12-03: \
                   error[E0425]: cannot find value `h` in this scope",
    },
    CorpusInvalid {
        suite: "kani",
        rel: "Intrinsics/Assert/uninit_valid_panic.rs",
        evidence: "uses `intrinsics::assert_uninit_valid`, removed from rustc \
                   (renamed `assert_mem_uninitialized_valid` ~1.69); probe on \
                   nightly-2025-12-03 — the corpus checkout's own \
                   rust-toolchain.toml pin, so Kani itself cannot build it \
                   either: error[E0425]: cannot find function \
                   `assert_uninit_valid` in module `std::intrinsics`",
    },
];

/// The quarantine evidence for a test, if it is manifest-listed.
pub fn corpus_invalid_evidence(suite: &str, rel: &str) -> Option<&'static str> {
    CORPUS_INVALID.iter().find(|e| e.suite == suite && e.rel == rel).map(|e| e.evidence)
}

/// Reclassify a would-be `Error` row of a quarantined source to
/// `CorpusInvalid`. Any other classification passes through untouched: the
/// quarantine must never mask a run that produced a verdict (or a crash,
/// timeout, …) — those still measure trust-mc.
pub fn apply_corpus_quarantine(
    class: Classification,
    suite: &str,
    rel: &str,
) -> (Classification, Option<&'static str>) {
    if class == Classification::Error {
        if let Some(evidence) = corpus_invalid_evidence(suite, rel) {
            return (Classification::CorpusInvalid, Some(evidence));
        }
    }
    (class, None)
}

/// A test whose *derived* oracle is provably wrong, with the verified
/// ground-truth verdict and evidence.
pub struct OracleFixup {
    pub suite: &'static str,
    pub rel: &'static str,
    pub oracle: Verdict,
    pub evidence: &'static str,
}

/// Oracle corrections verified from the test source. Scope discipline: only
/// tests where the source itself proves the verdict (planted constant-false
/// assertions), never judgment calls — an ambiguous ground truth stays on
/// the derived oracle.
pub const ORACLE_FIXUPS: &[OracleFixup] = &[
    OracleFixup {
        suite: "kani",
        rel: "Unwind-Attribute/fixme_lib.rs",
        oracle: Verdict::Fail,
        evidence: "harness `main` is the planted constant-false \
                   `assert!(1 == 2)` and harness `harness` asserts \
                   `counter < 10` inside `loop {}` with `#[kani::unwind(10)]` \
                   — ground truth is FAIL. The default-success oracle was a \
                   fabrication: no expected file exists and Kani's \
                   compiletest skips `fixme` paths entirely \
                   (tools/compiletest/src/header.rs:193)",
    },
];

/// The oracle fixup for a test, if it is manifest-listed.
pub fn oracle_fixup(suite: &str, rel: &str) -> Option<&'static OracleFixup> {
    ORACLE_FIXUPS.iter().find(|e| e.suite == suite && e.rel == rel)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Classification as C;

    /// The quarantine flips ONLY manifest-listed `Error` rows; verdicts,
    /// crashes and unlisted errors pass through untouched.
    #[test]
    fn quarantine_only_reclassifies_listed_error_rows() {
        let (c, note) = apply_corpus_quarantine(C::Error, "kani", "Intrinsics/fixme_try.rs");
        assert_eq!(c, C::CorpusInvalid);
        assert!(note.unwrap().contains("std::intrinsics::r#try"));

        // Unlisted error: untouched.
        let (c, note) = apply_corpus_quarantine(C::Error, "kani", "SomeOther/test.rs");
        assert_eq!(c, C::Error);
        assert!(note.is_none());

        // A quarantined file that somehow produced a verdict / crash / timeout
        // still measures trust-mc: never reclassified.
        for keep in [C::Parity, C::MissedBug, C::Crash, C::Timeout, C::Unknown] {
            let (c, note) = apply_corpus_quarantine(keep, "kani", "Intrinsics/fixme_try.rs");
            assert_eq!(c, keep);
            assert!(note.is_none());
        }
    }

    /// Manifest hygiene: every entry quotes a reproducible compiler
    /// diagnostic, and every entry is a `fixme` path Kani's compiletest skips
    /// — except the explicitly documented `uninit_valid_panic.rs`, whose
    /// removed intrinsic fails to compile on the corpus checkout's OWN
    /// toolchain pin (nightly-2025-12-03), so Kani cannot build it either. A
    /// new non-fixme entry must be added to the exception list here with the
    /// same standard of evidence, or it would quarantine a test Kani actually
    /// runs — exactly the dishonesty this manifest must never enable.
    #[test]
    fn quarantine_entries_are_fixme_paths_or_documented_exceptions() {
        const NON_FIXME_EXCEPTIONS: &[&str] = &["Intrinsics/Assert/uninit_valid_panic.rs"];
        for e in CORPUS_INVALID {
            assert!(
                e.evidence.contains("error[E") || e.evidence.contains("error:") || e.evidence.contains("into_compile_error"),
                "{}/{} evidence does not quote a compiler diagnostic",
                e.suite,
                e.rel
            );
            assert!(
                e.rel.to_lowercase().contains("fixme") || NON_FIXME_EXCEPTIONS.contains(&e.rel),
                "{}/{} is neither a fixme path nor a documented exception",
                e.suite,
                e.rel
            );
        }
    }

    #[test]
    fn oracle_fixup_lookup() {
        let fx = oracle_fixup("kani", "Unwind-Attribute/fixme_lib.rs").unwrap();
        assert_eq!(fx.oracle, crate::model::Verdict::Fail);
        assert!(fx.evidence.contains("assert!(1 == 2)"));
        assert!(oracle_fixup("kani", "Unwind-Attribute/other.rs").is_none());
    }
}
