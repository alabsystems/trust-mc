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

/// A verdict-indeterminate expected file that quotes only the MESSAGE of a
/// compile-time diagnostic, without the `error` level that
/// `discover::compile_fail_basis` recognises lexically — so nothing in the
/// file itself says "this is a compile error". Membership is an explicit
/// allowlist with the upstream evidence, and it applies only while the
/// expected file still contains `expected_quote`.
pub struct CompileFailOracle {
    pub suite: &'static str,
    pub rel: &'static str,
    /// Text the expected file must still contain for the entry to apply.
    pub expected_quote: &'static str,
    /// Upstream's diagnostic IS a compiler panic that carries the quoted
    /// message, so a panic in trust-mc's output does not disqualify the match.
    pub upstream_ice: bool,
    pub evidence: &'static str,
}

/// Measured 2026-09-14 from upstream Kani built at the pinned corpus rev
/// (`kani-src`, reporting `kani 0.67.0`; the `results-verification-kanisrc`
/// run's unit logs): every entry exits 1 with no `VERIFICATION:-` verdict, and
/// the quoted message is part of a compile-time diagnostic (or, for the two
/// `offset-invalid-args` units, of kani-compiler's panic).
pub const COMPILE_FAIL_ORACLES: &[CompileFailOracle] = &[
    CompileFailOracle {
        suite: "expected",
        rel: "assert-arg-error/test.rs",
        expected_quote: "cannot find value `foo` in this scope",
        upstream_ice: false,
        evidence: "kani-compiler exits 101: `error[E0425]: cannot find value `foo` in this scope`, \
                   `error: aborting due to 1 previous error`; no verdict, exit 1",
    },
    CompileFailOracle {
        suite: "expected",
        rel: "async_proof/main.rs",
        expected_quote: "cannot be applied to async functions that take arguments for now",
        upstream_ice: false,
        evidence: "kani-compiler exits 101: `error: `foo` is not a valid option for `#[kani::proof]`.`, \
                   `error: `#[kani::proof]` cannot be applied to async functions that take arguments for now`, \
                   `error: aborting due to 2 previous errors`; no verdict, exit 1",
    },
    CompileFailOracle {
        suite: "expected",
        rel: "function-contract/history/ui/noncopy_ignore.rs",
        expected_quote: "use of moved value: `ptr`",
        upstream_ice: false,
        evidence: "a `ui` compile-fail test (E0382 message); kani-compiler exits 101 with \
                   `error[E0614]: type `u32` cannot be dereferenced` instead, so Kani's own run \
                   misses the quoted line; no verdict, exit 1. Upstream-ignored (`ignore` in the path)",
    },
    CompileFailOracle {
        suite: "expected",
        rel: "function-contract/history/ui/old_result.rs",
        expected_quote: "cannot find value `result` in this scope",
        upstream_ice: false,
        evidence: "kani-compiler exits 101: `error[E0425]: cannot find value `result` in this scope`, \
                   `error: aborting due to 1 previous error`; no verdict, exit 1",
    },
    CompileFailOracle {
        suite: "expected",
        rel: "offset-invalid-args/invalid_offset_ty.rs",
        expected_quote: "Cannot offset by non-isize type u32",
        upstream_ice: true,
        evidence: "kani-compiler exits 101 during codegen: `error: internal compiler error: … broken MIR`, \
                   the message `Cannot offset by non-isize type u32`, `Kani unexpectedly panicked during \
                   compilation.`; no verdict, exit 1",
    },
    CompileFailOracle {
        suite: "expected",
        rel: "offset-invalid-args/non_ptr_arg.rs",
        expected_quote: "Cannot offset non-pointer type",
        upstream_ice: true,
        evidence: "kani-compiler exits 101 during codegen: `error: internal compiler error: … broken MIR`, \
                   the message `Cannot offset non-pointer type &'{erased} [i32; 1_usize]`, `Kani unexpectedly \
                   panicked during compilation.`; no verdict, exit 1",
    },
    CompileFailOracle {
        suite: "expected",
        rel: "stub-set-cycle/main.rs",
        expected_quote: "circular stub set reference: `set_a`",
        upstream_ice: false,
        evidence: "kani-compiler exits 101: `error: circular stub set reference: `set_a``, \
                   `error: aborting due to 1 previous error; 1 warning emitted`; no verdict, exit 1",
    },
    CompileFailOracle {
        suite: "expected",
        rel: "stub-set-invalid-entry/main.rs",
        expected_quote: "unknown entry in stub set:",
        upstream_ice: false,
        evidence: "kani-compiler exits 101: `error: unknown entry in stub set: `unknown_entry (real_fn , mock_fn)`. \
                   Expected `stub(...)` or `use_stub_set(...)``; no verdict, exit 1",
    },
    CompileFailOracle {
        suite: "expected",
        rel: "stub-set-not-a-stub-set/main.rs",
        expected_quote: "is not a stub set (missing `kani::stub_set!` definition)",
        upstream_ice: false,
        evidence: "kani-compiler exits 101: `error: `NOT_A_STUB_SET` is not a stub set (missing \
                   `kani::stub_set!` definition)`; no verdict, exit 1",
    },
    CompileFailOracle {
        suite: "expected",
        rel: "stubbing-type-mismatch-after-rename/main.rs",
        expected_quote: "Cannot stub `original` by `wrong_return_type`",
        upstream_ice: false,
        evidence: "kani-compiler exits 101: `error: Cannot stub `original` by `wrong_return_type`.` with \
                   `- Expected return type `T`, but found `bool``; no verdict, exit 1",
    },
];

/// The compile-fail oracle entry for a test, if it is manifest-listed.
pub fn compile_fail_oracle(suite: &str, rel: &str) -> Option<&'static CompileFailOracle> {
    COMPILE_FAIL_ORACLES.iter().find(|e| e.suite == suite && e.rel == rel)
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

    /// The compile-fail manifest names each unit once, with a non-empty quote
    /// and evidence, and looks up only what it lists.
    #[test]
    fn compile_fail_manifest_is_unique_and_quoted() {
        let mut seen = std::collections::BTreeSet::new();
        for e in COMPILE_FAIL_ORACLES {
            assert!(seen.insert((e.suite, e.rel)), "{}/{} listed twice", e.suite, e.rel);
            assert!(!e.expected_quote.trim().is_empty() && e.evidence.contains("exit"), "{}/{}", e.suite, e.rel);
            assert!(compile_fail_oracle(e.suite, e.rel).is_some());
            assert_eq!(e.upstream_ice, e.evidence.contains("panicked"), "{}/{}: the ICE flag must match its evidence", e.suite, e.rel);
        }
        assert!(compile_fail_oracle("expected", "assert-arg-error/other.rs").is_none());
        assert!(compile_fail_oracle("kani", "assert-arg-error/test.rs").is_none());
    }

    #[test]
    fn oracle_fixup_lookup() {
        let fx = oracle_fixup("kani", "Unwind-Attribute/fixme_lib.rs").unwrap();
        assert_eq!(fx.oracle, crate::model::Verdict::Fail);
        assert!(fx.evidence.contains("assert!(1 == 2)"));
        assert!(oracle_fixup("kani", "Unwind-Attribute/other.rs").is_none());
    }
}
