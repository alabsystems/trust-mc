#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Unit tests for scripts/soundness-dual-gate.py: manifest parsing, harness
discovery, driver-output parsing, classification and gating."""

from __future__ import annotations

import importlib.util
import os
import subprocess
import sys
import tempfile
import textwrap
import tomllib
import unittest
from unittest import mock
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
_SPEC = importlib.util.spec_from_file_location("soundness_dual_gate", SCRIPTS / "soundness-dual-gate.py")
gate = importlib.util.module_from_spec(_SPEC)
sys.modules["soundness_dual_gate"] = gate
_SPEC.loader.exec_module(gate)


def manifest_from(text: str, base: Path | None = None) -> "gate.Manifest":
    path = (base or Path("/nonexistent")) / "manifest.toml"
    return gate.parse_manifest_data(tomllib.loads(textwrap.dedent(text)), path)


MINIMAL = """
schema = "trust-mc.soundness-dual-manifest/v1"

[[entry]]
path = "a_dual.rs"
kind = "dual"
flags = ["-Z", "function-contracts"]
lanes = ["bmc", "chc"]
oracle = "header: MUST FAIL"

[[entry.harness]]
name = "bug"
expected = "FAILED"
property = "assertion"

[[entry.harness]]
name = "twin"
expected = "SUCCESSFUL"
"""


BMC_SAMPLE = """\
trust_mc Rust Verifier 0.6.0 (standalone)
[AY:CODEGEN_COMPLETE:harnesses=2]
Checking harness check_none_ne_some...
[AY:PROOF_QUALIFIERS:clean]

RESULTS:
Check 1: check_none_ne_some.array_bounds.1
\t - Status: SUCCESS
\t - Description: "index out of bounds: the length is less than or equal to the given index"

Check 2: check_none_ne_some.assertion.1
\t - Status: SUCCESS
\t - Description: "assertion failed: a[i] == Some(0)"


SUMMARY:
 ** 0 of 2 failed

VERIFICATION:- SUCCESSFUL
Verification Time: 0.14523967s

Checking harness check_none_eq_none...
[AY:CTREX_CAT:Unknown]
[AY:UNKNOWN_REASON:UndecidedModel]

RESULTS:
Check 1: check_none_eq_none.assertion.1
\t - Status: UNDETERMINED
\t - Description: "assertion failed: a[i] == None"

VERIFICATION:- INCONCLUSIVE (solver undecided — try --ay-chc for unbounded proofs)
"""

CHC_SAMPLE = """\
Checking harness check_none_ne_some...
[AY:CTREX] CHC verification: counterexample reachable (exact CHC derivation)
[AY:CTREX_CAT:Genuine]

RESULTS:
Check 1: check_none_ne_some.memory_safety.0
\t - Status: UNDETERMINED
\t - Description: "CHC verification: memory safety"

Check 2: check_none_ne_some.assertion.5
\t - Status: FAILURE
\t - Description: "assertion failed: a[i] == Some(0)"

VERIFICATION:- FAILED
Checking harness unsatisfiable_cover_control...
[AY:PROOF] CHC verification: property proven [AY:PROOF_TRANSCRIPT_METADATA:v1:json_hex=7b22]
Check 1: unsatisfiable_cover_control.assertion.1
\t - Status: SUCCESS
\t - Description: "assertion failed: a == a"

Check 2: unsatisfiable_cover_control.cover.1
\t - Status: UNSATISFIABLE
\t - Description: "cover property 0"

VERIFICATION:- SUCCESSFUL
"""


class ManifestParsingTests(unittest.TestCase):
    def test_minimal_manifest_parses(self) -> None:
        manifest = manifest_from(MINIMAL)
        (entry,) = manifest.entries
        self.assertEqual(entry.flags, ("-Z", "function-contracts"))
        self.assertEqual([h.name for h in entry.harnesses], ["bug", "twin"])
        self.assertEqual(entry.harnesses[0].property, "assertion")
        self.assertFalse(entry.harnesses[0].known_red)

    def assert_rejected(self, text: str, fragment: str) -> None:
        with self.assertRaises(gate.ManifestError) as caught:
            manifest_from(text)
        joined = "\n".join(caught.exception.problems)
        self.assertIn(fragment, joined)

    def test_known_red_needs_evidence(self) -> None:
        self.assert_rejected(MINIMAL.replace('property = "assertion"', 'property = "assertion"\nknown_red = true'),
                             "needs the audit evidence id")

    def test_known_red_lanes_default_to_entry_lanes(self) -> None:
        text = MINIMAL.replace('property = "assertion"',
                               'property = "assertion"\nknown_red = true\nknown_red_class = "missed-bug"\n'
                               'evidence = "soundness/x"')
        spec = manifest_from(text).entries[0].harnesses[0]
        self.assertEqual(spec.known_red_lanes, ("bmc", "chc"))
        self.assertEqual(spec.known_red_class, "missed-bug")

    def test_known_red_needs_class(self) -> None:
        self.assert_rejected(MINIMAL.replace('property = "assertion"',
                                             'property = "assertion"\nknown_red = true\nevidence = "soundness/x"'),
                             "needs known_red_class")

    def test_known_red_class_validated(self) -> None:
        red = 'property = "assertion"\nknown_red = true\nevidence = "soundness/x"\n'
        self.assert_rejected(MINIMAL.replace('property = "assertion"', red + 'known_red_class = "match"'),
                             "known_red_class must be one of")
        self.assert_rejected(MINIMAL.replace('property = "assertion"',
                                             'property = "assertion"\nknown_red_class = "missed-bug"'),
                             "known_red_class without known_red = true")

    def test_known_red_lanes_must_be_subset(self) -> None:
        text = MINIMAL.replace('lanes = ["bmc", "chc"]', 'lanes = ["chc"]').replace(
            'property = "assertion"',
            'property = "assertion"\nknown_red = true\nknown_red_lanes = ["bmc"]\n'
            'known_red_class = "missed-bug"\nevidence = "e"')
        self.assert_rejected(text, "known_red_lanes must be a non-empty subset")

    def test_expected_and_needs_review_are_exclusive(self) -> None:
        self.assert_rejected(MINIMAL.replace('expected = "SUCCESSFUL"',
                                             'expected = "SUCCESSFUL"\nneeds_review = "unclear"'),
                             "exclusive")

    def test_harness_needs_expectation_or_reason(self) -> None:
        self.assert_rejected(MINIMAL.replace('expected = "SUCCESSFUL"\n', ""), "needs an expected verdict")

    def test_unknown_expected_value(self) -> None:
        self.assert_rejected(MINIMAL.replace('expected = "SUCCESSFUL"', 'expected = "PASS"'), "expected must be one of")

    def test_unknown_key_is_rejected(self) -> None:
        self.assert_rejected(MINIMAL.replace('name = "twin"', 'name = "twin"\nexpect = "SUCCESSFUL"'), "unknown keys")

    def test_property_only_on_failing_expectations(self) -> None:
        self.assert_rejected(MINIMAL.replace('expected = "SUCCESSFUL"', 'expected = "SUCCESSFUL"\nproperty = "assertion"'),
                             "property only applies")

    def test_reserved_flags_are_rejected(self) -> None:
        self.assert_rejected(MINIMAL.replace('flags = ["-Z", "function-contracts"]', 'flags = ["--ay-chc"]'),
                             "set by the gate")

    def test_chc_track_flag_requires_chc_only_lane(self) -> None:
        self.assert_rejected(MINIMAL.replace('flags = ["-Z", "function-contracts"]', 'flags = ["--ay-chc-track=ptr"]'),
                             "CHC-only")

    def test_check_truth_validated(self) -> None:
        self.assert_rejected(MINIMAL.replace('property = "assertion"',
                                             'property = "assertion"\nchecks = [{ description = "c", truth = "UNDETERMINED" }]'),
                             "check truth")

    def test_duplicate_harness(self) -> None:
        self.assert_rejected(MINIMAL.replace('name = "twin"', 'name = "bug"'), "duplicate harness")

    def test_wrong_schema(self) -> None:
        self.assert_rejected(MINIMAL.replace("manifest/v1", "manifest/v0"), "schema must be")

    def test_cover_truth_validated(self) -> None:
        self.assert_rejected(MINIMAL.replace('expected = "SUCCESSFUL"',
                                             'expected = "SUCCESSFUL"\ncovers = [{ description = "c", truth = "SUCCESS" }]'),
                             "cover truth")

    def test_drift_against_source_tree(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            (base / "a_dual.rs").write_text(
                "#[kani::proof]\nfn bug() {}\n#[kani::proof]\nfn extra() {}\n", encoding="utf-8")
            (base / "unlisted_dual.rs").write_text("#[kani::proof]\nfn x() {}\n", encoding="utf-8")
            manifest = manifest_from(MINIMAL, base)
            problems = gate.validate_against_tree(manifest)
            joined = "\n".join(problems)
            self.assertIn("not in manifest: ['extra']", joined)
            self.assertIn("not in source: ['twin']", joined)
            self.assertIn("unlisted_dual.rs: dual file has no manifest entry", joined)

    def test_committed_manifest_matches_tree(self) -> None:
        manifest = gate.load_manifest(gate.DEFAULT_MANIFEST)
        self.assertEqual(gate.validate_against_tree(manifest), [])
        kinds = {entry.kind for entry in manifest.entries}
        self.assertEqual(kinds, {"dual", "negative", "ledger"})
        for entry in manifest.entries:
            for spec in entry.harnesses:
                if spec.known_red:
                    self.assertTrue(spec.evidence, f"{entry.path}::{spec.name}")


class DiscoveryTests(unittest.TestCase):
    def test_discovers_proof_shapes(self) -> None:
        source = textwrap.dedent(
            """
            // #[kani::proof]
            // fn commented_out() {}
            #[kani::proof]
            fn plain() {}

            #[kani::proof]
            #[kani::unwind(6)]
            pub unsafe fn with_attr() {}

            #[kani::proof_for_contract(bump)]
            fn contract_check() {}

            /// doc
            #[cfg_attr(kani, kani::proof)]
            fn cfg_attr_form() {}

            fn not_a_harness() {}
            #[kani::proof] fn same_line() {}
            """
        )
        self.assertEqual(gate.discover_harnesses(source),
                         ["plain", "with_attr", "contract_check", "cfg_attr_form", "same_line"])


class OutputParsingTests(unittest.TestCase):
    def test_bmc_sample(self) -> None:
        runs = gate.parse_driver_output(BMC_SAMPLE)
        self.assertEqual(sorted(runs), ["check_none_eq_none", "check_none_ne_some"])
        ne = runs["check_none_ne_some"]
        self.assertEqual(ne.verdict, "SUCCESSFUL")
        self.assertEqual([(c.property_class, c.status) for c in ne.checks],
                         [("array_bounds", "SUCCESS"), ("assertion", "SUCCESS")])
        self.assertIsNone(ne.ctrex_category)
        eq = runs["check_none_eq_none"]
        self.assertEqual(gate.normalize_verdict(eq.verdict), "INCONCLUSIVE")
        self.assertEqual(eq.ctrex_category, "Unknown")

    def test_chc_sample_category_markers_and_covers(self) -> None:
        runs = gate.parse_driver_output(CHC_SAMPLE)
        ne = runs["check_none_ne_some"]
        self.assertEqual(ne.verdict, "FAILED")
        self.assertEqual(ne.ctrex_category, "Genuine")
        self.assertEqual(ne.checks[1].description, "assertion failed: a[i] == Some(0)")
        cover = runs["unsatisfiable_cover_control"]
        self.assertTrue(any(c.property_class == "cover" for c in cover.checks))

    def test_qualified_harness_lookup(self) -> None:
        runs = {"module::inner": gate.HarnessRun(name="module::inner", verdict="FAILED")}
        self.assertIs(gate.find_run(runs, "inner"), runs["module::inner"])
        self.assertIsNone(gate.find_run(runs, "other"))

    def test_transcript_marker_is_truncated(self) -> None:
        body = "PROOF_TRANSCRIPT_METADATA:v1:json_hex=" + "ab" * 400
        self.assertEqual(gate._short_marker(body), "PROOF_TRANSCRIPT_METADATA:v1")

    def test_property_categories(self) -> None:
        self.assertIn("memory-safety", gate.property_categories("assertion", "memcpy src/dst overlap"))
        self.assertIn("valid-value", gate.property_categories("assertion", "Undefined Behavior: Invalid value of type `bool`"))
        self.assertIn("overflow", gate.property_categories("arithmetic_overflow", "attempt to add with overflow"))
        self.assertEqual(gate.property_categories("assertion", "assertion failed: x == 1"), {"assertion"})
        self.assertIn("contract", gate.property_categories("assertion", "|result| *result == a + 2"))


class ClassificationTests(unittest.TestCase):
    def check(self, expected, verdict, want, **kw):
        self.assertEqual(gate.classify_verdict(expected, verdict, **kw)[0], want,
                         f"{expected} x {verdict} {kw}")

    def test_failed_expectation(self) -> None:
        self.check("FAILED", "FAILED", "match")
        self.check("FAILED", "SUCCESSFUL", "missed-bug")
        self.check("FAILED", "SUCCESSFUL", "missed-bug", zero_checks=True)
        self.check("FAILED", "INCONCLUSIVE", "unknown")
        self.check("FAILED", "FAILED", "false-certificate", genuine=True, forbid_genuine=True)
        self.check("NOT_SUCCESSFUL", "FAILED", "match", genuine=True)
        self.check("FAILED", "FAILED", "match", genuine=False, forbid_genuine=True)

    def test_not_successful_expectation(self) -> None:
        self.check("NOT_SUCCESSFUL", "INCONCLUSIVE", "match")
        self.check("NOT_SUCCESSFUL", "FAILED", "match")
        self.check("NOT_SUCCESSFUL", "SUCCESSFUL", "missed-bug")

    def test_successful_expectation(self) -> None:
        self.check("SUCCESSFUL", "SUCCESSFUL", "match")
        self.check("SUCCESSFUL", "FAILED", "false-failure")
        self.check("SUCCESSFUL", "FAILED", "false-certificate", genuine=True)
        self.check("SUCCESSFUL", "SUCCESSFUL", "unknown", zero_checks=True)
        self.check("SUCCESSFUL", "INCONCLUSIVE", "unknown")

    def test_not_genuine_expectation(self) -> None:
        self.check("NOT_GENUINE", "SUCCESSFUL", "match")
        self.check("NOT_GENUINE", "FAILED", "match", genuine=False)
        self.check("NOT_GENUINE", "FAILED", "false-certificate", genuine=True)

    def test_certified_obligation_free_expectation(self) -> None:
        # D16: the twin of a statement site — nothing to prove, and the run says so.
        self.check("CERTIFIED_OBLIGATION_FREE", "SUCCESSFUL", "match",
                   zero_checks=True, certified_no_checks=True)
        # A zero-check SUCCESSFUL WITHOUT the certificate is the clean proof of
        # nothing the expectation exists to refuse.
        self.check("CERTIFIED_OBLIGATION_FREE", "SUCCESSFUL", "missed-bug", zero_checks=True)
        # Checks mean it is not the twin it claims to be.
        self.check("CERTIFIED_OBLIGATION_FREE", "SUCCESSFUL", "unknown", certified_no_checks=True)
        # A refused certificate is exit 1 on a correct program.
        self.check("CERTIFIED_OBLIGATION_FREE", "INCONCLUSIVE", "false-failure")
        self.check("CERTIFIED_OBLIGATION_FREE", "FAILED", "false-failure")
        self.check("CERTIFIED_OBLIGATION_FREE", "FAILED", "false-certificate", genuine=True)
        self.assertEqual(
            gate.classify_verdict("CERTIFIED_OBLIGATION_FREE", "INCONCLUSIVE")[1],
            "obligation-free-not-certified",
        )

    def test_certified_no_checks_is_read_from_the_qualifier_marker(self) -> None:
        text = textwrap.dedent("""\
            Checking harness certified...
            [AY:VACUOUS:no-checks] certified: the harness produced no verification conditions
            [AY:PROOF_QUALIFIERS:no_checks=compiler_certified_obligation_free]
            VERIFICATION:- SUCCESSFUL (no checks — compiler-certified obligation-free)
            Checking harness clean...
            [AY:PROOF_QUALIFIERS:clean]
            VERIFICATION:- SUCCESSFUL
            Checking harness refused...
            [AY:VACUOUS:no-checks] refused: the harness produced no verification conditions
            VERIFICATION:- INCONCLUSIVE (no checks)
        """)
        runs = gate.parse_driver_output(text)
        self.assertTrue(gate.run_is_certified_no_checks(runs["certified"]))
        self.assertFalse(gate.run_is_certified_no_checks(runs["clean"]))
        self.assertFalse(gate.run_is_certified_no_checks(runs["refused"]))
        self.assertEqual(gate.normalize_verdict(runs["certified"].verdict), "SUCCESSFUL")

    def test_tolerated_and_unclassified(self) -> None:
        self.check("TOLERATED", "FAILED", "match")
        self.check("TOLERATED", "SUCCESSFUL", "match")
        self.check(None, "SUCCESSFUL", "unclassified")

    def test_missing_verdict(self) -> None:
        self.check("FAILED", None, "error")
        self.check("FAILED", None, "unknown", timed_out=True)

    def test_cover_classification(self) -> None:
        self.assertEqual(gate.classify_cover("SATISFIED", "SATISFIED")[0], "match")
        self.assertEqual(gate.classify_cover("SATISFIED", "UNDETERMINED")[0], "match")
        self.assertEqual(gate.classify_cover("UNSATISFIABLE", "UNREACHABLE")[0], "match")
        self.assertEqual(gate.classify_cover("SATISFIED", "SUCCESS")[0], "missed-bug")
        self.assertEqual(gate.classify_cover("SATISFIED", "UNSATISFIABLE")[0], "missed-bug")
        self.assertEqual(gate.classify_cover("UNSATISFIABLE", "SATISFIED")[0], "false-failure")
        self.assertEqual(gate.classify_cover("SATISFIED", None)[0], "error")

    def test_cover_matched_by_message_then_ordinal(self) -> None:
        checks = [gate.CheckRow("h.cover.1", "cover", "SATISFIED", "cover property 0"),
                  gate.CheckRow("h.cover.2", "cover", "SUCCESS", "named cover")]
        first = gate.CoverSpec("unprinted message", "SATISFIED")
        second = gate.CoverSpec("named cover", "SATISFIED")
        self.assertEqual(gate.match_cover_status(first, 0, checks), "SATISFIED")
        self.assertEqual(gate.match_cover_status(second, 1, checks), "SUCCESS")
        self.assertIsNone(gate.match_cover_status(first, 5, []))

    def test_check_expectation_classification(self) -> None:
        self.assertEqual(gate.classify_check("FAILURE", "FAILURE")[0], "match")
        self.assertEqual(gate.classify_check("FAILURE", "UNDETERMINED")[0], "match")
        self.assertEqual(gate.classify_check("FAILURE", "SUCCESS")[0], "missed-bug")
        self.assertEqual(gate.classify_check("FAILURE", "UNREACHABLE")[0], "missed-bug")
        self.assertEqual(gate.classify_check("SUCCESS", "FAILURE")[0], "false-failure")
        # A safe check certified failed by a Genuine run is a false certificate.
        self.assertEqual(
            gate.classify_check("SUCCESS", "FAILURE", genuine=True),
            ("false-certificate", "check-failure-genuine-but-safe"),
        )
        self.assertEqual(gate.classify_check("FAILURE", "FAILURE", genuine=True)[0], "match")
        self.assertEqual(gate.classify_check("SUCCESS", None)[0], "error")

    def test_starved_requery_success_is_soundness_class(self) -> None:
        spec = gate.HarnessSpec(name="h", expected="FAILED", property="assertion",
                                checks=(gate.CheckSpec("violable only by factoring", "FAILURE"),))
        run = gate.HarnessRun(name="h", verdict="FAILED", checks=[
            gate.CheckRow("h.assertion.1", "assertion", "FAILURE", "cheap violable assertion"),
            gate.CheckRow("h.assertion.2", "assertion", "SUCCESS", "violable only by factoring")])
        row = gate.classify_harness(spec, "bmc", run, timed_out=False)
        self.assertEqual((row["class"], row["detail"]), ("missed-bug", "check-success-but-violable"))
        run.checks[1] = gate.CheckRow("h.assertion.2", "assertion", "UNDETERMINED", "violable only by factoring")
        self.assertEqual(gate.classify_harness(spec, "bmc", run, timed_out=False)["class"], "match")

    def test_duplicate_matching_checks_take_most_severe(self) -> None:
        spec = gate.HarnessSpec(name="h", expected="FAILED", checks=(gate.CheckSpec("dup", "FAILURE"),))
        run = gate.HarnessRun(name="h", verdict="FAILED", checks=[
            gate.CheckRow("h.assertion.1", "assertion", "FAILURE", "dup"),
            gate.CheckRow("h.assertion.2", "assertion", "SUCCESS", "dup")])
        row = gate.classify_harness(spec, "bmc", run, timed_out=False)
        self.assertEqual((row["class"], row["check_expectations"][0]["status"]), ("missed-bug", "SUCCESS"))

    def test_any_genuine_marker_counts(self) -> None:
        text = ("Checking harness twin...\n[AY:CTREX_CAT:OverApproximation]\n[AY:CTREX_CAT:Genuine]\n"
                "Check 1: twin.assertion.1\n\t - Status: FAILURE\n\t - Description: \"x\"\n"
                "VERIFICATION:- FAILED\n")
        run = gate.parse_driver_output(text)["twin"]
        self.assertEqual(run.ctrex_category, "OverApproximation")
        self.assertTrue(run.genuine)
        spec = gate.HarnessSpec(name="twin", expected="NOT_GENUINE")
        self.assertEqual(gate.classify_harness(spec, "chc", run, timed_out=False)["class"], "false-certificate")

    def test_harness_row_takes_most_severe_class(self) -> None:
        spec = gate.HarnessSpec(name="h", expected="SUCCESSFUL",
                                covers=(gate.CoverSpec("c", "SATISFIED"),))
        run = gate.HarnessRun(name="h", verdict="SUCCESSFUL",
                              checks=[gate.CheckRow("h.assertion.1", "assertion", "SUCCESS", "x"),
                                      gate.CheckRow("h.cover.1", "cover", "SUCCESS", "c")])
        row = gate.classify_harness(spec, "bmc", run, timed_out=False)
        self.assertEqual(row["class"], "missed-bug")
        self.assertEqual(row["detail"], "cover-status-success")
        self.assertTrue(row["soundness"])

    def test_property_ok_is_informational(self) -> None:
        spec = gate.HarnessSpec(name="h", expected="FAILED", property="memory-safety")
        run = gate.HarnessRun(name="h", verdict="FAILED",
                              checks=[gate.CheckRow("h.pointer_dereference.1", "pointer_dereference", "FAILURE",
                                                    "`src` must be properly aligned")])
        row = gate.classify_harness(spec, "bmc", run, timed_out=False)
        self.assertEqual(row["class"], "match")
        self.assertTrue(row["property_ok"])
        run.checks[0] = gate.CheckRow("h.assertion.1", "assertion", "FAILURE", "assertion failed: v == 1")
        row = gate.classify_harness(spec, "bmc", run, timed_out=False)
        self.assertEqual(row["class"], "match")
        self.assertFalse(row["property_ok"])

    def test_harness_not_run_is_error(self) -> None:
        spec = gate.HarnessSpec(name="h", expected="FAILED")
        self.assertEqual(gate.classify_harness(spec, "chc", None, timed_out=False)["class"], "error")
        self.assertEqual(gate.classify_harness(spec, "chc", None, timed_out=True)["class"], "unknown")


class GatingTests(unittest.TestCase):
    def row(self, cls: str, lane: str, red_lanes: tuple[str, ...] = (),
            red_class: str | None = None) -> dict:
        expected, verdict, genuine = {
            "missed-bug": ("FAILED", "SUCCESSFUL", False),
            "match": ("FAILED", "FAILED", False),
            "unknown": ("FAILED", "INCONCLUSIVE", False),
            "false-certificate": ("NOT_GENUINE", "FAILED", True),
            "false-failure": ("SUCCESSFUL", "FAILED", False),
        }[cls]
        spec = gate.HarnessSpec(name="h", expected=expected, known_red=bool(red_lanes),
                                known_red_lanes=red_lanes,
                                known_red_class=(red_class or cls) if red_lanes else None,
                                evidence="soundness/x" if red_lanes else None)
        out = gate.classify_harness(spec, lane, gate.HarnessRun(
            name="h", verdict=verdict, genuine=genuine,
            checks=[gate.CheckRow("h.assertion.1", "assertion", "SUCCESS", "x")]),
            timed_out=False)
        self.assertEqual(out["class"], cls)
        out["path"] = "p.rs"
        return out

    def test_known_red_suppresses_only_its_lanes(self) -> None:
        bmc = self.row("missed-bug", "bmc", red_lanes=("bmc",))
        chc = self.row("missed-bug", "chc", red_lanes=("bmc",))
        self.assertFalse(gate.is_gating(bmc))
        self.assertTrue(gate.is_gating(chc))
        summary = gate.summarize([bmc, chc], ("bmc", "chc"), strict=False)
        self.assertEqual(summary["gate"], "fail")
        self.assertEqual(len(summary["soundness_rows"]), 2)
        self.assertEqual([r["lane"] for r in summary["gating_rows"]], ["chc"])

    def test_non_soundness_rows_gate_only_when_strict(self) -> None:
        unknown = self.row("unknown", "bmc")
        self.assertFalse(gate.is_gating(unknown))
        self.assertTrue(gate.is_gating(unknown, strict=True))

    def test_error_rows_gate_without_strict(self) -> None:
        spec = gate.HarnessSpec(name="h", expected="FAILED")
        err = gate.classify_harness(spec, "bmc", None, timed_out=False)
        err["path"] = "p.rs"
        self.assertEqual(err["class"], "error")
        self.assertTrue(gate.is_gating(err))
        summary = gate.summarize([err], ("bmc",), strict=False)
        self.assertEqual(summary["gate"], "fail")
        self.assertIn("gating-rows", summary["gate_reasons"])

    def test_no_decided_verdict_fails_the_gate(self) -> None:
        # A driver that hangs on every file yields only unknown rows; that must
        # not read as a pass even though no single row gates.
        unknown = self.row("unknown", "bmc")
        self.assertFalse(gate.is_gating(unknown))
        summary = gate.summarize([unknown], ("bmc",), strict=False)
        self.assertEqual(summary["gate"], "fail")
        self.assertEqual(summary["gate_reasons"], ["no-decided-verdict"])
        self.assertEqual(gate.summarize([], ("bmc",), strict=False)["gate_reasons"], ["no-rows-scored"])

    def test_false_certificate_gates_without_strict(self) -> None:
        cert = self.row("false-certificate", "bmc")
        self.assertFalse(cert["soundness"])
        self.assertTrue(gate.is_gating(cert))
        summary = gate.summarize([cert], ("bmc",), strict=False)
        self.assertEqual(summary["gate"], "fail")
        self.assertEqual(len(summary["false_certificate_rows"]), 1)
        self.assertEqual(summary["per_lane"]["bmc"]["false-certificate"], 1)
        # A demoted FAILED on a safe program claims nothing and stays --strict only.
        demoted = self.row("false-failure", "bmc")
        self.assertFalse(gate.is_gating(demoted))
        self.assertTrue(gate.is_gating(demoted, strict=True))

    def test_known_red_excuses_only_its_class(self) -> None:
        parked = self.row("false-certificate", "bmc", red_lanes=("bmc",))
        self.assertFalse(gate.is_gating(parked))
        # Parked for a false certificate, now reporting SUCCESSFUL on the bug:
        # the flag must not hide the missed bug.
        regressed = self.row("missed-bug", "bmc", red_lanes=("bmc",), red_class="false-certificate")
        self.assertTrue(regressed["known_red"])
        self.assertTrue(gate.is_gating(regressed))
        summary = gate.summarize([parked, regressed], ("bmc",), strict=False)
        self.assertEqual(summary["gate"], "fail")
        self.assertEqual([r["class"] for r in summary["gating_rows"]], ["missed-bug"])
        self.assertEqual([r["class"] for r in summary["known_red_class_changed"]], ["missed-bug"])

    def test_known_red_now_green_is_reported(self) -> None:
        green = self.row("match", "bmc", red_lanes=("bmc",), red_class="missed-bug")
        summary = gate.summarize([green], ("bmc",), strict=False)
        self.assertEqual(summary["gate"], "pass")
        self.assertEqual(len(summary["known_red_now_green"]), 1)
        self.assertEqual(summary["per_lane"]["bmc"]["match"], 1)


class PreflightTests(unittest.TestCase):
    PIN = "94bf24d0f07fbcbfceea7ca3c509f8f35e9a8322"

    def test_ay_version_names_pin(self) -> None:
        text = f"ay 0.26.0+build.9565.{self.PIN}@2026-09-12T03:22:28Z\nbuild.commit={self.PIN}\n"
        self.assertEqual(gate.check_ay_version(text, self.PIN), self.PIN)

    def test_ay_version_other_commit_refused(self) -> None:
        other = "1" * 40
        with self.assertRaises(gate.GateRefusal):
            gate.check_ay_version(f"ay 0.23.0+build.1.{other}\n", self.PIN)

    def test_ay_version_short_sha_refused(self) -> None:
        with self.assertRaises(gate.GateRefusal):
            gate.check_ay_version("ay 0.26.0 (94bf24d0f)\n", self.PIN)

    def test_pinned_ay_cli_dir_is_keyed_by_pin_and_compiler(self) -> None:
        self.assertEqual(
            gate.pinned_ay_cli_dir(self.PIN, Path("/c"), "a" * 64),
            Path("/c/trust-mc-ay-cli-94bf24d0f") / ("compiler-" + "a" * 64) / "release"
        )
        with self.assertRaises(gate.GateRefusal):
            gate.pinned_ay_cli_dir("94bf24d0f", Path("/c"), "a" * 64)
        with self.assertRaises(gate.GateRefusal):
            gate.pinned_ay_cli_dir(self.PIN.upper(), Path("/c"), "a" * 64)
        with self.assertRaises(gate.GateRefusal):
            gate.pinned_ay_cli_dir(self.PIN, Path("/c"), "short")

    def test_ay_cli_cache_root_matches_the_build_script(self) -> None:
        self.assertEqual(
            gate.ay_cli_cache_root({"TRUST_MC_AY_CLI_CACHE_ROOT": "/x", "HOME": "/h"}), Path("/x")
        )
        expected = Path("/h/Library/Caches") if sys.platform == "darwin" else Path("/h/.cache")
        self.assertEqual(gate.ay_cli_cache_root({"HOME": "/h"}), expected)

    def test_default_ay_dir_agrees_with_compiler_bound_helper(self) -> None:
        from test_build_pinned_ay_cli import Fixture
        fixture = Fixture()
        self.addCleanup(fixture.temporary.cleanup)
        built = fixture.run()
        self.assertEqual(built.returncode, 0, built.stderr)
        with mock.patch.object(gate, "SCRIPTS_DIR", fixture.root / "scripts"):
            with mock.patch.dict(os.environ, fixture.env(), clear=True):
                default = gate.default_ay_dir()
        self.assertEqual(
            default,
            gate.pinned_ay_cli_dir(fixture.pin, fixture.caches, fixture.builder["key"]),
        )
        self.assertEqual(len(fixture.targo_calls()), 1)

    def test_default_ay_dir_refuses_when_compiler_cannot_resolve(self) -> None:
        from test_build_pinned_ay_cli import Fixture
        fixture = Fixture()
        self.addCleanup(fixture.temporary.cleanup)
        with mock.patch.object(gate, "SCRIPTS_DIR", fixture.root / "scripts"):
            with mock.patch.dict(os.environ, fixture.env(FAKE_RESOLVE_FAIL="1"), clear=True):
                with self.assertRaises(gate.GateRefusal):
                    gate.default_ay_dir()

    def test_default_route_refuses_missing_receipt_and_changed_same_pin_binary(self) -> None:
        from test_build_pinned_ay_cli import Fixture
        for change in ("missing_receipt", "changed_binary"):
            with self.subTest(change=change):
                fixture = Fixture()
                self.addCleanup(fixture.temporary.cleanup)
                self.assertEqual(fixture.run().returncode, 0)
                if change == "missing_receipt":
                    (fixture.cache / "builder.json").unlink()
                else:
                    fixture.binary.write_text(fixture.binary.read_text() + "# changed bytes\n")
                with mock.patch.object(gate, "SCRIPTS_DIR", fixture.root / "scripts"):
                    with mock.patch.dict(os.environ, fixture.env(), clear=True):
                        with self.assertRaises(gate.GateRefusal):
                            gate.default_ay_dir()
                self.assertEqual(len(fixture.targo_calls()), 1)

    def test_preflight_names_the_build_script_when_the_cli_is_missing(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            bundle = Path(tmp) / "bundle"
            (bundle / "bin").mkdir(parents=True)
            driver = bundle / "bin" / "trust-mc-driver"
            driver.write_text("#!/bin/sh\nexit 0\n")
            driver.chmod(0o755)
            with self.assertRaises(gate.GateRefusal) as caught:
                gate.preflight(bundle, Path(tmp) / "no-ay-here")
            self.assertIn("build-pinned-ay-cli.sh", str(caught.exception))

    def test_bundle_source_candidate_follows_given_path(self) -> None:
        self.assertEqual(gate.bundle_source_candidate(Path("/r/target/trust-mc")), Path("/r"))
        self.assertEqual(gate.bundle_source_candidate(Path("/r/target.noindex/trust-mc")), Path("/r"))
        self.assertIsNone(gate.bundle_source_candidate(Path("/opt/bundles/trust-mc")))
        with tempfile.TemporaryDirectory() as tmp:
            real = Path(tmp) / "target.noindex" / "trust-mc"
            real.mkdir(parents=True)
            (Path(tmp) / "target").symlink_to("target.noindex")
            self.assertEqual(gate.bundle_source_candidate(Path(tmp) / "target" / "trust-mc"), Path(tmp))

    def test_portable_paths_hide_home(self) -> None:
        home = Path.home()
        self.assertEqual(gate.portable(home / "trust-mc" / "target"), "~/trust-mc/target")
        self.assertEqual(gate.portable(home), "~")
        self.assertEqual(gate.portable("/opt/bundle"), "/opt/bundle")
        self.assertEqual(gate.portable(str(home) + "-other/x"), str(home) + "-other/x")

    def test_verdict_env_records_knobs_not_gate_values(self) -> None:
        env = {"TRUST_MC_NO_LOOP_RULE": "1", "TRUST_MC_SYSROOT": "/b", "RUSTFLAGS": "-Awarnings",
               "HOME": "/h", "AY_API_TOKEN": "s3cr3t", "RUSTUP_TOOLCHAIN": "trust"}
        self.assertEqual(gate.verdict_env(env), {"AY_API_TOKEN": "<redacted>", "RUSTUP_TOOLCHAIN": "trust",
                                                 "TRUST_MC_NO_LOOP_RULE": "1"})

    def test_wall_timeout_rule(self) -> None:
        entry = manifest_from(MINIMAL).entries[0]
        self.assertEqual(gate.wall_timeout(entry, 30, 180), 180 + 2 * 90)

    def test_command_shape(self) -> None:
        entry = manifest_from(MINIMAL).entries[0]
        job = gate.Job(entry, "chc", Path("/x/a_dual.rs"))
        cmd = gate.build_command(Path("/b/bin/trust-mc-driver"), job, 30)
        self.assertEqual(cmd, ["/b/bin/trust-mc-driver", "/x/a_dual.rs", "-Z", "unstable-options",
                               "--harness-timeout=30s", "--ay-chc", "-Z", "function-contracts"])
        bmc = gate.build_command(Path("/b/bin/trust-mc-driver"), gate.Job(entry, "bmc", Path("/x/a_dual.rs")), 30)
        self.assertNotIn("--ay-chc", bmc)
        copied = gate.build_command(Path("/b/bin/trust-mc-driver"), job, 30, Path("/tmp/run/a_dual.rs"))
        self.assertEqual(copied[1], "/tmp/run/a_dual.rs")


if __name__ == "__main__":
    unittest.main()
