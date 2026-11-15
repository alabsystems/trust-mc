# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


SCRIPTS = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS.parent
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))
PROGRESS_TOOLS = REPO_ROOT / "tools/replacement-inventory"
if str(PROGRESS_TOOLS) not in sys.path:
    sys.path.insert(0, str(PROGRESS_TOOLS))

import direct_driver_proof_core as direct_core
import compiletest_report_contract as report_contract
import driver_binary_attestation as driver_attestation
import extract_replacement_proof_report as proof_extractor
import generate_non_proof_closure as closure_generator
import replacement_harness_dispositions as dispositions
import replacement_public_runner as public_runner
import replacement_progress
import generate_inventory as inventory_generator
import zero_fallback_proof_gate as proof_gate


def cover_output(properties: list[dict[str, str]]) -> str:
    return "".join(
        f'Check {index + 1}: cover.{index}\n'
        f'\t - Status: {prop["status"]}\n'
        f'\t - Description: "{prop["description"]}"\n\n'
        for index, prop in enumerate(properties)
    )


class ReplacementCoverAccountingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.authority = json.loads(dispositions.COVER_ORACLES.read_text())
        cls.rows = [
            {"file": row["file"], "harness": row["harness"],
             "driver_harness": row["harness"], "expected": row["expected"]}
            for row in cls.authority["rows"]
        ]

    def parse(self, row, properties, *, extra="", replacement=None):
        text = cover_output(properties) if replacement is None else replacement
        return public_runner.parse_driver_result(row, public_runner.ProcessResult(
            0 if row["expected"] == "PROOF" else 1,
            f'Checking harness {row["harness"]}...\n' + text + extra
            + '[AY:CTREX_CAT:Genuine]\n[AY:PROOF_QUALIFIERS:clean]\n'
            + f'[AY:{row["expected"]}]\n', 0.01,
        ))

    def test_all_five_oracles_match_exact_original_objects(self) -> None:
        self.assertEqual(len(self.rows), 5)
        self.assertEqual(sum(len(r["properties"]) for r in self.authority["rows"]), 10)
        for item in self.authority["rows"]:
            for path_field, blob_field, sha_field in (
                ("file", "source_blob", "source_sha256"),
                ("expectation_file", "expectation_blob", "expectation_sha256"),
            ):
                spec = self.authority["fork_commit"] + ":" + item[path_field]
                original = subprocess.check_output(["git", "show", spec], cwd=REPO_ROOT)
                self.assertEqual(subprocess.check_output(
                    ["git", "rev-parse", spec], cwd=REPO_ROOT, text=True,
                ).strip(), item[blob_field])
                self.assertEqual(hashlib.sha256(original).hexdigest(), item[sha_field])
                self.assertEqual((REPO_ROOT / item[path_field]).read_bytes(), original)
            expected = (REPO_ROOT / item["expectation_file"]).read_text()
            pairs = re.findall(
                r'Status: (SATISFIED|UNSATISFIABLE|UNREACHABLE|UNDETERMINED)\\?\n'
                r'Description: "([^"\n]+)"', expected,
            )
            self.assertEqual(item["properties"], [
                {"description": desc, "status": status} for status, desc in pairs
            ])
            self.assertEqual(item["expected"],
                             "CTREX" if "VERIFICATION:- FAILED" in expected else "PROOF")

    def test_exact_named_cover_outcomes_pass_independent_of_order(self) -> None:
        for row in self.rows:
            with self.subTest(harness=row["harness"]):
                props = dispositions.cover_expectations(row)
                flat, runtime = self.parse(row, list(reversed(props)))
                self.assertEqual(flat["status"], "PASS")
                self.assertEqual(runtime["cover_properties"], flat["cover_properties"])

    def test_safety_markers_and_aggregate_cover_counts_supply_no_property_credit(self) -> None:
        for row in self.rows:
            props = dispositions.cover_expectations(row)
            for absent in ([], [{"description": f"cover property {i}", "status": p["status"]}
                                for i, p in enumerate(props)]):
                flat, _ = self.parse(row, absent, extra=" ** 5 of 5 cover properties satisfied\n")
                self.assertEqual(flat["status"], "FAIL")
                self.assertEqual(flat["verdict"], row["expected"])
                self.assertNotIn("trusted_proof", flat)

    def test_missing_extra_duplicate_wrong_and_malformed_properties_refuse(self) -> None:
        row = next(r for r in self.rows if r["harness"] == "cover_unreachable")
        props = dispositions.cover_expectations(row)
        variants = [props[:-1], props + props[:1],
                    props + [{"description": "another cover", "status": "SATISFIED"}],
                    [{**p, "status": "UNDETERMINED"} for p in props],
                    [{**p, "status": "UNSATISFIABLE"} for p in props]]
        for variant in variants:
            flat, _ = self.parse(row, variant)
            self.assertEqual(flat["status"], "FAIL")
        valid = cover_output(props)
        for malformed in (
            valid.replace("Check 1:", "Check 0:"),
            valid.replace("Check 2:", "Check 1:"),
            valid.replace("cover.1", "cover.0"),
            valid.replace(" - Status: UNREACHABLE", " - Status: ", 1),
            valid.replace(" - Status: UNREACHABLE", " - Status: UNREACHABLE\n - Status: SATISFIED", 1),
            valid.replace("cover.0", "ordinary.assertion.0", 1),
            valid + "Check broken cover header\n",
            valid + "Check 4: cover.3",
        ):
            flat, _ = self.parse(row, props, replacement=malformed)
            self.assertEqual(flat["status"], "FAIL")

    def test_progress_rechecks_properties_even_if_a_report_claims_pass(self) -> None:
        row = self.rows[-1]
        props = dispositions.cover_expectations(row)
        flat, _ = self.parse(row, props)
        inventory = {"rows": [row], "denominator": 1}
        for values, expected in ((props, 1), (None, 0), (props[:-1], 0),
                                 ([{**p, "status": "UNDETERMINED"} for p in props], 0)):
            forged = {**flat, "cover_properties": values}
            observed, _ = replacement_progress.parse_report([forged])
            progress = replacement_progress.compute_progress(inventory, observed)
            self.assertEqual(progress.proof_proven, expected)
            self.assertEqual(progress.complete, bool(expected))
        summary = {"harnesses": [{"harness": row["harness"], "file": row["file"],
                   "status": "success", "property_counts": {}}]}
        observed, _ = replacement_progress.parse_report(summary)
        self.assertEqual(replacement_progress.compute_progress(inventory, observed).proof_proven, 0)

    def test_malformed_status_and_description_fields_refuse(self) -> None:
        row = next(r for r in self.rows if r["harness"] == "cover_unreachable")
        props = dispositions.cover_expectations(row)
        valid = cover_output(props)
        for duplicate in (
            " - status: unknown\n",
            " - STATUS: UNREACHABLE\n",
            " - Status UNREACHABLE\n",
            " Status: UNREACHABLE\n",
            " - Description: unquoted\n",
            ' - description: "unquoted"\n',
            ' Description: "without the field marker"\n',
        ):
            with self.subTest(duplicate=duplicate):
                malformed = valid.replace(" - Status: UNREACHABLE\n", " - Status: UNREACHABLE\n" + duplicate, 1)
                flat, _ = self.parse(row, props, replacement=malformed)
                self.assertEqual(flat["status"], "FAIL")
                self.assertIn("malformed cover check", flat["cover_error"])
        for before, after in (
            (" - Status: UNREACHABLE", " - status: UNREACHABLE"),
            (' - Description: "cover condition: x == 2"', " - Description: unquoted"),
        ):
            with self.subTest(replacement=after):
                flat, _ = self.parse(row, props, replacement=valid.replace(before, after, 1))
                self.assertEqual(flat["status"], "FAIL")

    def test_final_proof_gate_rechecks_direct_cover_report(self) -> None:
        row = next(r for r in self.rows if r["harness"] == "cover_unreachable")
        properties = dispositions.cover_expectations(row)
        for values, expected_pass in (
            (properties, True),
            (None, False),
            ([], False),
            (properties[:-1], False),
            (properties + properties[:1], False),
            ([{**p, "status": "UNDETERMINED"} for p in properties], False),
            ([{**p, "description": f"cover property {i}"} for i, p in enumerate(properties)], False),
        ):
            with self.subTest(properties=values):
                report = AyProofContractTests.clean_report()
                report["harnesses"][0].update(row)
                if values is not None:
                    report["harnesses"][0]["cover_properties"] = values
                failures = proof_gate.find_gate_failures(
                    report, expected_ay_pin=AyProofContractTests.AY_PIN, expected_harnesses=1,
                )
                self.assertEqual(not failures, expected_pass, failures)
                if not expected_pass:
                    self.assertTrue(any("cover" in failure for failure in failures))
                # Submit directly to the strict gate, without proof extraction.
                # Authority loading is isolated here; it must still be requested.
                load_report = mock.Mock(return_value=report)
                with mock.patch.object(proof_gate, "_load_contract", return_value=load_report), \
                     mock.patch.object(proof_gate.LOGGER, "error"), \
                     mock.patch.object(proof_gate.LOGGER, "info"):
                    result = proof_gate.main([
                        "--expected-ay-pin", AyProofContractTests.AY_PIN,
                        "--expected-harnesses", "1", "report.json",
                    ])
                self.assertEqual(result, 0 if expected_pass else 1)
                load_report.assert_called_once_with(
                    Path("report.json"), repo_root=proof_gate.REPO_ROOT, require_current_head=True,
                )

    def test_final_proof_gate_refuses_invalid_cover_authority_only_for_cover_rows(self) -> None:
        row = next(r for r in self.rows if r["harness"] == "cover_unreachable")
        properties = dispositions.cover_expectations(row)
        report = AyProofContractTests.clean_report()
        report["harnesses"][0].update(row, cover_properties=properties)
        wrong_source = json.loads(json.dumps(self.authority))
        next(item for item in wrong_source["rows"] if item["harness"] == row["harness"])["source_sha256"] = "0" * 64
        with tempfile.TemporaryDirectory() as raw:
            authority_path = Path(raw) / "cover.json"
            for invalid in (
                None, "not json", json.dumps({"schema_version": 1, "rows": [None]}),
                json.dumps(wrong_source),
            ):
                if invalid is not None:
                    authority_path.write_text(invalid)
                with self.subTest(authority=invalid), mock.patch.object(dispositions, "COVER_ORACLES", authority_path):
                    failures = proof_gate.find_gate_failures(
                        report, expected_ay_pin=AyProofContractTests.AY_PIN, expected_harnesses=1,
                    )
                    self.assertTrue(any("invalid cover authority" in failure for failure in failures), failures)
                    self.assertEqual(proof_gate.find_gate_failures(
                        AyProofContractTests.clean_report(),
                        expected_ay_pin=AyProofContractTests.AY_PIN, expected_harnesses=1,
                    ), [])

    def test_cover_source_drift_and_malformed_authority_refuse(self) -> None:
        row = self.rows[0]
        authority = json.loads(json.dumps(self.authority))
        authority["rows"][0]["source_sha256"] = "0" * 64
        with mock.patch.object(dispositions, "_read_object", return_value=authority):
            with self.assertRaisesRegex(dispositions.DispositionError, "source changed"):
                dispositions.cover_expectations(row)
        authority = json.loads(json.dumps(self.authority))
        authority["rows"][0]["properties"][0]["status"] = []
        with mock.patch.object(dispositions, "_read_object", return_value=authority):
            with self.assertRaisesRegex(dispositions.DispositionError, "malformed"):
                dispositions.cover_expectations(row)


class DriverBinaryAttestationTests(unittest.TestCase):
    TRUST_MC_SHA = "89abcdef0123456789abcdef0123456789abcdef"
    AY_PIN = "0123456789abcdef0123456789abcdef01234567"

    @classmethod
    def authority_line(cls) -> str:
        return (
            "trust_mc-version-authority version=0.2.0 invocation=standalone "
            f"trust_mc_sha={cls.TRUST_MC_SHA} trust_mc_dirty=0 "
            f"ay_version=0.13.0 ay_pin={cls.AY_PIN} "
            f"ay_linked_sha={cls.AY_PIN} ay_linked_dirty=0 ay_authority=matched"
        )

    def test_exact_driver_binary_is_attested(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            driver = Path(raw) / "trust-mc-driver"
            driver.write_text(
                "#!/bin/sh\nprintf '%s\\n' '" + self.authority_line() + "'\n",
                encoding="utf-8",
            )
            driver.chmod(0o755)
            attestation = driver_attestation.attest_driver_binary(
                driver,
                expected_trust_mc_sha=self.TRUST_MC_SHA,
                expected_ay_pin=self.AY_PIN,
            )
        self.assertEqual(attestation["trust_mc_sha"], self.TRUST_MC_SHA)
        self.assertEqual(attestation["ay_linked_sha"], self.AY_PIN)
        self.assertRegex(attestation["sha256"], r"^[0-9a-f]{64}$")

    def test_driver_authority_rejects_noise_dirty_and_wrong_commit(self) -> None:
        with self.assertRaises(driver_attestation.DriverAttestationError):
            driver_attestation.parse_authority_output(
                "untrusted noise\n" + self.authority_line() + "\n"
            )
        fields = {
            "name": "trust-mc-driver",
            "path": "/tmp/trust-mc-driver",
            "sha256": "a" * 64,
            "version": "0.2.0",
            "invocation": "standalone",
            "trust_mc_sha": "f" * 40,
            "trust_mc_dirty": True,
            "ay_version": "0.13.0",
            "ay_pin": self.AY_PIN,
            "ay_linked_sha": self.AY_PIN,
            "ay_linked_dirty": False,
            "ay_authority": "matched",
        }
        failures = driver_attestation.validate_attestation(
            fields,
            expected_trust_mc_sha=self.TRUST_MC_SHA,
            expected_ay_pin=self.AY_PIN,
        )
        self.assertTrue(any("trust_mc_sha" in failure for failure in failures))
        self.assertTrue(any("trust_mc_dirty" in failure for failure in failures))

    def test_driver_diagnostics_do_not_replace_stdout_authority(self) -> None:
        diagnostics = "[AY] in-process ay memory cap: 32768 MiB\n"
        with tempfile.TemporaryDirectory() as raw:
            driver = Path(raw) / "trust-mc-driver"
            driver.write_text(
                "#!/bin/sh\nprintf '%s\\n' '" + self.authority_line() + "'\n"
                "printf '%s\\n' '[AY] in-process ay memory cap: 32768 MiB' >&2\n",
                encoding="utf-8",
            )
            driver.chmod(0o755)
            attestation = driver_attestation.attest_driver_binary(
                driver,
                expected_trust_mc_sha=self.TRUST_MC_SHA,
                expected_ay_pin=self.AY_PIN,
            )
            self.assertEqual(attestation["trust_mc_sha"], self.TRUST_MC_SHA)
            self.assertEqual(attestation["diagnostic_stderr"], diagnostics)

            # An authority-looking stderr line cannot supply missing stdout.
            driver.write_text(
                "#!/bin/sh\nprintf '%s\\n' '" + self.authority_line() + "' >&2\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                driver_attestation.DriverAttestationError, "exactly one authority line"
            ):
                driver_attestation.attest_driver_binary(
                    driver,
                    expected_trust_mc_sha=self.TRUST_MC_SHA,
                    expected_ay_pin=self.AY_PIN,
                )

    def test_nonzero_driver_exit_retains_both_streams_and_refuses(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            driver = Path(raw) / "trust-mc-driver"
            driver.write_text(
                "#!/bin/sh\nprintf '%s\\n' '" + self.authority_line() + "'\n"
                "printf '%s\\n' 'runtime refused' >&2\nexit 7\n",
                encoding="utf-8",
            )
            driver.chmod(0o755)
            with self.assertRaises(driver_attestation.DriverAttestationError) as error:
                driver_attestation.attest_driver_binary(
                    driver,
                    expected_trust_mc_sha=self.TRUST_MC_SHA,
                    expected_ay_pin=self.AY_PIN,
                )
            self.assertIn("exited 7", str(error.exception))
            self.assertIn(self.authority_line(), str(error.exception))
            self.assertIn("runtime refused", str(error.exception))


class ReplacementDispositionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.artifact = dispositions.build_dispositions(
            dispositions.DEFAULT_INVENTORY,
            dispositions.DEFAULT_PROOF_INVENTORY,
            dispositions.DEFAULT_NON_PROOF,
        )

    def test_canonical_source_bound_counts_and_credits(self) -> None:
        summary = self.artifact["summary"]
        self.assertEqual(summary["historical_total"], 818)
        self.assertEqual(summary["active"], 786)
        self.assertEqual(summary["inactive_accounted"], 32)
        self.assertEqual(
            summary["resolution_counts"],
            {
                "cargo-default-feature": 1,
                "cfg-disabled-upstream": 32,
                "exact": 739,
                "unique-qualified-alias": 46,
            },
        )
        self.assertEqual(summary["proof"]["historical"], 485)
        self.assertEqual(summary["proof"]["active"], 453)
        self.assertEqual(summary["proof"]["inactive_zero_credit"], 32)
        # The BAR is what the incumbent does: all 32 inactive PROOF rows are
        # upstream-disabled, none are ours, so none of them block the gate.
        self.assertEqual(summary["proof"]["bar"], 453)
        self.assertEqual(summary["proof"]["upstream_inactive"], 32)
        self.assertEqual(summary["proof"]["local_inactive"], 0)
        self.assertEqual(
            sum(summary["proof"]["supersession_candidates"].values()), 32
        )
        self.assertEqual(summary["non_proof"]["historical"], 333)
        self.assertEqual(summary["non_proof"]["active"], 333)
        self.assertEqual(summary["non_proof"]["inactive_zero_credit"], 0)
        self.assertEqual(summary["non_proof"]["local_inactive"], 0)
        self.assertEqual(
            sum(row["executor"] == "cargo" for row in self.artifact["rows"]),
            98,
        )

    def test_inherent_impl_scope_qualifies_harnesses_and_ends_at_its_brace(self) -> None:
        source = """
struct First;
impl First {
    #[kani::proof]
    fn check() {}
}
mod nested {
    struct Second;
    impl Second {
        #[kani::proof]
        fn check() {}
    }
    #[kani::proof]
    fn outside_impl() {}
}
#[kani::proof]
fn outside_module() {}
"""
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "associated.rs"
            path.write_text(source)
            self.assertEqual(dispositions.extract_proof_harnesses(path), [
                "First::check", "nested::Second::check", "nested::outside_impl",
                "outside_module",
            ])

    def test_associated_harness_matches_its_original_compiler_name(self) -> None:
        row = next(row for row in self.artifact["rows"]
                   if row["file"] == "tests/expected/associated-fn/associated_fn.rs")
        self.assertEqual(row["harness"], "new")
        self.assertEqual(row["driver_harness"], "Dummy::new")
        self.assertEqual(row["resolution"], "unique-qualified-alias")
        original = subprocess.check_output([
            "git", "show", "c4d858036efec56e02caa743f8732582da973d5a:"
            "tests/expected/associated-fn/expected",
        ], cwd=REPO_ROOT, text=True)
        self.assertIn("Checking harness Dummy::new...", original)

    def test_same_bare_method_in_two_impls_has_no_implicit_selection(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            source = root / "tests/associated.rs"
            source.parent.mkdir()
            source.write_text("""
struct First;
impl First {
    #[kani::proof]
    fn check() {}
}
struct Second;
impl Second {
    #[kani::proof]
    fn check() {}
}
""")
            with mock.patch.object(dispositions, "REPO_ROOT", root):
                with self.assertRaisesRegex(dispositions.DispositionError,
                                            "ambiguous qualified aliases"):
                    dispositions._plan_row({
                        "file": "tests/associated.rs", "harness": "check",
                        "expected": "PROOF", "lane": "tests/expected",
                    })

    def test_original_failure_oracles_are_not_false_proof_requirements(self) -> None:
        correction = json.loads((PROGRESS_TOOLS / "oracle-corrections-2026-11-14.json").read_text())
        self.assertEqual(len(correction["corrections"]), 27)
        rows = {(row["file"], row["harness"]): row for row in self.artifact["rows"]}
        for evidence in correction["corrections"]:
            key = (evidence["file"], evidence["harness"])
            with self.subTest(key=key):
                self.assertEqual(rows[key]["expected"], "CTREX")
                source = REPO_ROOT / evidence["file"]
                self.assertEqual(len(inventory_generator.extract_proof_harnesses(source)), 1)
                self.assertRegex(source.read_text(), r"(?m)^//\s*kani-verify-fail\b")
        # Correcting oracle labels cannot remove or rename historical cases.
        keys = sorted((row["file"], row["harness"], row["lane"]) for row in self.artifact["rows"])
        digest = hashlib.sha256(json.dumps(keys, separators=(",", ":")).encode()).hexdigest()
        self.assertEqual(digest, "e3aa42ae95cdadf691caaf92e67f71b95f359a44f9878f6a0fc292f449d63bf1")

    def test_corrected_failure_requires_genuine_refutation_not_proof_or_guess(self) -> None:
        row = next(row for row in self.artifact["rows"] if row["file"] == "tests/smack/basic/add.rs")
        for marker, expected_status in [
            ("[AY:CTREX]\n[AY:CTREX_CAT:Genuine]", "PASS"),
            ("[AY:PROOF]\n[AY:PROOF_QUALIFIERS:clean]", "FAIL"),
            ("[AY:CTREX]\n[AY:CTREX_CAT:OverApproximation]", "FAIL"),
            ("[AY:CTREX]", "FAIL"),
        ]:
            with self.subTest(marker=marker):
                result = public_runner.ProcessResult(
                    returncode=1 if "CTREX" in marker else 0,
                    output="Checking harness main...\n" + marker + "\n",
                    elapsed_seconds=0.1,
                )
                flat, _runtime = public_runner.parse_driver_result(row, result)
                self.assertEqual(flat["status"], expected_status)

    def test_semantic_oracles_bind_the_selected_harness_to_unchanged_source(self) -> None:
        correction = json.loads(
            (PROGRESS_TOOLS / "oracle-semantic-corrections-2026-11-14.json").read_text()
        )
        rows = {(row["file"], row["harness"]): row for row in self.artifact["rows"]}
        self.assertEqual(len(correction["corrections"]), 6)
        self.assertEqual(
            sorted(item["after"] for item in correction["corrections"]),
            ["CTREX"] * 3 + ["PROOF"] * 3,
        )
        for item in correction["corrections"]:
            with self.subTest(file=item["file"], harness=item["harness"]):
                self.assertEqual(rows[(item["file"], item["harness"])]["expected"], item["after"])
                source = (REPO_ROOT / item["file"]).read_bytes()
                self.assertEqual(hashlib.sha256(source).hexdigest(), item["current_source_sha256_at_audit"])
                self.assertTrue(item["program_unchanged_except_full_line_comments"])

    def test_dead_pointer_negation_requires_proof_not_an_unsupported_memory_failure(self) -> None:
        evidence = json.loads(
            (PROGRESS_TOOLS / "memory-predicate-oracle-correction-2026-11-14.json").read_text()
        )
        item, = evidence["corrections"]
        row = next(row for row in self.artifact["rows"]
                   if (row["file"], row["harness"]) == (item["file"], item["harness"]))
        self.assertEqual(row["expected"], "PROOF")
        source = (REPO_ROOT / item["file"]).read_bytes()
        self.assertEqual(hashlib.sha256(source).hexdigest(), item["source_sha256"])
        self.assertIn(b"assert!(!can_dereference(raw_ptr))", source)
        expected = subprocess.check_output([
            "git", "show", evidence["fork_commit"] + ":" + item["expectation_file"]
        ], cwd=REPO_ROOT)
        self.assertEqual(hashlib.sha256(expected).hexdigest(), item["expectation_sha256"])
        self.assertIn(b"Kani does not support reasoning about pointer to unallocated memory", expected)
        sibling = next(row for row in self.artifact["rows"]
                       if row["file"] == item["file"] and row["harness"] == "check_invalid_array")
        self.assertEqual(sibling["expected"], "CTREX")

    def test_independent_prior_argument_is_not_a_contract_precondition(self) -> None:
        evidence = json.loads(
            (PROGRESS_TOOLS / "contract-prior-oracle-corrections-2026-11-14.json").read_text()
        )
        self.assertEqual(len(evidence["corrections"]), 2)
        rows = {(row["file"], row["harness"]): row for row in self.artifact["rows"]}
        for item in evidence["corrections"]:
            with self.subTest(file=item["file"]):
                self.assertEqual(rows[(item["file"], "modify_harness")]["expected"], "CTREX")
                self.assertEqual(rows[(item["file"], "main")]["expected"], "PROOF")
                source = (REPO_ROOT / item["file"]).read_bytes()
                self.assertEqual(hashlib.sha256(source).hexdigest(), item["source_sha256"])
                original = subprocess.check_output([
                    "git", "show", evidence["fork_commit"] + ":" + item["expectation_file"]
                ], cwd=REPO_ROOT)
                self.assertEqual(hashlib.sha256(original).hexdigest(), item["expectation_sha256"])
                self.assertIn(b"main.assertion", original)
                self.assertNotIn(b"modify_harness", original)

    def test_safe_niche_oracles_use_statuses_not_assertion_descriptions(self) -> None:
        evidence = json.loads(
            (PROGRESS_TOOLS / "niche-oracle-corrections-2026-11-14.json").read_text()
        )
        self.assertEqual(len(evidence["corrections"]), 2)
        rows = {(row["file"], row["harness"]): row for row in self.artifact["rows"]}
        for item in evidence["corrections"]:
            with self.subTest(file=item["file"]):
                self.assertEqual(rows[(item["file"], "main")]["expected"], "PROOF")
                for key, sha_key, blob_key in (
                    ("file", "source_sha256", "source_blob"),
                    ("expectation_file", "expectation_sha256", "expectation_blob"),
                ):
                    original = subprocess.check_output([
                        "git", "show", evidence["fork_commit"] + ":" + item[key]
                    ], cwd=REPO_ROOT)
                    self.assertEqual(original, (REPO_ROOT / item[key]).read_bytes())
                    self.assertEqual(hashlib.sha256(original).hexdigest(), item[sha_key])
                    blob = subprocess.check_output([
                        "git", "rev-parse", evidence["fork_commit"] + ":" + item[key]
                    ], cwd=REPO_ROOT, text=True).strip()
                    self.assertEqual(blob, item[blob_key])
                expected = (REPO_ROOT / item["expectation_file"]).read_text()
                statuses = [line.rstrip("\\") for line in expected.splitlines()
                            if line.rstrip("\\") in {"SUCCESS", "UNREACHABLE"}]
                self.assertEqual(statuses, item["expected_property_statuses"])
                self.assertIn("assertion failed:", expected)
                self.assertNotIn("FAILURE", expected)

    def test_remaining_oracles_bind_renames_and_preserve_negative_union_controls(self) -> None:
        evidence = json.loads(
            (PROGRESS_TOOLS / "remaining-oracle-corrections-2026-11-14.json").read_text()
        )
        self.assertEqual(len(evidence["corrections"]), 16)
        self.assertEqual(sorted(item["after"] for item in evidence["corrections"]),
                         ["CTREX"] * 5 + ["PROOF"] * 11)
        rows = {(row["file"], row["harness"]): row for row in self.artifact["rows"]}
        for item in evidence["corrections"]:
            with self.subTest(file=item["file"], harness=item["harness"]):
                self.assertEqual(rows[(item["file"], item["harness"])]["expected"], item["after"])
                spec = evidence["fork_commit"] + ":" + item["original_file"]
                original = subprocess.check_output(["git", "show", spec], cwd=REPO_ROOT)
                self.assertEqual(subprocess.check_output(
                    ["git", "rev-parse", spec], cwd=REPO_ROOT, text=True,
                ).strip(), item["source_blob"])
                self.assertEqual(hashlib.sha256(original).hexdigest(), item["source_sha256"])
                current = (REPO_ROOT / item["file"]).read_bytes()
                self.assertEqual(hashlib.sha256(current).hexdigest(), item["current_source_sha256"])
                relation = item["source_relation"]
                if relation == "byte-identical":
                    self.assertEqual(current, original)
                else:
                    self.assertIn(relation, {"comments-and-unused-binding-prefixes",
                                             "comments-and-stabilized-feature-attribute"})
                    def normalized(data):
                        text = re.sub(r"^\s*//.*\n?", "", data.decode(), flags=re.M)
                        if relation == "comments-and-unused-binding-prefixes":
                            text = re.sub(r"\b(?:padding|_padding)\b", "_padding", text)
                            text = re.sub(r"\b(?:non_padding|_non_padding)\b", "_non_padding", text)
                        else:
                            text = text.replace("#![feature(c_str_literals)]", "")
                        return re.sub(r"\s+", "", text)
                    self.assertEqual(normalized(current), normalized(original))
                if "expectation_file" in item:
                    expected_spec = evidence["fork_commit"] + ":" + item["expectation_file"]
                    expected = subprocess.check_output(["git", "show", expected_spec], cwd=REPO_ROOT)
                    self.assertEqual(hashlib.sha256(expected).hexdigest(), item["expectation_sha256"])
                    self.assertEqual(subprocess.check_output(
                        ["git", "rev-parse", expected_spec], cwd=REPO_ROOT, text=True,
                    ).strip(), item["expectation_blob"])
        self.assertEqual(len(evidence["preserved_controls"]), 5)
        for control in evidence["preserved_controls"]:
            self.assertEqual(rows[(control["file"], control["harness"])]["expected"], "PROOF")

    def test_upstream_inactive_authority_is_bound_to_the_fork_commit(self) -> None:
        """Exclusion is PROVED against the fork commit, not asserted from the tree."""
        authority = json.loads(
            (REPO_ROOT / "tests/trust-mc/replacement-upstream-inactive.json").read_text(
                encoding="utf-8"
            )
        )
        self.assertEqual(len(authority["rows"]), 32)
        self.assertTrue(authority["fork_commit"])
        # Every excluded row must be an upstream CBMC limitation, not our own.
        eligible = {
            "CBMC consumes more than 10 GB",
            "CBMC takes more than 15 minutes",
            "requires pthread_key_create",
            "requires memchr",
            "requires syscall",
            "requires write",
        }
        for row in authority["rows"]:
            self.assertIn(row["reason"], eligible)
            self.assertTrue(row["file"].startswith("tests/slow/tokio-proofs/"))

    def test_the_bar_narrows_but_the_denominator_does_not(self) -> None:
        summary = self.artifact["summary"]
        # 818 historical rows remain the authority; only the BAR moves.
        self.assertEqual(summary["historical_total"], 818)
        self.assertEqual(
            summary["proof"]["historical"] + summary["non_proof"]["historical"], 818
        )
        self.assertEqual(summary["proof"]["bar"], 453)
        self.assertEqual(summary["proof"]["upstream_inactive"], 32)
        self.assertEqual(summary["proof"]["local_inactive"], 0)
        self.assertEqual(len(self.artifact["rows"]), 818)

    def test_a_locally_disabled_proof_row_still_blocks_the_bar(self) -> None:
        """THE ANTI-CHEAT. Disabling a row of our own must never shrink the bar,
        even when its comment forges an upstream CBMC reason."""
        rows = [dict(row) for row in self.artifact["rows"]]
        victim = next(
            row
            for row in rows
            if row["expected"] == "PROOF" and row["disposition"] == "active"
        )
        victim.update(
            disposition="inactive",
            inactive_origin="local",
            reason="cfg-disabled",
            execution_credit=False,
            proof_credit=False,
        )
        summary = dispositions._subset_summary(rows, expected_proof=True, authority_digest="x")
        self.assertEqual(summary["local_inactive"], 1)
        self.assertEqual(summary["upstream_inactive"], 32)

    def test_an_upstream_row_that_is_activated_moves_into_the_bar(self) -> None:
        rows = [dict(row) for row in self.artifact["rows"]]
        freed = next(
            row
            for row in rows
            if row["disposition"] == "inactive"
            and row.get("inactive_origin") == "upstream"
        )
        freed.update(disposition="active", inactive_origin=None, execution_credit=True)
        summary = dispositions._subset_summary(rows, expected_proof=True, authority_digest="x")
        self.assertEqual(summary["bar"], 454)
        self.assertEqual(summary["upstream_inactive"], 31)
        self.assertEqual(summary["local_inactive"], 0)

    def test_active_proof_inventory_is_the_bar_and_parses_as_an_inventory(self) -> None:
        """The audit denominator is the BAR, so it needs the bar as an inventory."""
        inventory = dispositions.active_proof_inventory(self.artifact)
        summary = self.artifact["summary"]["proof"]
        self.assertEqual(inventory["suite"], "tests/trust-mc")
        self.assertEqual(inventory["denominator"], 453)
        self.assertEqual(len(inventory["rows"]), 453)
        self.assertEqual(inventory["row_sha256"], summary["active_inventory_row_sha256"])

        frozen = json.loads(
            dispositions.DEFAULT_PROOF_INVENTORY.read_text(encoding="utf-8")
        )
        frozen_keys = {(row["file"], row["harness"]) for row in frozen["rows"]}
        active_keys = {(row["file"], row["harness"]) for row in inventory["rows"]}
        self.assertTrue(active_keys < frozen_keys)
        self.assertEqual(len(frozen_keys - active_keys), 32)

        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "active-proof.json"
            path.write_text(dispositions._render(inventory), encoding="utf-8")
            _, rows = dispositions._validate_inventory(path)
        self.assertEqual(len(rows), 453)

    def test_every_inactive_row_is_source_bound_cfg_disabled_zero_credit(self) -> None:
        inactive = [
            row for row in self.artifact["rows"] if row["disposition"] == "inactive"
        ]
        self.assertEqual(len(inactive), 32)
        for row in inactive:
            self.assertEqual(row["expected"], "PROOF")
            self.assertEqual(row["reason"], "cfg-disabled-upstream")
            self.assertEqual(row["inactive_origin"], "upstream")
            self.assertIs(row["execution_credit"], False)
            self.assertIs(row["proof_credit"], False)
            source_line = (REPO_ROOT / row["file"]).read_text(encoding="utf-8").splitlines()[
                row["source_line"] - 1
            ]
            self.assertRegex(source_line, rf"\bfn\s+{row['harness']}\s*\(")

    def test_every_active_cargo_row_has_reachable_unique_qualified_identity(self) -> None:
        seen: set[tuple[str, str]] = set()
        active_cargo = [
            row
            for row in self.artifact["rows"]
            if row["disposition"] == "active" and row["executor"] == "cargo"
        ]
        self.assertEqual(len(active_cargo), 66)
        for row in active_cargo:
            modules = dispositions._cargo_module_path(
                REPO_ROOT / row["file"],
                REPO_ROOT / row["cargo_manifest"],
            )
            self.assertTrue(modules)
            prefix = "::".join(modules) + "::"
            self.assertTrue(row["driver_harness"].startswith(prefix), row)
            key = (row["cargo_dir"], row["driver_harness"])
            self.assertNotIn(key, seen)
            seen.add(key)
            defaults = dispositions._default_features(REPO_ROOT / row["cargo_manifest"])
            self.assertTrue(set(row.get("required_features", [])).issubset(defaults))

        sync_rows = [
            row
            for row in active_cargo
            if row["file"] == "tests/slow/tokio-proofs/src/tokio/sync_mpsc.rs"
        ]
        self.assertEqual(len(sync_rows), 16)
        self.assertTrue(
            all(row.get("required_features") == ["full"] for row in sync_rows)
        )

    def test_file_level_nondefault_feature_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            crate = root / "tests/demo"
            source = crate / "src/lib.rs"
            source.parent.mkdir(parents=True)
            source.write_text(
                '#![cfg(feature = "off")]\n#[kani::proof]\nfn check() {}\n',
                encoding="utf-8",
            )
            (crate / "Cargo.toml").write_text(
                '[package]\nname="demo"\nversion="0.1.0"\n[features]\ndefault=[]\n',
                encoding="utf-8",
            )
            (crate / "Cargo.lock").write_text(
                "# generated test lock\nversion = 4\n", encoding="utf-8"
            )
            with mock.patch.object(dispositions, "REPO_ROOT", root):
                with self.assertRaisesRegex(
                    dispositions.DispositionError,
                    "file-level cfg feature 'off' is not enabled by default",
                ):
                    dispositions._plan_row(
                        {
                            "file": "tests/demo/src/lib.rs",
                            "harness": "check",
                            "expected": "PROOF",
                            "lane": "tests/demo",
                        }
                    )

    def test_missing_cargo_lock_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            crate = root / "tests/demo"
            source = crate / "src/lib.rs"
            source.parent.mkdir(parents=True)
            source.write_text("#[kani::proof]\nfn check() {}\n", encoding="utf-8")
            (crate / "Cargo.toml").write_text(
                '[package]\nname="demo"\nversion="0.1.0"\n', encoding="utf-8"
            )
            with mock.patch.object(dispositions, "REPO_ROOT", root):
                with self.assertRaisesRegex(
                    dispositions.DispositionError, "missing Cargo.lock"
                ):
                    dispositions._plan_row(
                        {
                            "file": "tests/demo/src/lib.rs",
                            "harness": "check",
                            "expected": "PROOF",
                            "lane": "tests/demo",
                        }
                    )

    def test_disposition_help_and_check_are_read_only(self) -> None:
        path = dispositions.DEFAULT_OUTPUT
        before = hashlib.sha256(path.read_bytes()).hexdigest()
        help_run = subprocess.run(
            [sys.executable, str(SCRIPTS / "replacement_harness_dispositions.py"), "--help"],
            cwd=REPO_ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(help_run.returncode, 0, help_run.stderr)
        check_run = subprocess.run(
            [
                sys.executable,
                str(SCRIPTS / "replacement_harness_dispositions.py"),
                "--check",
            ],
            cwd=REPO_ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(check_run.returncode, 0, check_run.stderr)
        self.assertEqual(before, hashlib.sha256(path.read_bytes()).hexdigest())

    def test_unknown_and_ambiguous_source_changes_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            unknown = root / "tests/demo/unknown.rs"
            unknown.parent.mkdir(parents=True)
            unknown.write_text(
                '#[cfg(feature = "off")]\n#[kani::proof]\nfn check() {}\n',
                encoding="utf-8",
            )
            (unknown.parent / "Cargo.toml").write_text(
                '[package]\nname="demo"\nversion="0.1.0"\n[features]\ndefault=[]\n',
                encoding="utf-8",
            )
            ambiguous = root / "tests/demo/ambiguous.rs"
            ambiguous.write_text(
                "mod a { #[kani::proof]\nfn check() {} }\n"
                "mod b { #[kani::proof]\nfn check() {} }\n",
                encoding="utf-8",
            )
            with mock.patch.object(dispositions, "REPO_ROOT", root):
                with self.assertRaises(dispositions.DispositionError):
                    dispositions._plan_row(
                        {
                            "file": "tests/demo/unknown.rs",
                            "harness": "check",
                            "expected": "PROOF",
                            "lane": "tests/demo",
                        }
                    )
                with self.assertRaises(dispositions.DispositionError):
                    dispositions._plan_row(
                        {
                            "file": "tests/demo/ambiguous.rs",
                            "harness": "check",
                            "expected": "PROOF",
                            "lane": "tests/demo",
                        }
                    )

    def test_runtime_accounting_requires_exact_executed_and_inactive_rows(self) -> None:
        records = []
        for row in self.artifact["rows"]:
            if row["disposition"] == "active":
                records.append(
                    {
                        "schema_version": 2,
                        "file": row["file"],
                        "harness": row["harness"],
                        "verdict": row["expected"],
                        "status": "PASS",
                        "expected": row["expected"],
                        "metadata": {"execution": {"state": "complete"}},
                    }
                )
                covers = dispositions.cover_expectations(row)
                if covers is not None:
                    records[-1]["cover_properties"] = covers
            else:
                records.append(
                    {
                        "schema_version": 2,
                        "file": row["file"],
                        "harness": row["harness"],
                        "verdict": "SKIP",
                        "status": "SKIP",
                        "expected": row["expected"],
                        "metadata": {
                            "execution": {
                                "state": "inactive_accounted",
                                "details": row["reason"],
                            }
                        },
                    }
                )
        with tempfile.TemporaryDirectory() as raw:
            records_path = Path(raw) / "records.jsonl"
            records_path.write_text(
                "".join(json.dumps(record) + "\n" for record in records),
                encoding="utf-8",
            )
            runtime = dispositions.validate_runtime_records(self.artifact, records_path)
            self.assertEqual(runtime["historical_total"], 818)
            self.assertEqual(runtime["active_executed"], 786)
            self.assertEqual(runtime["inactive_accounted"], 32)
            self.assertEqual(runtime["proof"]["inactive_zero_credit"], 32)
            # The accounting carries the split, so a consumer can tell an
            # upstream-disabled row (outside the bar) from one of ours.
            self.assertEqual(runtime["proof"]["bar"], 453)
            self.assertEqual(runtime["proof"]["upstream_inactive"], 32)
            self.assertEqual(runtime["proof"]["local_inactive"], 0)
            self.assertEqual(runtime["non_proof"]["bar"], 333)
            self.assertEqual(runtime["non_proof"]["local_inactive"], 0)

            active_index = next(i for i, row in enumerate(self.artifact["rows"])
                                if row["disposition"] == "active")
            failed_records = json.loads(json.dumps(records))
            failed_records[active_index].update(verdict="ERROR", status="FAIL")
            failed_records[active_index]["metadata"]["execution"].update(state="identity_mismatch")
            records_path.write_text("".join(json.dumps(r) + "\n" for r in failed_records))
            failed_runtime = dispositions.validate_runtime_records(self.artifact, records_path)
            self.assertEqual(failed_runtime["active_identity_mismatch"], 1)
            self.assertEqual(failed_runtime["active_attempted"], 786)
            self.assertEqual(failed_runtime["active_completed"], 785)
            self.assertEqual(failed_runtime["execution_states"]["identity_mismatch"], 1)
            self.assertEqual(failed_runtime["historical_total"], 818)
            for invalid in ({"status": "PASS"}, {"verdict": "PROOF"}):
                bad = json.loads(json.dumps(failed_records))
                bad[active_index].update(invalid)
                records_path.write_text("".join(json.dumps(r) + "\n" for r in bad))
                with self.assertRaisesRegex(dispositions.DispositionError, "received verdict credit"):
                    dispositions.validate_runtime_records(self.artifact, records_path)

            inactive_index = next(
                index
                for index, row in enumerate(self.artifact["rows"])
                if row["disposition"] == "inactive"
            )
            cover_index = next(i for i, row in enumerate(records) if "cover_properties" in row)
            mutations = (
                lambda rows: rows[0].update(schema_version=1),
                lambda rows: rows[0].update(status="SKIP"),
                lambda rows: rows[0]["metadata"]["execution"].update(
                    state="inactive_accounted"
                ),
                lambda rows: rows[inactive_index]["metadata"]["execution"].update(
                    details="unbound-reason"
                ),
                lambda rows: rows[cover_index].pop("cover_properties"),
            )
            for mutate in mutations:
                bad_records = json.loads(json.dumps(records))
                mutate(bad_records)
                records_path.write_text(
                    "".join(json.dumps(record) + "\n" for record in bad_records),
                    encoding="utf-8",
                )
                with self.assertRaises(dispositions.DispositionError):
                    dispositions.validate_runtime_records(self.artifact, records_path)


class ClosureGeneratorTests(unittest.TestCase):
    def test_inventory_digest_drift_fails_closed(self) -> None:
        inventory = json.loads(closure_generator.INVENTORY_PATH.read_text(encoding="utf-8"))
        inventory["row_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "row_sha256 does not match rows"):
            closure_generator.build_closure(inventory, "inventory.json")

    def test_help_and_check_do_not_rewrite_closure(self) -> None:
        closure = closure_generator.OUTPUT_PATH
        before = hashlib.sha256(closure.read_bytes()).hexdigest()
        for args in (["--help"], ["--check"]):
            run = subprocess.run(
                [sys.executable, str(SCRIPTS / "generate_non_proof_closure.py"), *args],
                cwd=REPO_ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(run.returncode, 0, run.stderr)
        self.assertEqual(before, hashlib.sha256(closure.read_bytes()).hexdigest())

    def test_check_detects_drift_without_rewriting(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            output = Path(raw) / "closure.json"
            output.write_text("{}\n", encoding="utf-8")
            run = subprocess.run(
                [
                    sys.executable,
                    str(SCRIPTS / "generate_non_proof_closure.py"),
                    "--check",
                    "--output",
                    str(output),
                ],
                cwd=REPO_ROOT,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertNotEqual(run.returncode, 0)
            self.assertEqual(output.read_text(encoding="utf-8"), "{}\n")


class ReplacementPublicRunnerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.artifact = dispositions.build_dispositions(
            dispositions.DEFAULT_INVENTORY,
            dispositions.DEFAULT_PROOF_INVENTORY,
            dispositions.DEFAULT_NON_PROOF,
        )

    @staticmethod
    def _config(root: Path) -> public_runner.RunnerConfig:
        return public_runner.RunnerConfig(
            driver=Path("/tmp/trust-mc-driver"),
            solver="ay",
            timeout_seconds=60,
            report_dir=root,
            target_dir=root / "target",
        )

    def test_actual_exit_manifest_survives_final_validation_refusal(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            directory = Path(raw)
            driver = directory / "driver"
            driver.write_text("unused mocked driver")
            driver.chmod(0o755)
            args = public_runner.build_parser().parse_args([
                "--driver", str(driver), "--report-dir", str(directory),
            ])
            executed = [{"file": "input.rs", "harness": "check", "exit_code": 7,
                         "command": [str(driver), "input.rs"], "log": "captured.log"}]
            with (
                mock.patch.object(public_runner, "checked_disposition_report", return_value=self.artifact),
                mock.patch.object(public_runner, "clean_measurement_fingerprint", return_value="frozen"),
                mock.patch.object(public_runner, "solver_attestation", return_value={}),
                mock.patch.object(public_runner, "attest_driver_binary", return_value={}),
                mock.patch.object(public_runner, "execute_plan", return_value=([], [], executed)),
                mock.patch.object(public_runner, "validate_runtime",
                                  side_effect=dispositions.DispositionError("invalid row")),
            ):
                with self.assertRaisesRegex(dispositions.DispositionError, "invalid row"):
                    public_runner.run(args)
            manifest = json.loads((directory / public_runner.DEFAULT_RUN_MANIFEST.name).read_text())
            self.assertFalse(manifest["finalized"])
            self.assertEqual(manifest["runs"], executed)
            self.assertEqual(manifest["tree_fingerprint"], "frozen")
            self.assertFalse((directory / public_runner.DEFAULT_REPORT.name).exists())

    def test_failed_identity_attempt_writes_a_failed_report(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            directory = Path(raw)
            driver = directory / "driver"
            driver.write_text("unused mocked driver")
            driver.chmod(0o755)
            args = public_runner.build_parser().parse_args([
                "--driver", str(driver), "--report-dir", str(directory),
            ])
            row = {"file": "input.rs", "harness": "check", "verdict": "ERROR",
                   "status": "FAIL", "expected": "PROOF", "time_sec": 0.1,
                   "execution_state": "identity_mismatch"}
            runtime = {"historical_total": 1, "active_executed": 1, "inactive_accounted": 0,
                       "proof": {"bar": 1, "upstream_inactive": 0, "local_inactive": 0},
                       "non_proof": {"bar": 0, "local_inactive": 0}}
            report = {"tree_fingerprint": "frozen", "harnesses": [row]}
            with (
                mock.patch.object(public_runner, "checked_disposition_report", return_value=self.artifact),
                mock.patch.object(public_runner, "clean_measurement_fingerprint", return_value="frozen"),
                mock.patch.object(public_runner, "solver_attestation", return_value={}),
                mock.patch.object(public_runner, "attest_driver_binary", return_value={}),
                mock.patch.object(public_runner, "execute_plan", return_value=([row], [], [])),
                mock.patch.object(public_runner, "validate_runtime", return_value=runtime),
                mock.patch.object(public_runner, "build_report", return_value=report),
                mock.patch("builtins.print"),
            ):
                self.assertEqual(public_runner.run(args), 1)
            written = json.loads((directory / public_runner.DEFAULT_REPORT.name).read_text())
            self.assertEqual(written["harnesses"][0]["status"], "FAIL")
            self.assertEqual(written["harnesses"][0]["execution_state"], "identity_mismatch")
            manifest = json.loads((directory / public_runner.DEFAULT_RUN_MANIFEST.name).read_text())
            self.assertTrue(manifest["finalized"])

    def test_solver_attestation_accepts_only_the_pinned_build_commit(self) -> None:
        expected_pin = "0123456789abcdef0123456789abcdef01234567"
        with tempfile.TemporaryDirectory() as raw:
            solver = Path(raw) / "ay"
            solver.write_text(
                "#!/bin/sh\n"
                "printf '%s\\n' 'ay 0.19.0' "
                "'build.commit=0123456789abcdef0123456789abcdef01234567'\n",
                encoding="utf-8",
            )
            solver.chmod(0o755)
            with mock.patch.object(public_runner.shutil, "which", return_value=str(solver)):
                attestation = public_runner.solver_attestation("ay", expected_pin)

        self.assertEqual(attestation["path"], str(solver))
        self.assertEqual(attestation["commit"], expected_pin)

    def test_solver_attestation_rejects_a_different_or_unstamped_ay(self) -> None:
        expected_pin = "0123456789abcdef0123456789abcdef01234567"
        with tempfile.TemporaryDirectory() as raw:
            solver = Path(raw) / "ay"
            solver.write_text(
                "#!/bin/sh\n"
                "printf '%s\\n' 'ay 0.19.0' "
                "'build.commit=ffffffffffffffffffffffffffffffffffffffff'\n",
                encoding="utf-8",
            )
            solver.chmod(0o755)
            with mock.patch.object(public_runner.shutil, "which", return_value=str(solver)):
                with self.assertRaisesRegex(
                    public_runner.ReplacementRunError,
                    "does not match pinned AY",
                ):
                    public_runner.solver_attestation("ay", expected_pin)

            solver.write_text(
                "#!/bin/sh\nprintf '%s\\n' 'ay 0.19.0 without authority stamp'\n",
                encoding="utf-8",
            )
            with mock.patch.object(public_runner.shutil, "which", return_value=str(solver)):
                with self.assertRaisesRegex(
                    public_runner.ReplacementRunError,
                    "does not include a 7- to 40-character build commit",
                ):
                    public_runner.solver_attestation("ay", expected_pin)

    def test_invocations_preserve_current_driver_shapes_and_one_harness(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            config = self._config(Path(raw))
            drop = next(
                row
                for row in self.artifact["rows"]
                if row["file"] == "tests/expected/per-harness/drop.rs"
                and row["harness"] == "check_drop_bar"
            )
            direct = public_runner.build_invocation(drop, config, ordinal=1)
            self.assertEqual(direct.command.count("--harness"), 1)
            harness_index = direct.command.index("--harness")
            self.assertEqual(direct.command[harness_index + 1], "check_drop_bar")
            self.assertEqual(direct.command.count("--exact"), 1)
            self.assertEqual(direct.command[-1], str(REPO_ROOT / drop["file"]))
            self.assertEqual(direct.cwd, REPO_ROOT)
            output = Path(direct.command[direct.command.index("--target-dir") + 1])
            self.assertTrue(output.is_relative_to(config.target_dir))
            self.assertFalse(output.is_relative_to(REPO_ROOT / "tests"))
            sibling = {**drop, "harness": "another", "driver_harness": "another"}
            other = public_runner.build_invocation(sibling, config, ordinal=2)
            self.assertNotEqual(output, Path(other.command[other.command.index("--target-dir") + 1]))

            cargo_row = next(
                row
                for row in self.artifact["rows"]
                if row.get("resolution") == "cargo-default-feature"
            )
            cargo = public_runner.build_invocation(cargo_row, config, ordinal=2)
            self.assertEqual(cargo.command[1], "trust-mc")
            self.assertEqual(cargo.command.count("--locked"), 1)
            self.assertEqual(cargo.command.count("--harness"), 1)
            self.assertEqual(cargo.command.count("--exact"), 1)
            self.assertEqual(
                cargo.command[cargo.command.index("--harness") + 1],
                "tokio::sync_mpsc::recv_timeout",
            )
            self.assertEqual(cargo.cwd, REPO_ROOT / "tests/slow/tokio-proofs")
            self.assertIn("--target-dir", cargo.command)

    def test_forwarded_cbmc_tail_cannot_consume_input_or_target_paths(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            config = self._config(Path(raw))
            for path in (
                "tests/expected/function-contract/history/stub.rs",
                "tests/expected/function-contract/interior-mutability/whole-struct/refcell.rs",
                "tests/expected/loop-contract/multiple_loops.rs",
            ):
                row = next(row for row in self.artifact["rows"] if row["file"] == path)
                with self.subTest(path=path):
                    invocation = public_runner.build_invocation(row, config, ordinal=1)
                    forwarded = invocation.command.index("--cbmc-args")
                    self.assertLess(invocation.command.index(str(REPO_ROOT / path)), forwarded)
                    self.assertLess(invocation.command.index("--target-dir") + 1, forwarded)
                    self.assertEqual(invocation.command[forwarded + 1], "--object-bits")
                    self.assertEqual(len(invocation.command[forwarded:]), 3)
                    # Cargo has no positional source, but its target path must
                    # stay a driver option before the same forwarded tail.
                    cargo = public_runner.build_invocation(
                        {**row, "executor": "cargo", "cargo_dir": "tests/example"},
                        config, ordinal=2,
                    )
                    self.assertLess(cargo.command.index("--target-dir") + 1,
                                    cargo.command.index("--cbmc-args"))

    def test_dirty_pre_or_post_run_tree_fails_closed(self) -> None:
        with mock.patch.object(
            public_runner, "_current_tree_state", return_value="dirty"
        ):
            with self.assertRaisesRegex(
                public_runner.ReplacementRunError, "tree_state is 'dirty'"
            ):
                public_runner.clean_measurement_fingerprint("post-run")

    def test_modified_lock_is_measurement_tree_dirtiness(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            lock = root / "Cargo.lock"
            lock.write_text("version = 4\n", encoding="utf-8")
            commands = (
                ["git", "init", "--quiet"],
                ["git", "config", "user.email", "evidence@example.invalid"],
                ["git", "config", "user.name", "Evidence Test"],
                ["git", "add", "Cargo.lock"],
                ["git", "commit", "--quiet", "-m", "fixture"],
            )
            for command in commands:
                subprocess.run(command, cwd=root, check=True)
            self.assertEqual(report_contract._current_tree_state(root), "clean")
            lock.write_text("version = 4\n# drift\n", encoding="utf-8")
            self.assertEqual(report_contract._current_tree_state(root), "dirty")

    def test_marker_parser_does_not_invent_missing_proof_metadata(self) -> None:
        row = next(
            row
            for row in self.artifact["rows"]
            if row["disposition"] == "active" and row["expected"] == "PROOF"
        )
        clean, _ = public_runner.parse_driver_result(
            row,
            public_runner.ProcessResult(
                returncode=0,
                output=(
                    f"Checking harness {row['driver_harness']}...\n"
                    "[AY:SOUND_FALLBACK:0]\n"
                    "[AY:PROOF_QUALIFIERS:clean]\n"
                    "[AY:PROOF]\n"
                ),
                elapsed_seconds=0.125,
            ),
        )
        self.assertEqual(clean["status"], "PASS")
        self.assertEqual(clean["proof_qualifiers"], "clean")
        self.assertEqual(clean["execution_details"], "final_marker=PROOF")

        missing, _ = public_runner.parse_driver_result(
            row,
            public_runner.ProcessResult(
                returncode=0,
                output=f"Checking harness {row['driver_harness']}...\n[AY:PROOF]\n",
                elapsed_seconds=0.125,
            ),
        )
        self.assertEqual(missing["status"], "PASS")
        self.assertNotIn("proof_qualifiers", missing)
        failures = proof_gate.find_gate_failures(
            {
                **AyProofContractTests.clean_report(),
                "harnesses": [missing],
            },
            expected_ay_pin=AyProofContractTests.AY_PIN,
            expected_harnesses=1,
        )
        self.assertTrue(any("proof_qualifiers" in failure for failure in failures))

        no_verdict, _ = public_runner.parse_driver_result(
            row,
            public_runner.ProcessResult(
                returncode=0,
                output=(
                    f"Checking harness {row['driver_harness']}...\n"
                    "driver returned without an AY marker\n"
                ),
                elapsed_seconds=0.125,
            ),
        )
        self.assertEqual(no_verdict["verdict"], "ERROR")
        self.assertEqual(no_verdict["status"], "FAIL")
        self.assertEqual(no_verdict["execution_state"], "missing_verdict")

        wrong_harness, _ = public_runner.parse_driver_result(
            row,
            public_runner.ProcessResult(
                returncode=0,
                output="Checking harness some_other_harness...\n[AY:PROOF]\n",
                elapsed_seconds=0.125,
            ),
        )
        self.assertEqual(wrong_harness["status"], "FAIL")
        self.assertEqual(wrong_harness["execution_state"], "identity_mismatch")

    def test_expected_panic_keeps_its_checked_counterexample_outcome(self) -> None:
        row = next(
            row for row in self.artifact["rows"]
            if row["file"] == "tests/expected/derive-arbitrary/safety_constraint_helper/safety_constraint_helper.rs"
            and row["harness"] == "check_invariant_helper_fail"
        )
        self.assertEqual(row["expected"], "CTREX")
        output = (
            f"Checking harness {row['driver_harness']}...\n"
            "[AY:CTREX]\n[AY:CTREX_CAT:Genuine]\n"
            "[AY:EFFECTIVE_SUCCESS:should_panic_panics_only]\n"
        )
        result = public_runner.ProcessResult(0, output, 0.125)
        flat, runtime = public_runner.parse_driver_result(row, result)
        self.assertEqual((flat["verdict"], flat["status"]), ("CTREX", "PASS"))
        self.assertEqual((runtime["verdict"], runtime["status"]), ("CTREX", "PASS"))
        self.assertEqual(flat["effective_success"], "should_panic_panics_only")
        self.assertNotIn("trusted_proof", flat)

        # The exact same observation cannot prove a safety expectation.
        proof, _ = public_runner.parse_driver_result({**row, "expected": "PROOF"}, result)
        self.assertEqual((proof["verdict"], proof["status"]), ("CTREX", "FAIL"))
        self.assertNotIn("trusted_proof", proof)

        # Test-level success never replaces independent refutation evidence.
        for classification in ("OverApproximation", "Unknown", ""):
            with self.subTest(classification=classification):
                unqualified = output.replace(
                    "[AY:CTREX_CAT:Genuine]\n",
                    f"[AY:CTREX_CAT:{classification}]\n" if classification else "",
                )
                refused, _ = public_runner.parse_driver_result(
                    row, public_runner.ProcessResult(0, unqualified, 0.125)
                )
                self.assertEqual(refused["status"], "FAIL")

    def test_only_locally_disabled_rows_block_the_public_runner(self) -> None:
        """Upstream-disabled rows are outside the bar; ours still block it."""
        self.assertEqual(public_runner.locally_inactive_rows(self.artifact), [])
        rows = [dict(row) for row in self.artifact["rows"]]
        victim = next(
            row
            for row in rows
            if row["expected"] == "PROOF" and row["disposition"] == "active"
        )
        victim.update(
            disposition="inactive",
            inactive_origin="local",
            reason="cfg-disabled",
            execution_credit=False,
            proof_credit=False,
        )
        blocked = public_runner.locally_inactive_rows({"rows": rows})
        self.assertEqual(len(blocked), 1)
        self.assertEqual(blocked[0]["harness"], victim["harness"])

    def test_full_818_plan_accounts_every_row_and_credits_only_the_bar(self) -> None:
        invocations: list[tuple[dict[str, object], public_runner.Invocation]] = []

        def fake_process(
            row: dict[str, object],
            invocation: public_runner.Invocation,
            _config: public_runner.RunnerConfig,
        ) -> public_runner.ProcessResult:
            invocations.append((row, invocation))
            if row["expected"] == "PROOF":
                output = (
                    f"Checking harness {row['driver_harness']}...\n"
                    "[AY:PROOF_QUALIFIERS:clean]\n[AY:PROOF]\n"
                )
                return_code = 0
            else:
                output = (
                    f"Checking harness {row['driver_harness']}...\n"
                    "[AY:CTREX_CAT:Genuine]\n[AY:CTREX]\n"
                )
                return_code = 1
            covers = dispositions.cover_expectations(row)
            if covers is not None:
                output += cover_output(covers)
            return public_runner.ProcessResult(
                returncode=return_code,
                output=output,
                elapsed_seconds=0.001,
            )

        with tempfile.TemporaryDirectory() as raw:
            config = self._config(Path(raw))
            with mock.patch("builtins.print"):
                rows, runtime_records, runs = public_runner.execute_plan(
                    self.artifact,
                    config,
                    process_runner=fake_process,
                )
            runtime = public_runner.validate_runtime(self.artifact, runtime_records)

        self.assertEqual(len(rows), 818)
        self.assertEqual(len(invocations), 786)
        self.assertEqual(len(runs), 786)
        self.assertEqual(runtime["historical_total"], 818)
        self.assertEqual(runtime["active_executed"], 786)
        self.assertEqual(runtime["inactive_accounted"], 32)
        self.assertEqual(runtime["proof"]["inactive_zero_credit"], 32)
        self.assertEqual(sum(row["status"] == "PASS" for row in rows), 786)
        self.assertEqual(sum(row["status"] == "SKIP" for row in rows), 32)
        self.assertEqual(
            sum(row["executor"] == "cargo" for row, _ in invocations),
            66,
        )
        self.assertEqual(
            sum(row["executor"] == "single-file" for row, _ in invocations),
            720,
        )

    def test_clean_runner_cli_keeps_existing_options(self) -> None:
        help_run = subprocess.run(
            ["bash", str(SCRIPTS / "ay-compiletest.sh"), "--help"],
            cwd=REPO_ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(help_run.returncode, 0, help_run.stderr)
        for option in (
            "--mode MODE",
            "--timeout SECS",
            "--filter NAME",
            "--force-rerun",
            "--chc",
            "--skip-build",
            "--replacement-public",
            "--self-test",
        ):
            self.assertIn(option, help_run.stdout)

        bad_run = subprocess.run(
            ["bash", str(SCRIPTS / "ay-compiletest.sh"), "--not-an-option"],
            cwd=REPO_ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(bad_run.returncode, 2)
        self.assertIn("unknown option", bad_run.stderr)


class ReplacementProofExtractionTests(unittest.TestCase):
    """The proof-only packet holds the BAR and still accounts for the rest."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.artifact = dispositions.build_dispositions(
            dispositions.DEFAULT_INVENTORY,
            dispositions.DEFAULT_PROOF_INVENTORY,
            dispositions.DEFAULT_NON_PROOF,
        )
        cls.inventory = json.loads(
            dispositions.DEFAULT_PROOF_INVENTORY.read_text(encoding="utf-8")
        )

    @staticmethod
    def _source_report(artifact: dict[str, object]) -> dict[str, object]:
        """A clean 818-row run: every active row passes, the 32 stay SKIP."""
        harnesses = []
        for row in artifact["rows"]:
            base = {
                "file": row["file"],
                "harness": row["harness"],
                "expected": row["expected"],
                "sound_fallback_count": 0,
                "translation_drop_reasons": {},
            }
            if row["disposition"] == "inactive":
                base.update(
                    verdict="SKIP",
                    status="SKIP",
                    execution_state="inactive_accounted",
                    execution_details=row["reason"],
                )
            elif row["expected"] == "PROOF":
                base.update(
                    verdict="PROOF",
                    status="PASS",
                    execution_state="complete",
                    execution_details="final_marker=PROOF",
                    proof_qualifiers="clean",
                    trusted_proof=True,
                )
            else:
                verdict = "BMC" if row["expected"] == "BMC_SAFE" else row["expected"]
                base.update(
                    verdict=verdict,
                    status="PASS",
                    execution_state="complete",
                    execution_details=f"final_marker={verdict}",
                )
            covers = dispositions.cover_expectations(row)
            if covers is not None:
                base["cover_properties"] = covers
            harnesses.append(base)
        return {"schema_version": 2, "harnesses": harnesses}

    def _derive(
        self,
        report: dict[str, object] | None = None,
        artifact: dict[str, object] | None = None,
    ) -> dict[str, object]:
        return proof_extractor.derive_proof_report(
            report if report is not None else self._source_report(self.artifact),
            self.inventory,
            artifact if artifact is not None else self.artifact,
        )

    def test_cover_proof_extraction_rejects_missing_or_wrong_property_evidence(self) -> None:
        for replacement in (None, [], [{"description": "cover property 0", "status": "SATISFIED"}]):
            report = self._source_report(self.artifact)
            row = next(r for r in report["harnesses"] if r["harness"] == "cover_unreachable")
            row["cover_properties"] = replacement
            with self.assertRaisesRegex(ValueError, "cover properties"):
                self._derive(report)

    def test_proof_report_is_the_bar_and_records_the_excluded_rows(self) -> None:
        proof_report = self._derive()
        self.assertEqual(len(proof_report["harnesses"]), 453)
        self.assertEqual(proof_report["summary"]["total"], 453)
        self.assertEqual(proof_report["summary"]["proof"], 453)
        self.assertEqual(proof_report["summary"]["skip"], 0)

        bar = proof_report["replacement_bar"]
        self.assertEqual(bar["historical"], 485)
        self.assertEqual(bar["bar"], 453)
        self.assertEqual(bar["upstream_inactive_zero_credit"], 32)
        self.assertEqual(bar["local_inactive"], 0)
        self.assertEqual(len(bar["upstream_inactive_rows"]), 32)
        self.assertEqual(sum(bar["supersession_candidates"].values()), 32)
        self.assertEqual(
            bar["active_inventory_row_sha256"],
            dispositions.active_proof_inventory(self.artifact)["row_sha256"],
        )
        # 485 = 453 credited + 32 named-but-uncredited. Nothing vanished.
        credited = {
            (row["file"], row["harness"]) for row in proof_report["harnesses"]
        }
        excluded = {
            (row["file"], row["harness"]) for row in bar["upstream_inactive_rows"]
        }
        frozen = {(row["file"], row["harness"]) for row in self.inventory["rows"]}
        self.assertEqual(credited | excluded, frozen)
        self.assertEqual(credited & excluded, set())

    def test_a_missing_upstream_inactive_row_fails_closed(self) -> None:
        report = self._source_report(self.artifact)
        report["harnesses"] = [
            row for row in report["harnesses"] if row["status"] != "SKIP"
        ][:]
        with self.assertRaisesRegex(ValueError, "missing upstream-inactive harness"):
            self._derive(report)

    def test_an_upstream_inactive_row_claiming_credit_fails_closed(self) -> None:
        for mutation in (
            {"status": "PASS", "verdict": "PROOF"},
            {"execution_state": "complete"},
            {"execution_details": "cfg-disabled"},
            {"trusted_proof": True},
            {"sound_fallback_count": 1},
        ):
            report = self._source_report(self.artifact)
            skipped = next(row for row in report["harnesses"] if row["status"] == "SKIP")
            skipped.update(mutation)
            with self.assertRaises(ValueError):
                self._derive(report)

    def test_a_locally_disabled_proof_row_stays_inside_the_bar(self) -> None:
        artifact = json.loads(json.dumps(self.artifact))
        victim = next(
            row
            for row in artifact["rows"]
            if row["expected"] == "PROOF" and row["disposition"] == "active"
        )
        victim.update(
            disposition="inactive",
            inactive_origin="local",
            reason="cfg-disabled",
            execution_credit=False,
            proof_credit=False,
        )
        with self.assertRaisesRegex(ValueError, "LOCALLY-disabled PROOF row"):
            self._derive(self._source_report(artifact), artifact)

    def test_activating_an_upstream_row_pulls_it_back_into_the_bar(self) -> None:
        artifact = json.loads(json.dumps(self.artifact))
        freed = next(
            row
            for row in artifact["rows"]
            if row["disposition"] == "inactive"
            and row.get("inactive_origin") == "upstream"
        )
        report = self._source_report(artifact)
        freed.update(disposition="active", inactive_origin=None, execution_credit=True)
        summary = artifact["summary"]["proof"]
        summary.update(bar=454, upstream_inactive=31, inactive_zero_credit=31)
        # The row is demanded now, and the run that skipped it is not evidence.
        with self.assertRaisesRegex(ValueError, "is not PASS/PROOF"):
            self._derive(report, artifact)

    def test_an_inventory_that_is_not_the_bound_authority_fails_closed(self) -> None:
        inventory = json.loads(json.dumps(self.inventory))
        inventory["row_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "source-bound proof authority"):
            proof_extractor.derive_proof_report(
                self._source_report(self.artifact), inventory, self.artifact
            )

    def test_extractor_rejects_a_stale_disposition_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            stale = Path(raw) / "dispositions.json"
            stale.write_text("{}\n", encoding="utf-8")
            with mock.patch.object(dispositions, "DEFAULT_OUTPUT", stale):
                with self.assertRaisesRegex(ValueError, "dispositions are stale"):
                    proof_extractor.checked_dispositions()


class ReplacementProgressSchemaV2Tests(unittest.TestCase):
    @staticmethod
    def _row(
        file_name: str,
        harness: str,
        expected: str,
        verdict: str,
        *,
        status: str = "PASS",
        execution_state: str = "complete",
    ) -> dict[str, object]:
        row: dict[str, object] = {
            "file": file_name,
            "harness": harness,
            "expected": expected,
            "verdict": verdict,
            "status": status,
            "execution_state": execution_state,
            "sound_fallback_count": 0,
        }
        if verdict == "PROOF":
            row["proof_qualifiers"] = "clean"
            row["trusted_proof"] = True
        return row

    def test_schema_v2_verdicts_and_zero_credit_skip_are_not_misclassified(self) -> None:
        inventory = {
            "suite": "tests/trust-mc",
            "denominator": 3,
            "rows": [
                {
                    "file": "tests/a.rs",
                    "harness": "same",
                    "expected": "PROOF",
                    "lane": "a",
                },
                {
                    "file": "tests/b.rs",
                    "harness": "same",
                    "expected": "CTREX",
                    "lane": "b",
                },
                {
                    "file": "tests/c.rs",
                    "harness": "disabled",
                    "expected": "PROOF",
                    "lane": "c",
                },
            ],
        }
        report = {
            "schema_version": 2,
            "harnesses": [
                self._row("tests/a.rs", "same", "PROOF", "PROOF"),
                self._row("tests/b.rs", "same", "CTREX", "CTREX"),
                self._row(
                    "tests/c.rs",
                    "disabled",
                    "PROOF",
                    "SKIP",
                    status="SKIP",
                    execution_state="inactive_accounted",
                ),
            ],
        }
        observed, kind = replacement_progress.parse_report(report)
        progress = replacement_progress.compute_progress(inventory, observed)
        self.assertEqual(kind, "ay-compiletest")
        self.assertEqual(progress.proof_proven, 1)
        self.assertEqual(progress.nonproof_closed, 1)
        self.assertEqual(progress.proof_regressed, 1)
        self.assertEqual(progress.rows[-1].actual, "INACTIVE")
        self.assertFalse(progress.complete)

    def test_schema_v2_missing_clean_qualifier_receives_no_proof_credit(self) -> None:
        inventory = {
            "suite": "tests/trust-mc",
            "denominator": 1,
            "rows": [
                {
                    "file": "tests/a.rs",
                    "harness": "proof",
                    "expected": "PROOF",
                    "lane": "a",
                }
            ],
        }
        row = self._row("tests/a.rs", "proof", "PROOF", "PROOF")
        row.pop("proof_qualifiers")
        observed, _ = replacement_progress.parse_report({"harnesses": [row]})
        progress = replacement_progress.compute_progress(inventory, observed)
        self.assertEqual(progress.proof_proven, 0)
        self.assertEqual(progress.proof_regressed, 1)


class CanonicalAuthoritySurfaceTests(unittest.TestCase):
    def test_active_authority_paths_do_not_reference_deleted_inventory(self) -> None:
        active_files = (
            "ay-replacement-proof.sh",
            "ay_compiletest_report_authority.sh",
            "compiletest_report_contract.py",
            "compiletest_report_paths.py",
            "driver_binary_attestation.py",
            "direct_driver_proof_core.py",
            "direct_driver_proof_report.py",
            "extract_replacement_proof_report.py",
        )
        for name in active_files:
            text = (SCRIPTS / name).read_text(encoding="utf-8")
            self.assertNotIn("replacement-proof-inventory.json", text, name)
            self.assertNotIn("generate_trust-mc_harness_inventory.py", text, name)

    def test_strict_proof_checks_source_dispositions_and_inactive_credit(self) -> None:
        script = (SCRIPTS / "ay-replacement-proof.sh").read_text(encoding="utf-8")
        self.assertIn("replacement_harness_dispositions.py", script)
        # The gate keys on LOCALLY-disabled rows. Upstream-disabled rows are
        # outside the bar; ours still block it.
        self.assertIn(".summary.proof.local_inactive", script)
        self.assertIn("upstream-disabled rows are excluded from the bar", script)
        self.assertIn("LOCALLY-disabled PROOF rows", script)
        self.assertIn("supersession candidates", script)
        # The report denominator is the BAR, checked against the ACTIVE proof
        # inventory derived from the same checked plan; the frozen 485-row
        # authority is still asserted separately.
        self.assertIn("--emit-active-proof-inventory", script)
        self.assertIn("require_report_replacement_bar", script)
        self.assertIn('--expected-harnesses "$PROOF_BAR"', script)
        self.assertIn('--inventory "$ACTIVE_PROOF_INVENTORY"', script)
        self.assertIn('--expected-inventory-sha "$ACTIVE_PROOF_INVENTORY_SHA"', script)

    def test_legacy_local_generator_cannot_validate_public_proof_inventory(self) -> None:
        run = subprocess.run(
            [
                sys.executable,
                str(SCRIPTS / "generate_trust-mc_harness_inventory.py"),
                "--expectation-filter",
                "PROOF",
                "--check",
                str(dispositions.DEFAULT_PROOF_INVENTORY),
            ],
            cwd=REPO_ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertNotEqual(run.returncode, 0)

    def test_direct_driver_accepts_canonical_public_test_paths(self) -> None:
        canonical = "tests/expected/MemPredicates/adt_with_metadata.rs"
        self.assertTrue(direct_core._looks_like_test_file(canonical))
        self.assertEqual(
            direct_core._normalize_file(
                str(REPO_ROOT / canonical),
                repo_root=REPO_ROOT,
                label="test",
            ),
            canonical,
        )


class AyProofContractTests(unittest.TestCase):
    AY_PIN = "0123456789abcdef0123456789abcdef01234567"

    @classmethod
    def clean_report(cls) -> dict[str, object]:
        commit = "89abcdef0123456789abcdef0123456789abcdef"
        return {
            "schema_version": 2,
            "commit": commit,
            "ay_pin": cls.AY_PIN,
            "tree_state": "clean",
            "tree_fingerprint": "f" * 64,
            "solver": "ay",
            "replacement_evidence": True,
            "solver_binary": {
                "name": "ay",
                "path": "/tmp/ay",
                "version": f"ay {cls.AY_PIN}",
                "commit": cls.AY_PIN[:12],
            },
            "driver_binary": {
                "name": "trust-mc-driver",
                "path": "/tmp/trust-mc-driver",
                "sha256": "a" * 64,
                "version": "0.2.0",
                "invocation": "standalone",
                "trust_mc_sha": commit,
                "trust_mc_dirty": False,
                "ay_version": "0.13.0",
                "ay_pin": cls.AY_PIN,
                "ay_linked_sha": cls.AY_PIN,
                "ay_linked_dirty": False,
                "ay_authority": "matched",
            },
            "summary": {
                "total": 1,
                "proof": 1,
                "execution_complete": 1,
                "ctrex": 0,
                "unknown": 0,
                "error": 0,
                "bmc": 0,
                "xfail": 0,
                "skip": 0,
                "execution_gated": 0,
                "proof_breakdown": {
                    "clean": 1,
                    "should_panic": 0,
                    "crosschecked": 0,
                    "sound_qualified": 0,
                    "mem_overapprox_qualified": 0,
                },
            },
            "harnesses": [
                {
                    "file": "tests/demo.rs",
                    "harness": "proof",
                    "status": "PASS",
                    "expected": "PROOF",
                    "verdict": "PROOF",
                    "execution_state": "complete",
                    "execution_details": "final_marker=PROOF",
                    "sound_fallback_count": 0,
                    "proof_qualifiers": "clean",
                }
            ],
        }

    def test_schema_v2_contract_accepts_ay_report_without_head_authority(self) -> None:
        report = self.clean_report()
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "report.json"
            path.write_text(json.dumps(report), encoding="utf-8")
            loaded = report_contract.load_schema_v2_report(
                path,
                repo_root=REPO_ROOT,
                require_current_head=False,
            )
        self.assertEqual(loaded["solver"], "ay")
        self.assertEqual(loaded["ay_pin"], self.AY_PIN)

    def test_zero_fallback_gate_accepts_clean_ay_attestation(self) -> None:
        failures = proof_gate.find_gate_failures(
            self.clean_report(),
            expected_ay_pin=self.AY_PIN,
            expected_harnesses=1,
        )
        self.assertEqual(failures, [])

    def test_zero_fallback_gate_rejects_legacy_z4_attestation(self) -> None:
        report = self.clean_report()
        report["solver"] = "z4"
        report["z4_pin"] = report.pop("ay_pin")
        solver_binary = report["solver_binary"]
        assert isinstance(solver_binary, dict)
        solver_binary["name"] = "z4"
        failures = proof_gate.find_gate_failures(
            report,
            expected_ay_pin=self.AY_PIN,
            expected_harnesses=1,
        )
        self.assertTrue(any("solver 'z4' != 'ay'" in failure for failure in failures))
        self.assertTrue(any("report ay_pin" in failure for failure in failures))
        self.assertTrue(any("solver_binary.name 'z4'" in failure for failure in failures))

    def test_zero_fallback_gate_rejects_missing_driver_attestation(self) -> None:
        report = self.clean_report()
        report.pop("driver_binary")
        failures = proof_gate.find_gate_failures(
            report,
            expected_ay_pin=self.AY_PIN,
            expected_harnesses=1,
        )
        self.assertIn(
            "driver_binary attestation is missing or not an object",
            failures,
        )

    def test_zero_fallback_cli_accepts_expected_ay_pin(self) -> None:
        args = proof_gate.parse_args(
            [
                "--expected-ay-pin",
                self.AY_PIN,
                "--expected-harnesses",
                "1",
                "report.json",
            ]
        )
        self.assertEqual(args.expected_ay_pin, self.AY_PIN)
        self.assertEqual(args.expected_harnesses, 1)


if __name__ == "__main__":
    unittest.main()
