# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

from __future__ import annotations

import hashlib
import json
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
import generate_non_proof_closure as closure_generator
import replacement_harness_dispositions as dispositions
import replacement_public_runner as public_runner
import replacement_progress
import zero_fallback_proof_gate as proof_gate


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
                "cfg-disabled": 32,
                "exact": 740,
                "unique-qualified-alias": 45,
            },
        )
        self.assertEqual(summary["proof"]["historical"], 504)
        self.assertEqual(summary["proof"]["active"], 472)
        self.assertEqual(summary["proof"]["inactive_zero_credit"], 32)
        self.assertEqual(summary["non_proof"]["historical"], 314)
        self.assertEqual(summary["non_proof"]["active"], 314)
        self.assertEqual(summary["non_proof"]["inactive_zero_credit"], 0)
        self.assertEqual(
            sum(row["executor"] == "cargo" for row in self.artifact["rows"]),
            98,
        )

    def test_every_inactive_row_is_source_bound_cfg_disabled_zero_credit(self) -> None:
        inactive = [
            row for row in self.artifact["rows"] if row["disposition"] == "inactive"
        ]
        self.assertEqual(len(inactive), 32)
        for row in inactive:
            self.assertEqual(row["expected"], "PROOF")
            self.assertEqual(row["reason"], "cfg-disabled")
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
                                "details": "cfg-disabled",
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

            inactive_index = next(
                index
                for index, row in enumerate(self.artifact["rows"])
                if row["disposition"] == "inactive"
            )
            mutations = (
                lambda rows: rows[0].update(schema_version=1),
                lambda rows: rows[0].update(status="SKIP"),
                lambda rows: rows[0]["metadata"]["execution"].update(
                    state="inactive_accounted"
                ),
                lambda rows: rows[inactive_index]["metadata"]["execution"].update(
                    details="unbound-reason"
                ),
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

    def test_full_818_plan_accounts_every_row_and_keeps_inactive_proof_red(self) -> None:
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
        self.assertIn(".summary.proof.inactive_zero_credit", script)
        self.assertIn("source-inactive PROOF rows with zero credit", script)

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
