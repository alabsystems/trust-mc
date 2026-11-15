#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Unit tests for scripts/landing-gate.py and the dual gate's reuse: the cache
keys hold their complete input set, the leg inputs agree with the selector,
and the side-by-side judgment is at least as strict as the by-hand landing
convention it automates.

Tests read the modules under test from ``gate_mod`` / ``dual_mod``;
scripts/test_landing_mutants.py re-runs them against mutated copies."""

from __future__ import annotations

import importlib.util
import hashlib
import json
import subprocess
import tempfile
from unittest import mock
import argparse
import contextlib
import io
import os
import signal
import sys
import time
import unittest
from pathlib import Path
from types import SimpleNamespace

from python_executable import python_executable_header

SCRIPTS = Path(__file__).resolve().parent


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


landing_gate = load("landing_gate", SCRIPTS / "landing-gate.py")
dual_gate = sys.modules["soundness_dual_gate"]
sys.path.insert(0, str(SCRIPTS))
import test_landing_select as tls  # noqa: E402


def row(path="a.rs", harness="h", lane="chc", cls="match", known_red=False, known_red_class=None):
    return {"path": path, "harness": harness, "lane": lane, "class": cls, "known_red": known_red,
            "known_red_class": known_red_class, "evidence": "E-1" if known_red else None}


class ToolchainIdentity(unittest.TestCase):
    def test_the_gate_identifies_the_resolved_compiler_without_an_ay_source(self):
        # 81233a557 gave ay_cli_build_identity.identify an AY source and pin;
        # the gate's call kept four arguments, so every run ended in a
        # TypeError before its first leg. The gate keys reuse on the compiler
        # alone (compiler_identity): run its own resolution against a seal.
        with tempfile.TemporaryDirectory(prefix="landing-toolchain-") as directory:
            root = Path(directory).resolve()
            seal, scripts, repo = root / "seal", root / "scripts", root / "repo"
            for path in (seal / "bin", seal / "lib", scripts, repo):
                path.mkdir(parents=True)
            trustc = seal / "bin" / "trustc"
            trustc.write_text(
                "#!/bin/sh\ncase \"$*\" in\n"
                "  -vV) printf 'trustc fixture\\ncommit-hash: c\\n' ;;\n"
                f"  '--print sysroot') printf '%s\\n' '{seal}' ;;\n"
                "  *) exit 2 ;;\nesac\n"
            )
            (seal / "bin" / "targo").write_text("targo\n")
            (seal / "lib" / "librustc_driver-fixture.dylib").write_text("driver\n")
            resolver = scripts / "resolve-trust-tool.sh"
            resolver.write_text(
                "#!/bin/sh\ncase \"$1\" in\n"
                f"  sysroot) printf '%s\\n' '{seal}' ;;\n"
                f"  *) printf '%s\\n' '{seal}/bin/'\"$1\" ;;\n"
                "esac\n"
            )
            for path in (trustc, resolver):
                path.chmod(0o755)
            with mock.patch.object(landing_gate, "SCRIPTS_DIR", scripts):
                toolchain = landing_gate.toolchain_identity(repo)
            self.assertEqual(toolchain["sysroot"], str(seal))
            self.assertEqual(toolchain["trustc_vV_sha256"],
                             hashlib.sha256(b"trustc fixture\ncommit-hash: c\n").hexdigest())
            self.assertEqual(toolchain["artifact_driver_name"], "librustc_driver-fixture.dylib")
            self.assertNotIn("build_policy", toolchain)


class PinnedAyCompilerCache(unittest.TestCase):
    def test_baseline_and_candidate_helpers_receive_the_same_compiler_namespace(self):
        with tempfile.TemporaryDirectory() as tmp:
            runner = object.__new__(landing_gate.Runner)
            runner.logs = Path(tmp)
            runner.build_jobs = lambda _label: "1"
            first = {"sysroot": "/seal/9192", "trustc_vV_sha256": "old"}
            runner.state = {"toolchain": first}
            runner.targo = lambda: runner.state["toolchain"]["sysroot"] + "/bin/targo"
            calls = []

            @contextlib.contextmanager
            def capture(argv, **kwargs):
                env = kwargs["env"]
                self.assertEqual(env["TRUST_MC_TARGO"], runner.targo())
                self.assertEqual(env["RUSTC"],
                                 runner.state["toolchain"]["sysroot"] + "/bin/trustc")
                self.assertNotIn("RUSTC_WORKSPACE_WRAPPER", env)
                calls.append(env["TRUST_MC_AY_CLI_CACHE_ROOT"])
                yield SimpleNamespace(returncode=0,
                                      communicate=lambda: (b"/fake/release/ay\n", None))

            with mock.patch.dict(landing_gate.os.environ,
                                 {"TRUST_MC_AY_CLI_CACHE_ROOT": "/cache",
                                  "TRUST_MC_TARGO": "/foreign/targo",
                                  "RUSTC": "/foreign/trustc",
                                  "RUSTC_WORKSPACE_WRAPPER": "/foreign/wrapper"}, clear=True):
                with mock.patch.object(landing_gate, "_owned_process", side_effect=capture):
                    runner.pinned_ay_cli(Path("/baseline"), "baseline")
                    runner.pinned_ay_cli(Path("/candidate"), "candidate")
                    runner.state["toolchain"] = {
                        "sysroot": "/seal/15698", "trustc_vV_sha256": "new"}
                    runner.pinned_ay_cli(Path("/candidate"), "another-compiler")
            expected = "/cache/compiler-" + landing_gate.sha256_text(json.dumps(first, sort_keys=True))
            self.assertEqual(calls[:2], [expected, expected])
            self.assertNotEqual(calls[2], expected)


class MainReportCompilerBinding(unittest.TestCase):
    def fixture(self, *, no_reuse=False):
        from types import SimpleNamespace
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        (root / "ay").write_bytes(b"compiled AY")
        runner = object.__new__(landing_gate.Runner)
        runner.args = SimpleNamespace(no_reuse=no_reuse)
        runner.state = {"toolchain": {"sysroot": "/seal", "artifact_driver_sha256": "D"}}
        runner.ensure_main_tree = mock.Mock(return_value=Path("/baseline"))
        runner.pinned_ay_cli = mock.Mock(return_value=root)
        runner.ensure_bundle = mock.Mock(side_effect=RuntimeError("recompute"))
        identity = {"protocol": getattr(landing_gate, "AY_BUILD_PROTOCOL",
                                              "trust-mc.ay-compiler-bound/v1"),
                    "toolchain": runner.state["toolchain"],
                    "ay_binary_sha256": hashlib.sha256((root / "ay").read_bytes()).hexdigest()}
        return runner, root / "main.json", identity

    def test_legacy_unbound_budget_independent_report_is_not_reused(self):
        runner, report, _ = self.fixture()
        report.write_text(json.dumps({"schema": dual_gate.REPORT_SCHEMA,
                                     "runs": [{"budget_bound": False}],
                                     "provenance": {"ay": {"version": "ay same pin"}}}))
        with self.assertRaisesRegex(RuntimeError, "recompute"):
            runner.main_side_own_tree("chc", report)
        runner.pinned_ay_cli.assert_called_once()

    def test_bound_report_checks_current_ay_bytes_before_reuse(self):
        runner, report, identity = self.fixture()
        data = {"ay_execution": identity, "runs": [{"budget_bound": False}]}
        report.write_text(json.dumps(data))
        self.assertEqual(runner.main_side_own_tree("chc", report), (0, data))
        runner.pinned_ay_cli.assert_called_once()
        (report.parent / "ay").write_bytes(b"changed AY bytes")
        with self.assertRaisesRegex(RuntimeError, "recompute"):
            runner.main_side_own_tree("chc", report)

    def test_no_reuse_recomputes_even_a_current_bound_report(self):
        runner, report, identity = self.fixture(no_reuse=True)
        report.write_text(json.dumps({"ay_execution": identity, "runs": [{"budget_bound": False}]}))
        with self.assertRaisesRegex(RuntimeError, "recompute"):
            runner.main_side_own_tree("chc", report)

    def test_no_reuse_disables_same_identity_main_and_branch_entry_reads(self):
        from types import SimpleNamespace
        runner, report, _ = self.fixture(no_reuse=True)
        root = report.parent
        runner.repo = root
        runner.cache = root / "cache"
        runner.out_dir = root / "out"
        runner.args = SimpleNamespace(no_reuse=True, main_tree=root / "main")
        runner.state.update(main_bundle_identity="same", branch_bundle_identity="same",
                            dirty=False, main_pins={"ay": "A"}, head_pins={"ay": "A"})
        runner.ensure_bundle = mock.Mock(return_value=root / "bundle")
        calls = []

        def fresh_report(*args, **kwargs):
            self.assertFalse(kwargs.get("cache_only", False))
            calls.append(kwargs)
            return 0, {"rows": [], "summary": {"per_lane": {"chc": {}}}}

        runner.dual_report = fresh_report
        runner.run_dual("dual-chc")
        self.assertEqual(len(calls), 2)

    def test_no_reuse_does_not_pass_entry_cache_to_dual_process(self):
        from types import SimpleNamespace
        runner, report, _ = self.fixture(no_reuse=True)
        runner.args = SimpleNamespace(no_reuse=True, harness_timeout=30)
        runner.ensure_ay_cli = lambda: report.parent
        runner.python = sys.executable
        runner.cache = report.parent / "cache"
        calls = []

        def run(_label, argv, **_kwargs):
            calls.append(argv)
            report.write_text("{}")
            return 0, ""

        runner.run = run
        runner.dual_report("chc", bundle=None, identity="I", report=report, history=None)
        self.assertNotIn("--entry-cache", calls[0])


class DualJudgment(unittest.TestCase):
    gate_mod = landing_gate

    def judge(self, branch, main, alone=None):
        comparison = self.gate_mod.compare_dual(branch, main)
        alone_map = {self.gate_mod.row_id(r): r for r in (alone or [])}
        return comparison, self.gate_mod.judge_dual(comparison, alone_map)

    def test_identical_rows_pass(self) -> None:
        _, verdict = self.judge([row(cls="false-failure")], [row(cls="false-failure")])
        self.assertTrue(verdict["pass"])

    def test_gating_on_main_too_is_not_new(self) -> None:
        comparison, verdict = self.judge([row(cls="missed-bug")], [row(cls="missed-bug")])
        self.assertEqual(comparison["new_gating"], [])
        self.assertTrue(verdict["pass"])

    def test_new_missed_bug_fails_whatever_the_alone_run_says(self) -> None:
        comparison, verdict = self.judge([row(cls="missed-bug")], [row(cls="match")], alone=[row(cls="match")])
        self.assertEqual(len(comparison["new_gating"]), 1)
        self.assertFalse(verdict["pass"])

    def test_a_more_severe_gating_class_than_main_is_new(self) -> None:
        comparison, verdict = self.judge([row(cls="missed-bug")], [row(cls="error")], alone=[row(cls="error")])
        self.assertEqual(len(comparison["new_gating"]), 1)
        self.assertEqual(comparison["worse"], [])
        self.assertFalse(verdict["pass"])

    def test_new_false_certificate_fails(self) -> None:
        _, verdict = self.judge([row(cls="false-certificate")], [row()], alone=[row()])
        self.assertFalse(verdict["pass"])

    def test_worse_row_that_matches_alone_is_a_load_flip(self) -> None:
        comparison, verdict = self.judge([row(cls="unknown")], [row()], alone=[row()])
        self.assertEqual(len(comparison["worse"]), 1)
        self.assertTrue(verdict["pass"])
        self.assertTrue(verdict["resolved"])

    def test_worse_row_still_worse_alone_fails_unless_recorded(self) -> None:
        _, verdict = self.judge([row(cls="false-failure")], [row()], alone=[row(cls="false-failure")])
        self.assertFalse(verdict["pass"])
        recorded = row(cls="false-failure", known_red=True, known_red_class="false-failure")
        _, verdict = self.judge([recorded], [row()], alone=[recorded])
        self.assertTrue(verdict["pass"])
        self.assertTrue(verdict["recorded"])

    def test_known_red_for_another_class_does_not_excuse(self) -> None:
        wrong = row(cls="false-failure", known_red=True, known_red_class="unknown")
        _, verdict = self.judge([wrong], [row()], alone=[wrong])
        self.assertFalse(verdict["pass"])

    def test_an_error_gates_unless_it_resolves_alone(self) -> None:
        comparison, verdict = self.judge([row(cls="error")], [row()], alone=[row(cls="error")])
        self.assertEqual(len(comparison["new_gating"]), 1)
        self.assertFalse(verdict["pass"])
        _, verdict = self.judge([row(cls="error")], [row()], alone=[row()])
        self.assertTrue(verdict["pass"])

    def test_a_flagged_row_never_re_run_fails(self) -> None:
        _, verdict = self.judge([row(cls="unknown")], [row()], alone=[])
        self.assertFalse(verdict["pass"])

    def test_a_row_main_lacks_counts_as_main_matching(self) -> None:
        comparison, verdict = self.judge([row(harness="new", cls="false-failure")], [], alone=[])
        self.assertEqual(len(comparison["worse"]), 1)
        self.assertFalse(verdict["pass"])

    def test_improvements_are_listed(self) -> None:
        comparison, verdict = self.judge([row()], [row(cls="false-failure")])
        self.assertEqual(len(comparison["better"]), 1)
        self.assertTrue(verdict["pass"])


BASE_KEY = dict(input_digest="d", toolchain={"sysroot": "/s", "trustc_vV_sha256": "t"},
                siblings={"ay": {"rev": "a"}}, command=["x", "--flag"], base="b", extra={"main_bundle": "m"})


class CacheKeys(unittest.TestCase):
    gate_mod = landing_gate
    dual_mod = dual_gate

    def test_every_leg_key_element_changes_the_key(self) -> None:
        base = self.gate_mod.leg_key("dual-chc", **BASE_KEY)
        variants = {
            "input_digest": "d2",
            "toolchain": {"sysroot": "/s", "trustc_vV_sha256": "t2"},
            "siblings": {"ay": {"rev": "a2"}},
            "command": ["x", "--flag2"],
            "base": "b2",
            "extra": {"main_bundle": "m2"},
        }
        for name, value in variants.items():
            with self.subTest(element=name):
                kw = dict(BASE_KEY)
                kw[name] = value
                self.assertNotEqual(self.gate_mod.leg_key("dual-chc", **kw), base)
        self.assertNotEqual(self.gate_mod.leg_key("dual-bmc", **BASE_KEY), base)

    def test_leg_key_reads_the_verdict_environment(self) -> None:
        import os
        base = self.gate_mod.leg_key("dual-chc", **BASE_KEY)
        for name in ("TRUST_MC_TEST_PROBE", "AY_TEST_TOKEN_PROBE"):
            with self.subTest(name=name):
                os.environ[name] = "1"
                try:
                    self.assertNotEqual(self.gate_mod.leg_key("dual-chc", **BASE_KEY), base)
                    if "TOKEN" in name:
                        # A secret-looking value keys by digest, never verbatim.
                        self.assertTrue(self.gate_mod.verdict_env()[name].startswith("sha256:"))
                finally:
                    del os.environ[name]

    def test_report_and_history_paths_are_not_verdict_inputs(self) -> None:
        argv = ["py", "gate.py", "--base-ref", "B", "--report", "/a/r.json", "--history", "/h.json", "--x"]
        self.assertEqual(self.gate_mod.key_command(argv), ["py", "gate.py", "--base-ref", "B", "--x"])

    def test_the_base_ref_keys_by_the_tsv_it_reads(self) -> None:
        # Main moving without touching the TSV keeps the key; the TSV moving
        # changes it, whatever the revision is called.
        one = self.gate_mod.key_command(["gate.py", "--base-ref", "sha1"], "blobA")
        two = self.gate_mod.key_command(["gate.py", "--base-ref", "sha2"], "blobA")
        three = self.gate_mod.key_command(["gate.py", "--base-ref", "sha1"], "blobB")
        self.assertEqual(one, two)
        self.assertNotEqual(one, three)
        self.assertIn("--base-ref", one)

    def entry_key(self, **overrides):
        entry = self.dual_mod.EntrySpec(path="a.rs", kind="dual", flags=overrides.pop("flags", ("-Z", "x")),
                                        lanes=("chc", "bmc"), oracle="o", harnesses=())
        job = self.dual_mod.Job(entry=entry, lane=overrides.pop("lane", "chc"), source=Path("/a.rs"))
        kw = dict(bundle_identity="B", ay_version="ay 1",
                  ay_identity={"binary_sha256": "A", "builder": None}, job=job, source_sha256="S", harness_timeout=30,
                  wall_limit_s=240, gate_sha256="G", inherited_env={"TRUST_X": "1"})
        kw.update(overrides)
        return self.dual_mod.entry_cache_key(**kw)

    def test_every_entry_key_element_changes_the_key(self) -> None:
        base = self.entry_key()
        for name, value in {"bundle_identity": "B2", "ay_version": "ay 2", "source_sha256": "S2",
                            "harness_timeout": 31, "wall_limit_s": 241, "gate_sha256": "G2",
                            "inherited_env": {"TRUST_X": "2"},
                            "ay_identity": {"binary_sha256": "B", "builder": None}, "flags": ("-Z", "y"), "lane": "bmc"}.items():
            with self.subTest(element=name):
                self.assertNotEqual(self.entry_key(**{name: value}), base)

    def test_legacy_entry_schema_and_builder_changes_cannot_reuse(self) -> None:
        key = self.entry_key()
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = self.dual_mod.cache_path(root, key)
            path.parent.mkdir(parents=True)
            path.write_text(json.dumps({"schema": "trust-mc.dual-entry-cache/v1", "key": key}))
            self.assertIsNone(self.dual_mod.cache_load(root, key))
        self.assertNotEqual(key, self.entry_key(
            ay_identity={"binary_sha256": "A", "builder": {"compiler": "different"}}))

    def test_bundle_identity_reads_toolchain_siblings_and_inputs(self) -> None:
        by_path = {"trust-mc-core/src/lib.rs": {"dual-chc", "dual-bmc"}, "docs/a.md": {"docs-links"},
                   "tools/soundness-duals/a.rs": {"dual-chc"}}
        blobs = {"trust-mc-core/src/lib.rs": "1", "docs/a.md": "2", "tools/soundness-duals/a.rs": "3"}
        tc, sib = {"t": "1"}, {"ay": {"rev": "a"}}
        base = self.gate_mod.bundle_identity(by_path, blobs, tc, sib)
        self.assertNotEqual(self.gate_mod.bundle_identity(by_path, {**blobs, "trust-mc-core/src/lib.rs": "9"},
                                                          tc, sib), base)
        self.assertNotEqual(self.gate_mod.bundle_identity(by_path, blobs, {"t": "2"}, sib), base)
        self.assertNotEqual(self.gate_mod.bundle_identity(by_path, blobs, tc, {"ay": {"rev": "b"}}), base)
        with mock.patch.object(self.gate_mod, "AY_BUILD_PROTOCOL", "legacy"):
            self.assertNotEqual(self.gate_mod.bundle_identity(by_path, blobs, tc, sib), base)
        # Prose and the dual data (keyed per run) are not bundle inputs.
        self.assertEqual(self.gate_mod.bundle_identity(by_path, {**blobs, "docs/a.md": "9"}, tc, sib), base)
        self.assertEqual(self.gate_mod.bundle_identity(
            by_path, {**blobs, "tools/soundness-duals/a.rs": "9"}, tc, sib), base)

    def test_gate_code_no_crate_reads_is_no_bundle_input(self) -> None:
        # Every leg is selected by a gate script (None), but the bundle is
        # not built from one no crate names; a build input stays an input.
        by_path = {"trust-mc-core/src/lib.rs": {"dual-chc", "dual-bmc"}, "scripts/landing-gate.py": None,
                   "Cargo.lock": None}
        blobs = {"trust-mc-core/src/lib.rs": "1", "scripts/landing-gate.py": "2", "Cargo.lock": "3"}
        tc, sib, gate = {"t": "1"}, {"ay": {"rev": "a"}}, {"scripts/landing-gate.py"}
        base = self.gate_mod.bundle_identity(by_path, blobs, tc, sib, gate)
        self.assertEqual(self.gate_mod.bundle_identity(
            by_path, {**blobs, "scripts/landing-gate.py": "9"}, tc, sib, gate), base)
        self.assertNotEqual(self.gate_mod.bundle_identity(by_path, {**blobs, "Cargo.lock": "9"}, tc, sib, gate),
                            base)
        self.assertNotEqual(self.gate_mod.bundle_identity(
            by_path, {**blobs, "scripts/landing-gate.py": "9"}, tc, sib), base)

    def test_a_gate_script_a_crate_names_stays_a_bundle_input(self) -> None:
        sel = self.gate_mod.sel
        fx = tls.Fixture()
        try:
            ctx = sel.build_context(sel.Tree(fx.root, fx.base))
            gate_only = self.gate_mod.gate_only_paths(ctx)
            self.assertIn("scripts/soundness-dual-gate.py", gate_only)
            # (compile-timer names all of scripts/, but feeds no bundle.) The
            # fixture's driver names scripts/ay-soundness-gate.sh: were it a
            # gate script, it would still be the driver's input.
            ctx.gate_scripts.add("scripts/ay-soundness-gate.sh")
            self.assertNotIn("scripts/ay-soundness-gate.sh", self.gate_mod.gate_only_paths(ctx))
        finally:
            fx.close()


class BudgetBoundRuns(unittest.TestCase):
    """A run whose outcome depends on the time or memory it had is never a
    cache entry: a load-dependent verdict on main would otherwise stand for
    main beside every later branch, and hide a branch regressing the same
    harness to the same class."""

    dual_mod = dual_gate
    gate_mod = landing_gate

    def test_markers(self) -> None:
        bound = self.dual_mod.budget_bound
        self.assertTrue(bound("x\n[AY:UNKNOWN_REASON:Timeout]\n"))
        self.assertTrue(bound("[AY:UNKNOWN_REASON:Memout]"))
        self.assertTrue(bound("[AY:STAGE_SKIPPED:bmc-crosscheck:BudgetExhausted] 0.3s of the deadline left"))
        self.assertFalse(bound("[AY:UNKNOWN_REASON:UndecidedModel]\nVERIFICATION:- INCONCLUSIVE"))
        self.assertFalse(bound("VERIFICATION:- SUCCESSFUL"))

    def run_done(self, output: str) -> list[Path]:
        import tempfile
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        source = root / "a.rs"
        source.write_text("fn main() {}\n")
        harness = self.dual_mod.HarnessSpec(name="h", expected="SUCCESSFUL")
        entry = self.dual_mod.EntrySpec(path="a.rs", kind="dual", flags=(), lanes=("chc",), oracle="o",
                                        harnesses=(harness,))
        job = self.dual_mod.Job(entry=entry, lane="chc", source=source)
        results: list = []
        task = self.dual_mod._dual_task(0, job, driver=Path("/bin/true"), env={}, harness_timeout=30, slack=180,
                                        log_dir=root / "logs", history={}, results=results,
                                        announce=lambda *a: None, cache=(root / "cache", "k" * 64))
        task.prepare()
        outcome = self.dual_mod._host_room().Outcome(exit_code=0, timed_out=False, wall_s=1.0, cpu_s=1.0,
                                                    peak_rss_mb=10, cap_mb=None)
        task.done(output, outcome)
        task.cleanup()
        return list((root / "cache").rglob("*.json"))

    def test_a_budget_bound_run_is_not_stored(self) -> None:
        self.assertEqual(self.run_done("[AY:UNKNOWN_REASON:Timeout]\nVERIFICATION:- INCONCLUSIVE\n"), [])
        self.assertEqual(len(self.run_done("VERIFICATION:- SUCCESSFUL\n")), 1)

    def test_an_own_tree_report_with_budget_bound_runs_is_recomputed(self) -> None:
        reusable = self.gate_mod.reusable_main_report
        identity = {"protocol": self.gate_mod.AY_BUILD_PROTOCOL, "toolchain": {}, "ay_binary_sha256": "A"}
        self.assertTrue(reusable({"ay_execution": identity, "runs": [{"budget_bound": False}]}, identity))
        self.assertFalse(reusable({"ay_execution": identity, "runs": [
            {"budget_bound": False}, {"budget_bound": True}]}, identity))
        self.assertFalse(reusable({"ay_execution": identity, "runs": [{}]}, identity))
        self.assertFalse(reusable({"ay_execution": identity, "runs": []}, identity))


class LivePinChecks(unittest.TestCase):
    """A pin check failing because upstream moved past a pin main shares is
    reported; any other failure is the change's."""

    gate_mod = landing_gate

    def test_the_same_failure_on_main_is_main_s(self) -> None:
        same = self.gate_mod.same_live_failure
        out = "note: /w/b/trust-mc lags\nerror: TrustIR live main moved past pin 7e35\n"
        main_out = "note: /m/trust-mc lags\nerror: TrustIR live main moved past pin 7e35\n"
        self.assertTrue(same(1, out, Path("/w/b/trust-mc"), 1, main_out, Path("/m/trust-mc")))

    def test_any_difference_is_the_change_s(self) -> None:
        same = self.gate_mod.same_live_failure
        out = "error: TrustIR live main moved past pin 7e35\n"
        self.assertFalse(same(1, out, Path("/b"), 0, "", Path("/m")), "main passes")
        self.assertFalse(same(1, out, Path("/b"), 2, out, Path("/m")), "another status")
        self.assertFalse(same(1, out + "error: ay pin\n", Path("/b"), 1, out, Path("/m")), "another output")
        self.assertFalse(same(0, "", Path("/b"), 0, "", Path("/m")), "nothing failed")


class LockedFetch(unittest.TestCase):
    """The live pin checks resolve the locked graph offline. On a host whose
    Cargo home was pruned, the gate first fetches exactly the lockfile's
    packages into it, for the change's tree and for main's. A fetch decides
    no verdict."""

    gate_mod = landing_gate

    def fake_targo(self, status: int, stderr: str = "") -> tuple[Path, Path]:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        record = root / "argv"
        targo = root / "targo"
        targo.write_text("#!/bin/sh\nprintf '%s\\n' \"$@\" > " + str(record) + "\n"
                         f"printf '%s\\n' {stderr!r} >&2\nexit {status}\n")
        targo.chmod(0o755)
        (root / "tree").mkdir()
        return targo, root

    def runner(self, targo: Path):
        runner = object.__new__(self.gate_mod.Runner)
        runner.targo = mock.Mock(return_value=str(targo))
        return runner

    def test_the_fetch_is_exactly_the_tree_s_lockfile(self) -> None:
        targo, root = self.fake_targo(0)
        tree = root / "tree"
        self.assertEqual(self.runner(targo).fetch_locked(tree), [])
        self.assertEqual((root / "argv").read_text().splitlines(),
                         ["fetch", "--locked", "--manifest-path", str(tree / "Cargo.toml")])

    def test_a_failed_fetch_is_a_note_never_a_verdict(self) -> None:
        targo, root = self.fake_targo(101, "error: cannot update the lock file")
        notes = self.runner(targo).fetch_locked(root / "tree")
        self.assertEqual(len(notes), 1)
        self.assertIn("exited 101", notes[0])
        self.assertIn("cannot update the lock file", notes[0])

    def test_both_live_legs_fetch_before_their_check_on_both_sides(self) -> None:
        for leg in ("ay-pin", "shared-pins"):
            with self.subTest(leg=leg):
                runner = object.__new__(self.gate_mod.Runner)
                runner.repo = Path("/change")
                runner.python = "python3"
                runner.state = {"base": "b", "main_tip": "m"}
                runner.args = SimpleNamespace(main="m")
                order = mock.Mock()
                runner.ensure_pin_siblings = order.siblings
                order.siblings.return_value = []
                runner.fetch_locked = order.fetch
                order.fetch.return_value = []
                runner.ensure_main_tree = mock.Mock(return_value=Path("/main"))
                runner.run = order.run
                order.run.return_value = (1, "error: TrustIR live main moved past pin 7e35\n")
                result = runner.run_leg(leg)
                self.assertEqual(result.status, "pass", "the same live failure on main is main's")
                calls = [(c[0], c[1][0] if c[1] else None, c[2].get("cwd")) for c in order.mock_calls]
                self.assertEqual(calls, [
                    ("siblings", None, None),
                    ("fetch", Path("/change"), None),
                    ("run", leg, Path("/change")),
                    ("siblings", Path("/main"), None),
                    ("fetch", Path("/main"), None),
                    ("run", f"{leg}-main", Path("/main")),
                ])


class DualPoolNeed(unittest.TestCase):
    """One heavy file must not size every driver of the pool."""

    dual_mod = dual_gate

    def test_the_pool_need_is_a_high_quantile_not_the_largest_peak(self) -> None:
        history = {(f"f{i}.rs", "chc"): {"peak_rss_mb": 41} for i in range(99)}
        history[("big.rs", "chc")] = {"peak_rss_mb": 9235}
        self.assertEqual(self.dual_mod.history_need_mb(history, ["chc"], 2048), 2048)
        many = {(f"f{i}.rs", "chc"): {"peak_rss_mb": 4000} for i in range(100)}
        self.assertEqual(self.dual_mod.history_need_mb(many, ["chc"], 2048), 5000)

    def test_a_run_known_to_outgrow_the_cap_runs_alone(self) -> None:
        self.assertTrue(self.dual_mod.runs_alone({"peak_rss_mb": 9235}, 2400))
        self.assertFalse(self.dual_mod.runs_alone({"peak_rss_mb": 500}, 2400))
        self.assertFalse(self.dual_mod.runs_alone(None, 2400))


class ThisRepositoryBudgetReasons(unittest.TestCase):
    """The dual gate's budget-bound reasons are the driver's (read from this
    tree, so not among the mutant classes, which run on a copy of scripts/)."""

    def test_the_reasons_are_the_drivers_budget_bound_ones(self) -> None:
        import re
        source = (SCRIPTS.parent / "trust-mc-driver/src/verification_provenance.rs").read_text()
        body = source.split("fn is_budget_bound(self) -> bool {", 1)[1].split("}", 1)[0]
        self.assertEqual(set(re.findall(r"Self::(\w+)", body)), set(dual_gate.BUDGET_BOUND_REASONS))


class ScriptTestFailures(unittest.TestCase):
    gate_mod = landing_gate

    def test_judgment_reads_the_alone_run(self) -> None:
        judge = self.gate_mod.judge_script_failures
        a, b = "T.test_a::test_a", "T.test_b::test_b"
        # Failing beside other files, passing alone: a concurrency flip.
        self.assertTrue(judge({"t.py": {a}}, {"t.py": set()}, {})["pass"])
        # Failing alone too, and main does not: the change's.
        self.assertFalse(judge({"t.py": {a}}, {"t.py": {a}}, {})["pass"])
        # Main fails the same tests: reported.
        self.assertTrue(judge({"t.py": {a}}, {}, {"t.py": {a}})["pass"])
        # The alone run is what counts, not the union.
        self.assertFalse(judge({"t.py": {a}}, {"t.py": {a, b}}, {"t.py": {a}})["pass"])

    def test_failing_ids_are_read_from_unittest_output(self) -> None:
        text = ("FAIL: test_a (__main__.T.test_a) (text='x')\nERROR: test_b (__main__.T.test_b)\n"
                "FAIL: test_a (__main__.T.test_a) (text='y')\nok\n")
        self.assertEqual(self.gate_mod.failing_test_ids(text), {"__main__.T.test_a::test_a (text='x')",
                                                                "__main__.T.test_a::test_a (text='y')",
                                                                "__main__.T.test_b::test_b"})

    def test_a_subtest_main_does_not_fail_is_new(self) -> None:
        branch = self.gate_mod.failing_test_ids("FAIL: test_a (__main__.T.test_a) (text='y')\n")
        main = self.gate_mod.failing_test_ids("FAIL: test_a (__main__.T.test_a) (text='x')\n")
        self.assertTrue(branch - main)

    def test_a_crash_is_keyed_by_its_exception(self) -> None:
        a = self.gate_mod.crash_id("Traceback\n  File x\nModuleNotFoundError: No module named 'a'\n")
        b = self.gate_mod.crash_id("Traceback\n  File x\nSyntaxError: invalid syntax\n")
        self.assertNotEqual(a, b)


class LegCommands(unittest.TestCase):
    """The selector's registry of what each leg runs agrees with the commands."""

    gate_mod = landing_gate

    def test_each_leg_runs_its_registered_scripts(self) -> None:
        import argparse
        runner = self.gate_mod.Runner.__new__(self.gate_mod.Runner)
        runner.args = argparse.Namespace(main="origin/main", harness_timeout=30)
        runner.python = "py"
        runner.out_dir = Path("/out")
        runner.cache = Path("/cache")
        runner.repo = Path("/repo")
        runner.state = {"base": "b", "main_tip": "t"}
        runner.targo = lambda: "targo"
        for leg, roots in self.gate_mod.sel.LEG_SCRIPTS.items():
            with self.subTest(leg=leg):
                command = runner.leg_command(leg)
                first = roots[0]
                if first.endswith("*.py"):
                    # Discovery runs every test_*.py of the directory it starts in.
                    self.assertEqual(command[1:], ["-m", "unittest"])
                    self.assertEqual(runner.leg_cwd(leg), Path("/repo") / first.rsplit("/", 1)[0])
                else:
                    self.assertIn(first, " ".join(command))
        self.assertEqual(runner.leg_command("tsv-validate")[-1], "t")


class PinnedCliOutput(unittest.TestCase):
    gate_mod = landing_gate

    def runner_and_tree(self, root, program):
        tree = root / "source tree"
        builder = tree / "scripts" / "build-pinned-ay-cli.sh"
        builder.parent.mkdir(parents=True)
        builder.write_text(python_executable_header(sys.executable) + "import os, sys\n" + program)
        builder.chmod(0o755)
        runner = self.gate_mod.Runner(argparse.Namespace(), root / "runner")
        runner.build_jobs = lambda label: "3"
        runner.state["toolchain"] = {"sysroot": "/test-toolchain", "trustc_vV_sha256": "fixture"}
        runner.targo = lambda: "/test-toolchain/bin/targo"
        return runner, tree

    def test_stdout_path_stderr_log_cwd_and_job_share_are_preserved(self):
        with tempfile.TemporaryDirectory(prefix="pinned CLI output ") as directory:
            root = Path(directory)
            binary = root / "cache with spaces" / "release" / "ay"
            runner, tree = self.runner_and_tree(root,
                "print('stdout build progress')\n"
                f"print({str(binary)!r})\n"
                "print('builder diagnostics', file=sys.stderr)\n"
                "print('jobs=' + os.environ['CARGO_BUILD_JOBS'], file=sys.stderr)\n"
                "print('cwd=' + os.getcwd(), file=sys.stderr)\n")
            before = signal.getsignal(signal.SIGTERM)
            console = io.StringIO()
            with contextlib.redirect_stdout(console):
                actual = runner.pinned_ay_cli(tree, "probe")
            self.assertEqual(actual, binary.parent)
            self.assertEqual((runner.logs / "probe.log").read_text(),
                             f"builder diagnostics\njobs=3\ncwd={tree.resolve()}\n")
            self.assertNotIn("stdout build progress", console.getvalue())
            self.assertEqual(signal.getsignal(signal.SIGTERM), before)

    def test_nonzero_exit_refuses_even_when_stdout_names_a_binary(self):
        with tempfile.TemporaryDirectory(prefix="pinned CLI failure ") as directory:
            runner, tree = self.runner_and_tree(Path(directory),
                "print('/cache/release/ay')\n"
                "print('build failed', file=sys.stderr)\nraise SystemExit(7)\n")
            before = signal.getsignal(signal.SIGTERM)
            with self.assertRaisesRegex(self.gate_mod.GateError, "logs/probe.log"):
                runner.pinned_ay_cli(tree, "probe")
            self.assertEqual((runner.logs / "probe.log").read_text(), "build failed\n")
            self.assertEqual(signal.getsignal(signal.SIGTERM), before)

    def test_success_without_a_stdout_path_is_refused(self):
        with tempfile.TemporaryDirectory(prefix="pinned CLI empty ") as directory:
            runner, tree = self.runner_and_tree(Path(directory),
                "print('no binary was built', file=sys.stderr)\n")
            with self.assertRaisesRegex(self.gate_mod.GateError, "logs/probe.log"):
                runner.pinned_ay_cli(tree, "probe")
            self.assertEqual((runner.logs / "probe.log").read_text(), "no binary was built\n")

    def test_invalid_stdout_encoding_is_still_refused(self):
        with tempfile.TemporaryDirectory(prefix="pinned CLI encoding ") as directory:
            runner, tree = self.runner_and_tree(Path(directory),
                "sys.stdout.buffer.write(b'\\xff\\n/cache/release/ay\\n')\n")
            with self.assertRaises(UnicodeDecodeError):
                runner.pinned_ay_cli(tree, "probe")

    def test_failed_launch_restores_signal_handlers(self):
        with tempfile.TemporaryDirectory(prefix="pinned CLI launch ") as directory:
            runner, tree = self.runner_and_tree(Path(directory), "pass\n")
            before = {sig: signal.getsignal(sig) for sig in (signal.SIGINT, signal.SIGTERM)}
            with mock.patch.object(self.gate_mod.subprocess, "Popen", side_effect=OSError("launch failed")):
                with self.assertRaisesRegex(OSError, "launch failed"):
                    runner.pinned_ay_cli(tree, "probe")
            self.assertEqual({sig: signal.getsignal(sig) for sig in before}, before)


class InterruptedLegProcesses(unittest.TestCase):
    # Execute the real Runner and host_room pool in separate processes. The
    # pool deliberately creates a new session, as native gate workers do.
    FIXTURE = r'''
import argparse
import importlib.util
import os
from pathlib import Path
import signal
import sys
import time

mode, root, scripts = sys.argv[1:]
root = Path(root)
sys.path.insert(0, scripts)
from python_executable import python_executable_header
spec = importlib.util.spec_from_file_location("fixture_landing", Path(scripts) / "landing-gate.py")
gate = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = gate
spec.loader.exec_module(gate)
if mode in ("runner", "runner-stubborn", "runner-launch-term", "ay-cli", "ay-cli-stubborn", "ay-cli-launch-term"):
    runner = gate.Runner(argparse.Namespace(), root)
    runner.state["toolchain"] = {"sysroot": "/test-toolchain", "trustc_vV_sha256": "fixture"}
    runner.targo = lambda: "/test-toolchain/bin/targo"
    child_mode = "stubborn" if mode in ("runner-stubborn", "ay-cli-stubborn") else "pool"
    if mode in ("runner-launch-term", "ay-cli-launch-term"):
        real_popen = gate.subprocess.Popen
        def interrupt_runner_launch(*args, **kwargs):
            child = real_popen(*args, **kwargs)
            while not (root / "leaf.pid").exists():
                time.sleep(0.01)
            os.kill(os.getpid(), signal.SIGTERM)
            return child
        gate.subprocess.Popen = interrupt_runner_launch
    if mode.startswith("ay-cli"):
        builder = root / "scripts" / "build-pinned-ay-cli.sh"
        builder.parent.mkdir()
        builder.write_text(python_executable_header(sys.executable) + "import os\nos.execv(" + repr(sys.executable)
            + ", " + repr([sys.executable, __file__, child_mode, str(root), scripts]) + ")\n")
        builder.chmod(0o755)
        runner.build_jobs = lambda label: "1"
        runner.pinned_ay_cli(root, "ay-cli")
    else:
        runner.run("child", [sys.executable, __file__, child_mode, str(root), scripts])
elif mode in ("pool", "direct-pool", "nested-pool", "nested-stubborn", "pool-stubborn", "notification-error", "launch-term"):
    (root / "pool.pid").write_text(str(os.getpid()))
    print("pool-ready", flush=True)
    print("pool-stderr-ready", file=sys.stderr, flush=True)
    room = gate.host_room
    reading = room.HostReading(platform="test", logical_cores=2, physical_cores=2,
        physical_mb=16384, available_mb=8192, available_source="test",
        pressure="normal", load1=0.0, taken_at=0.0)
    plan = room.plan(reading, need_mb=64, max_jobs=1, timing_sensitive=False)
    child_mode = {"nested-pool": "pool", "nested-stubborn": "pool-stubborn",
        "pool-stubborn": "leaf-stubborn", "notification-error": "exiting-leader"}.get(mode, "leaf")
    if mode == "notification-error":
        def fail_notification(pid):
            while not (root / "leaf.pid").exists():
                time.sleep(0.01)
            time.sleep(0.05)
            raise OSError("fixture notification failure")
        room._wait_child_exit = fail_notification
    if mode == "launch-term":
        real_popen = room.subprocess.Popen
        def interrupt_launch(*args, **kwargs):
            child = real_popen(*args, **kwargs)
            (root / "leaf.pid").write_text(str(child.pid))
            os.kill(os.getpid(), signal.SIGTERM)
            return child
        room.subprocess.Popen = interrupt_launch
    task = room.Task(key="leaf", expected_s=None,
        prepare=lambda: ([sys.executable, __file__, child_mode, str(root), scripts], None, None, 60),
        done=lambda output, outcome: None)
    room.run_tasks([task], plan, sample_s=0.05, sampler=lambda ids: {pid: 1 for pid in ids},
        available=lambda: 8192, pressure_now=lambda: "normal", log=lambda message: None)
elif mode == "stubborn":
    signal.signal(signal.SIGINT, signal.SIG_IGN)
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    for name in ("pool.pid", "leaf.pid"):
        (root / name).write_text(str(os.getpid()))
    print("pool-ready", flush=True)
    print("pool-stderr-ready", file=sys.stderr, flush=True)
    while True:
        signal.pause()
elif mode == "exiting-leader":
    import subprocess
    (root / "pool.pid").write_text(str(os.getpid()))
    subprocess.Popen([sys.executable, __file__, "leaf", str(root), scripts])
else:
    if mode == "leaf-stubborn":
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
    (root / "leaf.pid").write_text(str(os.getpid()))
    print("child-ready", flush=True)
    while True:
        signal.pause()
'''

    @staticmethod
    def exists(pid):
        try:
            os.kill(pid, 0)
            return True
        except ProcessLookupError:
            return False

    def check_interrupt(self, signum, mode="runner"):
        scratch = Path(tempfile.gettempdir()) / ".ubd"
        scratch.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="landing cancel ", dir=scratch) as directory:
            root = Path(directory)
            fixture = root / "worker.py"
            fixture.write_text(self.FIXTURE)
            output_path = root / "runner.log"
            with output_path.open("w") as output:
                proc = subprocess.Popen([sys.executable, str(fixture), mode, str(root), str(SCRIPTS)],
                                        stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
            children = []
            try:
                deadline = time.monotonic() + 15
                while time.monotonic() < deadline:
                    if ((root / "leaf.pid").is_file()
                            and (mode == "runner-launch-term" or mode.startswith("ay-cli")
                                 or "pool-ready" in output_path.read_text())):
                        break
                    self.assertIsNone(proc.poll(),
                                      "runner exited before creating its worker:\n"
                                      + output_path.read_text())
                    time.sleep(0.02)
                self.assertTrue((root / "leaf.pid").is_file(), "worker never started")
                children = [int((root / name).read_text()) for name in ("pool.pid", "leaf.pid")]
                if mode not in ("notification-error", "launch-term", "runner-launch-term", "ay-cli-launch-term"):
                    os.kill(proc.pid, signum)
                self.assertNotEqual(proc.wait(timeout=15), 0)
                deadline = time.monotonic() + 3
                while any(self.exists(pid) for pid in children) and time.monotonic() < deadline:
                    time.sleep(0.02)
                self.assertFalse([pid for pid in children if self.exists(pid)],
                                 "interrupt left owned workers alive or unreaped")
                if mode.startswith("ay-cli"):
                    self.assertEqual(proc.returncode, 128 + signum)
                if mode.startswith("runner"):
                    self.assertIn("pool-ready", (root / "target/landing-gate/logs/child.log").read_text())
                if mode.startswith("ay-cli"):
                    self.assertIn("pool-stderr-ready", (root / "target/landing-gate/logs/ay-cli.log").read_text())
            finally:
                # Only groups created by this fixture; also clean the failing
                # baseline so the regression itself cannot leak a worker.
                groups = set()
                for pid in [*reversed(children), proc.pid]:
                    try:
                        groups.add(os.getpgid(pid))
                    except ProcessLookupError:
                        pass
                for pgid in groups:
                    self.assertNotEqual(pgid, os.getpgrp(), "fixture must own a separate group")
                    try:
                        os.killpg(pgid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                proc.wait(timeout=15)

    def test_sigint_reaps_the_leg_and_its_separate_session_worker(self):
        self.check_interrupt(signal.SIGINT)

    def test_sigterm_reaps_the_leg_and_its_separate_session_worker(self):
        self.check_interrupt(signal.SIGTERM)

    def test_unresponsive_leg_is_killed_and_reaped(self):
        self.check_interrupt(signal.SIGINT, "runner-stubborn")

    def test_sigterm_reaps_direct_script_test_pool(self):
        self.check_interrupt(signal.SIGTERM, "direct-pool")

    def test_sigterm_reaps_nested_script_test_pools(self):
        self.check_interrupt(signal.SIGTERM, "nested-pool")

    def test_sigint_reaps_nested_script_test_pools(self):
        self.check_interrupt(signal.SIGINT, "nested-pool")

    def test_nested_pool_reaps_leaf_ignoring_cooperative_signals(self):
        self.check_interrupt(signal.SIGTERM, "nested-stubborn")

    def test_notification_failure_closes_exited_leaders_inherited_pipe(self):
        self.check_interrupt(signal.SIGTERM, "notification-error")

    def test_sigterm_during_launch_publishes_ownership_before_cleanup(self):
        self.check_interrupt(signal.SIGTERM, "launch-term")

    def test_runner_sigterm_during_launch_reaps_new_child(self):
        self.check_interrupt(signal.SIGTERM, "runner-launch-term")

    def test_sigint_reaps_pinned_cli_and_its_separate_session_worker(self):
        self.check_interrupt(signal.SIGINT, "ay-cli")

    def test_sigterm_reaps_pinned_cli_and_its_separate_session_worker(self):
        self.check_interrupt(signal.SIGTERM, "ay-cli")

    def test_unresponsive_pinned_cli_is_killed_and_reaped(self):
        self.check_interrupt(signal.SIGINT, "ay-cli-stubborn")

    def test_pinned_cli_sigterm_during_launch_reaps_new_child(self):
        self.check_interrupt(signal.SIGTERM, "ay-cli-launch-term")

    def test_ordinary_output_and_failure_status_are_preserved(self):
        with tempfile.TemporaryDirectory(prefix="landing-output-") as directory:
            runner = self.gate_mod.Runner(argparse.Namespace(), Path(directory))
            previous_term = signal.getsignal(signal.SIGTERM)
            code, output = runner.run("failure", [sys.executable, "-c",
                                                  "print('kept output'); raise SystemExit(7)"], quiet=True)
            self.assertEqual(code, 7)
            self.assertEqual(output, "kept output\n")
            self.assertEqual((runner.logs / "failure.log").read_text(), output)
            self.assertEqual(signal.getsignal(signal.SIGTERM), previous_term)

    gate_mod = landing_gate


class RunRecordCheckpoints(unittest.TestCase):
    def test_interrupted_main_keeps_completed_legs_and_names_the_active_leg(self):
        gate = landing_gate
        with tempfile.TemporaryDirectory(prefix="landing-record-") as directory:
            root = Path(directory)
            record = root / "record.json"
            record.write_text('{"verdict": "pass", "old": true}\n')
            selection = SimpleNamespace(selected=["first", "second"], skipped={}, everything=False,
                                        record=lambda: {}, report_lines=lambda: [])
            tree = SimpleNamespace(files=lambda: [])
            runner = SimpleNamespace(cache=root / "cache", state={},
                                     leg_command=lambda leg: ["fixture", leg],
                                     record_build_need=lambda *args: None)

            def run_leg(leg):
                checkpoint = json.loads(record.read_text())
                self.assertEqual(checkpoint["verdict"], "incomplete")
                self.assertEqual(checkpoint["active_leg"], leg)
                self.assertNotIn("old", checkpoint)
                if leg == "second":
                    raise KeyboardInterrupt
                return gate.LegResult(leg, "pass")

            runner.run_leg = run_leg
            with contextlib.ExitStack() as stack:
                for owner, name, value in (
                    (gate, "REPO_ROOT", root), (gate, "git", lambda *a, **k: "identity\n"),
                    (gate, "tree_is_clean", lambda *a: False),
                    (gate.sel, "merge_base", lambda *a: "base"),
                    (gate.sel, "diff_changes", lambda *a: []),
                    (gate.sel, "targo_metadata", lambda *a: {}),
                    (gate.sel, "Tree", lambda *a: tree),
                    (gate.sel, "build_context", lambda *a: object()),
                    (gate.sel, "select", lambda *a: selection),
                    (gate.host_room, "read_host", lambda: SimpleNamespace(record=lambda: {})),
                    (gate.host_room, "adopt_slot_share", lambda: None),
                    (gate.host_room, "TreePeak", lambda *a: contextlib.nullcontext(SimpleNamespace(peak_mb=0))),
                    (gate, "Runner", lambda *a: runner),
                    (gate, "hold_the_tuple_seal", lambda *a: None),
                    (gate, "toolchain_identity", lambda *a: {}),
                    (gate, "tuple_pins", lambda *a: {}),
                    (gate, "sibling_identity", lambda *a: {}),
                    (gate, "legs_by_path", lambda *a: {}),
                    (gate, "blob_ids", lambda *a: {}), (gate, "blob_at", lambda *a: ""),
                    (gate, "prune_cache", lambda *a: 0),
                ):
                    stack.enter_context(mock.patch.object(owner, name, value))
                with self.assertRaises(KeyboardInterrupt):
                    gate.main(["--no-reuse", "--record", str(record)])
                saved = json.loads(record.read_text())
                self.assertEqual(saved["verdict"], "incomplete")
                self.assertEqual(saved["active_leg"], "second")
                self.assertEqual([(row["leg"], row["status"]) for row in saved["legs"]], [("first", "pass")])
                record.write_text('{"verdict": "pass", "old": true}\n')
                with mock.patch.object(gate, "toolchain_identity", side_effect=gate.GateError("fixture setup failure")):
                    self.assertEqual(gate.main(["--no-reuse", "--record", str(record)]), 2)
                self.assertEqual(json.loads(record.read_text())["verdict"], "incomplete")
                self.assertNotIn("old", json.loads(record.read_text()))

    def test_failed_atomic_replace_retains_the_previous_record(self):
        with tempfile.TemporaryDirectory(prefix="landing-record-") as directory:
            record = Path(directory) / "record.json"
            record.write_text('{"verdict": "incomplete"}\n')
            with mock.patch.object(landing_gate.os, "replace", side_effect=OSError("fixture failure")):
                with self.assertRaises(OSError):
                    landing_gate.write_run_record(record, {"verdict": "pass"})
            self.assertEqual(json.loads(record.read_text()), {"verdict": "incomplete"})
            self.assertEqual(list(Path(directory).glob("*.tmp")), [])

    def test_partial_checkpoint_never_claims_a_landing_pass(self):
        with tempfile.TemporaryDirectory(prefix="landing-record-") as directory:
            path = Path(directory) / "record.json"
            landing_gate.checkpoint_run(path, {"partial": True, "legs": []}, "fixture")
            self.assertEqual(json.loads(path.read_text())["verdict"], "partial-incomplete")


class LegInputsAgreeWithTheSelector(unittest.TestCase):
    """A leg's cache key covers exactly the files whose change selects it."""

    gate_mod = landing_gate

    @classmethod
    def setUpClass(cls) -> None:
        cls.fixture = tls.Fixture()

    @classmethod
    def tearDownClass(cls) -> None:
        cls.fixture.close()

    def test_every_path(self) -> None:
        sel = self.gate_mod.sel
        tree = sel.Tree(self.fixture.root, self.fixture.base)
        ctx = sel.build_context(tree)
        by_path = self.gate_mod.legs_by_path(ctx, tree.files())
        universe = set(sel.all_legs(ctx.packages))
        for path in tree.files():
            with self.subTest(path=path):
                selected = set(sel.select([sel.Change(path, "M", "100644", "100644")], ctx).selected)
                keyed = universe if by_path[path] is None else by_path[path]
                self.assertEqual(keyed, selected)


if __name__ == "__main__":
    unittest.main()
