#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

"""Exercise the real gate and tuple checker with synthetic compiler frontends.

These tests do not build Rust or establish certification. The actual tuple
checker checks all dependency identities; the fake Targo records exactly the
policy and selection the shell gate would invoke after successful admission.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest

from python_executable import python_executable_header
from test_development_seal import HOST, SealFixture
from test_tuple_check import Fixture, TRUST_REV, render_tuple, write

ROOT = Path(__file__).resolve().parent.parent


class VerificationGateTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.fx = Fixture(Path(temporary.name).resolve())
        self.root = self.fx.root
        self.gate = self.root / "scripts/check-trust-verification.sh"
        shutil.copyfile(ROOT / "scripts/check-trust-verification.sh", self.gate)
        self.sysroot = self.fx.base / "store/trust/8560"
        self.compiler = self.fx.base / "bin/trustc"
        self.invocation = self.fx.base / "targo-invocation.json"
        self.port_marker = self.fx.base / "port-ran"
        write(
            self.root / "scripts/check-trust-lane-port.sh",
            "#!/bin/sh\n"
            f"touch {shlex.quote(str(self.port_marker))}\n"
            'exit "${FIXTURE_PORT_EXIT:-0}"\n',
            executable=True,
        )
        write(
            self.root / "tools/tuple-check",
            "#!/bin/sh\nexec " + shlex.quote(sys.executable) + " "
            + shlex.quote(str(ROOT / "scripts/tuple_check.py"))
            + " --repo-root " + shlex.quote(str(self.root)) + ' "$@"\n',
            executable=True,
        )
        self.env = {
            "PATH": os.defpath,
            "HOME": str(self.fx.base),
            "LC_ALL": "C",
            "KANI_DOMINATION_CORPUS_DIR": str(self.fx.kani),
        }
        self.write_frontends()

    def write_frontends(self) -> None:
        write(
            self.sysroot / "bin/targo",
            python_executable_header(sys.executable) +
            "import json, os, pathlib, sys\n"
            f"pathlib.Path({str(self.invocation)!r}).write_text(json.dumps({{"
            "'argv':sys.argv[1:], 'trustflags':os.environ.get('TRUSTFLAGS'),"
            "'seal':os.environ.get('TRUST_MC_TRUST_TOOLCHAIN')}))\n"
            "print('synthetic Targo invocation; no compiler executed')\n"
            "sys.exit(int(os.environ.get('FIXTURE_TARGO_EXIT','0')))\n",
            executable=True,
        )
        write(
            self.root / "scripts/resolve-trust-tool.sh",
            '#!/bin/sh\ncase "$1" in\n'
            f"sysroot) printf '%s\\n' {shlex.quote(str(self.sysroot))} ;;\n"
            f"trustc) printf '%s\\n' {shlex.quote(str(self.compiler))} ;;\n"
            f"targo) test \"$TRUST_MC_TRUST_TOOLCHAIN\" = {shlex.quote(str(self.sysroot))} "
            f"|| exit 29; printf '%s\\n' {shlex.quote(str(self.sysroot / 'bin/targo'))} ;;\n"
            '*) exit 2 ;;\nesac\n',
            executable=True,
        )

    def use_development(self) -> Path:
        seal = SealFixture(self.fx.base / "development-seal", TRUST_REV)
        self.sysroot = seal.root
        self.compiler = seal.root / "bin/trustc"
        self.write_frontends()
        write(
            self.compiler,
            '#!/bin/sh\n'
            f"printf '%s\\n' 'trustc synthetic' 'commit-hash: {TRUST_REV}' 'host: {HOST}'\n",
            executable=True,
        )
        # Rebind synthetic scripts as data in the synthetic identity manifest.
        for role in ("trustc", "targo"):
            data = (seal.root / "bin" / role).read_bytes()
            digest = hashlib.sha256(data).hexdigest()
            seal.table[role + "_sha256"] = digest
            seal.table[role + "_bytes"] = len(data)
            seal.fields["artifact_bin_" + role + "_sha256"] = digest
        seal.write_provenance()
        self.fx.tuple["schema"] = 2
        self.fx.tuple["trust"] = {
            "rev": TRUST_REV, "channel": "trust", "identity": "development"
        }
        self.fx.tuple["development_seal"] = seal.table
        selected = self.fx.base / "selected tuple.toml"
        write(selected, render_tuple(self.fx.tuple))
        return selected

    def run_gate(self, *args: str, **env: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["/bin/bash", str(self.gate), *args],
            cwd=self.fx.base, env={**self.env, **env},
            capture_output=True, text=True, timeout=20,
        )

    def report(self) -> tuple[Path, dict]:
        reports = list((self.root / "target/trust-verification").glob("run.*"))
        self.assertEqual(len(reports), 1)
        return reports[0], json.loads((reports[0] / "tuple.json").read_text())

    def assert_policy(self, mode: str, selection: list[str]) -> None:
        actual = json.loads(self.invocation.read_text())
        self.assertEqual(actual["argv"][:8], [
            "trust", mode, "--certify", "--hardened", "--trust-profile",
            "unix_hardened", "--config",
            "target.'cfg(all())'.rustflags=['-Ztrust-verify-include-dependencies=yes']",
        ])
        self.assertEqual(actual["argv"][8:-2], ["--locked", "-j", "1", *selection])
        self.assertEqual(actual["argv"][-2], "--report-dir")
        self.assertIsNone(actual["trustflags"], "Trust 0.12 ignores this obsolete channel")
        self.assertEqual(actual["seal"], str(self.sysroot))

    def test_default_numbered_tuple_retains_full_policy_and_report(self) -> None:
        result = self.run_gate(CARGO_BUILD_JOBS="1")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assert_policy("check", ["--workspace"])
        directory, report = self.report()
        self.assertTrue(report["ok"])
        self.assertEqual(report["tuple_path"], str(self.fx.tuple_path))
        self.assertEqual((directory / "tuple.json").stat().st_mode & 0o077, 0)
        self.assertTrue(self.port_marker.exists())

    def test_explicit_relative_development_tuple_runs_same_build_policy(self) -> None:
        selected = self.use_development()
        result = self.run_gate("--tuple", selected.name, "--build", CARGO_BUILD_JOBS="1")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assert_policy("build", ["--workspace"])
        _, report = self.report()
        self.assertEqual(report["trust"]["identity_classification"], "development")
        self.assertIn("no complete sysroot authentication", report["trust"]["identity_scope"])
        self.assertEqual(report["tuple_sha256"], hashlib.sha256(selected.read_bytes()).hexdigest())

    def test_implicit_development_tuple_still_refuses_before_compilation(self) -> None:
        selected = self.use_development()
        shutil.copyfile(selected, self.fx.tuple_path)
        result = self.run_gate()
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertFalse(self.invocation.exists())
        self.assertFalse(self.port_marker.exists())
        self.assertIn("requires explicit --tuple", result.stderr)

    def test_explicit_tuple_does_not_skip_a_dependency_mismatch(self) -> None:
        selected = self.use_development()
        write(self.fx.ay / "dirty", "source changed\n")
        result = self.run_gate("--tuple", str(selected))
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertFalse(self.invocation.exists())
        self.assertFalse(self.port_marker.exists())
        _, report = self.report()
        self.assertIn("ay.checkout", report["failed"])

    def test_package_selection_is_still_an_explicit_diagnostic(self) -> None:
        result = self.run_gate("-p", "trust-mc-core", "-p", "trust-mc-driver", CARGO_BUILD_JOBS="1")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assert_policy("check", ["-p", "trust-mc-core", "-p", "trust-mc-driver"])
        self.assertIn("DIAGNOSTIC SUBSET", result.stdout)

    def test_live_failure_exit_and_diagnostics_survive(self) -> None:
        result = self.run_gate(FIXTURE_TARGO_EXIT="17")
        self.assertEqual(result.returncode, 17, result.stderr)
        directory, _ = self.report()
        self.assertEqual((directory / "exit.txt").read_text().strip(), "17")
        self.assertIn("synthetic Targo", (directory / "live.log").read_text())

    def test_port_failure_prevents_targo(self) -> None:
        result = self.run_gate(FIXTURE_PORT_EXIT="23")
        self.assertEqual(result.returncode, 23, result.stderr)
        self.assertTrue(self.port_marker.exists())
        self.assertFalse(self.invocation.exists())

    def test_policy_override_and_bad_selection_refuse_before_compilation(self) -> None:
        for args, env in [
            (("--tuple",), {}),
            (("--tuple", "a", "--tuple", "b"), {}),
            (("--unverified",), {}),
            ((), {"TRUSTFLAGS": "-Ztrust-policy=advisory"}),
            ((), {"RUSTC": "/untrusted/compiler"}),
            ((), {"CARGO_BUILD_JOBS": "3"}),
        ]:
            with self.subTest(args=args, env=env):
                result = self.run_gate(*args, **env)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertFalse(self.invocation.exists())
                self.assertFalse(self.port_marker.exists())


if __name__ == "__main__":
    unittest.main()
