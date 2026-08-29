#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Regression tests for fail-closed Trust toolchain resolution."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
RESOLVER = ROOT / "scripts/resolve-trust-tool.sh"
ACTIVE_CARGO_SCRIPTS = (
    "ay-bump-canary.sh",
    "ay-compiletest.sh",
    "ay-replacement-proof.sh",
    "ay-soundness-gate.sh",
    "check-ay-pin.sh",
    "check-shared-pins.sh",
)
HELP_ENTRY_POINTS = (
    "ay-bump-canary.sh",
    "ay-compiletest.sh",
    "ay-replacement-proof.sh",
)


def write_executable(path: Path, source: str) -> None:
    path.write_text(source, encoding="utf-8")
    path.chmod(0o755)


class ResolveTrustToolTests(unittest.TestCase):
    def fixture(
        self, suffix: str = "", *, include_cargo: bool = True, include_targo: bool = True
    ) -> tuple[tempfile.TemporaryDirectory[str], dict[str, str], dict[str, Path]]:
        temporary = tempfile.TemporaryDirectory()
        root = Path(temporary.name)
        fake_bin = root / "ambient-bin"
        sysroot_bin = root / "trust-sysroot" / "bin"
        fake_bin.mkdir()
        sysroot_bin.mkdir(parents=True)
        paths = {
            "rustup": fake_bin / "rustup",
            "rustc": sysroot_bin / f"rustc{suffix}",
            "cargo": sysroot_bin / f"cargo{suffix}",
            "targo": sysroot_bin / f"targo{suffix}",
            "sysroot": sysroot_bin.parent,
            "rustup_log": root / "rustup.log",
            "rustc_log": root / "rustc.log",
        }
        write_executable(
            paths["rustup"],
            "#!/bin/sh\n"
            'printf "%s\\n" "$*" >> "$FAKE_RUSTUP_LOG"\n'
            'printf "%s\\n" "$FAKE_PINNED_RUSTC"\n',
        )
        write_executable(
            paths["rustc"],
            "#!/bin/sh\n"
            'printf "%s\\n" "$*" >> "$FAKE_RUSTC_LOG"\n'
            'printf "%s\\n" "$FAKE_TRUST_SYSROOT"\n',
        )
        if include_cargo:
            write_executable(paths["cargo"], "#!/bin/sh\nexit 0\n")
        if include_targo:
            write_executable(paths["targo"], "#!/bin/sh\nexit 0\n")
        # A hostile ambient cargo must never be selected.
        write_executable(fake_bin / "cargo", "#!/bin/sh\nexit 99\n")

        environment = os.environ.copy()
        environment.update(
            {
                "FAKE_PINNED_RUSTC": str(paths["rustc"]),
                "FAKE_RUSTC_LOG": str(paths["rustc_log"]),
                "FAKE_RUSTUP_LOG": str(paths["rustup_log"]),
                "FAKE_TRUST_SYSROOT": str(paths["sysroot"]),
                "PATH": f"{fake_bin}{os.pathsep}/usr/bin{os.pathsep}/bin",
                "TRUST_MC_RUSTUP": str(paths["rustup"]),
            }
        )
        return temporary, environment, paths

    def run_resolver(
        self, environment: dict[str, str], requested: str
    ) -> subprocess.CompletedProcess[str]:
        bash = shutil.which("bash")
        assert bash is not None
        return subprocess.run(
            [bash, str(RESOLVER), requested],
            cwd=ROOT,
            env=environment,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )

    def test_resolves_every_frontend_from_rustup_pinned_sysroot(self) -> None:
        for suffix in ("", ".exe"):
            with self.subTest(suffix=suffix):
                temporary, environment, paths = self.fixture(suffix)
                with temporary:
                    for requested in ("cargo", "targo", "rustc", "sysroot"):
                        result = self.run_resolver(environment, requested)
                        self.assertEqual(result.returncode, 0, result.stderr)
                        self.assertEqual(result.stdout.strip(), str(paths[requested]))
                    self.assertEqual(
                        paths["rustup_log"].read_text(encoding="utf-8").splitlines(),
                        ["which rustc --toolchain trust"] * 4,
                    )
                    self.assertEqual(
                        paths["rustc_log"].read_text(encoding="utf-8").splitlines(),
                        ["--print sysroot"] * 4,
                    )

    def test_missing_pinned_frontend_fails_closed(self) -> None:
        temporary, environment, _ = self.fixture(include_targo=False)
        with temporary:
            result = self.run_resolver(environment, "cargo")
            self.assertEqual(result.returncode, 2)
            self.assertIn("pinned Trust sysroot has no targo frontend", result.stderr)

    def test_rustup_failure_fails_closed(self) -> None:
        temporary, environment, paths = self.fixture()
        with temporary:
            write_executable(paths["rustup"], "#!/bin/sh\nexit 91\n")
            result = self.run_resolver(environment, "cargo")
            self.assertEqual(result.returncode, 2)
            self.assertIn("rustup cannot resolve rustc", result.stderr)

    def test_help_does_not_invoke_rustup(self) -> None:
        temporary, environment, paths = self.fixture()
        with temporary:
            result = self.run_resolver(environment, "--help")
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("cargo|targo|rustc|sysroot", result.stdout)
            self.assertFalse(paths["rustup_log"].exists())

    def test_entry_point_help_does_not_resolve_toolchain(self) -> None:
        temporary, environment, paths = self.fixture()
        with temporary:
            bash = shutil.which("bash")
            assert bash is not None
            for name in HELP_ENTRY_POINTS:
                result = subprocess.run(
                    [bash, str(ROOT / "scripts" / name), "--help"],
                    cwd=ROOT,
                    env=environment,
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    check=False,
                )
                self.assertEqual(result.returncode, 0, f"{name}: {result.stderr}")
            bump_help = subprocess.run(
                [sys.executable, str(ROOT / "scripts/bump-ay-pin.py"), "--help"],
                cwd=ROOT,
                env=environment,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
            self.assertEqual(bump_help.returncode, 0, bump_help.stderr)
            self.assertFalse(paths["rustup_log"].exists())

    def test_active_build_scripts_do_not_execute_ambient_cargo(self) -> None:
        for name in ACTIVE_CARGO_SCRIPTS:
            source = (ROOT / "scripts" / name).read_text(encoding="utf-8")
            for number, raw_line in enumerate(source.splitlines(), start=1):
                code = raw_line.lstrip()
                if code.startswith(("#", "echo ", "log ", "printf ")):
                    continue
                executes_bare = code == "cargo" or code.startswith("cargo ") or any(
                    marker in code for marker in ("&& cargo ", "$(cargo ", "( cargo ")
                )
                self.assertFalse(
                    executes_bare,
                    f"{name}:{number} executes ambient cargo: {raw_line}",
                )
            self.assertNotIn("command -v cargo", source, name)
            self.assertNotIn("require_command cargo", source, name)

        bump_source = (ROOT / "scripts/bump-ay-pin.py").read_text(encoding="utf-8")
        self.assertNotIn('["cargo", "metadata"', bump_source)


if __name__ == "__main__":
    unittest.main(verbosity=2)
