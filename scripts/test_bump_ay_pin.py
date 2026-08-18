#!/usr/bin/env python3
"""Regression tests for the transactional trust-mc AY pin helper."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts/bump-ay-pin.py"


class BumpAyPinTests(unittest.TestCase):
    def fixture(self) -> tuple[tempfile.TemporaryDirectory[str], Path, str]:
        temporary = tempfile.TemporaryDirectory()
        root = Path(temporary.name)
        (root / "scripts").mkdir()
        shutil.copy2(SCRIPT, root / "scripts/bump-ay-pin.py")
        shutil.copy2(
            ROOT / "scripts/check_first_party_git_pins.py",
            root / "scripts/check_first_party_git_pins.py",
        )
        revision = "a" * 40
        dependencies = "\n".join(
            f'{name} = {{ version = "0.8.0", git = "https://github.com/alabsystems/ay.git", rev = "{revision}" }}'
            for name in (
                "ay",
                "ay-bindings",
                "ay-chc",
                "ay-core",
                "ay-dpll",
                "ay-encode",
                "ay-frontend",
                "ay-sys",
            )
        )
        manifest = f"[workspace]\nmembers = []\n\n[workspace.dependencies]\n{dependencies}\n"
        (root / "Cargo.toml").write_text(manifest, encoding="utf-8")
        subprocess.run(["git", "init", "-q"], cwd=root, check=True)
        subprocess.run(["git", "add", "Cargo.toml"], cwd=root, check=True)
        fake_bin = root / "fake-bin"
        fake_bin.mkdir()
        cargo = fake_bin / "cargo"
        cargo.write_text('#!/bin/sh\nexit "${FAKE_CARGO_EXIT:-0}"\n', encoding="utf-8")
        cargo.chmod(0o755)
        return temporary, root, manifest

    def run_helper(self, root: Path, exit_code: int = 0) -> subprocess.CompletedProcess[str]:
        env = os.environ.copy()
        env["PATH"] = f"{root / 'fake-bin'}{os.pathsep}{env['PATH']}"
        env["FAKE_CARGO_EXIT"] = str(exit_code)
        return subprocess.run(
            [sys.executable, str(root / "scripts/bump-ay-pin.py"), "b" * 40, "0.9.0", "--root", str(root)],
            cwd=root,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )

    def test_updates_revision_and_version_uniformly(self) -> None:
        temporary, root, _ = self.fixture()
        with temporary:
            result = self.run_helper(root)
            self.assertEqual(result.returncode, 0, result.stdout)
            manifest = (root / "Cargo.toml").read_text(encoding="utf-8")
            self.assertEqual(manifest.count('version = "0.9.0"'), 8)
            self.assertEqual(manifest.count(f'rev = "{"b" * 40}"'), 8)
            self.assertNotIn('version = "0.8.0"', manifest)

    def test_metadata_failure_restores_manifest(self) -> None:
        temporary, root, original = self.fixture()
        with temporary:
            result = self.run_helper(root, exit_code=31)
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn("restored Cargo.toml", result.stdout)
            self.assertEqual((root / "Cargo.toml").read_text(encoding="utf-8"), original)

    def test_rejects_invalid_version_without_change(self) -> None:
        temporary, root, original = self.fixture()
        with temporary:
            result = subprocess.run(
                [sys.executable, str(root / "scripts/bump-ay-pin.py"), "b" * 40, "0.9", "--root", str(root)],
                cwd=root,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual((root / "Cargo.toml").read_text(encoding="utf-8"), original)


if __name__ == "__main__":
    unittest.main(verbosity=2)
