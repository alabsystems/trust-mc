#!/usr/bin/env python3
"""Regression tests for AY manifest/lock authority validation."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from ay_manifest_pin import expected_ay_pin_from_locked_workspace


AY_URL = "https://github.com/alabsystems/ay.git"


def git(repo: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(repo), *args], text=True
    ).strip()


class AyManifestPinTests(unittest.TestCase):
    def make_ay(self, base: Path, version: str = "0.15.0") -> tuple[Path, str]:
        ay = base / "ay"
        ay.mkdir()
        (ay / "Cargo.toml").write_text(
            f'[workspace]\nmembers = ["crates/*"]\n\n'
            f'[workspace.package]\nversion = "{version}"\n',
            encoding="utf-8",
        )
        for package in ("ay", "ay-chc", "ay-proof"):
            crate = ay / "crates" / package
            crate.mkdir(parents=True, exist_ok=True)
            (crate / "Cargo.toml").write_text(
                f'[package]\nname = "{package}"\nversion = "{version}"\n',
                encoding="utf-8",
            )
        subprocess.run(["git", "init", "-q", str(ay)], check=True)
        git(ay, "config", "user.name", "TrustMC tests")
        git(ay, "config", "user.email", "trust-mc-tests@example.invalid")
        git(ay, "remote", "add", "origin", AY_URL)
        git(ay, "add", ".")
        git(ay, "commit", "-q", "-m", "fixture")
        return ay, git(ay, "rev-parse", "HEAD")

    def write_manifest(
        self,
        root: Path,
        revision: str,
        version: str = "0.15.0",
        *,
        patch: bool = True,
        patch_path: str = "../ay/crates/ay",
    ) -> None:
        text = f'''[workspace]
members = []

[workspace.dependencies]
ay = {{ version = "{version}", git = "{AY_URL}", rev = "{revision}" }}
ay-chc = {{ version = "{version}", git = "{AY_URL}", rev = "{revision}" }}
'''
        if patch:
            text += f'''
[patch."{AY_URL}"]
ay = {{ path = "{patch_path}" }}
ay-chc = {{ path = "../ay/crates/ay-chc" }}
ay-proof = {{ path = "../ay/crates/ay-proof" }}
'''
        (root / "Cargo.toml").write_text(text, encoding="utf-8")

    def write_lock(
        self,
        root: Path,
        version: str = "0.15.0",
        *,
        revision: str | None = None,
        extra: tuple[str, ...] = ("ay-proof",),
    ) -> None:
        blocks: list[str] = []
        for package in ("ay", "ay-chc", *extra):
            source = ""
            if revision is not None:
                source = (
                    f'source = "git+{AY_URL}?rev={revision}#{revision}"\n'
                )
            blocks.append(
                f'[[package]]\nname = "{package}"\nversion = "{version}"\n{source}'
            )
        (root / "Cargo.lock").write_text(
            "version = 4\n\n" + "\n".join(blocks), encoding="utf-8"
        )

    def fixture(self) -> tuple[tempfile.TemporaryDirectory[str], Path, Path, str]:
        temporary = tempfile.TemporaryDirectory()
        base = Path(temporary.name)
        root = base / "trust-mc"
        root.mkdir()
        ay, revision = self.make_ay(base)
        self.write_manifest(root, revision)
        self.write_lock(root)
        return temporary, root, ay, revision

    def test_accepts_sourceless_lock_bound_to_exact_sibling(self) -> None:
        temporary, root, _, revision = self.fixture()
        with temporary:
            self.assertEqual(expected_ay_pin_from_locked_workspace(root), revision)

    def test_rejects_sourceless_lock_without_patch(self) -> None:
        temporary, root, _, revision = self.fixture()
        with temporary:
            self.write_manifest(root, revision, patch=False)
            with self.assertRaisesRegex(ValueError, "require a canonical .*patch"):
                expected_ay_pin_from_locked_workspace(root)

    def test_rejects_sourceless_lock_at_wrong_sibling_commit(self) -> None:
        temporary, root, ay, revision = self.fixture()
        with temporary:
            (ay / "README.md").write_text("new commit\n", encoding="utf-8")
            git(ay, "add", "README.md")
            git(ay, "commit", "-q", "-m", "advance")
            with self.assertRaisesRegex(ValueError, "sibling HEAD .* differs"):
                expected_ay_pin_from_locked_workspace(root)
            self.assertNotEqual(revision, git(ay, "rev-parse", "HEAD"))

    def test_rejects_sourceless_lock_version_not_in_sibling(self) -> None:
        temporary, root, _, _ = self.fixture()
        with temporary:
            self.write_lock(root, "0.14.0")
            with self.assertRaisesRegex(ValueError, "differs from sibling version"):
                expected_ay_pin_from_locked_workspace(root)

    def test_rejects_sourceless_package_absent_from_sibling(self) -> None:
        temporary, root, _, _ = self.fixture()
        with temporary:
            self.write_lock(root, extra=("ay-not-present",))
            with self.assertRaisesRegex(ValueError, "absent from"):
                expected_ay_pin_from_locked_workspace(root)

    def test_rejects_patch_outside_exact_sibling_crate(self) -> None:
        temporary, root, _, revision = self.fixture()
        with temporary:
            self.write_manifest(root, revision, patch_path="../ay/crates/ay-chc")
            with self.assertRaisesRegex(ValueError, "expected .*crates/ay"):
                expected_ay_pin_from_locked_workspace(root)

    def test_rejects_registry_ay_package(self) -> None:
        temporary, root, _, _ = self.fixture()
        with temporary:
            lock = (root / "Cargo.lock").read_text(encoding="utf-8")
            lock = lock.replace(
                'name = "ay-proof"\nversion = "0.15.0"',
                'name = "ay-proof"\nversion = "0.15.0"\n'
                'source = "registry+https://github.com/rust-lang/crates.io-index"',
            )
            (root / "Cargo.lock").write_text(lock, encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "unauthorised source"):
                expected_ay_pin_from_locked_workspace(root)

    def test_preserves_git_lock_validation_without_sibling(self) -> None:
        with tempfile.TemporaryDirectory() as name:
            root = Path(name) / "trust-mc"
            root.mkdir()
            revision = "a" * 40
            self.write_manifest(root, revision, patch=False)
            self.write_lock(root, revision=revision, extra=())
            self.assertEqual(expected_ay_pin_from_locked_workspace(root), revision)


if __name__ == "__main__":
    unittest.main(verbosity=2)
