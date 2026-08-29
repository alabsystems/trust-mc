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
AY_URL = "https://github.com/alabsystems/ay.git"
AY_PACKAGES = (
    "ay",
    "ay-bindings",
    "ay-chc",
    "ay-core",
    "ay-dpll",
    "ay-encode",
    "ay-frontend",
    "ay-sys",
)


def git(repo: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(repo), *args], text=True
    ).strip()


class BumpAyPinTests(unittest.TestCase):
    def make_ay(self, base: Path) -> tuple[str, str]:
        ay = base / "ay"
        ay.mkdir()
        (ay / "Cargo.toml").write_text(
            '[workspace]\nmembers = ["crates/*"]\n\n'
            '[workspace.package]\nversion = "0.8.0"\n',
            encoding="utf-8",
        )
        for package in AY_PACKAGES:
            crate = ay / "crates" / package
            crate.mkdir(parents=True, exist_ok=True)
            (crate / "Cargo.toml").write_text(
                f'[package]\nname = "{package}"\nversion = "0.8.0"\n',
                encoding="utf-8",
            )
        subprocess.run(["git", "init", "-q", str(ay)], check=True)
        git(ay, "config", "user.name", "TrustMC tests")
        git(ay, "config", "user.email", "trust-mc-tests@example.invalid")
        git(ay, "remote", "add", "origin", AY_URL)
        git(ay, "add", ".")
        git(ay, "commit", "-q", "-m", "old version")
        old_revision = git(ay, "rev-parse", "HEAD")
        root_manifest = ay / "Cargo.toml"
        root_manifest.write_text(
            root_manifest.read_text(encoding="utf-8").replace("0.8.0", "0.9.0"),
            encoding="utf-8",
        )
        for package in AY_PACKAGES:
            manifest = ay / "crates" / package / "Cargo.toml"
            manifest.write_text(
                manifest.read_text(encoding="utf-8").replace("0.8.0", "0.9.0"),
                encoding="utf-8",
            )
        git(ay, "add", ".")
        git(ay, "commit", "-q", "-m", "new version")
        return old_revision, git(ay, "rev-parse", "HEAD")

    def fixture(
        self,
    ) -> tuple[
        tempfile.TemporaryDirectory[str], Path, str, str, bytes, str
    ]:
        temporary = tempfile.TemporaryDirectory()
        base = Path(temporary.name)
        root = base / "trust-mc"
        (root / "scripts").mkdir(parents=True)
        for script in (
            "bump-ay-pin.py",
            "check_first_party_git_pins.py",
            "ay_manifest_pin.py",
            "resolve-trust-tool.sh",
        ):
            shutil.copy2(ROOT / "scripts" / script, root / "scripts" / script)
        shutil.copy2(ROOT / "rust-toolchain.toml", root)
        old_revision, new_revision = self.make_ay(base)
        dependencies = "\n".join(
            f'{name} = {{ version = "0.8.0", git = "{AY_URL}", '
            f'rev = "{old_revision}" }}'
            for name in AY_PACKAGES
        )
        patches = "\n".join(
            f'{name} = {{ path = "../ay/crates/{name}" }}'
            for name in AY_PACKAGES
        )
        manifest = (
            f"[workspace]\nmembers = []\n\n[workspace.dependencies]\n{dependencies}\n\n"
            f'[patch."{AY_URL}"]\n{patches}\n'
        )
        (root / "Cargo.toml").write_text(manifest, encoding="utf-8")
        lock = "version = 4\n\n" + "\n".join(
            f'[[package]]\nname = "{name}"\nversion = "0.8.0"\n'
            for name in AY_PACKAGES
        )
        (root / "Cargo.lock").write_text(lock, encoding="utf-8")
        subprocess.run(["git", "init", "-q", str(root)], check=True)
        git(root, "add", "Cargo.toml", "Cargo.lock")

        fake_bin = root / "fake-bin"
        fake_bin.mkdir()
        sysroot_bin = root / "trust-sysroot" / "bin"
        sysroot_bin.mkdir(parents=True)
        cargo = sysroot_bin / "cargo"
        cargo.write_text(
            f"""#!{sys.executable}
import os
import sys
from pathlib import Path

root = Path.cwd()
args = sys.argv[1:]
with Path(os.environ["FAKE_CARGO_LOG"]).open("a", encoding="utf-8") as log:
    log.write(" ".join(args) + "\\n")
mode = os.environ.get("FAKE_CARGO_MODE", "ok")
if "--locked" not in args:
    lock = root / "Cargo.lock"
    if mode != "stale-refresh":
        lock.write_text(
            lock.read_text(encoding="utf-8").replace("0.8.0", "0.9.0"),
            encoding="utf-8",
        )
    if mode == "refresh-failure":
        raise SystemExit(31)
elif mode == "locked-failure":
    raise SystemExit(32)
""",
            encoding="utf-8",
        )
        cargo.chmod(0o755)
        (sysroot_bin / "targo").write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        (sysroot_bin / "targo").chmod(0o755)
        (sysroot_bin / "rustc").write_text(
            '#!/bin/sh\nprintf "%s\\n" "$FAKE_TRUST_SYSROOT"\n',
            encoding="utf-8",
        )
        (sysroot_bin / "rustc").chmod(0o755)
        (fake_bin / "rustup").write_text(
            '#!/bin/sh\nprintf "%s\\n" "$FAKE_PINNED_RUSTC"\n',
            encoding="utf-8",
        )
        (fake_bin / "rustup").chmod(0o755)
        # If the helper regresses to ambient PATH selection, fail distinctly.
        (fake_bin / "cargo").write_text("#!/bin/sh\nexit 99\n", encoding="utf-8")
        (fake_bin / "cargo").chmod(0o755)
        return (
            temporary,
            root,
            manifest,
            lock,
            (root / "Cargo.lock").read_bytes(),
            new_revision,
        )

    def run_helper(
        self, root: Path, revision: str, mode: str = "ok"
    ) -> subprocess.CompletedProcess[str]:
        env = os.environ.copy()
        env["PATH"] = f"{root / 'fake-bin'}{os.pathsep}{env['PATH']}"
        env["FAKE_CARGO_MODE"] = mode
        env["FAKE_CARGO_LOG"] = str(root / "cargo.log")
        env["FAKE_PINNED_RUSTC"] = str(root / "trust-sysroot/bin/rustc")
        env["FAKE_TRUST_SYSROOT"] = str(root / "trust-sysroot")
        env["TRUST_MC_RUSTUP"] = str(root / "fake-bin/rustup")
        return subprocess.run(
            [
                sys.executable,
                str(root / "scripts/bump-ay-pin.py"),
                revision,
                "0.9.0",
                "--root",
                str(root),
            ],
            cwd=root,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )

    def test_refreshes_lock_before_locked_validation(self) -> None:
        temporary, root, _, _, _, new_revision = self.fixture()
        with temporary:
            result = self.run_helper(root, new_revision)
            self.assertEqual(result.returncode, 0, result.stdout)
            manifest = (root / "Cargo.toml").read_text(encoding="utf-8")
            lock = (root / "Cargo.lock").read_text(encoding="utf-8")
            self.assertEqual(manifest.count('version = "0.9.0"'), len(AY_PACKAGES))
            self.assertEqual(
                manifest.count(f'rev = "{new_revision}"'), len(AY_PACKAGES)
            )
            self.assertEqual(lock.count('version = "0.9.0"'), len(AY_PACKAGES))
            commands = (root / "cargo.log").read_text(encoding="utf-8").splitlines()
            self.assertEqual(
                commands,
                [
                    "metadata --format-version 1",
                    "metadata --locked --format-version 1",
                ],
            )

    def test_refresh_failure_restores_manifest_and_lock(self) -> None:
        temporary, root, original, _, original_lock, new_revision = self.fixture()
        with temporary:
            result = self.run_helper(root, new_revision, "refresh-failure")
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn("restored Cargo.toml and Cargo.lock", result.stdout)
            self.assertEqual((root / "Cargo.toml").read_text(encoding="utf-8"), original)
            self.assertEqual((root / "Cargo.lock").read_bytes(), original_lock)

    def test_stale_refresh_is_rejected_and_rolled_back(self) -> None:
        temporary, root, original, _, original_lock, new_revision = self.fixture()
        with temporary:
            result = self.run_helper(root, new_revision, "stale-refresh")
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertIn("differs from sibling version", result.stdout)
            self.assertEqual((root / "Cargo.toml").read_text(encoding="utf-8"), original)
            self.assertEqual((root / "Cargo.lock").read_bytes(), original_lock)
            self.assertEqual(
                (root / "cargo.log").read_text(encoding="utf-8").splitlines(),
                ["metadata --format-version 1"],
            )

    def test_locked_metadata_failure_restores_manifest_and_lock(self) -> None:
        temporary, root, original, _, original_lock, new_revision = self.fixture()
        with temporary:
            result = self.run_helper(root, new_revision, "locked-failure")
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertEqual((root / "Cargo.toml").read_text(encoding="utf-8"), original)
            self.assertEqual((root / "Cargo.lock").read_bytes(), original_lock)

    def test_rejects_invalid_version_without_change(self) -> None:
        temporary, root, original, _, original_lock, new_revision = self.fixture()
        with temporary:
            result = subprocess.run(
                [
                    sys.executable,
                    str(root / "scripts/bump-ay-pin.py"),
                    new_revision,
                    "0.9",
                    "--root",
                    str(root),
                ],
                cwd=root,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual((root / "Cargo.toml").read_text(encoding="utf-8"), original)
            self.assertEqual((root / "Cargo.lock").read_bytes(), original_lock)


if __name__ == "__main__":
    unittest.main(verbosity=2)
