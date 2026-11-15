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
OVERRIDE_ENV = "TRUST_MC_TRUST_TOOLCHAIN"
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
        self,
        suffix: str = "",
        *,
        include_cargo: bool = True,
        include_targo: bool = True,
        include_trustc: bool = True,
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
            "trustc": sysroot_bin / f"trustc{suffix}",
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
        if include_trustc:
            write_executable(paths["trustc"], "#!/bin/sh\nexit 0\n")
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
        # An override exported by whoever runs the tests must not leak in.
        environment.pop(OVERRIDE_ENV, None)
        return temporary, environment, paths

    def seal(
        self,
        base: Path,
        build: str,
        *,
        reports_sysroot: Path | None = None,
        include_targo: bool = True,
    ) -> Path:
        """A numbered seal directory, under a path with a space like the real
        store, whose bin/rustc reports it (or reports_sysroot) as its sysroot."""
        seal = base / "Application Support" / "store" / "trust" / build
        seal_bin = seal / "bin"
        seal_bin.mkdir(parents=True)
        write_executable(
            seal_bin / "rustc",
            "#!/bin/sh\n"
            'printf "%s\\n" "$*" >> "$FAKE_RUSTC_LOG"\n'
            f"printf '%s\\n' '{reports_sysroot or seal}'\n",
        )
        write_executable(seal_bin / "cargo", "#!/bin/sh\nexit 0\n")
        write_executable(seal_bin / "trustc", "#!/bin/sh\nexit 0\n")
        if include_targo:
            write_executable(seal_bin / "targo", "#!/bin/sh\nexit 0\n")
        return seal

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
                    for requested in ("targo", "trustc", "sysroot"):
                        result = self.run_resolver(environment, requested)
                        self.assertEqual(result.returncode, 0, result.stderr)
                        self.assertEqual(result.stdout.strip(), str(paths[requested]))
                    self.assertEqual(
                        paths["rustup_log"].read_text(encoding="utf-8").splitlines(),
                        ["which rustc --toolchain trust"] * 3,
                    )
                    self.assertEqual(
                        paths["rustc_log"].read_text(encoding="utf-8").splitlines(),
                        ["--print sysroot"] * 3,
                    )

    def test_override_unset_resolves_rust_toolchain_channel(self) -> None:
        temporary, environment, paths = self.fixture()
        with temporary:
            self.assertNotIn(OVERRIDE_ENV, environment)
            result = self.run_resolver(environment, "sysroot")
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.strip(), str(paths["sysroot"]))
            self.assertEqual(
                paths["rustup_log"].read_text(encoding="utf-8").splitlines(),
                ["which rustc --toolchain trust"],
            )

    def test_override_rustup_toolchain_replaces_the_channel_for_every_tool(self) -> None:
        temporary, environment, paths = self.fixture()
        with temporary:
            environment[OVERRIDE_ENV] = "trust-8560"
            for requested in ("targo", "trustc", "sysroot"):
                result = self.run_resolver(environment, requested)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.strip(), str(paths[requested]))
            self.assertEqual(
                paths["rustup_log"].read_text(encoding="utf-8").splitlines(),
                ["which rustc --toolchain trust-8560"] * 3,
            )

    def test_rustup_is_never_allowed_to_install_the_named_toolchain(self) -> None:
        temporary, environment, paths = self.fixture()
        with temporary:
            # This fake rustup resolves only when auto-install is off, the way
            # rustup 1.29 refuses rather than downloads an uninstalled toolchain.
            write_executable(
                paths["rustup"],
                "#!/bin/sh\n"
                'printf "%s\\n" "$*" >> "$FAKE_RUSTUP_LOG"\n'
                '[ "${RUSTUP_AUTO_INSTALL-}" = 0 ] || exit 7\n'
                'printf "%s\\n" "$FAKE_PINNED_RUSTC"\n',
            )
            environment["RUSTUP_AUTO_INSTALL"] = "1"
            for override in (None, "nightly-2026-09-01"):
                with self.subTest(override=override):
                    if override is not None:
                        environment[OVERRIDE_ENV] = override
                    result = self.run_resolver(environment, "sysroot")
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(result.stdout.strip(), str(paths["sysroot"]))

    def test_override_seal_directory_resolves_every_tool_without_rustup(self) -> None:
        temporary, environment, paths = self.fixture()
        with temporary:
            seal = self.seal(Path(temporary.name), "8560")
            # rustup, which would resolve the moving channel, must not be asked.
            write_executable(
                paths["rustup"],
                '#!/bin/sh\necho called >> "$FAKE_RUSTUP_LOG"\nexit 91\n',
            )
            environment[OVERRIDE_ENV] = str(seal)
            canonical = seal.resolve()
            expected = {
                "targo": canonical / "bin" / "targo",
                "trustc": canonical / "bin" / "trustc",
                "sysroot": canonical,
            }
            for requested, path in expected.items():
                result = self.run_resolver(environment, requested)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.strip(), str(path))
            self.assertFalse(paths["rustup_log"].exists())

    def test_override_seal_directory_prints_canonical_paths(self) -> None:
        # A parent link or a trailing slash still names one build, and every
        # tool is printed under that build's canonical directory.
        temporary, environment, paths = self.fixture()
        with temporary:
            base = Path(temporary.name)
            seal = self.seal(base, "8560")
            (base / "store-link").symlink_to(base / "Application Support" / "store")
            environment[OVERRIDE_ENV] = f"{base / 'store-link'}/trust/8560/"
            canonical = seal.resolve()
            expected = {
                "targo": canonical / "bin" / "targo",
                "trustc": canonical / "bin" / "trustc",
                "sysroot": canonical,
            }
            for requested, path in expected.items():
                result = self.run_resolver(environment, requested)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.strip(), str(path))
            self.assertFalse(paths["rustup_log"].exists())

    def test_unresolvable_override_fails_closed(self) -> None:
        cases = {
            "empty": ("", "is set but empty"),
            "relative path": (
                "store/trust/8560",
                "neither a rustup toolchain name nor an absolute seal directory",
            ),
            "option-shaped": (
                "--help",
                "neither a rustup toolchain name nor an absolute seal directory",
            ),
            "unknown rustup toolchain": (
                "trust-0000",
                "rustup cannot resolve rustc for TRUST_MC_TRUST_TOOLCHAIN=trust-0000",
            ),
            "missing directory": ("<base>/store/trust/9999", "names no directory"),
            "directory without rustc": ("<base>/empty", "it has no bin/rustc"),
            "proxy directory": ("<base>/proxy", "its bin/rustc reports sysroot"),
            "seal without targo": ("<base>/no-targo", "pinned Trust sysroot has no targo frontend"),
            # store/trust/current moves with the host's seal: naming it holds nothing.
            "moving seal link": ("<base>/current", "is a symbolic link"),
            "moving seal link with trailing slash": ("<base>/current/", "is a symbolic link"),
        }
        for name, (value, fragment) in cases.items():
            with self.subTest(case=name):
                temporary, environment, paths = self.fixture()
                with temporary:
                    base = Path(temporary.name)
                    (base / "empty").mkdir()
                    if name == "unknown rustup toolchain":
                        write_executable(paths["rustup"], "#!/bin/sh\nexit 1\n")
                    if name == "proxy directory":
                        # A directory whose rustc is really another toolchain's.
                        proxy = self.seal(base, "proxy", reports_sysroot=paths["sysroot"])
                        value = str(proxy)
                    if name == "seal without targo":
                        value = str(self.seal(base, "8560", include_targo=False))
                    if name.startswith("moving seal link"):
                        (base / "current").symlink_to(self.seal(base, "8571"))
                    environment[OVERRIDE_ENV] = value.replace("<base>", str(base))
                    for requested in ("targo", "sysroot"):
                        result = self.run_resolver(environment, requested)
                        self.assertEqual(result.returncode, 2, result.stdout)
                        self.assertEqual(result.stdout, "")
                        self.assertIn(fragment, result.stderr)
                        self.assertIn(OVERRIDE_ENV, result.stderr)

    def test_rustup_toolchain_linked_to_a_moving_seal_link_fails_closed(self) -> None:
        # ~/.rustup/toolchains/trust -> store/trust/current -> store/trust/8571.
        temporary, environment, paths = self.fixture()
        with temporary:
            base = Path(temporary.name)
            seal = self.seal(base, "8571")
            current = seal.parent / "current"
            current.symlink_to(seal)
            toolchains = base / "rustup-home" / "toolchains"
            toolchains.mkdir(parents=True)
            (toolchains / "trust").symlink_to(current)
            (toolchains / "trust-8571").symlink_to(seal)
            environment["FAKE_PINNED_RUSTC"] = str(toolchains / "trust" / "bin" / "rustc")
            environment[OVERRIDE_ENV] = "trust"
            for requested in ("targo", "sysroot"):
                result = self.run_resolver(environment, requested)
                self.assertEqual(result.returncode, 2, result.stdout)
                self.assertEqual(result.stdout, "")
                self.assertIn("itself a symbolic link", result.stderr)
                self.assertIn(f"{OVERRIDE_ENV}=trust", result.stderr)

            # The same seal through a toolchain linked to the numbered directory holds.
            environment["FAKE_PINNED_RUSTC"] = str(toolchains / "trust-8571" / "bin" / "rustc")
            environment[OVERRIDE_ENV] = "trust-8571"
            result = self.run_resolver(environment, "trustc")
            self.assertEqual(result.returncode, 0, result.stderr)

    def test_missing_pinned_frontend_fails_closed(self) -> None:
        temporary, environment, _ = self.fixture(include_targo=False)
        with temporary:
            result = self.run_resolver(environment, "trustc")
            self.assertEqual(result.returncode, 2)
            self.assertIn("pinned Trust sysroot has no targo frontend", result.stderr)

    def test_missing_pinned_trustc_fails_closed(self) -> None:
        temporary, environment, _ = self.fixture(include_trustc=False)
        with temporary:
            result = self.run_resolver(environment, "targo")
            self.assertEqual(result.returncode, 2)
            self.assertEqual(result.stdout, "")
            self.assertIn("pinned Trust sysroot has no trustc compiler", result.stderr)

    def test_stock_names_are_refused_and_name_the_trust_spelling(self) -> None:
        # Owner ruling 2026-09-23: never a stock `cargo` or `rustc`. The sysroot's
        # `cargo` is the upstream-Cargo persona, so resolving it handed callers
        # stock cargo; `rustc` taught them the stock spelling of trustc.
        temporary, environment, paths = self.fixture()
        with temporary:
            for requested, trust_name in (("cargo", "targo"), ("rustc", "trustc")):
                with self.subTest(requested=requested):
                    result = self.run_resolver(environment, requested)
                    self.assertEqual(result.returncode, 2, result.stdout)
                    self.assertEqual(result.stdout, "")
                    self.assertIn(f"`{requested}` is a stock name", result.stderr)
                    self.assertIn(f"ask for `{trust_name}`", result.stderr)
            self.assertFalse(paths["rustup_log"].exists())

    def test_trust_names_resolve_without_a_cargo_persona(self) -> None:
        temporary, environment, paths = self.fixture(include_cargo=False)
        with temporary:
            for requested in ("targo", "trustc", "sysroot"):
                result = self.run_resolver(environment, requested)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.strip(), str(paths[requested]))

    def test_rustup_failure_fails_closed(self) -> None:
        temporary, environment, paths = self.fixture()
        with temporary:
            write_executable(paths["rustup"], "#!/bin/sh\nexit 91\n")
            result = self.run_resolver(environment, "targo")
            self.assertEqual(result.returncode, 2)
            self.assertIn("rustup cannot resolve rustc", result.stderr)

    def test_help_does_not_invoke_rustup(self) -> None:
        temporary, environment, paths = self.fixture()
        with temporary:
            result = self.run_resolver(environment, "--help")
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("targo|trustc|sysroot", result.stdout)
            self.assertNotIn("cargo|", result.stdout)
            self.assertIn(OVERRIDE_ENV, result.stdout)
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
        self.assertNotIn('[cargo, "metadata"', bump_source)
        self.assertIn('[targo, "metadata"', bump_source)


if __name__ == "__main__":
    unittest.main(verbosity=2)
