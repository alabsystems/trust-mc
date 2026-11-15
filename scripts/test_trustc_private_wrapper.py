#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Hermetic regression tests for the Trust rustc-private sysroot wrapper."""

from __future__ import annotations

import os
import platform
import subprocess
import tempfile
import unittest
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:
    import tomli as tomllib


ROOT = Path(__file__).resolve().parent.parent
WRAPPER = ROOT / "scripts/trustc-private-wrapper.sh"
# The wrapper picks the shared-library suffix from `uname -s`, so a fixture
# built with the other host's spelling never matches and every overlay test
# fails for a reason that has nothing to do with the wrapper's logic.
DRIVER_SUFFIX = "dylib" if platform.system() == "Darwin" else "so"
FIXTURE_TRIPLE = (
    "aarch64-apple-darwin" if platform.system() == "Darwin" else "aarch64-unknown-linux-gnu"
)
DRIVER_TARGETS = {
    "trust_mc_compiler",
    "trust_mc_codegen_shared",
    "trust_mc_codegen_types",
    "trust_mc_kani_types",
    "scanner",
    "scan",
    "trust_mc_engine",
    "rustc_codegen_trust_mc",
}


def write_executable(path: Path, source: str) -> None:
    path.write_text(source, encoding="utf-8")
    path.chmod(0o755)


class TrustPrivateWrapperTests(unittest.TestCase):
    def fixture(
        self, *, private_driver_hash: str = "a1b2c3d4"
    ) -> tuple[tempfile.TemporaryDirectory[str], dict[str, str], Path, Path]:
        temporary = tempfile.TemporaryDirectory(prefix="trust private wrapper ")
        root = Path(temporary.name)
        triple = FIXTURE_TRIPLE
        sysroot = root / "trust-sysroot"
        target_lib = sysroot / "lib/rustlib" / triple / "lib"
        target_lib.mkdir(parents=True)
        (sysroot / f"lib/librustc_driver-a1b2c3d4.{DRIVER_SUFFIX}").touch()
        (target_lib / "libstd-fixture.rlib").touch()

        private_root = root / "rustc-private-sysroots"
        tool_root = private_root / "rustc-private-tool-fixture"
        tool_lib = tool_root / triple
        tool_lib.mkdir(parents=True)
        (tool_lib / f"librustc_driver-{private_driver_hash}.{DRIVER_SUFFIX}").touch()
        (tool_lib / "librustc_middle-fixture.rmeta").touch()
        (tool_root / "host").mkdir()
        (tool_root / "host/libproc_macro-fixture.rlib").touch()

        log = root / "rustc.log"
        rustc = root / "fake-rustc"
        write_executable(
            rustc,
            "#!/bin/sh\n"
            'if [ "$1" = "--print" ] && [ "$2" = "sysroot" ]; then\n'
            '  printf "%s\\n" "$FAKE_SYSROOT"\n'
            "  exit 0\n"
            "fi\n"
            'if [ "$1" = "--print" ] && [ "$2" = "target-libdir" ]; then\n'
            '  printf "%s\\n" "$FAKE_TARGET_LIBDIR"\n'
            "  exit 0\n"
            "fi\n"
            'if [ "$1" = "--version" ] && [ "$2" = "--verbose" ]; then\n'
            '  printf "rustc 1.99.0-dev\\n"\n'
            '  [ -n "$FAKE_TRUST_COMPILER" ] && printf "trust: 0.1.0\\n"\n'
            "  exit 0\n"
            "fi\n"
            'printf "%s\\n" "$@" >> "$FAKE_RUSTC_LOG"\n',
        )
        environment = os.environ.copy()
        environment.update(
            {
                "CARGO_TARGET_DIR": str(root / "cargo-target"),
                "FAKE_RUSTC_LOG": str(log),
                "FAKE_SYSROOT": str(sysroot),
                "FAKE_TARGET_LIBDIR": str(target_lib),
                # These fixtures model the Trust compiler, the one that keeps
                # its rustc_private closure in a separate private sysroot.
                "FAKE_TRUST_COMPILER": "1",
                "TRUST_PRIVATE_SYSROOTS": str(private_root),
            }
        )
        return temporary, environment, rustc, log

    def invoke(
        self,
        environment: dict[str, str],
        rustc: Path,
        crate_name: str,
        crate_type: list[str] | None = None,
    ) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [
                str(WRAPPER),
                str(rustc),
                "--crate-name",
                crate_name,
                *(crate_type if crate_type is not None else ["--crate-type", "lib"]),
                "fixture.rs",
            ],
            cwd=ROOT,
            env=environment,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )

    def test_driver_target_gets_exact_overlay_and_dynamic_link_flags(self) -> None:
        temporary, environment, rustc, log = self.fixture()
        with temporary:
            overlay = Path(environment["CARGO_TARGET_DIR"]) / "trust-private-sysroot-a1b2c3d4"
            overlay.mkdir(parents=True)
            stale = overlay / "stale-before-rebuild"
            stale.touch()
            result = self.invoke(environment, rustc, "trust_mc_kani_types")
            self.assertEqual(result.returncode, 0, result.stderr)
            args = log.read_text(encoding="utf-8").splitlines()
            self.assertIn("--sysroot", args)
            # The wrapper reports a fully resolved path; on macOS the temporary
            # directory reaches it through the /var -> /private/var symlink.
            self.assertIn(str(overlay.resolve()), args)
            self.assertIn("-Cprefer-dynamic", args)
            self.assertFalse(stale.exists())
            libs = overlay / "lib/rustlib" / FIXTURE_TRIPLE / "lib"
            self.assertTrue((libs / "libstd-fixture.rlib").exists())
            self.assertTrue((libs / "librustc_middle-fixture.rmeta").exists())

    def test_backend_cdylib_gets_overlay_without_rpaths(self) -> None:
        # librustc_codegen_trust_mc is dlopened inside the compiler that already
        # loaded its driver: an absolute rpath could make dyld load a second one.
        for spelling in (["--crate-type", "cdylib"], ["--crate-type=cdylib"]):
            temporary, environment, rustc, log = self.fixture()
            with temporary:
                result = self.invoke(environment, rustc, "rustc_codegen_trust_mc", spelling)
                self.assertEqual(result.returncode, 0, result.stderr)
                args = log.read_text(encoding="utf-8").splitlines()
                overlay = Path(environment["CARGO_TARGET_DIR"]) / "trust-private-sysroot-a1b2c3d4"
                self.assertIn("--sysroot", args)
                self.assertIn(str(overlay.resolve()), args)
                self.assertNotIn("-Cprefer-dynamic", args)
                self.assertFalse(any("-rpath" in arg for arg in args), args)
                self.assertFalse(any(arg.startswith("-Clink-arg") for arg in args), args)

    def test_ordinary_dependency_bypasses_private_overlay(self) -> None:
        temporary, environment, rustc, log = self.fixture()
        with temporary:
            environment["TRUST_PRIVATE_SYSROOTS"] = str(
                Path(temporary.name) / "missing-private-root"
            )
            result = self.invoke(environment, rustc, "tracing_core")
            self.assertEqual(result.returncode, 0, result.stderr)
            args = log.read_text(encoding="utf-8").splitlines()
            self.assertNotIn("--sysroot", args)
            self.assertNotIn("-Cprefer-dynamic", args)
            self.assertFalse(any(arg.startswith("-Clink-arg") for arg in args))

    def test_a_driver_crate_on_a_stock_toolchain_bypasses_the_overlay(self) -> None:
        # The Kani lane builds these six crates on the frozen nightly-2025-12-03,
        # whose `rustc-dev` component IS its private closure. Demanding a Trust
        # private snapshot there fails closed on the only toolchain that can
        # currently build trust-mc-compiler at all.
        temporary, environment, rustc, log = self.fixture()
        with temporary:
            del environment["FAKE_TRUST_COMPILER"]
            environment["TRUST_PRIVATE_SYSROOTS"] = str(
                Path(temporary.name) / "missing-private-root"
            )
            result = self.invoke(environment, rustc, "trust_mc_compiler")
            self.assertEqual(result.returncode, 0, result.stderr)
            args = log.read_text(encoding="utf-8").splitlines()
            self.assertNotIn("--sysroot", args)
            self.assertNotIn("-Cprefer-dynamic", args)

    def test_driver_crate_on_trust_without_configured_snapshot_passes_through(self) -> None:
        # The overlay is opt-in. The fixture's rustc-private-sysroots directory
        # sits beside the Trust sysroot WITH a matching driver hash, which the
        # wrapper used to discover on its own; without TRUST_PRIVATE_SYSROOTS
        # that discovery must not arm the overlay.
        temporary, environment, rustc, log = self.fixture()
        with temporary:
            del environment["TRUST_PRIVATE_SYSROOTS"]
            result = self.invoke(environment, rustc, "trust_mc_compiler")
            self.assertEqual(result.returncode, 0, result.stderr)
            args = log.read_text(encoding="utf-8").splitlines()
            self.assertEqual(
                args,
                ["--crate-name", "trust_mc_compiler", "--crate-type", "lib", "fixture.rs"],
            )
            overlay = Path(environment["CARGO_TARGET_DIR"]) / "trust-private-sysroot-a1b2c3d4"
            self.assertFalse(overlay.exists())

    def test_empty_configured_snapshot_passes_through(self) -> None:
        temporary, environment, rustc, log = self.fixture()
        with temporary:
            environment["TRUST_PRIVATE_SYSROOTS"] = ""
            result = self.invoke(environment, rustc, "trust_mc_kani_types")
            self.assertEqual(result.returncode, 0, result.stderr)
            args = log.read_text(encoding="utf-8").splitlines()
            self.assertNotIn("--sysroot", args)
            self.assertNotIn("-Cprefer-dynamic", args)

    def test_configured_root_without_matching_snapshot_fails_closed(self) -> None:
        # An explicit configuration is honoured strictly: pointing at a root
        # that holds no snapshot for the active driver is a hard error, even
        # with matching snapshots where a bootstrap layout puts them. The
        # fixture already has one beside the sysroot; add one inside it too.
        # Only the configured roots are ever searched.
        temporary, environment, rustc, log = self.fixture()
        with temporary:
            root = Path(temporary.name)
            inner_lib = (
                root / "trust-sysroot/rustc-private-sysroots/rustc-private-tool-inner" / FIXTURE_TRIPLE
            )
            inner_lib.mkdir(parents=True)
            (inner_lib / f"librustc_driver-a1b2c3d4.{DRIVER_SUFFIX}").touch()
            empty_root = root / "configured-but-empty"
            empty_root.mkdir()
            environment["TRUST_PRIVATE_SYSROOTS"] = str(empty_root)
            result = self.invoke(environment, rustc, "trust_mc_kani_types")
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("no rustc-private-tool sysroot matches active driver hash a1b2c3d4", result.stderr)
            self.assertIn(f"searched {empty_root}\n", result.stderr)
            self.assertFalse(log.exists())

    def test_mismatched_private_driver_fails_closed(self) -> None:
        # Also the guard on the bypass above: this fixture IS the Trust
        # compiler, so identity-scoping must not weaken the refusal.
        temporary, environment, rustc, log = self.fixture(private_driver_hash="deadbeef")
        with temporary:
            result = self.invoke(environment, rustc, "trust_mc_kani_types")
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("no rustc-private-tool sysroot matches active driver hash a1b2c3d4", result.stderr)
            self.assertFalse(log.exists())

    def test_writable_cache_file_is_never_executed(self) -> None:
        temporary, environment, rustc, log = self.fixture()
        with temporary:
            target = Path(environment["CARGO_TARGET_DIR"])
            target.mkdir(parents=True)
            marker = Path(temporary.name) / "cache-code-executed"
            (target / ".trust-private-env").write_text(
                f'touch "{marker}"\nTMC_SYSROOT="/"\n', encoding="utf-8"
            )

            result = self.invoke(environment, rustc, "trust_mc_kani_types")

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertFalse(marker.exists(), "writable cache contents were executed")
            self.assertTrue(log.exists())

    def test_hyphenated_environment_names_reach_rustc(self) -> None:
        # cargo exports CARGO_BIN_EXE_<name> to integration-test compiles, and
        # this workspace has a binary named `trust-mc`. A name with a hyphen is
        # not a shell identifier, and dash (Debian and Ubuntu's /bin/sh) drops
        # such names from the environment it passes on exec, so tests/cli.rs
        # fails to compile through a /bin/sh wrapper on those hosts.
        temporary, environment, _rustc, _log = self.fixture()
        with temporary:
            root = Path(temporary.name)
            seen = root / "seen-environment"
            rustc = root / "fake-rustc-environment"
            write_executable(
                rustc,
                "#!/usr/bin/env python3\n"
                "import os, sys\n"
                "args = sys.argv[1:]\n"
                "if args[:2] == ['--print', 'sysroot']:\n"
                "    print(os.environ['FAKE_SYSROOT']); sys.exit(0)\n"
                "if args[:2] == ['--print', 'target-libdir']:\n"
                "    print(os.environ['FAKE_TARGET_LIBDIR']); sys.exit(0)\n"
                "if args[:2] == ['--version', '--verbose']:\n"
                "    print('rustc 1.99.0-dev')\n"
                "    if os.environ.get('FAKE_TRUST_COMPILER'): print('trust: 0.1.0')\n"
                "    sys.exit(0)\n"
                "with open(os.environ['FAKE_SEEN'], 'a') as out:\n"
                "    out.write(os.environ.get('CARGO_BIN_EXE_trust-mc', '<missing>') + '\\n')\n",
            )
            environment["FAKE_SEEN"] = str(seen)
            environment["CARGO_BIN_EXE_trust-mc"] = "/fixture/bin/trust-mc"
            for crate in ("fixture_dependency", "trust_mc_compiler"):
                result = self.invoke(environment, rustc, crate)
                self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(
                seen.read_text(encoding="utf-8").splitlines(),
                ["/fixture/bin/trust-mc", "/fixture/bin/trust-mc"],
            )

    def test_config_does_not_set_reserved_authority_environment(self) -> None:
        config = (ROOT / ".cargo/config.toml").read_text(encoding="utf-8")
        self.assertNotIn("rustc-wrapper", tomllib.loads(config).get("build", {}))
        self.assertNotIn("TRUST_PRIVATE_DRIVER_CRATES", tomllib.loads(config).get("env", {}))

    def test_caller_cannot_replace_the_private_driver_target_list(self) -> None:
        temporary, environment, rustc, log = self.fixture()
        with temporary:
            environment["TRUST_PRIVATE_DRIVER_CRATES"] = "build_trust_mc"
            ordinary = self.invoke(environment, rustc, "build_trust_mc")
            self.assertEqual(ordinary.returncode, 0, ordinary.stderr)
            self.assertNotIn("--sysroot", log.read_text(encoding="utf-8"))
            log.unlink()
            driver = self.invoke(environment, rustc, "trust_mc_compiler")
            self.assertEqual(driver.returncode, 0, driver.stderr)
            self.assertIn("--sysroot", log.read_text(encoding="utf-8"))


if __name__ == "__main__":
    unittest.main(verbosity=2)
