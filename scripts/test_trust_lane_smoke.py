#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Regression tests for `scripts/trust-lane-smoke.sh` input canonicalization.

The smoke compares the backend dylib path it passed to `trust-mc-driver`
against the compile argv the driver records.  The route canonicalizes the
sysroot and the dylib before spawning trustc, so a KEY reached through a
symbolic link makes every one of those checks report a mismatch on a run whose
verdicts are all correct.  `target` is a symlink to `target.noindex` in every
checkout on this host, so that is the normal way to reach the KEY.

These tests drive the script's input handling only: the run dies on a missing
backend dylib, and the path it names in that message is the evidence of which
form of the KEY path the rest of the script would have used.
"""

from __future__ import annotations

import json
import os
import signal
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
SMOKE = ROOT / "scripts/trust-lane-smoke.sh"


def smoke_fixture_directory():
    # The real smoke rejects build outputs beneath /tmp. Its input-handling
    # fixtures must reach that code even when the runner's TMPDIR is /tmp/.ubd.
    base = Path.home() / ".cache" / "trust-mc-smoke-tests"
    base.mkdir(parents=True, exist_ok=True)
    return tempfile.TemporaryDirectory(prefix="fixture-", dir=base)


def write_executable(path: Path, source: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source, encoding="utf-8")
    path.chmod(0o755)


class SmokeKeyPathTests(unittest.TestCase):
    def fixture(self, root: Path) -> dict[str, str]:
        """A stub seal, driver and ay CLI, plus a KEY directory with no dylib."""
        seal = root / "seal"
        write_executable(seal / "bin/trustc", "#!/bin/sh\nexit 0\n")
        (seal / "lib").mkdir(parents=True)
        (seal / "lib/librustc_driver-0123456789abcdef.dylib").write_text("stub")
        (seal / "PROVENANCE").write_text(
            "artifact_driver_sha256=" + "a" * 64 + "\n", encoding="utf-8"
        )
        write_executable(root / "bin/trust-mc-driver", "#!/bin/sh\nexit 0\n")
        write_executable(root / "bin/ay", "#!/bin/sh\nexit 0\n")

        # The real KEY, and a symlinked route to it, as `target` gives.
        keyed = root / "real/keyed"
        key = keyed / ("driver-" + "a" * 16)
        (key / "codegen-backends").mkdir(parents=True)
        (key / "KEY.json").write_text(json.dumps({"key": key.name}), encoding="utf-8")
        (root / "link").symlink_to(keyed)

        out = root / "out"
        out.mkdir()
        env = dict(os.environ)
        env.update(
            TRUST_MC_SMOKE_TRUSTC=str(seal / "bin/trustc"),
            TRUST_MC_SMOKE_DRIVER=str(root / "bin/trust-mc-driver"),
            TRUST_MC_SMOKE_AY_BIN=str(root / "bin/ay"),
            TRUST_MC_SMOKE_OUT=str(out),
            TRUST_MC_SMOKE_STORE=str(root / "empty-store"),
        )
        (root / "empty-store").mkdir()
        return env

    def run_smoke(self, key: Path, env: dict[str, str]) -> subprocess.CompletedProcess:
        env = dict(env, TRUST_MC_SMOKE_KEY=str(key))
        return subprocess.run(
            [str(SMOKE)],
            cwd=str(ROOT),
            env=env,
            capture_output=True,
            text=True,
            check=False,
        )

    def test_a_key_reached_through_a_symlink_is_canonicalized(self) -> None:
        with smoke_fixture_directory() as temporary:
            root = Path(temporary).resolve()
            env = self.fixture(root)
            key_name = "driver-" + "a" * 16
            result = self.run_smoke(root / "link" / key_name, env)
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
            message = result.stderr
            self.assertIn("no backend dylib at", message)
            self.assertIn(
                str(root / "real/keyed" / key_name / "codegen-backends"), message
            )
            self.assertNotIn(str(root / "link"), message)

    def test_a_key_that_is_not_a_directory_is_refused(self) -> None:
        with smoke_fixture_directory() as temporary:
            root = Path(temporary).resolve()
            env = self.fixture(root)
            result = self.run_smoke(root / "absent", env)
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
            self.assertIn("no KEY directory at", result.stderr)


class SmokeOtherSealTests(unittest.TestCase):
    """The cross-seal refusal case needs another installed seal to name.

    The search took a seal's driver sha256 from its PROVENANCE only, while this
    seal's own identity (and the route's, and build-keyed's) falls back to the
    sha256 of its librustc_driver. Seals 9178 and 9192 ship no PROVENANCE, so on
    that store the search found nothing: `refuse-other-seal-trustc` was SKIPPED,
    or FAILED under TRUST_MC_SMOKE_REQUIRE_OTHER_SEAL=1, with a second seal
    installed beside this one.
    """

    def announced_other_seal(self, root: Path, own_driver: str, other_driver: str) -> str:
        store = root / "store"
        for build, driver in (("9192", own_driver), ("9178", other_driver)):
            seal = store / build
            write_executable(seal / "bin/trustc", "#!/bin/sh\nexit 0\n")
            (seal / "lib").mkdir(parents=True)
            (seal / f"lib/librustc_driver-{build}.dylib").write_text(driver)
            (store / f"{build}.ready").write_text("ok\n")
        write_executable(root / "bin/trust-mc-driver", "#!/bin/sh\nexit 0\n")
        write_executable(root / "bin/ay", "#!/bin/sh\nexit 0\n")
        key = root / "key"
        (key / "codegen-backends").mkdir(parents=True)
        (key / "KEY.json").write_text("{}", encoding="utf-8")
        (key / "codegen-backends/librustc_codegen_trust_mc.dylib").write_text("stub")
        (root / "out").mkdir()
        env = dict(os.environ)
        env.update(
            TRUST_MC_SMOKE_TRUSTC=str(store / "9192/bin/trustc"),
            TRUST_MC_SMOKE_DRIVER=str(root / "bin/trust-mc-driver"),
            TRUST_MC_SMOKE_AY_BIN=str(root / "bin/ay"),
            TRUST_MC_SMOKE_OUT=str(root / "out"),
            TRUST_MC_SMOKE_STORE=str(store),
            TRUST_MC_SMOKE_KEY=str(key),
            TRUST_MC_SMOKE_TIMEOUT="5",
        )
        # The announcement precedes every case; stop the run there.
        smoke = subprocess.Popen(
            [str(SMOKE)],
            cwd=str(ROOT),
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            start_new_session=True,
        )
        try:
            assert smoke.stdout is not None
            for line in smoke.stdout:
                if line.startswith("trust-lane-smoke: other-seal trustc="):
                    return line.strip().split("=", 1)[1]
            self.fail("the smoke never announced the other seal: " + smoke.stderr.read())
        finally:
            try:
                if smoke.poll() is None:
                    try:
                        os.killpg(smoke.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                try:
                    smoke.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(smoke.pid, signal.SIGKILL)
                    smoke.wait(timeout=5)
            finally:
                smoke.stdout.close()
                smoke.stderr.close()
        return ""

    def test_a_seal_without_provenance_is_found_by_its_driver_sha256(self) -> None:
        with smoke_fixture_directory() as temporary:
            root = Path(temporary).resolve()
            found = self.announced_other_seal(root, "driver 9192", "driver 9178")
            self.assertEqual(found, str(root / "store/9178/bin/trustc"))

    def test_a_seal_with_the_same_driver_is_not_another_seal(self) -> None:
        with smoke_fixture_directory() as temporary:
            root = Path(temporary).resolve()
            self.assertEqual(self.announced_other_seal(root, "one driver", "one driver"), "none")

    def test_early_failure_preserves_error_and_reaps_smoke(self) -> None:
        with smoke_fixture_directory() as temporary:
            root = Path(temporary).resolve()
            refused = root / "refused-smoke"
            write_executable(refused, "#!/bin/sh\necho 'fixture refusal' >&2\nexit 2\n")
            with mock.patch(__name__ + ".SMOKE", refused):
                with self.assertRaisesRegex(AssertionError, "never announced.*fixture refusal"):
                    self.announced_other_seal(root, "own driver", "other driver")


if __name__ == "__main__":
    unittest.main()
