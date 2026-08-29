#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

"""Regression tests for the AY bump canary's compiletest routing."""

from __future__ import annotations

import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent

CANARY_FILES = (
    "tests/ay/debug_array_option.rs",
    "tests/ay/memory_store_load.rs",
    "tests/ay/multi_struct_debug.rs",
    "tests/ay/tier2_unbounded.rs",
    "tests/ay/tier2_loop_for.rs",
    "tests/ay/test_vec_iter_soundness.rs",
    "tests/ay/ay_self_verify_bv_bitblast.rs",
    "tests/ay/btreemap_store_dual_select.rs",
    "tests/ay/tier2_loop_while.rs",
    "tests/ay/tier2_loop_loop.rs",
    "tests/ay/factorial.rs",
    "tests/ay/test_enumerate_loop.rs",
    "tests/trust-mc/Panic/prove_safety_only.rs",
    "tests/ay/realloc_stale_pointer_fail.rs",
    "tests/ay/ay_self_verify_conflict_analysis.rs",
)


def write_executable(path: Path, source: str) -> None:
    path.write_text(source, encoding="utf-8")
    path.chmod(0o755)


class AyBumpCanaryTests(unittest.TestCase):
    def test_compiletest_files_use_exact_suite_and_filter_once(self) -> None:
        with tempfile.TemporaryDirectory() as raw_root:
            root = Path(raw_root)
            scripts = root / "scripts"
            scripts.mkdir()
            shutil.copy2(ROOT / "scripts/ay-bump-canary.sh", scripts)
            shutil.copy2(ROOT / "scripts/ay_python.sh", scripts)
            shutil.copy2(ROOT / "scripts/resolve-trust-tool.sh", scripts)
            shutil.copy2(ROOT / "rust-toolchain.toml", root)

            for relative in CANARY_FILES:
                source = root / relative
                source.parent.mkdir(parents=True, exist_ok=True)
                source.touch()

            capture = root / "compiletest-calls.tsv"
            write_executable(
                scripts / "ay-compiletest.sh",
                """#!/bin/sh
set -eu
printf '%s\\t%s' "${AY_TEST_TIMEOUT:-missing}" \
    "${AY_EXPECTED_HARNESSES:-missing}" >> "$AY_CANARY_CAPTURE"
for argument in "$@"; do
    printf '\\t%s' "$argument" >> "$AY_CANARY_CAPTURE"
done
printf '\\n' >> "$AY_CANARY_CAPTURE"
""",
            )

            fake_bin = root / "fake-bin"
            fake_bin.mkdir()
            sysroot_bin = root / "trust-sysroot" / "bin"
            sysroot_bin.mkdir(parents=True)
            write_executable(fake_bin / "cargo", "#!/bin/sh\nexit 99\n")
            write_executable(sysroot_bin / "cargo", "#!/bin/sh\nexit 0\n")
            write_executable(sysroot_bin / "targo", "#!/bin/sh\nexit 0\n")
            write_executable(
                sysroot_bin / "rustc",
                '#!/bin/sh\nprintf "%s\\n" "$FAKE_TRUST_SYSROOT"\n',
            )
            write_executable(
                fake_bin / "rustup",
                '#!/bin/sh\nprintf "%s\\n" "$FAKE_PINNED_RUSTC"\n',
            )
            write_executable(
                fake_bin / "python3",
                """#!/bin/sh
if [ "${1:-}" = "-c" ]; then
    exit 0
fi
printf '%s\\n' 1111111111111111111111111111111111111111
""",
            )

            environment = os.environ.copy()
            environment.update(
                {
                    "AY_CANARY_CAPTURE": str(capture),
                    "AY_PYTHON": str(fake_bin / "python3"),
                    "AY_PYTHON_BIN": str(fake_bin / "python3"),
                    "FAKE_PINNED_RUSTC": str(sysroot_bin / "rustc"),
                    "FAKE_TRUST_SYSROOT": str(sysroot_bin.parent),
                    "PATH": f"{fake_bin}{os.pathsep}{environment['PATH']}",
                    "TRUST_MC_RUSTUP": str(fake_bin / "rustup"),
                }
            )
            result = subprocess.run(
                ["bash", "scripts/ay-bump-canary.sh"],
                cwd=root,
                env=environment,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
            self.assertEqual(
                result.returncode,
                0,
                msg=f"stdout:\n{result.stdout}\nstderr:\n{result.stderr}",
            )

            calls = [line.split("\t") for line in capture.read_text().splitlines()]
            self.assertEqual(len(calls), len(CANARY_FILES))
            # The length assertion above supplies the same fail-closed property
            # as zip(strict=True), while keeping this test runnable on the
            # repository's supported system Python 3.9.
            for call, source in zip(calls, CANARY_FILES):
                relative = source.removeprefix("tests/")
                suite, filename = relative.rsplit("/", 1)
                expected_timeout = "30"
                if source.endswith("test_vec_iter_soundness.rs"):
                    expected_timeout = "120"
                elif source.endswith("ay_self_verify_bv_bitblast.rs"):
                    expected_timeout = "90"
                self.assertEqual(
                    call,
                    [
                        expected_timeout,
                        "1",
                        "--skip-build",
                        "--force-rerun",
                        "--filter",
                        filename,
                        suite,
                    ],
                )


if __name__ == "__main__":
    unittest.main()
