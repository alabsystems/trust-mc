#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_live_main import (
    LiveMainError,
    fetch_live_main,
    require_exact_main,
    require_frozen_main_ancestor,
)


FETCH = ("fetch", "--quiet", "origin", "main")
REV_PARSE = ("rev-parse", "refs/remotes/origin/main")
LS_REMOTE = ("ls-remote", "origin", "refs/heads/main")


def completed(
    arguments: Sequence[str], returncode: int = 0, stdout: str = "", stderr: str = ""
) -> subprocess.CompletedProcess[str]:
    return subprocess.CompletedProcess(arguments, returncode, stdout, stderr)


class ScriptedGit:
    def __init__(
        self, results: dict[tuple[str, ...], subprocess.CompletedProcess[str]]
    ) -> None:
        self.results = results
        self.calls: list[tuple[str, ...]] = []

    def __call__(
        self, _checkout: Path, arguments: Sequence[str]
    ) -> subprocess.CompletedProcess[str]:
        key = tuple(arguments)
        self.calls.append(key)
        return self.results[key]


class LiveMainTests(unittest.TestCase):
    def _git(self, checkout: Path, *arguments: str) -> str:
        return subprocess.check_output(
            ["git", "-C", str(checkout), *arguments],
            text=True,
            stderr=subprocess.PIPE,
        ).strip()

    def _history(self, root: Path) -> tuple[Path, str, str]:
        remote = root / "remote.git"
        seed = root / "seed"
        checkout = root / "checkout"
        subprocess.run(
            ["git", "init", "--bare", str(remote)], check=True, capture_output=True, text=True
        )
        subprocess.run(
            ["git", "init", "-b", "main", str(seed)],
            check=True,
            capture_output=True,
            text=True,
        )
        self._git(seed, "config", "user.name", "Trust MC Test")
        self._git(seed, "config", "user.email", "trust-mc-test@example.invalid")
        (seed / "authority.txt").write_text("first\n", encoding="utf-8")
        self._git(seed, "add", "authority.txt")
        self._git(seed, "commit", "-m", "first")
        first = self._git(seed, "rev-parse", "HEAD")
        self._git(seed, "remote", "add", "origin", str(remote))
        self._git(seed, "push", "-u", "origin", "main")
        subprocess.run(
            ["git", "clone", "--branch", "main", str(remote), str(checkout)],
            check=True,
            capture_output=True,
            text=True,
        )
        self._git(checkout, "config", "user.name", "Trust MC Test")
        self._git(checkout, "config", "user.email", "trust-mc-test@example.invalid")
        (seed / "authority.txt").write_text("second\n", encoding="utf-8")
        self._git(seed, "add", "authority.txt")
        self._git(seed, "commit", "-m", "second")
        second = self._git(seed, "rev-parse", "HEAD")
        self._git(seed, "push", "origin", "main")
        return checkout, first, second

    def test_fetch_refreshes_stale_tracking_ref(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            checkout, first, second = self._history(Path(directory))
            self.assertEqual(self._git(checkout, "rev-parse", "origin/main"), first)
            self.assertEqual(require_exact_main(checkout, "origin", second), second)
            self.assertEqual(self._git(checkout, "rev-parse", "origin/main"), second)

    def test_missing_live_ref_is_rejected(self) -> None:
        commit = "1" * 40
        runner = ScriptedGit(
            {
                FETCH: completed(FETCH),
                REV_PARSE: completed(REV_PARSE, stdout=f"{commit}\n"),
                LS_REMOTE: completed(LS_REMOTE),
            }
        )
        with self.assertRaisesRegex(LiveMainError, "live origin/main is missing"):
            fetch_live_main(Path("checkout"), "origin", run_git=runner)

    def test_fetched_live_mismatch_is_rejected(self) -> None:
        fetched = "1" * 40
        live = "2" * 40
        runner = ScriptedGit(
            {
                FETCH: completed(FETCH),
                REV_PARSE: completed(REV_PARSE, stdout=f"{fetched}\n"),
                LS_REMOTE: completed(
                    LS_REMOTE, stdout=f"{live}\trefs/heads/main\n"
                ),
            }
        )
        with self.assertRaisesRegex(LiveMainError, "differs from live main"):
            fetch_live_main(Path("checkout"), "origin", run_git=runner)

    def test_exact_authority_rejects_stale_expected_commit(self) -> None:
        current = "1" * 40
        stale = "2" * 40
        runner = ScriptedGit(
            {
                FETCH: completed(FETCH),
                REV_PARSE: completed(REV_PARSE, stdout=f"{current}\n"),
                LS_REMOTE: completed(
                    LS_REMOTE, stdout=f"{current}\trefs/heads/main\n"
                ),
            }
        )
        with self.assertRaisesRegex(LiveMainError, "differs from expected"):
            require_exact_main(
                Path("checkout"), "origin", stale, run_git=runner
            )

    def test_exact_authority_rejects_all_zero_expected_commit(self) -> None:
        with self.assertRaisesRegex(LiveMainError, "nonzero full Git commit"):
            require_exact_main(Path("checkout"), "origin", "0" * 40)

    def test_frozen_content_accepts_descendant_live_main(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            checkout, first, second = self._history(Path(directory))
            self.assertEqual(
                require_frozen_main_ancestor(checkout, "origin", first), second
            )

    def test_frozen_content_rejects_nonancestor(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            checkout, first, _second = self._history(Path(directory))
            self._git(checkout, "switch", "-c", "side", first)
            (checkout / "side.txt").write_text("side\n", encoding="utf-8")
            self._git(checkout, "add", "side.txt")
            self._git(checkout, "commit", "-m", "side")
            side = self._git(checkout, "rev-parse", "HEAD")
            self._git(checkout, "switch", "main")
            with self.assertRaisesRegex(LiveMainError, "is not an ancestor"):
                require_frozen_main_ancestor(checkout, "origin", side)


if __name__ == "__main__":
    unittest.main()
