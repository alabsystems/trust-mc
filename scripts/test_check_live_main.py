#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

from __future__ import annotations

import subprocess
import json
import sys
import tempfile
import unittest
from unittest.mock import patch
from pathlib import Path
from typing import Sequence

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_live_main import (
    LiveMainError,
    fetch_live_main,
    require_exact_main,
    require_frozen_main_ancestor,
)
import check_live_main


FETCH = ("fetch", "--quiet", "origin", "main")
REV_PARSE = ("rev-parse", "refs/remotes/origin/main")
LS_REMOTE = ("ls-remote", "origin", "refs/heads/main")
AGH_MAIN = ("repo", "refs", "alabsystems/ay", "--ref", "refs/heads/main")


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
        (seed / "src").mkdir()
        (seed / "authority.txt").write_text("first\n", encoding="utf-8")
        (seed / "src/lib.rs").write_text("pub fn selected() -> bool { true }\n")
        self._git(seed, "add", ".")
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
        (seed / "src/lib.rs").write_text("pub fn selected() -> bool { false }\n")
        self._git(seed, "add", ".")
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

    def _agh_fixture(self, root: Path, checkout: Path, commits: list[str], *, fetch_oid: str | None = None):
        calls: list[tuple[str, ...]] = []
        observations = iter(commits)

        def agh(actual_checkout: Path, arguments: Sequence[str]):
            self.assertEqual(actual_checkout, checkout)
            args = tuple(arguments)
            calls.append(args)
            if args == AGH_MAIN:
                return completed(args, stdout=json.dumps([
                    {"oid": next(observations), "ref": "refs/heads/main"},
                ]))
            self.assertEqual(args[:4], ("repo", "fetch", "alabsystems/ay", str(checkout)))
            self.assertEqual(args[4], "--ref")
            self.assertEqual(args[6], "--into")
            self.assertTrue(args[7].startswith("refs/agh/trust-mc-live-main/"))
            self._git(checkout, "fetch", "--quiet", str(root / "remote.git"), f"{fetch_oid or args[5]}:{args[7]}")
            return completed(args)

        return agh, calls

    def _local_only_git(self, checkout: Path, arguments: Sequence[str]):
        self.assertNotIn(arguments[0], ("fetch", "ls-remote"), "GitHub network read bypassed agh")
        return subprocess.run(["git", "-C", str(checkout), *arguments], capture_output=True, text=True)

    def test_aterm_github_uses_agh_and_removes_private_ref(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            checkout, _first, second = self._history(root)
            self._git(checkout, "remote", "set-url", "origin", "git@github.com:alabsystems/ay.git")
            agh, calls = self._agh_fixture(root, checkout, [second, second])
            with patch.object(check_live_main, "_run_git", side_effect=self._local_only_git), \
                    patch.object(check_live_main, "_run_agh", side_effect=agh):
                self.assertEqual(require_exact_main(checkout, "origin", second), second)
            self.assertEqual(len(calls), 3)
            self.assertEqual(self._git(checkout, "rev-parse", "origin/main"), second)
            self.assertEqual(self._git(checkout, "for-each-ref", "refs/agh/"), "")

    def test_aterm_reuses_current_tracking_object_after_two_live_observations(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            checkout, _first, second = self._history(root)
            self._git(checkout, "fetch", "--quiet", "origin", "main")
            self.assertEqual(self._git(checkout, "rev-parse", "origin/main"), second)
            self._git(checkout, "remote", "set-url", "origin", "https://github.com/alabsystems/ay.git")
            agh, calls = self._agh_fixture(root, checkout, [second, second])
            with patch.object(check_live_main, "_run_git", side_effect=self._local_only_git), \
                    patch.object(check_live_main, "_run_agh", side_effect=agh):
                self.assertEqual(require_exact_main(checkout, "origin", second), second)
            self.assertEqual(calls, [AGH_MAIN, AGH_MAIN])
            self.assertEqual(self._git(checkout, "rev-parse", "origin/main"), second)
            self.assertEqual(self._git(checkout, "for-each-ref", "refs/agh/"), "")

    def test_aterm_requires_exact_fetch_when_tracking_object_has_shallow_history(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _full, _first, second = self._history(root)
            shallow = root / "shallow"
            subprocess.run(
                ["git", "clone", "--depth", "1", (root / "remote.git").as_uri(), str(shallow)],
                check=True, capture_output=True, text=True,
            )
            self.assertEqual(self._git(shallow, "rev-parse", "origin/main"), second)
            self.assertEqual(self._git(shallow, "rev-parse", "--is-shallow-repository"), "true")
            self._git(shallow, "remote", "set-url", "origin", "https://github.com/alabsystems/ay.git")
            calls: list[tuple[str, ...]] = []

            def agh(_checkout: Path, arguments: Sequence[str]):
                calls.append(tuple(arguments))
                if tuple(arguments) == AGH_MAIN:
                    return completed(arguments, stdout=json.dumps([
                        {"oid": second, "ref": "refs/heads/main"},
                    ]))
                return completed(arguments, 3, stderr="exact fetch unavailable")

            with patch.object(check_live_main, "_run_git", side_effect=self._local_only_git), \
                    patch.object(check_live_main, "_run_agh", side_effect=agh):
                with self.assertRaisesRegex(LiveMainError, "exact fetch unavailable"):
                    fetch_live_main(shallow, "origin")
            self.assertEqual(calls[0], AGH_MAIN)
            self.assertEqual(calls[1][:2], ("repo", "fetch"))
            self.assertEqual(len(calls), 2)
            self.assertEqual(self._git(shallow, "for-each-ref", "refs/agh/"), "")

    def test_frozen_ancestry_checks_both_live_tips_and_leaves_tracking_unchanged(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            checkout, pinned, tracked = self._history(Path(directory))
            self._git(checkout, "fetch", "--quiet", "origin", "main")
            self._git(checkout, "remote", "set-url", "origin", "https://github.com/alabsystems/ay.git")
            self.assertEqual(self._git(checkout, "rev-parse", "origin/main"), tracked)
            confirmed = "e" * 40
            queries = [{"ancestor": oid, "descendant": confirmed} for oid in (pinned, tracked)]

            for failure in (None, "rewind", "numeric-judgment", "substituted-query"):
                with self.subTest(failure=failure):
                    calls: list[tuple[str, ...]] = []
                    tips = iter((tracked, confirmed))

                    def agh(actual_checkout: Path, arguments: Sequence[str]):
                        self.assertEqual(actual_checkout, checkout)
                        args = tuple(arguments)
                        calls.append(args)
                        if args == AGH_MAIN:
                            return completed(args, stdout=json.dumps([
                                {"oid": next(tips), "ref": "refs/heads/main"},
                            ]))
                        self.assertEqual(args[:-1], (
                            "repo", "commit-ancestry", "alabsystems/ay", str(checkout.resolve()), "--input",
                        ))
                        self.assertEqual(json.loads(Path(args[-1]).read_text()), {
                            "commits": [confirmed], "queries": queries,
                        })
                        answers = [{**query, "contained": True} for query in queries]
                        if failure == "rewind":
                            answers[-1]["contained"] = False
                        elif failure == "numeric-judgment":
                            answers[0]["contained"] = 1
                        elif failure == "substituted-query":
                            answers[0]["ancestor"] = confirmed
                        return completed(args, stdout=json.dumps({
                            "schema": 1, "scope": "commit-parent-ancestry-only-v1",
                            "commits": [confirmed], "queries": answers,
                            "refs_written": False, "checkout_complete": False,
                        }))

                    with patch.object(check_live_main, "_run_git", side_effect=self._local_only_git), \
                            patch.object(check_live_main, "_run_agh", side_effect=agh):
                        if failure is None:
                            self.assertEqual(require_frozen_main_ancestor(
                                checkout, "origin", pinned, commit_ancestry_only=True,
                            ), confirmed)
                        else:
                            message = "is not an ancestor" if failure == "rewind" else "malformed agh ancestry"
                            with self.assertRaisesRegex(LiveMainError, message):
                                require_frozen_main_ancestor(
                                    checkout, "origin", pinned, commit_ancestry_only=True,
                                )
                    self.assertEqual(calls[:2], [AGH_MAIN, AGH_MAIN])
                    self.assertEqual(len(calls), 3)
                    self.assertEqual(self._git(checkout, "rev-parse", "origin/main"), tracked)
                    self.assertEqual(self._git(checkout, "for-each-ref", "refs/agh/"), "")

    def test_aterm_accepts_checked_advancing_main_and_refreshes_tracking_ref(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            checkout, first, second = self._history(root)
            self._git(checkout, "remote", "set-url", "origin", "https://github.com/alabsystems/ay.git")
            agh, _calls = self._agh_fixture(root, checkout, [first, second])
            with patch.object(check_live_main, "_run_git", side_effect=self._local_only_git), \
                    patch.object(check_live_main, "_run_agh", side_effect=agh):
                self.assertEqual(fetch_live_main(checkout, "origin"), second)
            self.assertEqual(self._git(checkout, "rev-parse", "origin/main"), second)
            self.assertEqual(self._git(checkout, "for-each-ref", "refs/agh/"), "")

    def test_aterm_observation_rewind_or_fork_is_refused(self):
        for fork in (False, True):
            with self.subTest(fork=fork), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                checkout, first, second = self._history(root)
                other = first
                if fork:
                    self._git(checkout, 'switch', '-c', 'side', first)
                    (checkout / 'src/lib.rs').write_text('pub fn forked() {}\n')
                    self._git(checkout, 'add', '.')
                    self._git(checkout, 'commit', '-m', 'fork')
                    other = self._git(checkout, 'rev-parse', 'HEAD')
                    self._git(checkout, 'push', str(root / 'remote.git'), 'side')
                self._git(checkout, 'remote', 'set-url', 'origin', 'https://github.com/alabsystems/ay.git')
                agh, _ = self._agh_fixture(root, checkout, [second, other])
                with patch.object(check_live_main, '_run_git', side_effect=self._local_only_git), \
                     patch.object(check_live_main, '_run_agh', side_effect=agh):
                    with self.assertRaisesRegex(LiveMainError, 'rewound or forked'):
                        fetch_live_main(checkout, 'origin')
                self.assertEqual(self._git(checkout, 'rev-parse', 'origin/main'), first)
                self.assertEqual(self._git(checkout, 'for-each-ref', 'refs/agh/'), '')

    def test_aterm_wrong_canonical_url_is_refused_without_transport(self):
        for url in ('https://github.com/alabsystems/ay.git?ref=main',
                    'https://github.com/alabsystems/ay/extra'):
            runner = ScriptedGit({('remote', 'get-url', 'origin'): completed([], stdout=url)})
            with patch.object(check_live_main, '_run_git', side_effect=runner), \
                 patch.object(check_live_main, '_run_agh', side_effect=AssertionError('unexpected transport')):
                with self.assertRaisesRegex(LiveMainError, 'canonical GitHub remote URL'):
                    fetch_live_main(Path('checkout'), 'origin')

    def test_aterm_tracking_update_compares_the_previous_oid(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            checkout, first, second = self._history(root)
            self._git(checkout, "fetch", "--quiet", str(root / "remote.git"), "main")
            self._git(checkout, "remote", "set-url", "origin", "https://github.com/alabsystems/ay.git")
            agh, _calls = self._agh_fixture(root, checkout, [first, first])

            def concurrent_git(actual_checkout: Path, arguments: Sequence[str]):
                if tuple(arguments[:2]) == ("update-ref", "refs/remotes/origin/main"):
                    self._git(checkout, "update-ref", "refs/remotes/origin/main", second, first)
                return self._local_only_git(actual_checkout, arguments)

            with patch.object(check_live_main, "_run_git", side_effect=concurrent_git), \
                    patch.object(check_live_main, "_run_agh", side_effect=agh):
                with self.assertRaisesRegex(LiveMainError, "possibly changed concurrently"):
                    fetch_live_main(checkout, "origin")
            self.assertEqual(self._git(checkout, "rev-parse", "origin/main"), second)
            self.assertEqual(self._git(checkout, "for-each-ref", "refs/agh/"), "")

    def test_aterm_second_observation_must_succeed_completely(self):
        for interrupted in (False, True):
            with self.subTest(interrupted=interrupted), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                checkout, first, second = self._history(root)
                self._git(checkout, "remote", "set-url", "origin", "https://github.com/alabsystems/ay.git")
                agh, calls = self._agh_fixture(root, checkout, [second])

                def incomplete_agh(actual_checkout: Path, arguments: Sequence[str]):
                    if tuple(arguments) == AGH_MAIN and calls:
                        if interrupted:
                            return completed(arguments, 3, stderr="advertisement interrupted")
                        return completed(arguments, stdout="[]")
                    return agh(actual_checkout, arguments)

                with patch.object(check_live_main, "_run_git", side_effect=self._local_only_git), \
                        patch.object(check_live_main, "_run_agh", side_effect=incomplete_agh):
                    with self.assertRaises(LiveMainError):
                        fetch_live_main(checkout, "origin")
                self.assertEqual(self._git(checkout, "rev-parse", "origin/main"), first)
                self.assertEqual(self._git(checkout, "for-each-ref", "refs/agh/"), "")

    def test_aterm_fetched_noncommit_object_is_refused_and_cleaned(self):
        for kind in ("blob", "tree"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                checkout, first, _second = self._history(root)
                expression = f"{first}:authority.txt" if kind == "blob" else f"{first}^{{tree}}"
                oid = self._git(checkout, "rev-parse", expression)
                self.assertEqual(self._git(checkout, "cat-file", "-t", oid), kind)
                # Without an existing tracking commit, the fetched-object type
                # check must itself prevent publishing a noncommit authority.
                self._git(checkout, "update-ref", "-d", "refs/remotes/origin/main")
                self._git(checkout, "remote", "set-url", "origin", "https://github.com/alabsystems/ay.git")
                agh, _calls = self._agh_fixture(root, checkout, [oid, oid])
                with patch.object(check_live_main, "_run_git", side_effect=self._local_only_git), \
                        patch.object(check_live_main, "_run_agh", side_effect=agh):
                    with self.assertRaisesRegex(LiveMainError, "observed main is not a commit object"):
                        fetch_live_main(checkout, "origin")
                self.assertEqual(self._git(checkout, "for-each-ref", "refs/remotes/origin/main"), "")
                self.assertEqual(self._git(checkout, "for-each-ref", "refs/agh/"), "")

    def test_aterm_rejects_wrong_fetched_object_and_cleans_its_ref(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            checkout, first, second = self._history(root)
            self._git(checkout, "remote", "set-url", "origin", "ssh://git@github.com/alabsystems/ay")
            agh, _calls = self._agh_fixture(root, checkout, [second], fetch_oid=first)
            with patch.object(check_live_main, "_run_git", side_effect=self._local_only_git), \
                    patch.object(check_live_main, "_run_agh", side_effect=agh):
                with self.assertRaisesRegex(LiveMainError, "differs from observed main"):
                    fetch_live_main(checkout, "origin")
            self.assertEqual(self._git(checkout, "rev-parse", "origin/main"), first)
            self.assertEqual(self._git(checkout, "for-each-ref", "refs/agh/"), "")

    def test_aterm_agh_failure_does_not_fall_back_to_git(self) -> None:
        runner = ScriptedGit({("remote", "get-url", "origin"): completed([], stdout="https://github.com/alabsystems/ay.git\n")})
        with patch.object(check_live_main, "_run_git", side_effect=runner), \
                patch.object(check_live_main, "_run_agh", return_value=completed([], 1, stderr="agh unavailable")):
            with self.assertRaisesRegex(LiveMainError, "through agh"):
                fetch_live_main(Path("checkout"), "origin")
        self.assertEqual(runner.calls, [("remote", "get-url", "origin")])

    def test_aterm_never_rolls_back_a_newer_tracking_ref(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            checkout, first, second = self._history(root)
            self._git(checkout, "fetch", "--quiet", str(root / "remote.git"), "main")
            self._git(checkout, "update-ref", "refs/remotes/origin/main", second, first)
            self._git(checkout, "remote", "set-url", "origin", "https://github.com/alabsystems/ay.git")
            agh, _calls = self._agh_fixture(root, checkout, [first, first, first])
            with patch.object(check_live_main, "_run_git", side_effect=self._local_only_git), \
                    patch.object(check_live_main, "_run_agh", side_effect=agh):
                with self.assertRaisesRegex(LiveMainError, "tracking ref is ahead of or diverges"):
                    fetch_live_main(checkout, "origin")
            self.assertEqual(self._git(checkout, "rev-parse", "origin/main"), second)
            self.assertEqual(self._git(checkout, "for-each-ref", "refs/agh/"), "")

    def test_newer_concurrent_tracking_is_accepted_only_after_canonical_refresh(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            checkout, first, second = self._history(root)
            self._git(checkout, 'fetch', '--quiet', str(root / 'remote.git'), 'main')
            self._git(checkout, 'update-ref', 'refs/remotes/origin/main', second, first)
            self._git(checkout, 'remote', 'set-url', 'origin', 'https://github.com/alabsystems/ay.git')
            agh, _ = self._agh_fixture(root, checkout, [first, first, second])
            with patch.object(check_live_main, '_run_git', side_effect=self._local_only_git), \
                 patch.object(check_live_main, '_run_agh', side_effect=agh):
                self.assertEqual(fetch_live_main(checkout, 'origin'), second)
            self.assertEqual(self._git(checkout, 'rev-parse', 'origin/main'), second)
            self.assertEqual(self._git(checkout, 'for-each-ref', 'refs/agh/'), '')

    def test_aterm_malformed_main_response_is_rejected(self) -> None:
        entry = {"oid": "1" * 40, "ref": "refs/heads/main"}
        malformed = [
            "not JSON", json.dumps(None), json.dumps(entry), "[]", "[null]", "[[]]",
            json.dumps([entry, entry]),
            json.dumps([entry, {"oid": "2" * 40, "ref": "refs/heads/other"}]),
            json.dumps([dict(entry, ref="refs/heads/other")]),
            json.dumps([dict(entry, extra="unexpected")]),
            json.dumps([{"ref": "refs/heads/main"}]),
            json.dumps([{"oid": "1" * 40}]),
            json.dumps([dict(entry, oid=None)]),
            json.dumps([dict(entry, oid=1)]),
            json.dumps({"ref": "refs/heads/main", "object": {"type": "commit", "sha": "1" * 40}}),
            '[{"oid":"' + "1" * 40 + '","oid":"' + "2" * 40 + '","ref":"refs/heads/main"}]',
            '[{"oid":"' + "1" * 40 + '","ref":"refs/heads/other","ref":"refs/heads/main"}]',
        ]
        for response in malformed:
            with self.subTest(response=response), patch.object(check_live_main, "_run_agh", return_value=completed([], stdout=response)) as agh:
                with self.assertRaisesRegex(LiveMainError, "malformed agh response"):
                    check_live_main._agh_main(Path("checkout"), "alabsystems/ay")
                agh.assert_called_once_with(Path("checkout"), AGH_MAIN)

    def test_aterm_advertised_oid_must_be_one_exact_nonzero_commit(self) -> None:
        for oid in ("0" * 40, "1" * 39, "1" * 41, "A" * 40, "g" * 40, " " + "1" * 40):
            response = json.dumps([{"oid": oid, "ref": "refs/heads/main"}])
            with self.subTest(oid=oid), patch.object(check_live_main, "_run_agh", return_value=completed([], stdout=response)) as agh:
                with self.assertRaisesRegex(LiveMainError, "nonzero full Git commit"):
                    check_live_main._agh_main(Path("checkout"), "alabsystems/ay")
                agh.assert_called_once_with(Path("checkout"), AGH_MAIN)

    def test_native_agh_transport_disallows_anonymous_fallback(self):
        with patch.object(check_live_main.shutil, "which", return_value="/qualified/agh"), \
             patch.object(check_live_main.subprocess, "run", return_value=completed([])) as run:
            check_live_main._run_agh(Path("checkout"), AGH_MAIN)
        self.assertEqual(run.call_args.args[0], ["/qualified/agh", *AGH_MAIN, "--no-anonymous-api"])

    def test_failed_fetch_without_ref_preserves_original_refusal(self):
        with tempfile.TemporaryDirectory() as directory:
            checkout, first, second = self._history(Path(directory))
            self._git(checkout, "remote", "set-url", "origin", "https://github.com/alabsystems/ay.git")
            response = json.dumps([{"oid": second, "ref": "refs/heads/main"}])
            with patch.object(check_live_main, "_run_agh", side_effect=[
                    completed([], stdout=response), completed([], 1, stderr="fetch refused")]):
                with self.assertRaisesRegex(LiveMainError, "could not fetch.*fetch refused"):
                    fetch_live_main(checkout, "origin")
            self.assertEqual(self._git(checkout, "rev-parse", "origin/main"), first)
            self.assertEqual(self._git(checkout, "for-each-ref", "refs/agh/"), "")

    def test_aterm_missing_executable_is_not_a_git_fallback(self) -> None:
        with patch.object(check_live_main.shutil, "which", return_value=None):
            with self.assertRaisesRegex(LiveMainError, "cannot resolve agh"):
                check_live_main._run_agh(Path("checkout"), AGH_MAIN)

    def test_local_remote_preserves_git_transport(self) -> None:
        commit = "1" * 40
        runner = ScriptedGit({
            ("remote", "get-url", "origin"): completed([], stdout="/local/remote.git"),
            FETCH: completed(FETCH),
            REV_PARSE: completed(REV_PARSE, stdout=commit),
            LS_REMOTE: completed(LS_REMOTE, stdout=f"{commit}\trefs/heads/main\n"),
        })
        with patch.object(check_live_main, "_run_git", side_effect=runner), \
                patch.object(check_live_main, "_run_agh", side_effect=AssertionError("unexpected agh")):
            self.assertEqual(fetch_live_main(Path("checkout"), "origin"), commit)
        self.assertEqual(runner.calls, [("remote", "get-url", "origin"), FETCH, REV_PARSE, LS_REMOTE])


if __name__ == "__main__":
    unittest.main()
