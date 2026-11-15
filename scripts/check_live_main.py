#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

"""Fetch and validate an exact or frozen first-party private-main authority."""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import uuid
from pathlib import Path
from typing import Callable, Sequence


from git_authority_environment import git_environment


COMMIT_RE = re.compile(r"[0-9a-f]{40}")
GitRunner = Callable[[Path, Sequence[str]], subprocess.CompletedProcess[str]]
GITHUB_REMOTE_RE = re.compile(
    r"(?:https://github\.com/|ssh://git@github\.com/|git@github\.com:)"
    r"([A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+?)(?:\.git)?/?"
)


class LiveMainError(ValueError):
    """A remote main authority could not be established fail-closed."""


def _run_git(checkout: Path, arguments: Sequence[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", "-C", str(checkout), *arguments],
        check=False,
        env=git_environment(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )


def _require_success(
    result: subprocess.CompletedProcess[str], description: str
) -> str:
    if result.returncode != 0:
        detail = result.stderr.strip() or result.stdout.strip()
        suffix = f": {detail}" if detail else ""
        raise LiveMainError(f"{description}{suffix}")
    return result.stdout.strip()


def _require_commit(value: str, description: str) -> str:
    if COMMIT_RE.fullmatch(value) is None or value == "0" * 40:
        raise LiveMainError(
            f"{description} is not a nonzero full Git commit: {value!r}"
        )
    return value


def _run_agh(checkout: Path, arguments: Sequence[str]) -> subprocess.CompletedProcess[str]:
    executable = shutil.which("agh")
    if executable is None:
        raise LiveMainError("cannot resolve agh for GitHub authority reads")
    try:
        return subprocess.run(
            [executable, *arguments, "--no-anonymous-api"], cwd=checkout, check=False,
            env=git_environment(),
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        )
    except OSError as error:
        raise LiveMainError(f"cannot run agh: {error}") from error


def _agh_main(checkout: Path, repository: str) -> str:
    output = _require_success(
        _run_agh(checkout, ("repo", "refs", repository, "--ref", "refs/heads/main")),
        f"could not query live {repository}/main through agh",
    )

    def unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate reference field")
            result[key] = value
        return result

    try:
        response = json.loads(output, object_pairs_hook=unique_object)
        if not isinstance(response, list) or len(response) != 1:
            raise ValueError("expected exactly one advertised reference")
        reference = response[0]
        if not isinstance(reference, dict) or set(reference) != {"oid", "ref"}:
            raise ValueError("unexpected reference fields")
        if reference["ref"] != "refs/heads/main":
            raise ValueError("unexpected reference")
        commit = reference["oid"]
        if not isinstance(commit, str):
            raise ValueError("commit is not text")
    except (ValueError, KeyError, TypeError) as error:
        raise LiveMainError(f"malformed agh response for {repository}/main") from error
    return _require_commit(commit, f"live {repository}/main")


def _fetch_agh_main(checkout: Path, remote: str, repository: str, run_git: GitRunner) -> str:
    """Authenticate observed main snapshots and allow only proven forward motion."""
    observed = _agh_main(checkout, repository)
    temporary_refs: dict[str, str] = {}
    try:
        def fetch_observation(oid: str) -> str:
            private_ref = f"refs/agh/trust-mc-live-main/{uuid.uuid4().hex}"
            temporary_refs[private_ref] = oid
            _require_success(
                _run_agh(checkout, (
                    "repo", "fetch", repository, str(checkout),
                    "--ref", oid, "--into", private_ref,
                )),
                f"could not fetch {repository}/main through agh",
            )
            fetched = _require_commit(_require_success(
                run_git(checkout, ("rev-parse", private_ref)),
                "could not read agh's fetched main",
            ), "agh fetched main")
            temporary_refs[private_ref] = fetched
            if fetched != oid:
                raise LiveMainError(f"agh fetched main {fetched} differs from observed main {oid}")
            kind = _require_success(run_git(checkout, ("cat-file", "-t", fetched)), "could not inspect fetched main")
            if kind != "commit":
                raise LiveMainError("observed main is not a commit object")
            return fetched

        fetched = fetch_observation(observed)
        live = _agh_main(checkout, repository)
        if live != fetched:
            # Both objects came from independent canonical Agh observations.
            # An advancing branch does not change the selected immutable cut.
            # Fetch the second observed object and prove the direction; do not
            # insist on a quiescent branch or assert equivalence to future main.
            latest = fetch_observation(live)
            ancestor = run_git(checkout, ("merge-base", "--is-ancestor", fetched, latest))
            if ancestor.returncode == 1:
                raise LiveMainError("observed main rewound or forked between Agh observations")
            _require_success(ancestor, "could not compare observed main snapshots")
            fetched = latest
        tracking_ref = f"refs/remotes/{remote}/main"
        previous = run_git(checkout, ("rev-parse", "--verify", "--quiet", tracking_ref))
        if previous.returncode not in (0, 1):
            _require_success(previous, f"could not read {remote}/main tracking ref")
        old = _require_commit(previous.stdout.strip(), "old tracking main") if previous.returncode == 0 else "0" * 40
        if previous.returncode == 0 and old != fetched:
            ancestor = run_git(checkout, ("merge-base", "--is-ancestor", old, fetched))
            if ancestor.returncode == 1:
                # A concurrent checker may already have authenticated a newer
                # tracking snapshot. One bounded fresh canonical observation
                # can establish that forward motion; never trust tracking alone.
                refreshed = fetch_observation(_agh_main(checkout, repository))
                for before in (fetched, old):
                    direction = run_git(checkout, ("merge-base", "--is-ancestor", before, refreshed))
                    if direction.returncode == 1:
                        raise LiveMainError(f"{remote}/main tracking ref is ahead of or diverges from observed main")
                    _require_success(direction, "could not compare refreshed canonical main")
                fetched = refreshed
            else:
                _require_success(ancestor, "could not compare tracking and observed main")
        _require_success(
            run_git(checkout, ("update-ref", tracking_ref, fetched, old)),
            f"could not refresh {remote}/main tracking ref (possibly changed concurrently)",
        )
        return fetched
    finally:
        for private_ref, cleanup_oid in temporary_refs.items():
            present = run_git(checkout, ("rev-parse", "--verify", "--quiet", private_ref))
            if present.returncode == 1:
                continue
            _require_success(present, "could not inspect temporary agh main ref")
            _require_success(
                run_git(checkout, ("update-ref", "-d", private_ref, cleanup_oid)),
                "could not remove temporary agh main ref",
            )


def fetch_live_main(
    checkout: Path, remote: str, *, run_git: GitRunner | None = None
) -> str:
    """Authenticate canonical main observations; Agh snapshots may advance monotonically."""

    environment_transport = run_git is None
    run_git = _run_git if run_git is None else run_git
    if environment_transport:
        remote_url = _require_success(
            run_git(checkout, ("remote", "get-url", remote)),
            f"could not resolve {remote} authority",
        )
        github = GITHUB_REMOTE_RE.fullmatch(remote_url)
        if github is not None:
            return _fetch_agh_main(checkout, remote, github[1], run_git)
        if "github.com" in remote_url.lower():
            raise LiveMainError("GitHub authority requires a canonical GitHub remote URL")

    _require_success(
        run_git(checkout, ("fetch", "--quiet", remote, "main")),
        f"could not fetch {remote}/main",
    )
    fetched = _require_commit(
        _require_success(
            run_git(checkout, ("rev-parse", f"refs/remotes/{remote}/main")),
            f"checkout has no fetched {remote}/main",
        ),
        f"fetched {remote}/main",
    )
    live_output = _require_success(
        run_git(checkout, ("ls-remote", remote, "refs/heads/main")),
        f"could not query live {remote}/main",
    )
    if not live_output:
        raise LiveMainError(f"live {remote}/main is missing")
    lines = [line.split() for line in live_output.splitlines() if line.strip()]
    if len(lines) != 1 or len(lines[0]) != 2 or lines[0][1] != "refs/heads/main":
        raise LiveMainError(f"live {remote}/main response is malformed: {live_output!r}")
    live = _require_commit(lines[0][0], f"live {remote}/main")
    if fetched != live:
        raise LiveMainError(
            f"fetched {remote}/main {fetched} differs from live main {live}"
        )
    return fetched


def require_exact_main(
    checkout: Path,
    remote: str,
    expected: str,
    *,
    run_git: GitRunner | None = None,
) -> str:
    expected = _require_commit(expected, "expected authority")
    fetched = fetch_live_main(checkout, remote, run_git=run_git)
    if fetched != expected:
        raise LiveMainError(
            f"fetched {remote}/main {fetched} differs from expected {expected}"
        )
    return fetched


def require_frozen_main_ancestor(
    checkout: Path,
    remote: str,
    expected: str,
    *,
    run_git: GitRunner | None = None,
) -> str:
    expected = _require_commit(expected, "frozen authority")
    local_git = _run_git if run_git is None else run_git
    _require_success(
        local_git(checkout, ("cat-file", "-e", f"{expected}^{{commit}}")),
        f"frozen content commit does not exist locally: {expected}",
    )
    fetched = fetch_live_main(checkout, remote, run_git=run_git)
    ancestor = local_git(checkout, ("merge-base", "--is-ancestor", expected, fetched))
    if ancestor.returncode == 1:
        raise LiveMainError(
            f"frozen content {expected} is not an ancestor of live main {fetched}"
        )
    _require_success(ancestor, "could not compare frozen content with live main")
    return fetched


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("exact", "frozen"))
    parser.add_argument("checkout", type=Path)
    parser.add_argument("remote")
    parser.add_argument("expected")
    args = parser.parse_args(argv)
    try:
        if args.mode == "exact":
            resolved = require_exact_main(args.checkout, args.remote, args.expected)
        else:
            resolved = require_frozen_main_ancestor(
                args.checkout, args.remote, args.expected
            )
    except LiveMainError as error:
        print(f"check-live-main: error: {error}", file=sys.stderr)
        return 1
    print(resolved)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
