#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

"""Fetch and validate an exact or frozen first-party private-main authority."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path
from typing import Callable, Sequence


COMMIT_RE = re.compile(r"[0-9a-f]{40}")
GitRunner = Callable[[Path, Sequence[str]], subprocess.CompletedProcess[str]]


class LiveMainError(ValueError):
    """A remote main authority could not be established fail-closed."""


def _run_git(checkout: Path, arguments: Sequence[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", "-C", str(checkout), *arguments],
        check=False,
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


def fetch_live_main(
    checkout: Path, remote: str, *, run_git: GitRunner = _run_git
) -> str:
    """Refresh remote/main, query the live ref independently, and require equality."""

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
    run_git: GitRunner = _run_git,
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
    run_git: GitRunner = _run_git,
) -> str:
    expected = _require_commit(expected, "frozen authority")
    _require_success(
        run_git(checkout, ("cat-file", "-e", f"{expected}^{{commit}}")),
        f"frozen content commit does not exist locally: {expected}",
    )
    fetched = fetch_live_main(checkout, remote, run_git=run_git)
    ancestor = run_git(checkout, ("merge-base", "--is-ancestor", expected, fetched))
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
