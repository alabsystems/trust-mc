#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
"""The landing gate's doc and link check: no change adds a broken relative link.

Reads every tracked Markdown file at the base revision and at the head (a
revision, or the working tree), resolves each relative link target
(``[text](path)``, ``[text](path#anchor)``, ``<path>`` autolinks are not
links to files and are ignored, as are URLs with a scheme and pure
``#anchors``), and fails on every broken link the head has that the base did
not: a new link to nothing, or an old link whose target the change deleted or
renamed. Links that were already broken at the base are counted and
reported, not failed (the check ratchets; it does not re-judge main).

Exit 0 when the change adds no broken link, 1 otherwise. Python floor 3.9.
"""

from __future__ import annotations

import argparse
import posixpath
import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

REPO_ROOT = Path(__file__).resolve().parent.parent
# [text](target) and [text](target "title"); images too. Code spans are
# stripped first so `[a](b)` inside backticks is not a link.
_LINK_RE = re.compile(r"!?\[[^\]\n]*\]\(\s*<?([^)\s>]+)>?(?:\s+\"[^\"]*\")?\s*\)")
_FENCE_RE = re.compile(r"^(```|~~~).*?^\1", re.S | re.M)
_CODE_RE = re.compile(r"`[^`\n]*`")
_SCHEME_RE = re.compile(r"^[A-Za-z][A-Za-z0-9+.-]*:")


def _git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True,
                          text=True, errors="replace").stdout


def tree_files(repo: Path, rev: Optional[str]) -> Set[str]:
    if rev is None:
        out = _git(repo, "ls-files", "-z", "--cached", "--others", "--exclude-standard")
        return {p for p in out.split("\0") if p and (repo / p).exists()}
    return {p for p in _git(repo, "ls-tree", "-r", "-z", "--name-only", rev).split("\0") if p}


def read(repo: Path, rev: Optional[str], path: str) -> str:
    if rev is None:
        return (repo / path).read_text(encoding="utf-8", errors="replace")
    return _git(repo, "show", f"{rev}:{path}")


def links(text: str) -> List[str]:
    text = _FENCE_RE.sub("", text)
    text = _CODE_RE.sub("", text)
    return [m.group(1) for m in _LINK_RE.finditer(text)]


def resolve(doc: str, target: str) -> Optional[str]:
    """The repo path a relative link names, or None for a non-file link."""
    if _SCHEME_RE.match(target) or target.startswith("#") or target.startswith("//"):
        return None
    target = target.split("#", 1)[0].split("?", 1)[0]
    if not target:
        return None
    if target.startswith("/"):
        path = target.lstrip("/")
    else:
        path = posixpath.join(posixpath.dirname(doc), target)
    norm = posixpath.normpath(path)
    return norm


def read_many(repo: Path, rev: Optional[str], paths: List[str]) -> Dict[str, str]:
    """Every path's text at ``rev`` (or in the working tree), through one
    ``git cat-file --batch`` rather than a process per file."""
    if rev is None:
        out = {}
        for path in paths:
            try:
                out[path] = read(repo, None, path)
            except OSError:
                continue
        return out
    request = "".join(f"{rev}:{p}\n" for p in paths).encode()
    data = subprocess.run(["git", "-C", str(repo), "cat-file", "--batch"], input=request, check=True,
                          capture_output=True).stdout
    out: Dict[str, str] = {}
    pos = 0
    for path in paths:
        end = data.index(b"\n", pos)
        header = data[pos:end].split()
        pos = end + 1
        if len(header) < 3 or header[1] == b"missing":
            continue
        size = int(header[2])
        out[path] = data[pos:pos + size].decode("utf-8", "replace")
        pos += size + 1
    return out


def broken_links(repo: Path, rev: Optional[str]) -> Set[Tuple[str, str]]:
    files = tree_files(repo, rev)
    dirs = set()
    for f in files:
        parts = f.split("/")
        for i in range(1, len(parts)):
            dirs.add("/".join(parts[:i]))
    broken = set()
    docs = sorted(f for f in files if f.endswith(".md"))
    texts = read_many(repo, rev, docs)
    for doc in docs:
        text = texts.get(doc)
        if text is None:
            continue
        for target in links(text):
            path = resolve(doc, target)
            if path is None:
                continue
            if path.startswith(".."):
                broken.add((doc, target))      # leaves the repository
                continue
            if path in files or path in dirs or path == ".":
                continue
            broken.add((doc, target))
    return broken


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--repo", type=Path, default=REPO_ROOT)
    parser.add_argument("--base", required=True, help="base revision (the landing gate passes the merge base)")
    parser.add_argument("--head", help="head revision (default: the working tree)")
    args = parser.parse_args(argv)
    before = broken_links(args.repo, args.base)
    after = broken_links(args.repo, args.head)
    new = sorted(after - before)
    fixed = len(before - after)
    for doc, target in new:
        print(f"check-doc-links: BROKEN (new): {doc}: ({target})")
    print(f"check-doc-links: {len(new)} new broken links; {len(after & before)} already broken at the base "
          f"(reported, not failed); {fixed} fixed")
    return 1 if new else 0


if __name__ == "__main__":
    sys.exit(main())
