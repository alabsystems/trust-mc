# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Pinned Kani checkouts in a cache outside every cargo workspace.

Layout: $KANI_SPEC_CACHE or $HOME/Library/Caches/trust-mc/kani-spec/<rev>.
A checkout is created by fetching the pinned commit (from a local seed clone
when one has the object, else from upstream with --depth 1) and checking it
out detached. Test-bearing submodules are fetched the same way at their
gitlink sha. Generation refuses a checkout whose HEAD, gitlinks or cleanliness
disagree with the pins, so a stale or edited cache can never feed the spec.
"""
from __future__ import annotations

import os
import subprocess
import tomllib
from pathlib import Path

from . import SpecError
from .pins import Pins, RevPin


def cache_root() -> Path:
    env = os.environ.get("KANI_SPEC_CACHE")
    if env:
        return Path(env)
    return Path.home() / "Library" / "Caches" / "trust-mc" / "kani-spec"


def _git(args, cwd=None, check=True, env_extra=None):
    env = dict(os.environ)
    env["GIT_LFS_SKIP_SMUDGE"] = "1"
    env["GIT_TERMINAL_PROMPT"] = "0"
    # Replacement refs and grafts would let HEAD's sha name different content.
    env["GIT_NO_REPLACE_OBJECTS"] = "1"
    if env_extra:
        env.update(env_extra)
    proc = subprocess.run(["git", *args], cwd=cwd, env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if check and proc.returncode != 0:
        raise SpecError(f"git {' '.join(args)} failed in {cwd}: {proc.stderr.strip()}")
    return proc


def _has_commit(repo: Path, sha: str) -> bool:
    return _git(["cat-file", "-e", f"{sha}^{{commit}}"], cwd=repo, check=False).returncode == 0


def _fetch_commit(repo: Path, sha: str, sources: list) -> None:
    if _has_commit(repo, sha):
        return
    errors = []
    for src in sources:
        proc = _git(["fetch", "--quiet", "--depth", "1", "--no-tags", str(src), sha],
                    cwd=repo, check=False)
        if proc.returncode == 0 and _has_commit(repo, sha):
            return
        errors.append(f"{src}: {proc.stderr.strip()}")
    raise SpecError(f"could not fetch {sha} into {repo}: " + " | ".join(errors))


def _init_repo(path: Path) -> None:
    path.mkdir(parents=True, exist_ok=True)
    if not (path / ".git").exists():
        _git(["init", "--quiet", str(path)])


def ensure_checkout(pins: Pins, pin: RevPin, seeds=(), offline=False) -> Path:
    dest = cache_root() / pin.rev
    _init_repo(dest)
    sources = [s for s in seeds if Path(s).is_dir()]
    if not offline:
        sources.append(pins.upstream)
    _fetch_commit(dest, pin.rev, sources)
    head = _git(["rev-parse", "--verify", "--quiet", "HEAD"], cwd=dest, check=False).stdout.strip()
    if head != pin.rev:
        _git(["checkout", "--quiet", "--detach", pin.rev], cwd=dest)
    for sub, sha in pin.submodules.items():
        sub_dir = dest / sub
        _init_repo(sub_dir)
        sub_sources = []
        for seed in sources:
            candidate = Path(seed) / sub
            if Path(seed).is_dir() and (candidate / ".git").exists():
                sub_sources.append(candidate)
        if not offline:
            url = pins.submodule_urls.get(sub)
            if not url:
                raise SpecError(f"no submodule_urls entry for {sub}")
            sub_sources.append(url)
        _fetch_commit(sub_dir, sha, sub_sources)
        sub_head = _git(["rev-parse", "--verify", "--quiet", "HEAD"], cwd=sub_dir, check=False).stdout.strip()
        if sub_head != sha:
            _git(["checkout", "--quiet", "--detach", sha], cwd=sub_dir)
    verify_checkout(dest, pin)
    return dest


def verify_checkout(path: Path, pin: RevPin) -> dict:
    """Refuse unless the checkout is exactly the pinned, clean tree."""
    path = Path(path)
    if not (path / ".git").exists():
        raise SpecError(f"{path} is not a git checkout (run: kani-spec fetch)")
    head = _git(["rev-parse", "HEAD"], cwd=path).stdout.strip()
    if head != pin.rev:
        raise SpecError(f"{path}: HEAD {head} != pinned {pin.rev}")
    toolchain = tomllib.loads((path / "rust-toolchain.toml").read_text(encoding="utf-8"))
    channel = toolchain.get("toolchain", {}).get("channel", "")
    if channel != pin.nightly:
        raise SpecError(f"{path}: rust-toolchain channel {channel} != pinned {pin.nightly}")
    gitlinks = {}
    for line in _git(["ls-tree", "-r", "HEAD"], cwd=path).stdout.splitlines():
        meta, _, name = line.partition("\t")
        if meta.startswith("160000 commit "):
            gitlinks[name] = meta.split()[2]
    for sub, sha in pin.submodules.items():
        if gitlinks.get(sub) != sha:
            raise SpecError(f"{path}: gitlink {sub} is {gitlinks.get(sub)}, pinned {sha}")
        sub_head = _git(["rev-parse", "HEAD"], cwd=path / sub).stdout.strip()
        if sub_head != sha:
            raise SpecError(f"{path / sub}: HEAD {sub_head} != gitlink {sha}")
        dirty = _git(["status", "--porcelain", "--ignored", "--untracked-files=all"],
                     cwd=path / sub).stdout
        if dirty.strip():
            raise SpecError(f"{path / sub}: submodule checkout is not clean:\n{dirty[:2000]}")
    if (path / ".git" / "info" / "grafts").exists():
        raise SpecError(f"{path}: .git/info/grafts present; the checkout content is not HEAD's")
    hidden = [ln for ln in _git(["ls-files", "-v"], cwd=path).stdout.splitlines()
              if ln[:1].islower() or ln[:1] == "S"]
    if hidden:
        raise SpecError(f"{path}: assume-unchanged or skip-worktree entries hide edits from git status: "
                        + ", ".join(ln[2:] for ln in hidden[:10]))
    status = _git(["status", "--porcelain", "--ignored", "--untracked-files=all",
                   "--ignore-submodules=none"], cwd=path).stdout
    if status.strip():
        raise SpecError(f"{path}: checkout is not clean (generation reads upstream files only):\n{status[:2000]}")
    return {"head": head, "nightly": channel, "gitlinks": dict(sorted(gitlinks.items()))}
