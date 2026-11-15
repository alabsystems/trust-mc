#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
"""Which landing legs a change can reach: the selector of scripts/landing-gate.py.

Maps every changed path (``git diff --raw`` from the base: the merge base with
``origin/main`` by default) to what owns it, through the real build graph,
takes the reverse-dependency closure, and selects exactly the legs whose inputs
intersect it. FAIL-CLOSED: each of these selects EVERYTHING, with its reason:

  * the build graph cannot be read (the workspace manifests do not parse, a
    member is missing, or ``targo metadata`` disagrees with the manifests);
  * any build input changed: a ``Cargo.toml`` or ``build.rs`` anywhere,
    ``Cargo.lock``, ``rust-toolchain*``, ``.cargo/``, ``.gitattributes``,
    ``.gitmodules``, ``tools/tuple.toml``, a lint or deny config, the pin
    exclusions;
  * a gate script, a script a gate script reaches, or this selector's own code;
  * a symbolic link or submodule on either side of the diff, or a path whose
    case-folded spelling another tracked path shares (APFS opens one for the
    other);
  * a path no rule maps (``unmapped``).

A docs-only change selects only ``docs-links``. Every skipped leg is listed
with the reason it was skipped. The rules, and why each is sound, are in
docs/landing-gates.md ("Selection rules"); the mutants in
scripts/test_landing_select.py each drop one rule and must fail a test.

Paths -> owners:

  crate     a path under a workspace member's directory, or under the
            directory of one of its targets' roots (trust-mc-engine compiles
            ``trust-mc-compiler/src``); the root package owns ``src/`` only.
            A ``.md`` file inside a crate directory is owned by the crate only
            when a string literal of the crate names it.
  literal   a string literal in a crate's ``.rs`` sources that names a repo
            path (``"../../tests/ay/x.rs"`` resolved against the file and the
            manifest directory, or ``"scripts/x.sh"`` from the repo root)
            makes that path (and everything under it) an input of the crate.
  data      ``tools/soundness-duals/`` (dual sources: the lanes their manifest
            entry runs in; the manifest: both), ``tools/engine-suite/``
            (the engine suite), ``tools/port/`` (the lane port check).
  scripts   any other ``scripts/`` file: the script unit tests.
  docs      ``docs/``, ``designs/``, ``ideas/``, ``papers/``, ``rfc/``,
            ``guide/**.md``, ``tools/ay-ask/``, the duals' ``reports/`` and
            README, and root-level ``*.md`` / ``LICENSE-*``, unless a crate
            literal names them.

Python floor 3.11 (tomllib).
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import posixpath
import re
import subprocess
import sys
import tomllib
from pathlib import Path
from typing import Any, Callable, Iterable

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent

EVERYTHING = "EVERYTHING"

# --------------------------------------------------------------------------
# The registry: legs, and the crates / paths each one reads.
# --------------------------------------------------------------------------

# The development bundle the dual gate runs: build-trust-mc builds
# trust-mc-compiler, trust-mc-driver and trust-mc-backend (sysroot.rs
# build_bin), trust-mc-cov (build_tools) and the verification libraries
# (VERIFICATION_PACKAGES, NO_CORE_PACKAGES) with the dev compiler.
BUNDLE_CRATES = frozenset({
    "trust-mc-compiler", "trust-mc-engine", "trust-mc-driver", "trust-mc-backend",
    "build-trust-mc", "trust-mc-cov", "kani", "kani_core", "kani_macros", "std",
})
# scripts/check-trust-lane-build.sh builds these (and runs the engine's lints).
LANE_BUILD_CRATES = frozenset({
    "trust-mc-driver", "trust-mc-backend", "trust-mc", "build-trust-mc", "trust-mc-engine",
})
# Crates whose tests the engine suite gate runs (`-p trust-mc-engine --lib`).
ENGINE_CRATES = frozenset({"trust-mc-engine"})
# Crates with a plain `targo --unverified test --locked -p <crate>` leg. The
# rustc_private crates are left to the engine suite and the lane build (their
# tests link the seal's librustc_driver), the no_core libraries to the bundle.
RUSTC_PRIVATE_CRATES = frozenset({
    "trust-mc-compiler", "trust-mc-engine", "trust-mc-backend", "trust-mc-codegen-shared",
    "trust-mc-codegen-types", "trust-mc-kani-types", "scanner",
})
LIBRARY_CRATES = frozenset({"kani", "kani_core", "kani_macros", "std"})

LANES = ("chc", "bmc")
DUAL_LEGS = tuple(f"dual-{lane}" for lane in LANES)

# Every leg, in the order the landing gate runs them (cheap first).
FIXED_LEGS = (
    "docs-links",
    "script-tests",
    "port-tests",
    "kani-spec-tests",
    "dual-validate",
    "tsv-validate",
    "lane-port",
    "ay-pin",
    "shared-pins",
    "lane-build",
    "engine-suite",
    "dual-chc",
    "dual-bmc",
    "kani-domination-tests",
)

# The landing legs' own code: a change here selects everything. The helpers
# each one reaches are added by `gate_script_closure`.
ROOT_GATE_SCRIPTS = (
    "scripts/landing_select.py",
    "scripts/landing-gate.py",
    "scripts/host_room.py",
    "scripts/check_doc_links.py",
    "scripts/soundness-dual-gate.py",
    "scripts/engine-suite-gate.py",
    "scripts/check-trust-lane-build.sh",
    "scripts/check-trust-lane-port.sh",
    "scripts/check-ay-pin.sh",
    "scripts/check-shared-pins.sh",
    "scripts/build-pinned-ay-cli.sh",
    "scripts/resolve-trust-tool.sh",
    "scripts/trustc-private-wrapper.sh",
    "tools/tuple-check",
)
# Files a gate script can reach by name: the closure is taken over these.
GATE_HELPER_DIRS = ("scripts", "scripts/lib", "tools/port")

# The scripts each leg runs. Their code closure (every script, module or tool
# they name, transitively) and every repository path that code names are the
# leg's inputs: a change to a file a leg's scripts read selects the leg, even
# when the file sits in a region whose own rule maps it elsewhere
# (scripts/tuple_check.py, run by the lane build, reads
# tools/kani-domination/src/clone.rs and tools/kani-spec/pins.toml). The test
# legs (script, port, kani-spec) are rooted at their test files; the cargo legs
# read what the crate rule maps. A ``*`` suffix is a glob over one directory.
LEG_SCRIPTS: dict[str, tuple[str, ...]] = {
    "docs-links": ("scripts/check_doc_links.py",),
    "dual-validate": ("scripts/soundness-dual-gate.py",),
    "tsv-validate": ("scripts/engine-suite-gate.py",),
    "lane-port": ("scripts/check-trust-lane-port.sh",),
    "ay-pin": ("scripts/check-ay-pin.sh",),
    "shared-pins": ("scripts/check-shared-pins.sh",),
    "lane-build": ("scripts/check-trust-lane-build.sh",),
    "engine-suite": ("scripts/engine-suite-gate.py",),
    "dual-chc": ("scripts/soundness-dual-gate.py", "scripts/build-pinned-ay-cli.sh"),
    "dual-bmc": ("scripts/soundness-dual-gate.py", "scripts/build-pinned-ay-cli.sh"),
    "port-tests": ("tools/port/test_trust_only_arms.py",),
    "kani-spec-tests": ("tools/kani-spec/tests/*.py",),
}
# The selector and the orchestrator: what they read decides selection, not a
# verdict, and every path they name is classified by the rules they implement.
SELECTOR_SCRIPTS = frozenset({"scripts/landing_select.py", "scripts/landing-gate.py", "scripts/host_room.py"})
SCRIPT_TEST_GLOB = "scripts/test_*.py"
# The script tests that run the selector over this repository's own tree
# (ThisRepository: the graph, the exclusions, the CHC reachability fact), so
# what the selector reads is theirs. Any other test reaching the selector runs
# it on fixtures: its names and reads are not followed for that test.
SELECTOR_TREE_TESTS = frozenset({"scripts/test_landing_select.py"})

# Reviewed: a path a leg's code names that it does not read for a verdict, or
# whose every read the region's own rule already maps more precisely. Keyed
# (file naming it, path named); each entry is checked to still occur (a stale
# entry fails the selector's tests). Anything not listed here is a read.
DATA_REF_EXCLUSIONS: dict[tuple[str, str], str] = {
    ("scripts/soundness-dual-gate.py", "tools/soundness-duals"):
        "the manifest's directory: the gate reads the manifest and the sources its entries name, "
        "which the duals rule maps (manifest: both lanes; an entry's source: its lanes; any other "
        "non-prose file: both lanes); it never reads the README or reports/",
    ("scripts/tuple_check.py", "tools/kani-domination"):
        "an error message's prose (the absent-checkout note); the reads are "
        "tools/kani-domination/src/clone.rs (DEFAULT_KANI_REV) and the corpus checkout outside the tree",
    ("scripts/test_pinned_package_paths.py", "docs"):
        "fixture trees under a TemporaryDirectory (exclusion patterns, drift probes); the real "
        "tree is read only for scripts/pin-exclusions.toml, every tracked *.sh/*.bash, "
        "publish/config.sh, tools/replacement-audit/Cargo.toml and tools/build-trust-mc/src/sysroot.rs",
    ("scripts/test_pinned_package_paths.py", "docs/*"):
        "fixture exclusion patterns (docs/**, docs/[ab]) checked by Exclusion.covers on strings",
    ("scripts/test_pinned_package_paths.py", "README.md"):
        "fixture paths given to Exclusion.covers; no test reads the repository's README.md",
    ("scripts/test_landing_select.py", "docs"):
        "fixture tree names and path_refs cases; the selector's own reads of the tree (DOCS_DIRS "
        "among them) count for this test through SELECTOR_TREE_TESTS",
    ("scripts/test_landing_select.py", "README.md"):
        "a fixture tree's file name (FIXTURE), written under a TemporaryDirectory",
    ("scripts/test_landing_select.py", "tools/soundness-duals/README.md"):
        "a fixture tree's file name (FIXTURE), written under a TemporaryDirectory",
    ("scripts/tuple_check.py", "tools/kani-spec/kani-spec"):
        "an error message names the command to run; tuple_check reads tools/kani-spec/pins.toml and "
        "spec/kani/, and never runs the tool",
}

# Build inputs: any of these selects everything.
BUILD_INPUT_NAMES = frozenset({
    "Cargo.toml", "Cargo.lock", "build.rs", ".gitattributes", ".gitmodules",
    "rust-toolchain", "rust-toolchain.toml",
})
BUILD_INPUT_PATHS = frozenset({
    "rust-toolchain.legacy.toml", "tools/tuple.toml", "deny.toml", "clippy.toml",
    "rustfmt.toml", "scripts/pin-exclusions.toml", ".gitignore",
})
BUILD_INPUT_DIRS = (".cargo/",)

DOCS_DIRS = ("docs/", "designs/", "ideas/", "papers/", "rfc/", "tools/ay-ask/",
             "tools/soundness-duals/reports/")
DOCS_FILES = frozenset({"tools/soundness-duals/README.md"})
DUALS_DIR = "tools/soundness-duals/"
DUAL_MANIFEST = "tools/soundness-duals/manifest.toml"
ENGINE_TSV = "tools/engine-suite/known-failures.tsv"
PORT_DIR = "tools/port/"
LANE_PORT_SOURCES = "trust-mc-compiler/src/"
KANI_DOMINATION_DIR = "tools/kani-domination/"
KANI_SPEC_DIR = "tools/kani-spec/"



# --------------------------------------------------------------------------
# Tree access (a revision, or the working tree)
# --------------------------------------------------------------------------


class GraphError(RuntimeError):
    """The build graph cannot be read: selection falls back to everything."""


class Tree:
    """Read-only view of the repository at one revision (``None`` = worktree)."""

    def __init__(self, repo: Path, rev: str | None):
        self.repo = repo
        self.rev = rev
        self._files: list[str] | None = None
        self._modes: dict[str, str] | None = None

    def _git(self, *args: str) -> str:
        return subprocess.run(["git", "-C", str(self.repo), *args], check=True,
                              capture_output=True, text=True).stdout

    def files(self) -> list[str]:
        if self._files is None:
            if self.rev is None:
                out = self._git("ls-files", "-z", "--cached", "--others", "--exclude-standard")
            else:
                out = self._git("ls-tree", "-r", "-z", "--name-only", self.rev)
            self._files = sorted({p for p in out.split("\0") if p})
        return self._files

    def modes(self) -> dict[str, str]:
        if self._modes is None:
            modes: dict[str, str] = {}
            if self.rev is None:
                out = self._git("ls-files", "-z", "-s")
                for rec in out.split("\0"):
                    if rec:
                        meta, path = rec.split("\t", 1)
                        modes[path] = meta.split()[0]
            else:
                out = self._git("ls-tree", "-r", "-z", self.rev)
                for rec in out.split("\0"):
                    if rec:
                        meta, path = rec.split("\t", 1)
                        modes[path] = meta.split()[0]
            self._modes = modes
        return self._modes

    def read(self, path: str) -> str | None:
        cache = self.__dict__.setdefault("_texts", {})
        if path not in cache:
            try:
                if self.rev is None:
                    cache[path] = (self.repo / path).read_text(encoding="utf-8", errors="replace")
                else:
                    cache[path] = subprocess.run(
                        ["git", "-C", str(self.repo), "show", f"{self.rev}:{path}"],
                        check=True, capture_output=True).stdout.decode("utf-8", "replace")
            except (OSError, subprocess.CalledProcessError):
                cache[path] = None
        return cache[path]

    def grep_literals(self, pathspecs: list[str]) -> list[tuple[str, str]]:
        """(file, literal) for every slash-bearing string literal in the files."""
        pattern = r'"([^"\\]|\\.)*/([^"\\]|\\.)*"'
        args = ["grep", "-I", "-o", "-E", pattern]
        if self.rev is not None:
            args.append(self.rev)
        args += ["--", *pathspecs]
        proc = subprocess.run(["git", "-C", str(self.repo), *args], capture_output=True, text=True)
        if proc.returncode not in (0, 1):
            raise GraphError(f"git grep failed: {proc.stderr.strip()}")
        return self._grep_output(proc.stdout)

    def grep_bare(self, pathspecs: list[str], pattern: str) -> list[tuple[str, str]]:
        """(file, literal) for every literal matching ``pattern`` exactly."""
        args = ["grep", "-I", "-o", "-E", pattern]
        if self.rev is not None:
            args.append(self.rev)
        args += ["--", *pathspecs]
        proc = subprocess.run(["git", "-C", str(self.repo), *args], capture_output=True, text=True)
        if proc.returncode not in (0, 1):
            raise GraphError(f"git grep failed: {proc.stderr.strip()}")
        return self._grep_output(proc.stdout)

    def _grep_output(self, text: str) -> list[tuple[str, str]]:
        found = []
        for line in text.splitlines():
            if self.rev is not None and line.startswith(self.rev + ":"):
                line = line[len(self.rev) + 1:]
            name, _, literal = line.partition(":")
            if literal.startswith('"') and literal.endswith('"'):
                found.append((name, literal[1:-1]))
        return found


# --------------------------------------------------------------------------
# The build graph
# --------------------------------------------------------------------------


@dataclasses.dataclass(frozen=True)
class Package:
    name: str
    dir: str                      # repo-relative manifest dir ("" for the root)
    roots: tuple[str, ...]        # repo-relative dirs of target roots
    deps: tuple[str, ...]         # workspace path dependencies (all kinds)


def _norm(path: str) -> str:
    out = posixpath.normpath(path)
    return "" if out == "." else out


def _member_dirs(root_manifest: dict[str, Any], tree: Tree) -> list[str]:
    ws = root_manifest.get("workspace", {})
    members = ws.get("members", [])
    if not isinstance(members, list):
        raise GraphError("[workspace] members is not a list")
    files = set(tree.files())
    dirs = []
    for member in members:
        if any(ch in member for ch in "*?["):
            raise GraphError(f"workspace member glob {member!r} is not supported by the selector")
        d = _norm(member)
        if f"{d}/Cargo.toml" not in files:
            raise GraphError(f"workspace member {member!r} has no Cargo.toml")
        dirs.append(d)
    return dirs


def _target_roots(manifest: dict[str, Any], mdir: str) -> list[str]:
    roots: list[str] = []
    paths: list[str] = []
    lib = manifest.get("lib")
    if isinstance(lib, dict) and isinstance(lib.get("path"), str):
        paths.append(lib["path"])
    for key in ("bin", "test", "example", "bench"):
        for target in manifest.get(key, []) or []:
            if isinstance(target, dict) and isinstance(target.get("path"), str):
                paths.append(target["path"])
    build = manifest.get("package", {}).get("build")
    if isinstance(build, str):
        paths.append(build)
    for p in paths:
        roots.append(_norm(posixpath.join(mdir, posixpath.dirname(p))))
    # Cargo's conventional roots.
    roots.append(_norm(posixpath.join(mdir, "src")))
    return sorted(set(roots))


def _path_deps(manifest: dict[str, Any], mdir: str) -> list[str]:
    tables: list[dict[str, Any]] = []
    for key in ("dependencies", "dev-dependencies", "build-dependencies"):
        if isinstance(manifest.get(key), dict):
            tables.append(manifest[key])
    for target in (manifest.get("target") or {}).values():
        if isinstance(target, dict):
            for key in ("dependencies", "dev-dependencies", "build-dependencies"):
                if isinstance(target.get(key), dict):
                    tables.append(target[key])
    out = []
    for table in tables:
        for spec in table.values():
            if isinstance(spec, dict) and isinstance(spec.get("path"), str):
                out.append(_norm(posixpath.join(mdir, spec["path"])))
    return out


def read_graph(tree: Tree) -> dict[str, Package]:
    """The workspace packages and their path dependencies, from the manifests."""
    text = tree.read("Cargo.toml")
    if text is None:
        raise GraphError("no root Cargo.toml")
    try:
        root = tomllib.loads(text)
    except tomllib.TOMLDecodeError as err:
        raise GraphError(f"root Cargo.toml does not parse: {err}") from err
    dirs = _member_dirs(root, tree)
    if "package" in root:
        dirs = [""] + dirs
    files = set(tree.files())
    by_dir: dict[str, tuple[str, dict[str, Any]]] = {}
    # Members, then every in-repository path dependency they reach (a
    # non-member such as library/kani_macros is still compiled from here).
    queue = list(dirs)
    while queue:
        d = queue.pop(0)
        if d in by_dir:
            continue
        mpath = f"{d}/Cargo.toml" if d else "Cargo.toml"
        mtext = tree.read(mpath)
        if mtext is None:
            raise GraphError(f"{mpath} cannot be read")
        try:
            manifest = tomllib.loads(mtext)
        except tomllib.TOMLDecodeError as err:
            raise GraphError(f"{mpath} does not parse: {err}") from err
        name = manifest.get("package", {}).get("name")
        if not isinstance(name, str):
            raise GraphError(f"{mpath} has no package name")
        by_dir[d] = (name, manifest)
        for dep_dir in _path_deps(manifest, d):
            if dep_dir.startswith(".."):
                continue        # a sibling checkout ([patch] ay / trust-ir): a pin, not a member
            if f"{dep_dir}/Cargo.toml" not in files:
                raise GraphError(f"{mpath}: path dependency {dep_dir!r} has no Cargo.toml")
            queue.append(dep_dir)
    packages: dict[str, Package] = {}
    for d, (name, manifest) in by_dir.items():
        roots = _target_roots(manifest, d)
        if d == "":
            # The root package compiles src/ (and build.rs, a build input); the
            # rest of the repository is not its source.
            roots = [r for r in roots if r]
        deps = []
        for dep_dir in _path_deps(manifest, d):
            if dep_dir in by_dir:
                deps.append(by_dir[dep_dir][0])
        packages[name] = Package(name, d, tuple(roots), tuple(sorted(set(deps))))
    return packages


def graph_from_metadata(metadata: dict[str, Any], repo: Path) -> dict[str, tuple[str, frozenset[str]]]:
    """(dir, path-dependency names) per workspace package, from ``targo metadata``."""
    root = str(repo.resolve())
    members = set(metadata.get("workspace_members", []))
    out = {}
    names = {p["id"]: p["name"] for p in metadata["packages"]}
    for pkg in metadata["packages"]:
        if pkg["id"] not in members:
            continue
        mdir = str(Path(pkg["manifest_path"]).parent.resolve())
        rel = "" if mdir == root else str(Path(mdir).relative_to(root))
        deps = frozenset(d["name"] for d in pkg["dependencies"] if d.get("path"))
        out[names[pkg["id"]]] = (rel, deps)
    return out


def cross_check_metadata(packages: dict[str, Package], metadata: dict[str, Any], repo: Path) -> list[str]:
    """Disagreements between the manifest reader and Cargo's own resolution."""
    cargo = graph_from_metadata(metadata, repo)
    problems = []
    missing = set(cargo) - set(packages)
    if missing:
        problems.append(f"workspace members the manifest reader missed: {sorted(missing)}")
    for name, (rel, deps) in cargo.items():
        mine = packages.get(name)
        if mine is None:
            continue
        if mine.dir != rel:
            problems.append(f"{name}: dir {mine.dir!r} vs metadata {rel!r}")
        ws_deps = {d for d in deps if d in packages}
        if set(mine.deps) != ws_deps:
            problems.append(f"{name}: path deps {sorted(mine.deps)} vs metadata {sorted(ws_deps)}")
    return problems


def reverse_closure(packages: dict[str, Package], seeds: Iterable[str]) -> set[str]:
    rdeps: dict[str, set[str]] = {name: set() for name in packages}
    for pkg in packages.values():
        for dep in pkg.deps:
            rdeps.setdefault(dep, set()).add(pkg.name)
    seen = set(seeds)
    stack = list(seen)
    while stack:
        for parent in rdeps.get(stack.pop(), ()):
            if parent not in seen:
                seen.add(parent)
                stack.append(parent)
    return seen


# --------------------------------------------------------------------------
# Literal references: what a crate's sources name outside the crate
# --------------------------------------------------------------------------


def literal_targets(file: str, literal: str, pkg_dir: str, top_level: set[str]) -> set[str]:
    """Repo paths a string literal may name, read from ``file`` of a crate in
    ``pkg_dir``. Over-approximates: every plausible reading is kept."""
    # A leading placeholder is a root the code computes ("{root}/tools/x",
    # concat!(env!("CARGO_MANIFEST_DIR"), "/x")): what follows it is read
    # against the repository root and the manifest directory.
    lit = re.sub(r"^\{[^{}]*\}", "", literal)
    lit = lit.split("{", 1)[0]          # a format string names a prefix
    lit = lit.replace("\\\\", "/")
    out: set[str] = set()
    if not lit.strip("/."):
        return out
    bases = [posixpath.dirname(file), pkg_dir]
    if "../" in lit or lit.startswith(".."):
        for base in bases:
            target = _norm(posixpath.join(base, lit.lstrip("/")))
            if target and not target.startswith(".."):
                out.add(target)
    elif lit.startswith("/") and pkg_dir:
        # CARGO_MANIFEST_DIR + "/x": the crate's own x (a .md file a crate
        # test reads is then the crate's input, not prose).
        out.add(_norm(posixpath.join(pkg_dir, lit.lstrip("/"))))
    first = lit.lstrip("./").split("/", 1)[0]
    if first in top_level:
        out.add(_norm(lit.lstrip("./")))
    return {t for t in out if t}


# A bare directory name (``root.join("scripts")``) names the whole region; only
# the regions a change can otherwise reach without selecting everything matter.
BARE_REGION_LITERALS = frozenset({"docs", "scripts", "tools", "designs", "ideas", "papers", "rfc", "guide"})
_BARE_RE = re.compile(r'"(%s)"' % "|".join(sorted(BARE_REGION_LITERALS)))
# Reviewed: a bare-region literal that names no read. Each entry is checked to
# still exist (a stale entry fails the selector's tests); anything not listed
# here is a read.
LITERAL_EXCLUSIONS = {
    ("build-trust-mc", "tools/build-trust-mc/src/main.rs", "scripts"):
        "bundle_trust_mc creates the release bundle's empty scripts/ directory; it reads nothing there",
    ("trust-mc", "src/frontend/topics.rs", "guide"):
        "a help-topic alias word, not a path",
}


def crate_literal_refs(tree: Tree, packages: dict[str, Package]) -> dict[str, set[str]]:
    top_level = {p.split("/", 1)[0] for p in tree.files()}
    owned = owners_index(packages)
    specs = sorted({f"{d}/*.rs" for pkg in packages.values() for d in (pkg.dir, *pkg.roots) if d})
    refs: dict[str, set[str]] = {name: set() for name in packages}
    for file, literal in tree.grep_literals(specs):
        crates = owners_of(file, owned)
        for crate in crates:
            pkg = packages[crate]
            for target in literal_targets(file, literal, pkg.dir, top_level):
                refs[crate].add(target)
    for file, literal in tree.grep_bare(specs, _BARE_RE.pattern):
        for crate in owners_of(file, owned):
            if (crate, file, literal) not in LITERAL_EXCLUSIONS:
                refs[crate].add(literal)
    # A slash-free Markdown name (``include_str!("notes.md")``, a doctest
    # source) is read beside the file or in the manifest directory: the crate
    # rule would otherwise call that file prose.
    for file, literal in tree.grep_bare(specs, r'"[^"/\\]+\.md"'):
        for crate in owners_of(file, owned):
            for base in (posixpath.dirname(file), packages[crate].dir):
                refs[crate].add(_norm(posixpath.join(base, literal)))
    return refs


def owners_index(packages: dict[str, Package]) -> list[tuple[str, str]]:
    """(dir prefix, crate), longest prefix first."""
    index = []
    for pkg in packages.values():
        if pkg.dir:
            index.append((pkg.dir + "/", pkg.name))
        for root in pkg.roots:
            if root:
                index.append((root + "/", pkg.name))
    return sorted(set(index), key=lambda item: -len(item[0]))


def owners_of(path: str, index: list[tuple[str, str]]) -> set[str]:
    """Every crate whose directory or target-root directory holds ``path``.

    A target root owns its files in addition to the directory's crate
    (trust-mc-compiler/src belongs to trust-mc-compiler and trust-mc-engine);
    a member nested in another member's directory would be owned by both,
    which only ever selects more."""
    return {crate for prefix, crate in index if path.startswith(prefix)}


# --------------------------------------------------------------------------
# Gate-script closure
# --------------------------------------------------------------------------


def _reference_patterns(path: str) -> list[re.Pattern[str]]:
    """How a gate script can name ``path``: its basename when that has an
    extension, its ``dir/name`` spelling, and for a Python module an import."""
    base = posixpath.basename(path)
    pats = [re.compile(r"(?<![A-Za-z0-9_.-])%s(?![A-Za-z0-9_-])" % re.escape(path))]
    if "." in base:
        pats.append(re.compile(r"(?<![A-Za-z0-9_-])%s(?![A-Za-z0-9_-])" % re.escape(base)))
    if base.endswith(".py"):
        stem = re.escape(base[:-3])
        pats.append(re.compile(r"^\s*(?:from\s+%s\s+import|import\s+%s\b)" % (stem, stem), re.MULTILINE))
    return pats


_TRIPLE_QUOTED = re.compile(r'("""|\'\'\')(?:.|\n)*?\1')


def _code_text(path: str, text: str) -> str:
    """A script's text without its full-line comments and Python docstrings:
    prose that mentions a script runs nothing. Strings in code stay, so a
    name in an error message still counts (an over-approximation)."""
    if path.endswith(".py"):
        text = _TRIPLE_QUOTED.sub(" ", text)
    return "\n".join(line for line in text.splitlines() if not line.lstrip().startswith("#"))


# Only executable code references another file; a data file listing paths
# (scripts/pin-exclusions.toml) runs nothing.
_CODE_SUFFIXES = (".py", ".sh", "")


def gate_script_closure(tree: Tree) -> set[str]:
    """The landing legs' own code: the roots and every helper they name."""
    files = set(tree.files())
    candidates = sorted(
        p for p in files
        if any(p.startswith(d + "/") and "/" not in p[len(d) + 1:] for d in GATE_HELPER_DIRS)
        and not posixpath.basename(p).startswith("test_")
    )
    return code_closure(tree, {p for p in ROOT_GATE_SCRIPTS if p in files}, RefMatcher(candidates))


class RefMatcher:
    """Which of ``candidates`` a code text names, by the spellings
    ``_reference_patterns`` lists (its path; its basename when that has an
    extension; a Python import of it), in one pass per text."""

    def __init__(self, candidates: Iterable[str]):
        self.by_name: dict[str, set[str]] = {}
        self.by_path: dict[str, set[str]] = {}
        self.by_stem: dict[str, set[str]] = {}
        for cand in candidates:
            base = posixpath.basename(cand)
            if "." in base:
                self.by_name.setdefault(base, set()).add(cand)
            else:
                self.by_path.setdefault(cand, set()).add(cand)
            if base.endswith(".py"):
                self.by_stem.setdefault(base[:-3], set()).add(cand)

        def alt(names: Iterable[str]) -> str:
            return "|".join(re.escape(n) for n in sorted(names, key=len, reverse=True)) or r"(?!)"

        # A path occurrence also spells its basename, so names with an
        # extension need only the basename pattern.
        self.name_re = re.compile(r"(?<![A-Za-z0-9_-])(%s)(?![A-Za-z0-9_-])" % alt(self.by_name))
        self.path_re = re.compile(r"(?<![A-Za-z0-9_.-])(%s)(?![A-Za-z0-9_-])" % alt(self.by_path))
        self.import_re = re.compile(r"^\s*(?:from\s+(%s)\s+import|import\s+(%s)\b)"
                                    % (alt(self.by_stem), alt(self.by_stem)), re.MULTILINE)

    def named(self, text: str) -> set[str]:
        out: set[str] = set()
        for m in self.name_re.finditer(text):
            out |= self.by_name[m.group(1)]
        for m in self.path_re.finditer(text):
            out |= self.by_path[m.group(1)]
        for m in self.import_re.finditer(text):
            out |= self.by_stem[m.group(1) or m.group(2)]
        return out


def code_closure(tree: Tree, roots: set[str], matcher: RefMatcher,
                 edges: dict[str, set[str]] | None = None, stop: frozenset[str] = frozenset()) -> set[str]:
    """``roots`` and every candidate their code names, transitively; a file in
    ``stop`` joins the closure but what it names is not followed. ``edges``
    memoizes what each file names, across closures of one tree."""
    edges = {} if edges is None else edges
    closure = set(roots)
    stack = list(closure)
    while stack:
        current = stack.pop()
        if posixpath.splitext(current)[1] not in _CODE_SUFFIXES or current in stop:
            continue
        if current not in edges:
            named = matcher.named(_code_text(current, tree.read(current) or ""))
            edges[current] = {n for n in named if (current, n) not in DATA_REF_EXCLUSIONS}
        for cand in edges[current] - closure:
            closure.add(cand)
            stack.append(cand)
    return closure


def code_candidates(tree: Tree, owners: list[tuple[str, str]]) -> list[str]:
    """Every file a script can run or import: tracked ``.py`` and ``.sh``
    files and suffix-free executables outside the crates' directories (a
    crate's code is mapped by the crate rule)."""
    modes = tree.modes()
    out = []
    for p in tree.files():
        suffix = posixpath.splitext(p)[1]
        if suffix in (".py", ".sh") or (suffix == "" and modes.get(p) == "100755"):
            if not owners_of(p, owners):
                out.append(p)
    return sorted(out)


# A run of quoted strings joined by ``/`` (pathlib) names one path:
# "tools" / "x" / "y.rs" -> "tools/x/y.rs" (the run is replaced by its joined
# spelling: its segments are not paths of their own). A run joined by ``,``
# (os.path.join, joinpath, Path(a, b), but also any argument list) keeps its
# segments and adds the joined spelling beside them.
_QUOTED = r"""(?:"[^"\n]*"|'[^'\n]*')"""
_SLASH_JOINED = re.compile(r"%s(?:\s*/\s*%s)+" % (_QUOTED, _QUOTED))
_COMMA_JOINED = re.compile(r"%s(?:\s*,\s*%s)+" % (_QUOTED, _QUOTED))


def _join_quoted(text: str) -> str:
    def parts(run: str) -> str:
        return "/".join(seg[1:-1].strip("/") for seg in re.findall(_QUOTED, run) if seg[1:-1])

    text = _SLASH_JOINED.sub(lambda m: '"' + parts(m.group(0)) + '"', text)
    return _COMMA_JOINED.sub(lambda m: m.group(0) + ' "' + parts(m.group(0)) + '"', text)


_SUFFIX_GLOB = re.compile(r"""["'](?:\*\*/)?\*(\.[A-Za-z0-9_]+)["']""")


def path_refs(text: str, top_level: set[str]) -> set[str]:
    """Repository paths (or path prefixes) a script's code names.

    A token starting with a top-level name counts when it starts a path: after
    a quote, a blank, ``(`` ``=`` ``:`` ``,`` ``[`` and the like, or after
    ``$VAR/``, ``${VAR}/``, ``$(...)/`` or ``./`` (so ``$ROOT/tools/x`` names
    tools/x and ``../ay/src`` names nothing here). A bare top-level name
    without a slash counts only as a whole quoted literal (``root / "docs"``).
    A token cut short by a glob or a computed part (``scripts/test_*.py``,
    ``f"tools/{name}"``) names every path starting with it (a ``*`` suffix).
    Over-approximates: a name in an error message still counts."""
    if not top_level:
        return set()
    names = "|".join(re.escape(t) for t in sorted(top_level, key=len, reverse=True))
    token = re.compile(r"(?<![A-Za-z0-9_.@+-])((?:%s)(?:/[A-Za-z0-9_.@+-]+)*/?)(?![A-Za-z0-9_.@+-])" % names)
    var_slash = re.compile(r"(?:\$[A-Za-z_][A-Za-z0-9_]*|\}|\)|(?<![A-Za-z0-9_.@+-])\.)/$")
    out: set[str] = set()
    text = _join_quoted(text)
    # A git pathspec by suffix ("*.sh", "**/*.md" given to ``git ls-files`` or
    # ``git grep``) reads every tracked file with that suffix, wherever it
    # sits. A glob relative to a directory (``dir.glob("*.rs")``, ``find
    # "$SRC" -name '*.rs'``) reads under that directory, which the code names
    # by its own path.
    for match in _SUFFIX_GLOB.finditer(text):
        if re.search(r"ls-files|\bgrep\b", text[max(0, match.start() - 300):match.start()]):
            out.add("**" + match.group(1))
    for match in token.finditer(text):
        spelled = match.group(1)
        start, end = match.start(1), match.end(1)
        before = text[max(0, start - 64):start]
        if before.endswith("/"):
            if not var_slash.search(before):
                continue
        elif before and before[-1] not in " \t\n\"'(=:,[`<>|;":
            continue
        following = text[end:end + 1]
        if following and following in "*{$[?" and "/" in spelled:
            out.add(spelled + "*")
            continue
        ref = spelled.rstrip("/")
        if "/" not in ref:
            quote = text[start - 1:start] if start else ""
            if quote not in ('"', "'") or following != quote:
                continue
        out.add(ref)
    return out


def _expand_roots(roots: Iterable[str], files: set[str]) -> set[str]:
    out = set()
    for root in roots:
        if root.endswith("*.py"):
            d = root[: -len("*.py")]
            out |= {p for p in files if p.startswith(d) and "/" not in p[len(d):] and p.endswith(".py")}
        elif root in files:
            out.add(root)
    return out


def leg_script_inputs(tree: Tree, owners: list[tuple[str, str]]) -> tuple[dict[str, set[str]], dict[str, set[str]]]:
    """(leg -> paths it reads, script test file -> paths it reads): the code
    closure of the leg's scripts (or of the test file) and every repository
    path that code names (less the reviewed exclusions), as path prefixes."""
    files = set(tree.files())
    top_level = {p.split("/", 1)[0] for p in files}
    matcher = RefMatcher(code_candidates(tree, owners))
    edges: dict[str, set[str]] = {}
    refs_of: dict[str, set[str]] = {}

    def refs(path: str) -> set[str]:
        if path not in refs_of:
            if posixpath.splitext(path)[1] not in _CODE_SUFFIXES:
                refs_of[path] = set()
            else:
                found = path_refs(_code_text(path, tree.read(path) or ""), top_level)
                refs_of[path] = {ref for ref in found if (path, ref) not in DATA_REF_EXCLUSIONS}
        return refs_of[path]

    def inputs(roots: set[str], stop: frozenset[str]) -> set[str]:
        closure = code_closure(tree, roots, matcher, edges, stop=stop)
        return closure | {ref for path in closure - stop for ref in refs(path)}

    # A leg: the selector and the orchestrator name every gate script and
    # region, and what they read is classified by the rules they implement,
    # so neither their names nor their reads are a leg's. A script test: only
    # the tests that run the selector on this tree read through it.
    legs = {leg: inputs(_expand_roots(roots, files), SELECTOR_SCRIPTS) for leg, roots in LEG_SCRIPTS.items()}
    tests = {t: inputs({t}, frozenset() if t in SELECTOR_TREE_TESTS else SELECTOR_SCRIPTS)
             for t in sorted(_expand_roots([SCRIPT_TEST_GLOB], files))}
    return legs, tests


# --------------------------------------------------------------------------
# Dual manifest: which lanes a dual source runs in
# --------------------------------------------------------------------------


def dual_entry_lanes(tree: Tree) -> dict[str, tuple[str, ...]] | None:
    """Repo path -> lanes, for every manifest entry; ``None`` if unreadable."""
    text = tree.read(DUAL_MANIFEST)
    if text is None:
        return None
    try:
        data = tomllib.loads(text)
    except tomllib.TOMLDecodeError:
        return None
    out = {}
    for entry in data.get("entry", []) or []:
        if not isinstance(entry, dict) or not isinstance(entry.get("path"), str):
            return None
        lanes = entry.get("lanes", list(LANES))
        if not isinstance(lanes, list) or not lanes or any(l not in LANES for l in lanes):
            return None
        out[_norm(posixpath.join(posixpath.dirname(DUAL_MANIFEST), entry["path"]))] = tuple(lanes)
    return out


# --------------------------------------------------------------------------
# Selection
# --------------------------------------------------------------------------


@dataclasses.dataclass(frozen=True)
class Change:
    path: str
    status: str
    old_mode: str
    new_mode: str


@dataclasses.dataclass
class Context:
    """Everything the per-path rules read, built once per tree."""

    packages: dict[str, Package]
    owners: list[tuple[str, str]]
    literal_refs: dict[str, set[str]]
    gate_scripts: set[str]
    dual_lanes: dict[str, tuple[str, ...]] | None
    casefold: dict[str, set[str]]
    files: set[str]
    graph_error: str | None = None
    # leg -> the paths (prefixes) its scripts read; script test file -> the same.
    leg_inputs: dict[str, set[str]] = dataclasses.field(default_factory=dict)
    script_test_inputs: dict[str, set[str]] = dataclasses.field(default_factory=dict)

    def read_by(self, path: str) -> tuple[set[str], list[str]]:
        """(legs whose scripts read ``path``, script test files that read it)."""
        legs = {leg for leg, refs in self.leg_inputs.items() if any(_under(path, r) for r in refs)}
        tests = [t for t, refs in self.script_test_inputs.items() if any(_under(path, r) for r in refs)]
        return legs, tests


def build_context(tree: Tree, metadata: dict[str, Any] | None = None) -> Context:
    files = set(tree.files())
    casefold: dict[str, set[str]] = {}
    for p in files:
        casefold.setdefault(p.casefold(), set()).add(p)
    graph_error = None
    packages: dict[str, Package] = {}
    refs: dict[str, set[str]] = {}
    try:
        packages = read_graph(tree)
        if metadata is not None:
            problems = cross_check_metadata(packages, metadata, tree.repo)
            if problems:
                raise GraphError("targo metadata disagrees with the manifests: " + "; ".join(problems))
        refs = crate_literal_refs(tree, packages)
    except GraphError as err:
        graph_error = str(err)
    owners = owners_index(packages) if packages else []
    leg_inputs, test_inputs = leg_script_inputs(tree, owners)
    return Context(
        packages=packages,
        owners=owners,
        literal_refs=refs,
        gate_scripts=gate_script_closure(tree),
        dual_lanes=dual_entry_lanes(tree),
        casefold=casefold,
        files=files,
        graph_error=graph_error,
        leg_inputs=leg_inputs,
        script_test_inputs=test_inputs,
    )


@dataclasses.dataclass(frozen=True)
class PathVerdict:
    """What one changed path reaches: crates, extra legs, or everything."""

    everything: str | None = None          # the reason, when it selects everything
    crates: frozenset[str] = frozenset()
    legs: frozenset[str] = frozenset()
    rule: str = ""


def _under(path: str, prefix: str) -> bool:
    """``path`` is ``prefix`` or under it; a ``*`` suffix is a raw string
    prefix, a ``**`` start a suffix anywhere (``**.sh``: every shell file)."""
    if prefix.startswith("**"):
        return path.endswith(prefix[2:])
    if prefix.endswith("*"):
        return path.startswith(prefix[:-1])
    return path == prefix or path.startswith(prefix.rstrip("/") + "/")


def is_docs_path(path: str) -> bool:
    if path in DOCS_FILES or any(path.startswith(d) for d in DOCS_DIRS):
        return True
    if path.startswith("guide/") and path.endswith(".md"):
        return True
    if "/" not in path and (path.endswith(".md") or path.startswith("LICENSE")):
        return True
    return False


def classify_path(path: str, ctx: Context, change: Change | None = None) -> PathVerdict:
    """The rule that maps one path. Order matters: fail-closed rules first."""
    base = posixpath.basename(path)
    if change is not None and {change.old_mode, change.new_mode} & {"120000", "160000"}:
        return PathVerdict(everything=f"{path}: symbolic link or submodule in the diff", rule="mode")
    if base in BUILD_INPUT_NAMES or path in BUILD_INPUT_PATHS or any(path.startswith(d) for d in BUILD_INPUT_DIRS):
        return PathVerdict(everything=f"{path}: build input", rule="build-input")
    if base.startswith("rust-toolchain"):
        return PathVerdict(everything=f"{path}: toolchain file", rule="build-input")
    if path in ctx.gate_scripts:
        return PathVerdict(everything=f"{path}: gate script (or a script a gate reaches)", rule="gate-script")
    others = ctx.casefold.get(path.casefold(), set()) - {path}
    if others:
        return PathVerdict(everything=f"{path}: shares its case-folded spelling with {sorted(others)}",
                           rule="casefold")
    if ctx.graph_error is not None:
        return PathVerdict(everything=f"build graph unreadable: {ctx.graph_error}", rule="graph")

    owners = owners_of(path, ctx.owners)
    region = path_region(path, owners)
    if region is None:
        # Not a crate, not prose, not a gate's data: something unknown may read
        # it (a test reading a list of fixtures, a tool outside the workspace).
        # A literal naming it does not make it mapped: it only adds readers.
        return PathVerdict(everything=f"{path}: unmapped (no rule names an owner)", rule="unmapped")
    crates: set[str] = {crate for crate, targets in ctx.literal_refs.items()
                        if any(_under(path, t) for t in targets)}
    legs: set[str] = set()
    rules: list[str] = [region] + (["literal"] if crates else [])
    if region == "crate":
        if path.endswith(".md") and not crates & owners:
            # A crate's prose: no literal of the crate names it.
            legs.add("docs-links")
            rules[0] = "crate-prose"
        else:
            crates |= owners
        if _under(path, LANE_PORT_SOURCES):
            legs |= {"lane-port", "lane-build"}
    elif region == "docs":
        legs.add("docs-links")
    elif region == "duals":
        legs.add("dual-validate")
        if path == DUAL_MANIFEST or ctx.dual_lanes is None:
            legs |= set(DUAL_LEGS)
        elif path in ctx.dual_lanes:
            legs |= {f"dual-{lane}" for lane in ctx.dual_lanes[path]}
            rules.append("dual-entry")
        elif path.endswith(".py"):
            legs.add("script-tests")
        else:
            # A dual source without an entry (the validation refuses it), or
            # other data either lane may read.
            legs |= set(DUAL_LEGS)
    elif region == "engine-data":
        legs.add("engine-suite")
        if path == ENGINE_TSV:
            legs.add("tsv-validate")
    elif region == "port":
        legs |= {"lane-port", "lane-build", "port-tests"}
    elif region == "kani-domination":
        legs.add("kani-domination-tests")
    elif region == "kani-spec":
        legs.add("kani-spec-tests")
    elif region == "scripts":
        legs.add("script-tests")
    # What the legs' own scripts read, wherever it sits.
    read_legs, read_tests = ctx.read_by(path)
    if read_legs - legs:
        rules.append("leg-read")
    legs |= read_legs
    if read_tests:
        legs.add("script-tests")
        rules.append("script-test-read")
    if path.endswith(".md") or (change is not None and change.status == "D"):
        legs.add("docs-links")
    return PathVerdict(crates=frozenset(crates), legs=frozenset(legs), rule="+".join(rules))


def path_region(path: str, owners: set[str]) -> str | None:
    """The mapped region holding ``path``; ``None`` means unmapped."""
    if owners:
        return "crate"
    if is_docs_path(path):
        return "docs"
    if path.startswith(DUALS_DIR):
        return "duals"
    if path.startswith("tools/engine-suite/"):
        return "engine-data"
    if path.startswith(PORT_DIR):
        return "port"
    if path.startswith(KANI_DOMINATION_DIR):
        return "kani-domination"
    if path.startswith(KANI_SPEC_DIR):
        return "kani-spec"
    if path.startswith("scripts/"):
        return "scripts"
    return None


def legs_for_crates(affected: set[str], packages: dict[str, Package]) -> dict[str, list[str]]:
    """Leg -> the affected crates that select it."""
    out: dict[str, list[str]] = {}

    def add(leg: str, crate: str) -> None:
        out.setdefault(leg, []).append(crate)

    for crate in sorted(affected):
        if crate in BUNDLE_CRATES:
            for leg in DUAL_LEGS:
                add(leg, crate)
            add("dual-validate", crate)
        if crate in ENGINE_CRATES:
            add("engine-suite", crate)
            add("tsv-validate", crate)
        if crate in LANE_BUILD_CRATES:
            add("lane-build", crate)
        if crate in packages and crate not in RUSTC_PRIVATE_CRATES and crate not in LIBRARY_CRATES:
            add(f"crate-tests:{crate}", crate)
    return out


def all_legs(packages: dict[str, Package]) -> list[str]:
    crate_legs = [f"crate-tests:{name}" for name in sorted(packages)
                  if name not in RUSTC_PRIVATE_CRATES and name not in LIBRARY_CRATES]
    return list(FIXED_LEGS) + crate_legs


@dataclasses.dataclass
class Selection:
    base: str
    head: str
    changes: list[Change]
    everything: list[str]
    selected: dict[str, list[str]]       # leg -> reasons
    skipped: dict[str, str]              # leg -> reason
    affected_crates: list[str]
    per_path: dict[str, dict[str, Any]]

    def record(self) -> dict[str, Any]:
        return {
            "base": self.base,
            "head": self.head,
            "changed_paths": len(self.changes),
            "everything": self.everything,
            "selected": self.selected,
            "skipped": self.skipped,
            "affected_crates": self.affected_crates,
            "per_path": self.per_path,
        }

    def report_lines(self) -> list[str]:
        lines = [f"[select] {len(self.changes)} changed paths, {self.base[:12]}..{self.head[:12] if self.head else 'worktree'}"]
        if self.everything:
            lines.append(f"[select] EVERYTHING: {self.everything[0]}"
                         + (f" (+{len(self.everything) - 1} more)" if len(self.everything) > 1 else ""))
        if self.affected_crates:
            lines.append(f"[select] affected crates (reverse closure): {', '.join(self.affected_crates)}")
        if self.everything:
            lines.append(f"[select] RUN  every leg ({len(self.selected)}): {', '.join(self.selected)}")
            return lines
        for leg, reasons in self.selected.items():
            shown = ", ".join(reasons[:4]) + (f" (+{len(reasons) - 4})" if len(reasons) > 4 else "")
            lines.append(f"[select] RUN  {leg}: {shown}")
        for leg, reason in self.skipped.items():
            lines.append(f"[select] SKIP {leg}: {reason}")
        return lines


def select(changes: list[Change], ctx: Context, base: str = "", head: str = "") -> Selection:
    everything: list[str] = []
    seeds: set[str] = set()
    extra: dict[str, list[str]] = {}
    per_path: dict[str, dict[str, Any]] = {}
    for change in changes:
        verdict = classify_path(change.path, ctx, change)
        per_path[change.path] = {"rule": verdict.rule, "crates": sorted(verdict.crates),
                                 "legs": sorted(verdict.legs), "everything": verdict.everything}
        if verdict.everything:
            everything.append(verdict.everything)
            continue
        seeds |= verdict.crates
        for leg in verdict.legs:
            extra.setdefault(leg, []).append(change.path)
    packages = ctx.packages
    legs_universe = all_legs(packages) if packages else list(FIXED_LEGS)
    if everything:
        selected = {leg: ["everything: " + everything[0]] for leg in legs_universe}
        return Selection(base, head, changes, everything, selected, {},
                         sorted(packages), per_path)
    affected = reverse_closure(packages, seeds)
    selected: dict[str, list[str]] = {}
    for leg, crates in legs_for_crates(affected, packages).items():
        selected.setdefault(leg, []).extend(f"crate {c}" for c in crates)
    for leg, paths in extra.items():
        selected.setdefault(leg, []).extend(paths)
    ordered = {leg: selected[leg] for leg in legs_universe if leg in selected}
    skipped = {}
    for leg in legs_universe:
        if leg in ordered:
            continue
        skipped[leg] = skip_reason(leg, affected)
    return Selection(base, head, changes, [], ordered, skipped, sorted(affected), per_path)


def script_tests_reached(ctx: Context, changes: list[Change], tree: Tree) -> list[str]:
    """The scripts/test_*.py files a change reaches: every one when it selects
    everything; else each test whose inputs (its code closure and the paths
    that code names) hold a changed path, or whose closure's code names a
    deleted path by any spelling the closure rule reads (a deleted file is no
    candidate any more, so only its name is left to find)."""
    tests = sorted(ctx.script_test_inputs)
    if any(classify_path(c.path, ctx, c).everything for c in changes):
        return tests
    chosen = []
    deleted = [c.path for c in changes if c.status == "D"]
    patterns = [pat for path in deleted for pat in _reference_patterns(path)]
    for test in tests:
        inputs = ctx.script_test_inputs[test]
        if any(any(_under(c.path, ref) for ref in inputs) for c in changes):
            chosen.append(test)
            continue
        if patterns:
            code = [p for p in inputs if p in ctx.files and posixpath.splitext(p)[1] in _CODE_SUFFIXES]
            if any(pat.search(_code_text(p, tree.read(p) or "")) for p in code for pat in patterns):
                chosen.append(test)
    return chosen


def skip_reason(leg: str, affected: set[str]) -> str:
    crates = ", ".join(sorted(affected)) or "none"
    if leg in DUAL_LEGS:
        return f"no bundle crate in the reverse closure ({crates}) and no dual source of this lane changed"
    if leg == "engine-suite":
        return f"trust-mc-engine is not in the reverse closure ({crates}) and its TSV is unchanged"
    if leg == "lane-build":
        return f"no crate it builds is in the reverse closure ({crates}), and trust-mc-compiler/src and tools/port are unchanged"
    if leg.startswith("crate-tests:"):
        return f"{leg.split(':', 1)[1]} is not in the reverse closure ({crates})"
    if leg in ("ay-pin", "shared-pins"):
        return "no manifest, lockfile or pin changed (those select everything)"
    return "none of its inputs changed"


# --------------------------------------------------------------------------
# Diffs
# --------------------------------------------------------------------------


def parse_raw_diff(text: str) -> list[Change]:
    """``git diff --raw -z --no-renames`` records -> changes."""
    out: list[Change] = []
    parts = text.split("\0")
    i = 0
    while i < len(parts) - 1:
        meta = parts[i]
        if not meta.startswith(":"):
            i += 1
            continue
        fields = meta[1:].split()
        old_mode, new_mode, status = fields[0], fields[1], fields[4][0]
        path = parts[i + 1]
        out.append(Change(path, status, old_mode, new_mode))
        i += 2
    return out


def diff_changes(repo: Path, base: str, head: str | None) -> list[Change]:
    args = ["git", "-C", str(repo), "diff", "--raw", "-z", "--no-renames", "--no-ext-diff", base]
    if head is not None:
        args.append(head)
    text = subprocess.run(args, check=True, capture_output=True, text=True).stdout
    changes = parse_raw_diff(text)
    if head is None:
        untracked = subprocess.run(["git", "-C", str(repo), "ls-files", "-z", "--others", "--exclude-standard"],
                                   check=True, capture_output=True, text=True).stdout
        changes += [Change(p, "A", "000000", "100644") for p in untracked.split("\0") if p]
    return changes


def merge_base(repo: Path, ref: str = "origin/main", head: str = "HEAD") -> str:
    return subprocess.run(["git", "-C", str(repo), "merge-base", head, ref], check=True,
                          capture_output=True, text=True).stdout.strip()


def targo_metadata(repo: Path) -> dict[str, Any] | None:
    """``targo metadata --no-deps`` for the worktree, or None when targo is absent."""
    try:
        targo = subprocess.run([str(SCRIPTS_DIR / "resolve-trust-tool.sh"), "targo"], check=True,
                               capture_output=True, text=True).stdout.strip()
        out = subprocess.run([targo, "metadata", "--offline", "--no-deps", "--format-version", "1"],
                             cwd=repo, check=True, capture_output=True, text=True).stdout
        return json.loads(out)
    except (OSError, subprocess.CalledProcessError, json.JSONDecodeError):
        return None


# --------------------------------------------------------------------------
# Replay
# --------------------------------------------------------------------------


def replay(repo: Path, rev: str, count: int) -> dict[str, Any]:
    """Select over the first-parent diffs of the last ``count`` commits of ``rev``."""
    commits = subprocess.run(["git", "-C", str(repo), "rev-list", "--first-parent", f"-{count}", rev],
                             check=True, capture_output=True, text=True).stdout.split()
    rows = []
    for commit in commits:
        parents = subprocess.run(["git", "-C", str(repo), "rev-list", "--parents", "-1", commit],
                                 check=True, capture_output=True, text=True).stdout.split()[1:]
        subject = subprocess.run(["git", "-C", str(repo), "log", "-1", "--format=%s", commit],
                                 check=True, capture_output=True, text=True).stdout.strip()
        if not parents:
            continue
        changes = diff_changes(repo, parents[0], commit)
        ctx = build_context(Tree(repo, commit))
        sel = select(changes, ctx, parents[0], commit)
        rows.append({
            "commit": commit[:9],
            "subject": subject[:72],
            "paths": len(changes),
            "everything": bool(sel.everything),
            "everything_reason": sel.everything[0] if sel.everything else None,
            "selected": sorted(sel.selected),
            "legs_universe": len(sel.selected) + len(sel.skipped),
        })
    return {"rev": rev, "commits": len(rows), "rows": rows}


def replay_summary(result: dict[str, Any]) -> list[str]:
    rows = result["rows"]
    counts: dict[str, int] = {}
    for row in rows:
        for leg in row["selected"]:
            key = "crate-tests:*" if leg.startswith("crate-tests:") else leg
            counts[key] = counts.get(key, 0) + (1 if not (leg.startswith("crate-tests:") and key in row.get("_seen", ())) else 0)
    per_leg: dict[str, int] = {}
    for row in rows:
        seen = set()
        for leg in row["selected"]:
            key = "crate-tests:*" if leg.startswith("crate-tests:") else leg
            if key not in seen:
                per_leg[key] = per_leg.get(key, 0) + 1
                seen.add(key)
    lines = [f"replay over {len(rows)} first-parent commits of {result['rev']}:"]
    lines.append(f"  everything: {sum(1 for r in rows if r['everything'])}; "
                 f"nothing beyond docs: {sum(1 for r in rows if set(r['selected']) <= {'docs-links'})}")
    for leg in list(FIXED_LEGS) + ["crate-tests:*"]:
        lines.append(f"  {leg:24} selected in {per_leg.get(leg, 0):3d} / {len(rows)} (before: {len(rows)} / {len(rows)})")
    return lines


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--repo", type=Path, default=REPO_ROOT)
    parser.add_argument("--base", help="base revision (default: merge-base of HEAD and --main)")
    parser.add_argument("--main", default="origin/main")
    parser.add_argument("--head", help="head revision (default: the working tree)")
    parser.add_argument("--no-metadata", action="store_true",
                        help="skip the targo metadata cross-check (replays, hosts without targo)")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--replay", type=int, metavar="N",
                        help="select over the last N first-parent commits of --main instead")
    args = parser.parse_args(argv)
    repo = args.repo.resolve()
    if args.replay:
        result = replay(repo, args.main, args.replay)
        if args.json:
            print(json.dumps(result, indent=2))
        else:
            for row in result["rows"]:
                legs = "EVERYTHING" if row["everything"] else (",".join(row["selected"]) or "-")
                print(f"{row['commit']} {row['paths']:4d} {legs}  # {row['subject']}")
            print("\n".join(replay_summary(result)))
        return 0
    base = args.base or merge_base(repo, args.main, args.head or "HEAD")
    changes = diff_changes(repo, base, args.head)
    metadata = None if (args.no_metadata or args.head) else targo_metadata(repo)
    ctx = build_context(Tree(repo, args.head), metadata)
    if metadata is None and not args.no_metadata and not args.head:
        ctx.graph_error = ctx.graph_error or "targo metadata unavailable: the manifests cannot be cross-checked"
    sel = select(changes, ctx, base, args.head or "")
    if args.json:
        print(json.dumps(sel.record(), indent=2, sort_keys=True))
    else:
        print("\n".join(sel.report_lines()))
    return 0


if __name__ == "__main__":
    sys.exit(main())
