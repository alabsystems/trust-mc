#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

"""Whether live main changed a frozen first-party pin, over its whole tree.

trust-mc pins a few packages of a sibling repository (TrustIR's `trust-ir` and
`trust-ir-build`, trust-vc's `trust-vc-merge-contract`) as frozen content: the
pin may trail live main only while nothing a consumer builds from changed there.

Drift is every path `git diff-tree` reports between the pin and live main, over
the whole tree: sources, manifests anywhere, root files, `.gitattributes`,
symbolic links, submodules. Three earlier rounds derived "what the packages
build from" (a source walk, one build's dep-info, the packages' directories),
and each was evaded by a file outside the derived set that Cargo or git still
reads: a case-folded `crates/A/build.rs` beside `crates/a`, a path dependency
spelled through a symbolic link that live main re-points, a root
`.gitattributes` rewriting the bytes `include_str!` reads, another manifest
declaring a pinned package's name, a new intermediate `[workspace]`. Nothing is
derived here, so each of those is a change, and a change is drift.

The only thing subtracted is a reviewed list, scripts/pin-exclusions.toml: per
repository, path patterns (`*` and `?` match within one component), each with
the reason it is unread. A changed path is excluded only if it lies under a
listed pattern as spelled, and

- no component of it is `Cargo.toml`, `.gitattributes`, `.gitmodules`, `.cargo`
  or `.git`, and it is no `build.rs` beside a `Cargo.toml`: Cargo and git read
  those by name (compared case- and normalization-folded, as APFS opens them);
- it is a regular file at the pin and at live main, where it exists: a symbolic
  link or a submodule changes what is read through it;
- no other tracked spelling, at the pin or at live main, folds onto it or onto a
  directory holding it: a case-insensitive checkout writes one over the other.

Anything else under a pattern is drift. When every change is excluded, what
they fall under must be unread by the pinned packages, or the gate refuses
(exit 2) naming the exclusion. That is checked on the tree of the pin as a
checkout writes it (`git checkout-index` from a scratch index), which is what
a path consumer's working tree and Cargo's checkout of a Git dependency hold:
`git archive` would apply `export-subst` and `export-ignore`, which no checkout
does. A path whose attributes name a filter driver or a working-tree encoding is
refused, since Git and Cargo's libgit2 write it differently. An excluded path
must not lie under, or be,

- the directory of a package the pinned ones reach by path (a normal or build
  dependency, on any target, optional or not), the directory of the library,
  procedural macro or build script root of one (modules resolve beneath it under
  any `cfg`), or a target, readme or license file its manifest names;
- a file rustc's dep-info names, the directory rustc resolves module files in
  beside it, a path a build script watches (`rerun-if-changed`), or a
  directory the linker searches for the libraries a build script links
  (`rustc-link-search`, `rustc-flags`: `check` never links, so no dep-info
  names what the linker reads), when the closure is checked (`targo
  --unverified check`, from the consumer's directory, in the dev and the
  release profile) as every build of the consumer can compile it. Dep-info is
  read exactly as rustc writes it (it escapes a space and nothing else, so the
  per-prerequisite lines decide and every rule must list exactly them), a
  build script's output as Cargo reads it (trimmed lines, `cargo:` and
  `cargo::`), and that reading must match what Cargo recorded (the run's
  fingerprint, the build-script-executed message); anything else, a name
  dep-info cannot spell, a linker argument (`rustc-link-arg*`), a relative
  search path or a library named by a path is refused. So is, before anything
  is built, a package of the closure that declares `links`: Cargo hands what
  its build script prints as metadata to the build script of every package
  depending on it, the consumer's included, and a value can name paths in any
  shape (one, a list, padded, relative), so what those build scripts read
  cannot be listed. So is an assembler directive reading a file, `.incbin` or
  `.include` in any ASCII case before the quoted name, in a file rustc's
  dep-info names for any unit the checks compile (registry and Git sources
  included) or in the compiler's expansion of a unit of the closure: the
  checks hand Cargo a compiler that runs Cargo's command line for such a unit
  once more with `-Zunpretty=hir`, so a template a macro builds (`concat!`, a
  procedural macro's `format!`) is searched as the compiler expanded it, and a
  unit compiled without that record is refused. The assembler reads what an
  `asm!` or `global_asm!` template names when rustc generates the code of a
  library, which `check` never does and no dep-info names. `mod m;` makes
  rustc look for both `m.rs` and `m/mod.rs` and dep-info names only the one
  it found, so the directory holding a named file (holding its directory, for
  a `mod.rs`) is read. The builds are checked two ways.
  Per package of the closure, every feature set a build can give it: the
  closure under its own `[features]` of what every edge of the consumer's
  graph into it requests, plus any of the features the consumer's
  `--all-features` graph gives it (whichever members a build selects, dev or
  not, with whatever features of theirs), its dependencies getting what it
  asks of them; more than MAX_FEATURE_SETS of them in all are refused before
  anything is built. And per build the consumer's lanes run, which the
  reviewed list's [consumer-builds] declares (the command after `targo`):
  every package that build compiles for the closure, dependencies included,
  exactly as Cargo's resolver gives it there. The gate asks Cargo for that
  build's unit graph (resolver 2 as the build runs it: dev-dependencies only
  when it compiles tests, the host's features apart for build scripts and
  procedural macros, the dependencies of its target platforms only) and checks
  a probe that asks for each such package by its exact source and version with
  exactly those features, on the side it was compiled for; the probe's own
  unit graph must list the same units (package, target, features, platform,
  and what each depends on), or the gate refuses. It refuses a consumer with
  no declared build, declared builds none of which compiles a pinned package,
  a command with an option whose effect on what Cargo compiles it does not
  model, a profile of the consumer's manifest or a build compiling a unit of
  the closure's graph with `panic = "abort"` (the checks unwind), and a
  compiled file that enables `cfg(overflow_checks)` (the checks set it with
  debug assertions, a profile need not). `targo trust <command>` resolves as
  `targo --unverified <command>`; it forces debug assertions and overflow
  checks on for every unit, in the release profile too, which the dev check
  compiles, and sets `cfg(trust_verify)` for a member of the consumer's
  workspace (measured with seal 9192), so such a build whose units of the
  closure's graph include a member is refused; for a dependency too only when
  TRUSTFLAGS asks with `-Ztrust-verify-include-dependencies`, a flag passed
  outside the command line (below). rustc reports every spelling it
  resolved (an alias, a macro argument, `#[path]`, a read through a link), and
  a read outside the pin's tree that is no registry source is refused: it is not
  pinned content;
- a file whatever those checks run reads, however it names or reaches it:
  rustc, a procedural macro, a build script and what that runs (the C
  preprocessor and the assembler on a `.S`, with the defines and includes it
  gives them, a template it writes to OUT_DIR, a file it reaches through a
  symbolic link). That is observed, not searched for. Before each check every
  excluded path that exists at the pin has its access time set back, and one
  whose access time moved during the check was read (a canary read first shows
  that the file system records reads, or the gate refuses). Then every probe is
  checked once more, in the dev and the release profile and a fresh target
  directory, with those paths removed from the tree: a check that then fails
  read one of them, and so did a build script of a package of the tree that
  then leaves otherwise (other directives, other entries in its OUT_DIR, other
  bytes in one; an ar archive is compared without its members' times). A
  copy leaves the original's access time as it was where it is a clone, as
  `std::fs::copy` makes one on APFS, and a build script may tolerate the
  file's absence (`let _ = std::fs::copy(..)`, a default of the same name) or
  only test whether it exists. The checks must leave the tree of the pin as
  they found it: a build script writing into it (a copy of an excluded file
  it keeps in sync there) makes the checks without the files compile what the
  checks with them left, so that is refused;
- a path that a tracked file names for the C preprocessor or an assembler that
  a build script runs (`#include`, `#include_next`, `#import`, `#embed`,
  `.incbin`, `.include`, NASM's `incbin` and `%include`), read from the files
  at the pin, so whichever host or configuration builds them, in union with
  what the checks observe. A build script can hand any file of the tree to the
  tool, watched or not, so every tracked regular file is read but the excluded
  changes themselves. The tool looks the name up in a directory the build
  script chooses (its working directory, an `-I`), so the name reads every
  path that some directory puts it at: each whose last components agree with
  the name's after its last `..`. A directive at the start of a statement
  whose name is no one string literal (a macro, a `-D` define, a template a
  program fills: `{blob}`, `$BLOB`, `@BLOB@`, `%s`) is refused, since what it
  reads cannot be listed, except in a file under a reviewed exclusion, which
  the list reviews as unread by any build (a shell comment there spells
  `# import`). A file under a reviewed exclusion that a build does read is
  read strictly after all: one a literal name of a strictly read file reaches,
  one a build script's string literal names, or one a symbolic link, a
  watched path, a Rust include or dep-info reads;
- a path that a Rust file a consumer can compile from a closure package (any
  of its files outside the directories of its test, bench, example and binary
  targets and Cargo's tests/, benches/ and examples/, where no root a consumer
  compiles lies, read through a symbolic link to a directory too), a Rust file
  one of those includes, or a module file one declares, names with
  `include_str!`, `include_bytes!`, `include!` (a string literal, or literals
  `concat!` puts together, after `env!("CARGO_MANIFEST_DIR")` or not) or a
  `path` attribute (`#[path]`, `#[cfg_attr(.., path = ..)]`), resolved as
  rustc resolves it (a `..` after a symbolic link climbs from where the link
  points), whatever `cfg` the item is under: the checks compile only this
  host's, and rustc names in dep-info only what they compile. An include in
  the body of a macro definition is resolved from the file calling the macro,
  which may be any, so its name reads every excluded path some directory puts
  it at; an include whose path no literal spells (a macro's argument, another
  `env!`) is refused, one from `OUT_DIR` aside. `mod m;` reads where rustc may
  look for its file (beside the declaring file and beneath its stem), unless
  a plain `#[path]` names the file, and that module file is read in turn;
- a path a string literal of a closure package's build script (its root, the
  module files it declares and the Rust files it includes) names from the
  package's directory, which Cargo runs it in, or from `CARGO_MANIFEST_DIR`
  after a placeholder (`"{dir}/../x"`), whatever host: a build script that
  hands a file to a tool, copies it, reads it or tests whether it exists, on
  a host the checks do not run it for or for a path only live main adds,
  spells it so;
- in a library search directory a build script gives beneath the target
  directory, what the linker opens there: what the directory resolves to where
  it is, or lies beneath, a symbolic link out of the target directory, and
  what each symbolic link in it resolves to (the linker and rustc bundling a
  static library read it at codegen; making a link reads nothing, so neither
  the read witness nor the absence check sees it); a hard link there is
  refused;
- the target of a tracked symbolic link;
- where the reviewed list says a pinned package runs Cargo on its own workspace
  at run time: the workspace's Cargo.lock, the directory of every member and of
  every path dependency of one, and a directory a member glob lists. Cargo loads
  every member (and infers its targets from its directory) and resolves with
  that lock before it builds anything;

and no other tracked manifest of the pin may declare a pinned package's name,
since a Git consumer resolves a dependency by name over every manifest of the
checkout.

What stays outside. A read of an excluded path in a configuration those checks
do not build (a host other than the one running the gate, whose toolchain
trust-mc's builds use; `cargo doc`'s `cfg(doc)`; a feature of a pinned package
that no manifest of the consumer asks for, named on a command line; a build no
lane declares, for the features it gives the closure's dependencies or a panic
strategy Cargo configuration, not the manifest, sets for it; a `--cfg` a lane
passes the compiler outside its command line, through RUSTFLAGS, or
TRUSTFLAGS' dependency verification, which check-trust-verification.sh turns
on and which gives a closure package `cfg(trust_verify)`) is seen only through
a name a tracked file spells for the C preprocessor or an assembler, a Rust
include or module, or a build script's string literal: what a build script
reads, copies, links, searches or tests the existence of there through a path
no literal of its own spells (one it puts together from pieces, as
`Path::new("..").join("shared")` or `format!("{dir}/../{name}")` does, or
reads from a file or the environment), a library search directory it gives
only there, what a procedural macro or the library of a build dependency
reads there, an include a procedural macro's output spells, and a `path`
attribute or a `mod m;` inside an inline module of a file outside the
package's directory (rustc resolves it beneath the module's name), stay
outside. So do a read by something the checks run that tolerates the path's
absence, leaves its access time as it was and changes neither what a build
script prints nor the entries and bytes of its OUT_DIR (rustc or a procedural
macro testing whether the path exists); a read of a path the pin does not hold
(live main adds it) that no such name reaches; a directive whose name is no
literal in an unchanged file under a reviewed exclusion that no build is seen
to read; a read the packages' code makes at run time; and one outside the
workspace's members by a package that run-time Cargo compiles. The environment (`env!`,
`rerun-if-env-changed`) is not pinned content. That residual is confined to the
listed exclusions, which is why each entry states why it holds there.

Threat model. The gate defends against accidental regressions by first-party
authors and agents: a forgotten file, an unpinned input, a silently capped
check, a parser that fails open. Each such shape is fixed where it arises, by
asking git, rustc, Cargo and the file system what they read rather than
guessing, and anything it cannot read is refused. It does not defend against
spellings written to evade it; these are out of model, one sentence each:

- a tracked file name crafted so that rustc's dep-info for it reads as a
  different well-formed list of existing paths, on the prerequisite lines and
  every rule at once;
- a `#[link(name = ..., modifiers = "+verbatim")]` in source whose name climbs
  out of the search directory it is found through with `../`;
- a symbolic link in a system library directory, which the linker searches on
  its own, pointing back into the tree;
- in an `asm!` or `global_asm!` template of a library of the closure, an
  assembler directive whose name a string literal spells with escapes
  (`\\x2e`, `\\u{..}`), or that only the assembler puts together (`.macro`,
  `.irp`);
- in a file a build script can hand the C preprocessor or an assembler, such
  a directive spelled so (escapes, `.macro`, `.irp`, token pasting, a
  digraph), or one whose name is no string literal written after other text
  on its line, where no statement starts;
- a template's placeholder spelled as a plain name inside quotes (`.incbin
  "BLOB_PATH"`, which a build script fills with `.replace`), read as a literal
  name that reaches nothing;
- a directive held in a Rust constant apart from its name (`const D: &str =
  ".incbin";`), or a GNU ld script named as a `lib*.a` whose `INPUT()` or
  `GROUP()` names another file.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import unicodedata
import urllib.parse
from dataclasses import dataclass
from fnmatch import fnmatchcase
from pathlib import Path
from typing import Any, Optional, Sequence

from python_executable import python_executable_header

if sys.version_info >= (3, 11):
    from tomllib import TOMLDecodeError, loads as toml_loads
else:
    from tomli import TOMLDecodeError, loads as toml_loads


class Refusal(Exception):
    """Whether the excluded changes are unread cannot be shown, or they are read."""


PROBE = "trust-mc-pin-probe"
REGULAR_FILE_MODES = frozenset({"100644", "100755"})
SYMBOLIC_LINK_MODE = "120000"
SUBMODULE_MODE = "160000"
ABSENT_MODE = "000000"
MANIFEST = "cargo.toml"
BUILD_SCRIPT = "build.rs"
MODULE_FILE = "mod.rs"
# Attributes under which Git's checkout (a path consumer's working tree) and
# libgit2's (Cargo's checkout of a Git dependency) write different bytes.
DIVERGENT_ATTRIBUTES = ("filter", "working-tree-encoding")
# The table of the reviewed list naming repositories whose pinned packages run
# Cargo on their own workspace at run time.
CARGO_AT_RUN_TIME = "cargo-at-run-time"
# The most feature sets the gate checks (each in the dev and the release
# profile, about 17 s apiece for trust-ir on this host); a consumer that can
# build the closure more ways is refused before anything is built.
MAX_FEATURE_SETS = 32
# What Cargo or git reads by name wherever it sits, folded.
READ_BY_NAME = frozenset({MANIFEST, ".gitattributes", ".gitmodules", ".cargo", ".git"})
# The targets of a package a consumer compiles, whose directories are module roots.
COMPILED_ROOT_KINDS = frozenset(
    {"lib", "rlib", "dylib", "cdylib", "staticlib", "proc-macro", "custom-build"}
)
PROFILES = ((), ("--release",))


def fold(name: str) -> str:
    """The key under which a case- and normalization-insensitive file system
    (APFS, HFS+) opens `name` (canonical caseless matching)."""
    return unicodedata.normalize("NFD", unicodedata.normalize("NFD", name).casefold())


def _under(path: str, directory: str) -> bool:
    """Whether the repository-relative `path` is `directory` or lies beneath it;
    `.` is the repository's root."""
    return directory == "." or path == directory or path.startswith(directory + "/")


def _git(
    checkout: Path,
    *arguments: str,
    env: Optional[dict[str, str]] = None,
    stdin: Optional[bytes] = None,
) -> bytes:
    try:
        return subprocess.run(
            ["git", "-C", str(checkout), *arguments],
            input=stdin, capture_output=True, check=True, env=env,
        ).stdout
    except (OSError, subprocess.CalledProcessError) as error:
        detail = getattr(error, "stderr", b"") or b""
        raise Refusal(
            f"git {' '.join(arguments)} failed in {checkout}: "
            f"{detail.decode(errors='replace').strip() or error}"
        ) from error


def _decode(name: bytes) -> str:
    return name.decode("utf-8", "surrogateescape")


# --- the reviewed exclusions -------------------------------------------------


@dataclass(frozen=True)
class Exclusion:
    """A path pattern of a pinned repository, and why nothing reads it."""

    pattern: str
    why: str

    def covers(self, path: str) -> bool:
        """Whether `path`, as spelled, is under the pattern."""
        parts, mine = path.split("/"), self.pattern.split("/")
        return len(parts) >= len(mine) and all(map(fnmatchcase, parts, mine))


def pattern_problem(pattern: str) -> Optional[str]:
    """Why `pattern` cannot be an exclusion, or None."""
    if not isinstance(pattern, str) or not pattern:
        return "a pattern is a non-empty relative path"
    for part in pattern.split("/"):
        if part in ("", ".", ".."):
            return "a pattern is a relative path of named components"
        if any(char in part for char in "[]\\") or "**" in part:
            return "only `*` and `?` match, each within one component"
        if fold(part) in READ_BY_NAME or fold(part) == BUILD_SCRIPT:
            return f"Cargo and git read {part} by name; it is never excluded"
    return None


def load_exclusions(path: Path, repository: str) -> list[Exclusion]:
    """The exclusions `path` lists for `repository`; none when it lists none."""
    try:
        document = toml_loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, TOMLDecodeError) as error:
        raise Refusal(f"cannot read the exclusions {path}: {error}") from error
    table = document.get(repository, {})
    if not isinstance(table, dict):
        raise Refusal(f"{path}: [{repository}] is not a table of pattern = reason")
    exclusions = []
    for pattern, why in table.items():
        problem = pattern_problem(pattern)
        if problem is not None:
            raise Refusal(f"{path}: [{repository}] {pattern!r}: {problem}")
        if not isinstance(why, str) or not why.strip():
            raise Refusal(f"{path}: [{repository}] {pattern!r} needs the reason it is unread")
        exclusions.append(Exclusion(pattern, why.strip()))
    return exclusions


def load_cargo_at_run_time(path: Path, repository: str) -> Optional[str]:
    """Why a pinned package of `repository` runs Cargo on its own workspace at
    run time, as `path` states it; None when it states nothing."""
    try:
        document = toml_loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, TOMLDecodeError) as error:
        raise Refusal(f"cannot read the exclusions {path}: {error}") from error
    table = document.get(CARGO_AT_RUN_TIME, {})
    if not isinstance(table, dict):
        raise Refusal(f"{path}: [{CARGO_AT_RUN_TIME}] is not a table of repository = reason")
    why = table.get(repository)
    if why is not None and (not isinstance(why, str) or not why.strip()):
        raise Refusal(f"{path}: [{CARGO_AT_RUN_TIME}] {repository!r} needs the reason")
    return why.strip() if why is not None else None


# --- what changed ------------------------------------------------------------


@dataclass(frozen=True)
class Change:
    """One path `git diff-tree` reports between the pin and live main."""

    path: str
    pin_mode: str  # ABSENT_MODE when live main adds it
    main_mode: str  # ABSENT_MODE when live main deletes it


def changes(checkout: Path, pin: str, main: str) -> list[Change]:
    """Every path whose entry differs between `pin` and `main`, whole tree."""
    fields = _git(checkout, "diff-tree", "-r", "-z", "--no-renames", "--raw", pin, main).split(
        b"\0"
    )
    found = []
    index = 0
    while index < len(fields):
        header = fields[index].decode()
        if not header:
            index += 1
            continue
        if not header.startswith(":") or index + 1 >= len(fields):
            raise Refusal(f"unexpected git diff-tree output {header!r}")
        pin_mode, main_mode = header[1:].split(" ")[:2]
        found.append(Change(_decode(fields[index + 1]), pin_mode, main_mode))
        index += 2
    return found


def tracked(checkout: Path, revision: str) -> dict[str, str]:
    """Repository-relative path -> mode of every entry of `revision` (files,
    symbolic links and submodules)."""
    entries = {}
    for entry in _git(checkout, "ls-tree", "-r", "-z", "--full-tree", revision).split(b"\0"):
        if entry:
            header, name = entry.split(b"\t", 1)
            entries[_decode(name)] = header.decode().split()[0]
    return entries


def classify(
    changed: Sequence[Change],
    exclusions: Sequence[Exclusion],
    pin_tree: dict[str, str],
    main_tree: dict[str, str],
) -> tuple[list[str], list[tuple[str, Exclusion]]]:
    """The drift (a path, or a path and why its exclusion does not apply), and
    the changes an exclusion covers."""
    spellings: dict[str, set[str]] = {}
    manifest_directories: set[str] = set()
    for tree in (pin_tree, main_tree):
        for name in tree:
            parts = name.split("/")
            for depth in range(1, len(parts) + 1):
                prefix = "/".join(parts[:depth])
                spellings.setdefault(fold(prefix), set()).add(prefix)
            if fold(parts[-1]) == MANIFEST:
                manifest_directories.add(fold("/".join(parts[:-1])))

    drift: list[str] = []
    excluded: list[tuple[str, Exclusion]] = []
    for change in changed:
        exclusion = next((each for each in exclusions if each.covers(change.path)), None)
        if exclusion is None:
            drift.append(change.path)
            continue
        reason = _not_excludable(change, spellings, manifest_directories)
        if reason is None:
            excluded.append((change.path, exclusion))
        else:
            drift.append(f"{change.path} (under exclusion {exclusion.pattern}, but {reason})")
    return drift, excluded


def _not_excludable(
    change: Change, spellings: dict[str, set[str]], manifest_directories: set[str]
) -> Optional[str]:
    parts = change.path.split("/")
    for part in parts:
        if fold(part) in READ_BY_NAME:
            return f"Cargo or git reads {part} by name"
    if fold(parts[-1]) == BUILD_SCRIPT and fold("/".join(parts[:-1])) in manifest_directories:
        return "a build.rs beside a Cargo.toml is a build script"
    for mode in (change.pin_mode, change.main_mode):
        if mode != ABSENT_MODE and mode not in REGULAR_FILE_MODES:
            return f"mode {mode} is no regular file: what is read through it changes"
    for depth in range(1, len(parts) + 1):
        prefix = "/".join(parts[:depth])
        others = sorted(spellings.get(fold(prefix), set()) - {prefix})
        if others:
            return f"tracked {others[0]} folds onto {prefix}"
    return None


# --- what the pinned packages read, at the pin -------------------------------


def extract_revision(checkout: Path, revision: str, destination: Path) -> dict[str, str]:
    """Write the tree of `revision` into `destination` as a checkout writes it:
    `git checkout-index` from a scratch index, so the conversions a checkout
    makes (end of line, `ident`) are made and the ones only `git archive` makes
    (`export-subst`, `export-ignore`) are not. Refuses a path whose attributes
    name a filter driver or a working-tree encoding: Git and libgit2 write it
    differently, so which bytes a consumer compiles is not one answer."""
    index = destination.parent / f"{destination.name}.index"
    environment = {**os.environ, "GIT_INDEX_FILE": str(index)}
    work_tree = ("--work-tree", str(destination))
    _git(checkout, *work_tree, "read-tree", revision, env=environment)
    entries = tracked(checkout, revision)
    files = sorted(name for name, mode in entries.items() if mode != SUBMODULE_MODE)
    fields = _git(
        checkout, *work_tree, "check-attr", "--cached", "-z", "--stdin", *DIVERGENT_ATTRIBUTES,
        env=environment,
        stdin=b"".join(name.encode("utf-8", "surrogateescape") + b"\0" for name in files),
    ).split(b"\0")
    for start in range(0, len(fields) - 2, 3):
        path, attribute, value = (_decode(field) for field in fields[start : start + 3])
        if value not in ("unspecified", "unset"):
            raise Refusal(
                f"{path} has attribute {attribute}={value} at {revision}: Git and libgit2 "
                "check it out differently, so what a consumer compiles cannot be read"
            )
    _git(checkout, *work_tree, "checkout-index", "--all", "--force", env=environment)
    missing = [name for name in files if not os.path.lexists(destination / name)]
    if missing:
        raise Refusal(
            f"checking out {revision} wrote {len(missing)} fewer tracked files than it "
            f"holds (first: {missing[0]}); what the gate reads must be the whole tree"
        )
    return entries


def _cargo_json(cargo: str, arguments: Sequence[str], cwd: Path) -> dict[str, Any]:
    try:
        output = subprocess.check_output([cargo, *arguments], stderr=subprocess.PIPE, cwd=cwd)
    except (OSError, subprocess.CalledProcessError) as error:
        detail = getattr(error, "stderr", b"") or b""
        raise Refusal(
            f"{cargo} {arguments[0]} failed in {cwd}: "
            f"{detail.decode(errors='replace').strip() or error}"
        ) from error
    return json.loads(output)


@dataclass(frozen=True)
class Member:
    """One package of the pinned workspace, as its manifest declares it."""

    name: str
    directory: Path
    # The directories of the roots a consumer compiles from it (library,
    # procedural macro, build script): modules resolve beneath them.
    roots: list[Path]
    # Every file its manifest names: targets of every kind, readme, license.
    named: list[Path]
    # The directories of its path dependencies, normal or build, on every
    # target, optional or not.
    path_dependencies: list[Path]
    # Its [features] table as Cargo reads it (implicit optional-dependency
    # features included): feature -> what enabling it enables.
    features: dict[str, list[str]]
    # Its `links` key: Cargo hands its build script's metadata to dependents.
    links: Optional[str] = None
    # The directories of its targets a consumer never compiles (tests, benches,
    # examples, binaries, and Cargo's tests/, benches/ and examples/) that hold
    # no root a consumer compiles.
    uncompiled_roots: tuple[Path, ...] = ()
    # The root files of its build scripts.
    build_scripts: tuple[Path, ...] = ()


@dataclass(frozen=True)
class Workspace:
    """The tree's workspace, as Cargo loads it."""

    members: dict[str, Member]
    # What loading it reads before anything is built: its Cargo.lock, the
    # directory of every member and of every path dependency of one (any kind),
    # and each directory a member glob lists.
    loaded: list[Path]


def tree_workspace(cargo: str, tree: Path, packages: Sequence[str]) -> Workspace:
    """Every member of the tree's workspace, whose root must be the repository root."""
    metadata = _cargo_json(
        cargo,
        [
            "metadata", "--format-version", "1", "--no-deps", "--offline",
            "--manifest-path", str(tree / "Cargo.toml"),
        ],
        tree.parent,
    )
    if Path(metadata["workspace_root"]).resolve() != tree:
        raise Refusal(
            f"the workspace root of the pin is {metadata['workspace_root']}, not the "
            "repository root"
        )
    members: dict[str, Member] = {}
    loaded = {tree / "Cargo.lock"}
    for package in metadata.get("packages", []):
        if package["name"] in members:
            raise Refusal(f"the workspace declares package {package['name']!r} twice")
        directory = Path(os.path.normpath(Path(package["manifest_path"]).parent))
        named = [Path(target["src_path"]) for target in package.get("targets", [])]
        for field_name in ("readme", "license_file"):
            if package.get(field_name):
                named.append(directory / package[field_name])
        loaded.add(directory)
        loaded.update(
            Path(os.path.normpath(dependency["path"]))
            for dependency in package.get("dependencies", [])
            if dependency.get("path")
        )
        roots = sorted(
            {
                Path(os.path.normpath(Path(target["src_path"]).parent))
                for target in package.get("targets", [])
                if COMPILED_ROOT_KINDS & set(target.get("kind", []))
            }
        )
        others = {
            Path(os.path.normpath(Path(target["src_path"]).parent))
            for target in package.get("targets", [])
            if not COMPILED_ROOT_KINDS & set(target.get("kind", []))
        } | {directory / name for name in ("tests", "benches", "examples")}
        members[package["name"]] = Member(
            package["name"],
            directory,
            roots,
            sorted({Path(os.path.normpath(path)) for path in named}),
            sorted(
                {
                    Path(os.path.normpath(dependency["path"]))
                    for dependency in package.get("dependencies", [])
                    if dependency.get("path") and dependency.get("kind") in (None, "normal", "build")
                }
            ),
            {name: list(enables) for name, enables in (package.get("features") or {}).items()},
            package.get("links"),
            tuple(
                sorted(
                    other for other in others
                    if not any(_under(str(root), str(other)) for root in roots)
                )
            ),
            tuple(
                sorted(
                    Path(os.path.normpath(target["src_path"]))
                    for target in package.get("targets", [])
                    if "custom-build" in target.get("kind", [])
                )
            ),
        )
    missing = sorted(set(packages) - set(members))
    if missing:
        raise Refusal(f"the workspace declares no package {missing}")
    try:
        root = toml_loads((tree / "Cargo.toml").read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, TOMLDecodeError) as error:
        raise Refusal(f"cannot read the pin's root manifest: {error}") from error
    for pattern in ((root.get("workspace") or {}).get("members") or []):
        parts = str(pattern).split("/")
        literal = next(
            (index for index, part in enumerate(parts) if any(char in part for char in "*?[")),
            None,
        )
        if literal is not None:  # Cargo lists this directory to expand the glob.
            loaded.add(Path(os.path.normpath(tree.joinpath(*parts[:literal]))))
    return Workspace(members, sorted(loaded))


def package_closure(members: dict[str, Member], packages: Sequence[str]) -> list[Member]:
    """`packages` and every member they reach by a path dependency a consumer
    can build, whatever the target, the features or the host."""
    closure: dict[str, Member] = {}
    pending = [members[name] for name in packages]
    while pending:
        member = pending.pop()
        if member.name in closure:
            continue
        closure[member.name] = member
        for directory in member.path_dependencies:
            real = os.path.realpath(directory)
            found = [other for other in members.values() if os.path.realpath(other.directory) == real]
            if len(found) != 1:
                raise Refusal(
                    f"{member.name} depends on {directory} by path, which is "
                    + ("no member" if not found else "more than one member")
                    + " of the pinned workspace, so what it builds from cannot be read"
                )
            pending.append(found[0])
    return sorted(closure.values(), key=lambda member: member.name)


def _package_key(name: str) -> str:
    return fold(name.replace("_", "-"))


def refuse_other_declarations(tree: Path, entries: dict[str, str], closure: Sequence[Member]) -> None:
    """Refuses a tracked manifest other than its own that declares the name of a
    package of the closure: a Git consumer resolves a dependency by name over
    every manifest of the checkout and takes the highest version."""
    owners = {_package_key(member.name): member for member in closure}
    for name, mode in sorted(entries.items()):
        if fold(name.rsplit("/", 1)[-1]) != MANIFEST:
            continue
        path = tree / name
        if mode not in REGULAR_FILE_MODES:
            raise Refusal(f"manifest {name} is tracked as mode {mode}; what it declares is unread")
        text = path.read_text(encoding="utf-8", errors="replace")
        try:
            package = toml_loads(text).get("package")
            declared = package.get("name") if isinstance(package, dict) else None
            candidates = [declared] if isinstance(declared, str) else []
        except TOMLDecodeError:
            # Cargo may still read it (or a later Cargo may): any closure name
            # it spells counts as declared.
            candidates = [member.name for member in closure if member.name in text]
        for candidate in candidates:
            owner = owners.get(_package_key(candidate))
            if owner is not None and not os.path.samefile(path, owner.directory / "Cargo.toml"):
                raise Refusal(
                    f"{name} declares package {candidate!r}, which a Git consumer may "
                    f"resolve in place of {owner.directory.relative_to(tree)}"
                )


def enabled(table: dict[str, list[str]], chosen: set[str]) -> frozenset[str]:
    """`chosen` and the features of `table` that enabling it names, transitively.
    Only a bare feature name counts (`dep:x`, `x/f` and `x?/f` count nothing):
    this may stop short of what Cargo enables, never go past it, so two feature
    requests it tells apart may compile alike but none it merges differ."""
    result, pending = set(chosen), list(chosen)
    while pending:
        for name in table.get(pending.pop(), []):
            if name in table and name not in result:
                result.add(name)
                pending.append(name)
    return frozenset(result)


def consumer_feature_sets(
    cargo: str, consumer: Path, members: dict[str, Member], closure: Sequence[Member],
    packages: Sequence[str], metadata: Optional[dict[str, Any]] = None,
) -> list[tuple[str, list[str]]]:
    """Every (package, features) with which a build of `consumer` can compile a
    package of the closure: whichever members it selects, dev or not, with
    whatever features of theirs. Per package, every feature set lies between the
    floor (what every edge of the consumer's graph into it requests, as enabled
    under its own table: some edge is taken whenever it is built) and the
    ceiling (what the consumer's `--all-features` graph, dev and every target
    included, gives it); each subset of the difference is requested, and Cargo
    enables what each request implies. `metadata` is `consumer_metadata`'s."""
    if metadata is None:
        metadata = consumer_metadata(cargo, consumer)
    ours = {member.name for member in closure}
    names = {package["id"]: package["name"] for package in metadata.get("packages", [])}
    ceilings: dict[str, set[str]] = {}
    for node in (metadata.get("resolve") or {}).get("nodes", []):
        name = names.get(node["id"])
        if name not in ours:
            continue
        if name in ceilings:
            raise Refusal(f"{consumer} resolves {name!r} twice; which one is pinned is unknown")
        ceilings[name] = set(node.get("features", []))
    missing = sorted(set(packages) - set(ceilings))
    if missing:
        raise Refusal(f"{consumer} does not resolve {missing}")
    requests: dict[str, list[set[str]]] = {name: [] for name in ceilings}
    for package in metadata.get("packages", []):
        for dependency in package.get("dependencies", []):
            if dependency.get("name") in requests:
                requests[dependency["name"]].append(
                    set(dependency.get("features") or [])
                    | ({"default"} if dependency.get("uses_default_features", True) else set())
                )
    sets: list[tuple[str, list[str]]] = []
    for name in sorted(ceilings):
        table = members[name].features
        asked = set.intersection(*requests[name]) if requests[name] else set()
        floor = enabled(table, asked & set(table))
        free = sorted(ceilings[name] - floor)
        if 2 ** len(free) > MAX_FEATURE_SETS:
            raise Refusal(
                f"{consumer} can build {name} with up to {2 ** len(free)} feature sets "
                f"({', '.join(free)} free); the gate checks at most {MAX_FEATURE_SETS}"
            )
        seen: set[frozenset[str]] = set()
        for mask in range(1 << len(free)):
            chosen = enabled(
                table, floor | {feature for bit, feature in enumerate(free) if mask >> bit & 1}
            )
            if chosen not in seen:
                seen.add(chosen)
                sets.append((name, sorted(chosen)))
    if len(sets) > MAX_FEATURE_SETS:
        raise Refusal(
            f"{consumer} can build the closure with {len(sets)} feature sets; the gate checks "
            f"at most {MAX_FEATURE_SETS}"
        )
    return sets


def consumer_metadata(cargo: str, consumer: Path) -> dict[str, Any]:
    """`cargo metadata` of the consumer with every feature, dev and every
    target included: every package any build of it can compile."""
    return _cargo_json(
        cargo,
        [
            "metadata", "--format-version", "1", "--locked", "--offline", "--all-features",
            "--manifest-path", str(consumer),
        ],
        consumer.parent,
    )


# --- the consumer's builds -----------------------------------------------------

# The table of the reviewed list naming the builds of the consumer: lane ->
# the command it runs, after the `targo` executable.
CONSUMER_BUILDS = "consumer-builds"
# The Cargo commands a declared build may run; the gate asks Cargo for the
# unit graph of the same command (of `build` for `run`).
BUILD_COMMANDS = frozenset({"build", "check", "test", "run"})
# Cargo options that select what a build compiles, with a value and without;
# each is handed to Cargo as spelled.
SELECTING_WITH_VALUE = frozenset(
    {"-p", "--package", "--exclude", "--bin", "--test", "--example", "--bench", "-F", "--features",
     "--profile", "--target"}
)
SELECTING_FLAGS = frozenset(
    {"--workspace", "--all", "--lib", "--bins", "--tests", "--examples", "--benches",
     "--all-targets", "--doc", "--all-features", "--no-default-features", "--release", "-r"}
)
# Options that change where or how loudly Cargo builds, not what it compiles.
INERT_WITH_VALUE = frozenset({"--target-dir", "-j", "--jobs", "--message-format", "--color"})
INERT_FLAGS = frozenset(
    {"--locked", "--frozen", "--offline", "-q", "--quiet", "-v", "-vv", "--verbose",
     "--keep-going", "--timings", "--no-run", "--no-fail-fast", "--ignore-rust-version"}
)
# Options of `targo trust` that choose how it verifies, not what Cargo resolves.
TRUST_WITH_VALUE = frozenset({"--trust-profile", "--report-dir", "--format"})
# Cargo's `--config KEY=VALUE`: in a `targo trust` lane, a rustflags setting
# made only of Trust verification options (`trust_rustflags_config`).
CONFIG_OPTION = "--config"
TRUST_FLAG_PREFIX = "-Ztrust-"
TRUST_FLAGS = frozenset(
    {"--allow-l0-gaps", "--allow-memory-safe-panics", "--memory-safe", "--hardened", "--certify",
     "--json"}
)
# Where the resolver puts a unit: with the target's features, or with the
# host's (a build script's dependencies, a procedural macro and its own).
TARGET_SIDE, HOST_SIDE = "target", "host"
# What a unit of the closure's graph may be: a mode and target kinds the
# probe compiles alike (`check` and `build` read the same sources).
UNIT_MODES = {"build": "compile", "check": "compile", "run-custom-build": "run"}
LIBRARY_KINDS = frozenset({"lib", "rlib", "dylib", "cdylib", "staticlib", "proc-macro"})
CRATES_IO = frozenset(
    {"registry+https://github.com/rust-lang/crates.io-index", "sparse+https://index.crates.io/"}
)


@dataclass(frozen=True)
class Build:
    """One build of the consumer, as its lane runs it."""

    lane: str
    command: str
    # What Cargo is asked for the unit graph of: the command and every option
    # that selects what it compiles.
    arguments: tuple[str, ...]
    # Its `--target` values, which the probe reproducing it is checked for.
    targets: tuple[str, ...]
    # Whether it runs `targo trust`.
    trust: bool = False


def trust_rustflags_config(value: str) -> bool:
    """Whether `--config value` only adds Trust verification options to the
    compiler flags: one TOML assignment of `build.rustflags` or
    `target.<cfg>.rustflags` to a list of `-Ztrust-` flags, which the lane's
    verification reads as it reads `--certify` (see `parse_build`). Anything
    else -- a config file, another key, another flag (a `--cfg` changes what
    rustc compiles) -- is not modeled."""
    try:
        document = toml_loads(value)
    except (TOMLDecodeError, ValueError):
        return False
    if list(document) == ["build"] and isinstance(document["build"], dict):
        table = document["build"]
    elif (
        list(document) == ["target"]
        and isinstance(document["target"], dict)
        and len(document["target"]) == 1
        and isinstance(next(iter(document["target"].values())), dict)
    ):
        table = next(iter(document["target"].values()))
    else:
        return False
    flags = table.get("rustflags") if list(table) == ["rustflags"] else None
    return (
        isinstance(flags, list)
        and bool(flags)
        and all(isinstance(flag, str) and flag.startswith(TRUST_FLAG_PREFIX) for flag in flags)
    )


def parse_build(lane: str, command: str) -> Build:
    """The build `command` (what the lane runs after `targo`) asks Cargo for.
    Refuses a command whose options it cannot tell the effect of on what Cargo
    compiles: which feature sets that build gives the closure cannot be derived.
    `targo trust <command>` resolves as `targo --unverified <command>`: the
    lane chooses verification, which changes compiler flags (see
    `build_cone`) but not what Cargo resolves."""

    def refuse(why: str) -> Refusal:
        return Refusal(
            f"the build `{lane}` ({command!r}) {why}, so which feature sets it gives the "
            "pinned packages cannot be derived"
        )

    try:
        words = shlex.split(command)
    except ValueError as error:
        raise refuse(f"is no command line ({error})") from error
    if words[:1] == ["--unverified"]:
        trust = False
    elif words[:1] == ["trust"]:
        trust = True
    else:
        raise refuse("names no Targo lane (`--unverified <command>` or `trust <command>`)")
    if len(words) < 2 or words[1] not in BUILD_COMMANDS:
        raise refuse(f"runs no Cargo command of {sorted(BUILD_COMMANDS)}")
    subcommand, rest = words[1], words[2:]
    # `run` compiles what `build` of the same selection does, then runs it; Cargo
    # draws no unit graph for `run`.
    arguments, targets = ["build" if subcommand == "run" else subcommand], []
    index = 0
    while index < len(rest):
        word = rest[index]
        index += 1
        if word == "--":
            if subcommand in ("test", "run"):  # the harness's or the program's arguments
                break
            raise refuse(f"passes `--` to `{subcommand}`")
        if word.startswith("--"):
            option, attached, value = word.partition("=")
        elif word.startswith("-") and len(word) > 2 and word[:2] in ("-p", "-F", "-j"):
            option, attached, value = word[:2], "=", word[2:]
        else:
            option, attached, value = word, "", ""
        takes_value = option in (
            SELECTING_WITH_VALUE
            | INERT_WITH_VALUE
            | (TRUST_WITH_VALUE | {CONFIG_OPTION} if trust else frozenset())
        )
        if takes_value and not attached:
            if index >= len(rest):
                raise refuse(f"gives {option} no value")
            value = rest[index]
            index += 1
        elif attached and not takes_value:
            raise refuse(f"gives {option}, which takes none, a value")
        if option in SELECTING_WITH_VALUE:
            arguments += [option, value]
            if option == "--target":
                targets.append(value)
        elif option in SELECTING_FLAGS:
            arguments.append(option)
        elif option in INERT_WITH_VALUE or option in INERT_FLAGS:
            continue
        elif trust and (option in TRUST_WITH_VALUE or option in TRUST_FLAGS):
            continue
        elif trust and option == CONFIG_OPTION and trust_rustflags_config(value):
            continue
        else:
            raise refuse(f"passes {word!r}, whose effect on what Cargo compiles is not modeled")
    return Build(lane, command, tuple(arguments), tuple(targets), trust)


def load_consumer_builds(path: Path) -> list[Build]:
    """Every build of the consumer `path` declares, each as its lane runs it."""
    try:
        document = toml_loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, TOMLDecodeError) as error:
        raise Refusal(f"cannot read the exclusions {path}: {error}") from error
    table = document.get(CONSUMER_BUILDS, {})
    if not isinstance(table, dict):
        raise Refusal(f"{path}: [{CONSUMER_BUILDS}] is not a table of lane = command")
    builds = []
    for lane, command in table.items():
        if not isinstance(command, str) or not command.strip():
            raise Refusal(f"{path}: [{CONSUMER_BUILDS}] {lane!r} needs the command it runs")
        builds.append(parse_build(lane, command))
    return builds


def unit_graph(
    cargo: str, arguments: Sequence[str], manifest: Path, cwd: Path, locked: bool
) -> dict[str, Any]:
    """Cargo's unit graph of `arguments` for `manifest`: every unit the command
    compiles, each with the features its resolver gave it."""
    command = [
        cargo, "--unverified", *arguments, "--unit-graph", "-Z", "unstable-options", "--offline",
        *(["--locked"] if locked else []), "--manifest-path", str(manifest),
    ]
    try:
        run = subprocess.run(command, capture_output=True, cwd=cwd, check=False)
    except OSError as error:
        raise Refusal(f"{cargo} could not run: {error}") from error
    if run.returncode != 0:
        raise Refusal(
            f"Cargo cannot say what `{' '.join(arguments)}` compiles for {manifest}:\n"
            f"{run.stderr.decode(errors='replace').strip()[-3000:]}"
        )
    try:
        graph = json.loads(run.stdout)
        if graph["version"] != 1 or not isinstance(graph["units"], list):
            raise ValueError(f"version {graph['version']}")
        for unit in graph["units"]:
            for field in ("pkg_id", "target", "mode", "features", "dependencies", "profile"):
                if field not in unit:
                    raise ValueError(f"a unit has no {field}")
    except (ValueError, KeyError, TypeError) as error:
        raise Refusal(
            f"Cargo's unit graph for {manifest} is not one this gate reads: {error}"
        ) from error
    return graph


def _describe_unit(unit: dict[str, Any]) -> str:
    """A unit for messages: its package spec, target and features."""
    features = ",".join(sorted(unit["features"]))
    return f"{unit['pkg_id']} {unit['target']['name']} ({unit['mode']}) [{features}]"


def _unit_identities(units: list[dict[str, Any]], key: Any) -> list[str]:
    """Per unit, what it compiles from, as a digest: its package (`key` of its
    id), target, mode, features and platform, and the identities of the units
    it depends on. Two builds compile a unit alike when its identity is equal:
    the same sources under the same features, against the same dependencies."""
    identities: list[Optional[str]] = [None] * len(units)
    for start in range(len(units)):
        stack, visiting = [(start, False)], set()
        while stack:
            index, expanded = stack.pop()
            if identities[index] is not None:
                continue
            children = [dependency["index"] for dependency in units[index]["dependencies"]]
            if not expanded:
                if index in visiting:
                    raise Refusal(
                        f"Cargo's unit graph has a cycle through {_describe_unit(units[index])}"
                    )
                visiting.add(index)
                stack.append((index, True))
                stack.extend((child, False) for child in children if identities[child] is None)
                continue
            unit = units[index]
            identities[index] = hashlib.sha256(
                json.dumps(
                    [
                        key(unit["pkg_id"]), unit["target"]["name"], sorted(unit["target"]["kind"]),
                        UNIT_MODES.get(unit["mode"], unit["mode"]), sorted(unit["features"]),
                        unit.get("platform"), sorted(identities[child] for child in children),
                    ]
                ).encode()
            ).hexdigest()
    return [identity or "" for identity in identities]


def _cone(units: list[dict[str, Any]], roots: Sequence[int]) -> set[int]:
    """`roots` and every unit they depend on."""
    found: set[int] = set()
    pending = list(roots)
    while pending:
        index = pending.pop()
        if index not in found:
            found.add(index)
            pending.extend(dependency["index"] for dependency in units[index]["dependencies"])
    return found


def _unit_sides(units: list[dict[str, Any]], roots: Sequence[int]) -> list[set[str]]:
    """For each unit, whether the resolver gave it the target's features, the
    host's, or both (one unit serving both when they agree): a build script's
    dependencies, a procedural macro and what it depends on are the host's."""
    sides: list[set[str]] = [set() for _ in units]
    pending = [
        (root, HOST_SIDE if "proc-macro" in units[root]["target"]["kind"] else TARGET_SIDE)
        for root in roots
    ]
    while pending:
        index, side = pending.pop()
        if side in sides[index]:
            continue
        sides[index].add(side)
        unit = units[index]
        builds_a_script = "custom-build" in unit["target"]["kind"] and unit["mode"] == "build"
        for dependency in unit["dependencies"]:
            child = dependency["index"]
            host = builds_a_script or "proc-macro" in units[child]["target"]["kind"]
            pending.append((child, HOST_SIDE if host else side))
    return sides


@dataclass(frozen=True)
class BuildCone:
    """What one build of the consumer compiles for the closure: every unit of a
    closure package and every unit they depend on."""

    build: Build
    # identity -> the unit, described
    units: dict[str, str]
    # (package id, side) -> the features Cargo gave it there
    requests: dict[tuple[str, str], tuple[str, ...]]
    # The closure packages it compiles.
    compiled: frozenset[str]
    # The id under which it compiles each closure package -> its name.
    closure_ids: dict[str, str]


def build_cone(
    graph: dict[str, Any], closure_names: frozenset[str], packages: dict[str, dict[str, Any]],
    build: Build, members: frozenset[str] = frozenset(),
) -> BuildCone:
    """The units `build` compiles for the closure, from its unit graph.
    `members` are the package ids of the consumer's workspace: `targo trust`
    compiles every unit with debug assertions and overflow checks forced on,
    which the dev check compiles, and a member alone with `cfg(trust_verify)`
    as well (measured with seal 9192, `--release` included), so a trust build
    whose units of the closure's graph include a member is refused."""
    units = graph["units"]

    def refuse(why: str) -> Refusal:
        return Refusal(
            f"the build `{build.lane}` {why}; what it compiles for the pinned packages cannot "
            "be reproduced"
        )

    ids: dict[str, set[str]] = {}
    for unit in units:
        package = packages.get(unit["pkg_id"])
        if package is None:
            raise refuse(f"compiles {unit['pkg_id']}, which the consumer's metadata does not list")
        if package["name"] in closure_names:
            ids.setdefault(package["name"], set()).add(unit["pkg_id"])
    for name, found in sorted(ids.items()):
        if len(found) != 1:
            raise refuse(f"compiles {name!r} from {sorted(found)}; which one is pinned is unknown")
    closure_ids = {next(iter(found)): name for name, found in ids.items()}
    cone = _cone(units, [index for index, unit in enumerate(units) if unit["pkg_id"] in closure_ids])
    for index in sorted(cone):
        unit = units[index]
        kinds = set(unit["target"]["kind"])
        if unit["mode"] not in UNIT_MODES or not kinds <= LIBRARY_KINDS | {"custom-build"}:
            raise refuse(f"compiles {_describe_unit(unit)}, which the probe does not reproduce")
        if unit["profile"].get("panic") != "unwind":
            raise refuse(
                f"compiles {_describe_unit(unit)} with panic = {unit['profile'].get('panic')!r}; "
                "the gate checks with unwinding, so `cfg(panic)` would be unmodeled"
            )
        if build.trust and unit["pkg_id"] in members:
            raise refuse(
                f"runs `targo trust`, which compiles {_describe_unit(unit)}, a member of the "
                "consumer's workspace, with `cfg(trust_verify)`; the checks do not"
            )
    identities = _unit_identities(
        units, lambda pkg_id: f"closure:{closure_ids[pkg_id]}" if pkg_id in closure_ids else pkg_id
    )
    sides = _unit_sides(units, graph.get("roots") or [])
    requests: dict[tuple[str, str], tuple[str, ...]] = {}
    for index in sorted(cone):
        unit = units[index]
        if not LIBRARY_KINDS & set(unit["target"]["kind"]):
            continue
        if not sides[index]:
            raise refuse(f"compiles {_describe_unit(unit)}, which no root of its graph reaches")
        for side in sides[index]:
            features = tuple(sorted(unit["features"]))
            if requests.setdefault((unit["pkg_id"], side), features) != features:
                raise refuse(
                    f"compiles {unit['pkg_id']} for the {side} with features {list(features)} and "
                    f"{list(requests[(unit['pkg_id'], side)])}"
                )
    return BuildCone(
        build,
        {identities[index]: _describe_unit(units[index]) for index in cone},
        requests,
        frozenset(
            closure_ids[units[index]["pkg_id"]] for index in cone if units[index]["pkg_id"] in closure_ids
        ),
        closure_ids,
    )


def _toml_string(text: str) -> str:
    return json.dumps(text, ensure_ascii=True)


def _source_spec(package: dict[str, Any], directory: Optional[Path]) -> str:
    """How a manifest names `package` so that Cargo, with the consumer's lock,
    resolves the same package: by its exact version and its source (`directory`
    for a package of the closure, which is checked from the tree of the pin)."""
    version = f"version = {_toml_string('=' + package['version'])}"
    if directory is not None:
        return f"path = {_toml_string(str(directory))}, {version}"
    source = package.get("source")
    if source is None:
        return f"path = {_toml_string(str(Path(package['manifest_path']).parent))}, {version}"
    if source in CRATES_IO:
        return version
    if source.startswith("git+"):
        location = source[len("git+"):].split("#", 1)[0]
        url, _, query = location.partition("?")
        spec = f"git = {_toml_string(url)}"
        if query:
            key, equals, value = query.partition("=")
            if key not in ("rev", "branch", "tag") or not equals or "&" in value:
                raise Refusal(
                    f"{package['id']} comes from {source}, a Git reference this gate cannot spell"
                )
            spec += f", {key} = {_toml_string(urllib.parse.unquote(value))}"
        return f"{spec}, {version}"
    raise Refusal(f"{package['id']} comes from {source}, a source this gate cannot spell")


def reproducing_manifest(
    cone: BuildCone, packages: dict[str, dict[str, Any]], directories: dict[str, Path]
) -> str:
    """A crate that asks for every package `cone` compiles with exactly the
    features the build gave it, on the side it was compiled for: the target's
    as a dependency, the host's as a build dependency (of an empty build
    script). `directories` holds the closure's packages in the tree of the pin."""
    ids = sorted({pkg_id for pkg_id, _ in cone.requests})
    keys = {pkg_id: f"p{index}" for index, pkg_id in enumerate(ids)}
    tables: dict[str, list[str]] = {TARGET_SIDE: [], HOST_SIDE: []}
    for (pkg_id, side), features in sorted(cone.requests.items()):
        package = packages[pkg_id]
        spec = _source_spec(package, directories.get(pkg_id))
        listed = ", ".join(_toml_string(feature) for feature in features)
        tables[side].append(
            f"{keys[pkg_id]} = {{ package = {_toml_string(package['name'])}, {spec}, "
            f"default-features = false, features = [{listed}] }}"
        )
    return "\n".join(
        [
            "[package]",
            f"name = {_toml_string(PROBE)}",
            'version = "0.0.0"',
            'edition = "2021"',
            "publish = false",
            *(['build = "build.rs"'] if tables[HOST_SIDE] else []),
            "",
            "[lib]",
            'path = "lib.rs"',
            "",
            "[dependencies]",
            *tables[TARGET_SIDE],
            "",
            "[build-dependencies]",
            *tables[HOST_SIDE],
            "",
            "[workspace]",
            "",
        ]
    )


def probe_manifest(dependencies: dict[str, tuple[Path, Optional[list[str]]]]) -> str:
    """A crate that depends on each package by path with exactly `features`
    (`None`: its default features)."""
    lines = [
        "[package]",
        f"name = {_toml_string(PROBE)}",
        'version = "0.0.0"',
        'edition = "2021"',
        "publish = false",
        "",
        "[lib]",
        'path = "lib.rs"',
        "",
        "[dependencies]",
    ]
    for name, (directory, features) in sorted(dependencies.items()):
        chosen = ""
        if features is not None:
            listed = ", ".join(_toml_string(feature) for feature in features)
            chosen = f", default-features = false, features = [{listed}]"
        lines.append(f"{_toml_string(name)} = {{ path = {_toml_string(str(directory))}{chosen} }}")
    lines += ["", "[workspace]", ""]
    return "\n".join(lines)


def check_messages(
    cargo: str, manifest: Path, target: Path, cwd: Path, profile: Sequence[str],
    env: Optional[dict[str, str]] = None,
) -> list[dict[str, Any]]:
    """Cargo's JSON messages for a `check` of `manifest` (`profile`: its profile
    and target options); refuses a failed build."""
    command = [
        cargo, "--unverified", "check", "--offline", "--message-format=json", *profile,
        "--manifest-path", str(manifest), "--target-dir", str(target),
    ]
    try:
        run = subprocess.run(command, capture_output=True, cwd=cwd, check=False, env=env)
    except OSError as error:
        raise Refusal(f"{cargo} check could not run: {error}") from error
    messages = []
    rendered = []
    for line in run.stdout.decode(errors="replace").splitlines():
        if not line.startswith("{"):
            continue
        message = json.loads(line)
        messages.append(message)
        if message.get("reason") == "compiler-message":
            rendered.append((message.get("message") or {}).get("rendered") or "")
    if run.returncode != 0:
        detail = "".join(rendered).strip() or run.stderr.decode(errors="replace").strip()
        raise Refusal(
            f"checking the pinned packages {' '.join(profile) or '(dev)'} failed, so what they "
            f"read cannot be listed:\n{detail[-4000:]}"
        )
    return messages


def dep_info_files(message: dict[str, Any]) -> list[Path]:
    """The dep-info files rustc wrote for one compiler artifact, in the unit's
    `out/` directory (Cargo's build directory, `build_script_stdout`):
    `<crate>-<hash>.d` beside a `lib<crate>-<hash>.rmeta`, and for a build
    script, compiled without `-C extra-filename`, `build_script_build.d` beside
    its executable `build_script_build`."""
    crate = message["target"]["name"].replace("-", "_")
    found = set()
    for filename in message.get("filenames") or []:
        path = Path(filename)
        stem = path.name.split(".", 1)[0] if path.suffix else path.name
        if stem.startswith("lib" + crate + "-"):
            stem = stem[3:]
        if stem.startswith(crate + "-") or (
            stem == crate and "custom-build" in message["target"].get("kind", [])
        ):
            candidates = [path.with_name(stem + ".d")]
        else:
            continue
        found.update(candidate for candidate in candidates if candidate.is_file())
    if not found:
        raise Refusal(
            f"no dep-info for {message['target']['name']} of {message['package_id']} "
            f"beside {message.get('filenames')}; what it compiled cannot be listed"
        )
    return sorted(found)


def _escape_prerequisite(name: str) -> str:
    """How rustc spells a prerequisite in dep-info: it escapes a space, nothing
    else (rustc_interface::passes::escape_dep_filename)."""
    return name.replace(" ", "\\ ")


def dep_info_paths(dep_info: Path) -> list[str]:
    """Every prerequisite of a dep-info file, read exactly as rustc writes one
    (rustc_interface::passes::write_out_deps): per output a rule `<output>:
    <prerequisites>` and a blank line, then a line `<prerequisite>:` per
    prerequisite, then, when the crate reads the environment, a blank line and
    `# env-dep:` lines, then any `# checksum:` lines. Only a space is escaped, so
    a rule alone has no unique reading once a name ends in a backslash (`x\\`
    then a separator reads as `x ` joined to the next name) or holds a newline;
    the prerequisite lines are read instead, and every rule must be exactly
    those names, escaped and joined. Refuses anything else, and a file with no
    rule for itself: what it names cannot be listed."""
    try:
        text = dep_info.read_bytes().decode("utf-8")
    except (OSError, UnicodeDecodeError) as error:
        raise Refusal(f"cannot read the dep-info {dep_info}: {error}") from error

    def refuse(why: str) -> Refusal:
        return Refusal(f"{dep_info} is not dep-info as rustc writes it ({why}); what it names cannot be listed")

    if not text.endswith("\n"):
        raise refuse("it does not end in a newline")
    lines = text[:-1].split("\n")
    end = len(lines)
    while end and lines[end - 1].startswith("# checksum:"):
        end -= 1
    comments = end
    while end and lines[end - 1].startswith("# env-dep:"):
        end -= 1
    if end < comments:
        if not end or lines[end - 1] != "":
            raise refuse("no blank line before its env-dep comments")
        end -= 1
    start = end
    while start and lines[start - 1] != "":
        start -= 1
    escaped = []
    for line in lines[start:end]:
        if not line.endswith(":") or len(line) == 1:
            raise refuse(f"prerequisite line {line!r} is no `<path>:`")
        name = line[:-1].replace("\\ ", " ")
        if _escape_prerequisite(name) != line[:-1]:
            raise refuse(f"prerequisite line {line!r} holds an unescaped space")
        escaped.append(line[:-1])
    rules = lines[:start]
    if not escaped or not rules or len(rules) % 2 or any(rules[1::2]):
        raise refuse("no prerequisites, or rules that are not each followed by one blank line")
    tail = ": " + " ".join(escaped)
    outputs = []
    for rule in rules[0::2]:
        if not rule.endswith(tail) or len(rule) == len(tail):
            raise refuse(f"rule {rule[:200]!r} does not list exactly its prerequisite lines")
        outputs.append(rule[: -len(tail)])
    if not any(os.path.realpath(output) == os.path.realpath(dep_info) for output in outputs):
        raise refuse("no rule names the file itself")
    return [name.replace("\\ ", " ") for name in escaped]


# What Rust's `str::trim` strips (char::is_whitespace); Python's `str.strip()`
# also strips U+001C..U+001F, which Rust keeps.
RUST_WHITESPACE = "".join(
    chr(code)
    for code in (
        0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x20, 0x85, 0xA0, 0x1680, *range(0x2000, 0x200B),
        0x2028, 0x2029, 0x202F, 0x205F, 0x3000,
    )
)
# The keys Cargo reads as directives after the old `cargo:` prefix; any other
# `cargo:KEY=VALUE` is metadata (cargo::core::compiler::custom_build).
RESERVED_DIRECTIVES = (
    "rustc-flags", "rustc-link-lib", "rustc-link-search", "rustc-link-arg-cdylib",
    "rustc-cdylib-link-arg", "rustc-link-arg-bins", "rustc-link-arg-bin", "rustc-link-arg-tests",
    "rustc-link-arg-benches", "rustc-link-arg-examples", "rustc-link-arg", "rustc-cfg",
    "rustc-check-cfg", "rustc-env", "warning", "error", "rerun-if-changed", "rerun-if-env-changed",
)
# Directives whose value goes to the linker as an argument: the files it reads
# through one cannot be listed.
LINK_ARGUMENTS = frozenset(
    key for key in RESERVED_DIRECTIVES if key.startswith("rustc-link-arg") or key == "rustc-cdylib-link-arg"
)


def build_script_directives(output: Path) -> list[tuple[str, str]]:
    """(key, value) of every directive a build script printed, read as Cargo
    reads its output (BuildOutput::parse): a line that is not UTF-8 is skipped,
    one is trimmed, then `cargo::KEY=VALUE` is a directive and `cargo:KEY=VALUE`
    one when KEY is reserved, else metadata (key `metadata`, value `KEY=VALUE`)."""
    try:
        data = output.read_bytes()
    except OSError as error:
        raise Refusal(f"cannot read the build script output {output}: {error}") from error
    directives = []
    for raw in data.split(b"\n"):
        try:
            line = raw.decode("utf-8").strip(RUST_WHITESPACE)
        except UnicodeDecodeError:
            continue
        if line.startswith("cargo::"):
            key, separator, value = line[len("cargo::") :].partition("=")
            if not separator:
                raise Refusal(f"{output}: {line!r} is no directive Cargo accepts")
        elif line.startswith("cargo:"):
            body = line[len("cargo:") :]
            if any(body.startswith(reserved + "=") for reserved in RESERVED_DIRECTIVES):
                key, _, value = body.partition("=")
            else:
                key, value = "metadata", body
        else:
            continue
        directives.append((key, value.rstrip(RUST_WHITESPACE)))
    return directives


def rustc_flags(value: str, output: Path) -> tuple[list[str], list[str]]:
    """The library paths and libraries a `rustc-flags` directive names, split as
    Cargo splits it: whitespace-separated `-L`/`-l`, the value attached or next."""
    words = [word for word in value.split() if word]
    paths: list[str] = []
    libraries: list[str] = []
    while words:
        word = words.pop(0)
        if word[:2] not in ("-L", "-l"):
            raise Refusal(f"{output}: rustc-flags {value!r} holds {word!r}, which Cargo refuses")
        argument = word[2:] or (words.pop(0) if words else "")
        if not argument:
            raise Refusal(f"{output}: rustc-flags {value!r} has {word} without a value")
        (paths if word[:2] == "-L" else libraries).append(argument)
    return paths, libraries


def search_directory(value: str) -> str:
    """The directory of a `-L [KIND=]PATH` value, split as rustc splits it."""
    for kind in ("native=", "crate=", "dependency=", "framework=", "all="):
        if value.startswith(kind):
            return value[len(kind) :]
    return value


def build_script_stdout(out_dir: Path) -> Path:
    """What a build script run whose OUT_DIR is `out_dir` printed, the output
    Cargo reads. Cargo's build directory (the tuple's Trust 0.12 Cargo) gives
    each unit one directory `build/<package>/<hash>/`: its outputs in `out/`,
    its fingerprint in `fingerprint/`, and for a build script run what the
    script printed in `run/stdout`. The layout before it (`build/<package>-<hash>/
    output`, fingerprints under `.fingerprint/`) is not read: a file missing
    here is refused, never looked for elsewhere."""
    return out_dir.parent / "run" / "stdout"


def cargo_rerun_if_changed(out_dir: Path) -> list[str]:
    """The `rerun-if-changed` paths Cargo recorded for one build script run, from
    its fingerprint (`local`: RerunIfChanged, RerunIfEnvChanged, Precalculated)
    in the run's unit directory (`build_script_stdout`)."""
    run = out_dir.parent
    found = sorted((run / "fingerprint").glob("run-build-script-*.json"))
    if len(found) != 1:
        raise Refusal(f"Cargo recorded {len(found)} fingerprints for the build script run {run}")
    try:
        local = json.loads(found[0].read_text(encoding="utf-8"))["local"]
        paths = []
        for entry in local:
            ((kind, value),) = entry.items()
            if kind == "RerunIfChanged":
                paths.extend(str(path) for path in value["paths"])
            elif kind not in ("RerunIfEnvChanged", "Precalculated"):
                raise ValueError(f"unknown entry {kind}")
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as error:
        raise Refusal(f"cannot read what Cargo watches for {run} from {found[0]}: {error}") from error
    return paths


def _registry_root() -> Path:
    home = os.environ.get("CARGO_HOME") or str(Path.home() / ".cargo")
    return Path(os.path.realpath(Path(home) / "registry" / "src"))


class Reads:
    """What the pinned packages read, as repository-relative paths (a file or
    a directory, everything beneath it), each with who reads it."""

    def __init__(self, tree: Path) -> None:
        self.tree = tree
        self.registry = _registry_root()
        self.paths: dict[str, str] = {}

    def add(self, reader: str, path: Path) -> None:
        """`path` as spelled (lexically normalized) and as the OS opens it."""
        if not path.is_absolute():
            raise Refusal(f"{reader} names the relative path {path}; its base is unknown")
        for candidate in (Path(os.path.normpath(path)), Path(os.path.realpath(path))):
            try:
                relative = candidate.relative_to(self.tree).as_posix()
            except ValueError:
                try:
                    candidate.relative_to(self.registry)
                except ValueError:
                    raise Refusal(
                        f"{reader} reads {candidate}, which is neither in the tree of the pin "
                        "nor a registry source: it is not pinned content"
                    ) from None
                continue
            self.paths.setdefault(relative or ".", reader)

    def refuse(self, excluded: Sequence[tuple[str, Exclusion]]) -> None:
        """Refuses when an excluded path is, or lies beneath, a read; names the
        nearest read above it."""
        found = []
        for path, exclusion in excluded:
            above = [read for read in self.paths if _under(fold(path), fold(read))]
            if above:
                read = max(above, key=lambda each: (len(each), each))
                found.append(
                    f"{exclusion.pattern} covers {path}, and {self.paths[read]} reads {read}"
                )
        if found:
            raise Refusal(
                "an exclusion covers what the pinned packages read; take it off "
                "scripts/pin-exclusions.toml:\n  " + "\n  ".join(found)
            )


def module_directory(path: Path) -> Path:
    """Where rustc looks for the module files declared beside the file it read
    as `path` (`mod m;` in it, or the other candidate of `path` itself): its
    directory, or the one holding that for a `mod.rs` (`m/mod.rs` and `m.rs`
    are the two candidates of one module)."""
    return path.parent.parent if fold(path.name) == MODULE_FILE else path.parent


# A directive with which the assembler reads a file, spelled with the string
# that names the file. LLVM's assembler, which rustc runs at codegen on every
# `asm!`, `global_asm!` and `naked_asm!` template, matches directive names in any
# ASCII case and takes the name only as a `"` string, which Rust source spells
# `\"` inside a literal (or `"` at a literal's end, a raw string or a .s file);
# blanks between may be spelled `\t` or a line continuation. Rust's `x.include`
# (a field) or `x.include(..)` is never followed by a quote, blanks aside.
ASSEMBLER_FILE_DIRECTIVE = re.compile(
    rb'\.(incbin|include)(?:[ \t]|\\t|\\\r?\n[ \t\r\n]*)*\\?"', re.IGNORECASE
)


def _directive_refusal(data: bytes, subject: str) -> Optional[Refusal]:
    """The refusal for `data` (what `subject` names) when it spells an
    assembler directive that reads a file, or None."""
    found = ASSEMBLER_FILE_DIRECTIVE.search(data)
    if found is None:
        return None
    line = data.count(b"\n", 0, found.start()) + 1
    return Refusal(
        f"{subject} spells the assembler directive '.{found.group(1).decode()}' on line {line}: "
        "the assembler reads the file it names at codegen, which `check` never reaches and "
        "no dep-info names, so what it reads cannot be listed"
    )


def refuse_assembler_file_directive(path: Path, reader: str) -> None:
    """Refuses when the file `path`, which `reader` compiles, spells an
    assembler directive that reads a file: the assembler reads it when rustc
    generates the code of a library, which `check` never does and no dep-info
    names."""
    if not path.is_absolute():
        raise Refusal(f"{reader} names the relative path {path}; its base is unknown")
    try:
        data = path.read_bytes()
    except OSError as error:
        raise Refusal(f"cannot read {path}, which {reader} compiles: {error}") from error
    refusal = _directive_refusal(data, f"{path}, which {reader} compiles,")
    if refusal is not None:
        raise refusal


# --- what a build script can hand the C preprocessor or an assembler -----------

# A directive with which the C preprocessor or an assembler that a build script
# runs (`cc` on a .c or .S file, `as`, NASM) reads another file: the GNU and
# LLVM assemblers' `.incbin` and `.include` (directive names in any ASCII
# case), NASM's `incbin` and `%include`, and the preprocessor's `#include`,
# `#include_next`, `#import` and `#embed`.
INPUT_DIRECTIVE = re.compile(
    rb"(?P<asm>(?i:\.incbin|\.include|%include|(?<![A-Za-z0-9_$.%])incbin))(?![A-Za-z0-9_$.])"
    rb"|(?P<cpp>#[ \t]*(?:include_next|include|import|embed))(?![A-Za-z0-9_$])"
)
# What may end the statement a directive's quoted name closes, blanks aside: a
# line, a `;` or `,` (`.incbin "f", skip, count`), a comment (`//`, `/*`, `#`,
# `@`), or the Rust string literal holding the template (`"`, a `\\n` escape).
NAME_FOLLOWERS = b"\n\r;,\"/#@"
# What ends the statement a directive starts, blanks aside: a line, a `;`, a
# label's `:`, a string literal's opening quote, or a `\\n` escape in one.
STATEMENT_ENDS = b"\n\r;:\"'`"
# What no file name a directive spells as one literal holds: an escape or a
# line break (the literal is not the name), and the marks of a placeholder a
# program fills (`{}`, `$`, `@`, `%`).
PLACEHOLDER_BYTES = b'\\\n\r\0"{}$@%'


def _skip_blanks(data: bytes, position: int) -> int:
    """Past the blanks at `position`: spaces, tabs, a `\\t` escape, and a line
    continuation (a backslash ending the line) with the blanks after it."""
    while position < len(data):
        if data[position] in b" \t":
            position += 1
        elif data.startswith(b"\\t", position):
            position += 2
        elif data.startswith(b"\\\n", position) or data.startswith(b"\\\r\n", position):
            position = data.index(b"\n", position) + 1
            while position < len(data) and data[position] in b" \t\r\n":
                position += 1
        else:
            break
    return position


def _starts_statement(data: bytes, position: int) -> bool:
    """Whether what begins at `position` begins a statement: nothing but blanks
    lie between it and the start of the file, a line, a `;`, a label, or a
    string literal (or a `\\n` escape in one) that holds it."""
    while position:
        if data[position - 1] in b" \t":
            position -= 1
        elif data[max(position - 2, 0) : position] == b"\\t":
            position -= 2
        else:
            break
    return (
        position == 0
        or data[position - 1] in STATEMENT_ENDS
        or data[max(position - 2, 0) : position] in (b"\\n", b"\\r")
    )


def _literal_name(data: bytes, position: int, preprocessor: bool) -> Optional[bytes]:
    """The file name a directive's operand at `position` spells as one string
    literal (`"f"`, `\\"f\\"` inside a Rust literal, `<f>` for the
    preprocessor), or None: the name is then made by something else (a macro, a
    `-D` define, a program filling a template, literals put together). A name
    holding a template's placeholder (`{blob}`, `$BLOB`, `$(X)`, CMake's and
    autoconf's `@BLOB@`, printf's `%s`, a batch file's `%BLOB%`) is one a
    program fills."""
    if data.startswith(b'\\"', position):
        start, close, escaped = position + 2, b'"', True
    elif data.startswith(b'"', position):
        start, close, escaped = position + 1, b'"', False
    elif preprocessor and data.startswith(b"<", position):
        start, close, escaped = position + 1, b">", False
    else:
        return None
    end = data.find(close, start)
    if end < 0:
        return None
    name = data[start:end]
    if escaped:
        if not name.endswith(b"\\"):  # the Rust literal ends before the name does
            return None
        name = name[:-1]
    if not name or any(byte in name for byte in PLACEHOLDER_BYTES):
        return None
    if not preprocessor:  # an assembler statement ends after the name
        after = _skip_blanks(data, end + 1)
        if (
            after < len(data)
            and data[after] not in NAME_FOLLOWERS
            and data[after : after + 2] not in (b"\\n", b"\\r")
        ):
            return None
    return name


def _name_parts(name: str) -> list[str]:
    """The components of a directive's file name that every directory it may be
    looked for in keeps: those after its last `..` (`.` and empty ones dropped)."""
    parts = [part for part in name.split("/") if part not in ("", ".")]
    while ".." in parts:
        parts = parts[parts.index("..") + 1 :]
    return parts


def _ends_alike(path: str, parts: Sequence[str]) -> bool:
    """Whether the repository-relative `path` and a name's `parts` agree on their
    last components, as many as the shorter has (folded): some directory puts
    the name at `path`."""
    mine = [fold(part) for part in path.split("/")]
    theirs = [fold(part) for part in parts]
    count = min(len(mine), len(theirs))
    return mine[-count:] == theirs[-count:]


# --- what rustc includes, under whatever cfg ------------------------------------

# One token of Rust source as rustc's lexer reads it; whitespace and comments
# are skipped, a nested block comment by hand. A raw string's end is found by
# hand too; a character literal is tried before a lifetime, so `'"'` opens no
# string.
RUST_TOKEN = re.compile(
    r"""(?P<blank>\s+)
    |(?P<line>//[^\n]*)
    |(?P<block>/\*)
    |(?P<raw>[bc]?r(?P<hashes>\#*)")
    |(?P<string>[bc]?"(?:[^"\\]|\\.)*")
    |(?P<char>b?'(?:[^'\\\n]|\\(?:u\{[0-9A-Fa-f_]*\}|x[0-9A-Fa-f]{2}|.))')
    |(?P<lifetime>'(?:r\#)?[^\W\d]\w*)
    |(?P<ident>(?:r\#)?[^\W\d]\w*)
    |(?P<number>\d[\w.]*)
    |(?P<punct>.)""",
    re.X | re.S,
)
RUST_ESCAPE = re.compile(r"\\(?:u\{([0-9A-Fa-f_]+)\}|x([0-9A-Fa-f]{2})|\n\s*|(.))", re.S)
RUST_ESCAPED = {"n": "\n", "t": "\t", "r": "\r", "0": "\0", "\\": "\\", "'": "'", '"': '"'}
# The macros with which rustc reads a file at compile time, relative to the
# file that invokes one; `include!` compiles what it reads as Rust.
RUST_INCLUDES = frozenset({"include_str", "include_bytes", "include"})


def _rust_unescape(body: str) -> str:
    def one(match: re.Match) -> str:
        code, byte, other = match.group(1), match.group(2), match.group(3)
        if code is not None:
            return chr(int(code.replace("_", ""), 16))
        if byte is not None:
            return chr(int(byte, 16))
        return RUST_ESCAPED.get(other, "") if other is not None else ""

    return RUST_ESCAPE.sub(one, body)


def rust_tokens(text: str) -> list[tuple[str, str, int]]:
    """(kind, text, offset) of every token of `text`, a string literal's text
    its value; comments and whitespace are left out."""
    tokens = []
    position = 0
    while position < len(text):
        match = RUST_TOKEN.match(text, position)
        assert match is not None  # `punct` takes any one character
        kind = match.lastgroup if match.lastgroup != "hashes" else "raw"
        if kind == "block":
            depth, position = 1, match.end()
            while position < len(text) and depth:
                if text.startswith("/*", position):
                    depth, position = depth + 1, position + 2
                elif text.startswith("*/", position):
                    depth, position = depth - 1, position + 2
                else:
                    position += 1
            continue
        if kind == "raw":
            closing = '"' + match.group("hashes")
            end = text.find(closing, match.end())
            if end < 0:
                break
            tokens.append(("string", text[match.end() : end], match.start()))
            position = end + len(closing)
            continue
        if kind == "string":
            body = match.group()
            tokens.append(("string", _rust_unescape(body[body.index('"') + 1 : -1]), match.start()))
        elif kind not in ("blank", "line"):
            tokens.append((kind, match.group(), match.start()))
        position = match.end()
    return tokens


@dataclass(frozen=True)
class RustRead:
    """One file the Rust source of a file names for rustc to read at compile
    time, under whatever `cfg`."""

    line: int
    what: str  # `include_str!`, `include_bytes!`, `include!` or `path attribute`
    # The path as its string literals spell it; None when none spells it.
    spelled: Optional[str]
    # The path rustc opens, joined but not normalized: a `..` after a symbolic
    # link climbs from where the link points, as the OS resolves it.
    joined: Optional[Path]
    # Whether it lies in the body of a macro definition: rustc resolves an
    # include there from the file of the macro's call site, not this one.
    in_macro: bool = False


def _macro_bodies(tokens: Sequence[tuple[str, str, int]]) -> list[tuple[int, int]]:
    """The token ranges of every macro definition's body (`macro_rules! m {..}`,
    `macro m(..) {..}`)."""
    bodies = []
    for index, (kind, value, _) in enumerate(tokens):
        if kind != "ident" or value not in ("macro_rules", "macro"):
            continue
        cursor = index + 1
        if value == "macro_rules":
            if cursor >= len(tokens) or tokens[cursor][:2] != ("punct", "!"):
                continue
            cursor += 1
        if cursor >= len(tokens) or tokens[cursor][0] != "ident":
            continue
        cursor += 1
        # The delimited groups that follow: one for macro_rules, the arguments
        # and the body for `macro`.
        while cursor < len(tokens) and tokens[cursor][:2] in (("punct", "{"), ("punct", "("), ("punct", "[")):
            opening = tokens[cursor][1]
            closing = {"{": "}", "(": ")", "[": "]"}[opening]
            depth, end = 1, cursor + 1
            while end < len(tokens) and depth:
                if tokens[end][:2] == ("punct", opening):
                    depth += 1
                elif tokens[end][:2] == ("punct", closing):
                    depth -= 1
                end += 1
            bodies.append((cursor, end))
            cursor = end
            if value == "macro_rules":
                break
    return bodies


def rust_reads(text: str, file: Path, package: Path) -> list[RustRead]:
    """Every file the Rust source `text` of `file`, a file of the package in
    `package`, names for rustc to read at compile time under whatever `cfg`:
    what `include_str!`, `include_bytes!` or `include!` names with one string
    literal or with literals `concat!` puts together (from the directory of
    `file`, or from the package's after `env!("CARGO_MANIFEST_DIR")`), and the
    literal of a `path` attribute (`#[path = ..]`, `#[cfg_attr(.., path =
    ..)]`, from the directory of `file`). An include whose path no literal
    spells (a macro's argument, another `env!`) is listed with no path, one
    from `OUT_DIR` aside: the package's build script writes it there."""
    tokens = rust_tokens(text)
    bodies = _macro_bodies(tokens)
    found = []

    def kinds(start: int, *expected: str) -> bool:
        """Whether the tokens from `start` on are `expected`: a string literal,
        an identifier, or that punctuation."""
        for index, want in enumerate(expected):
            if start + index >= len(tokens):
                return False
            kind, value, _ = tokens[start + index]
            if (kind != want) if want in ("string", "ident") else (kind, value) != ("punct", want):
                return False
        return True

    def at(offset: int) -> int:
        return text.count("\n", 0, offset) + 1

    def in_macro(index: int) -> bool:
        return any(start < index < end for start, end in bodies)

    for index, (kind, value, offset) in enumerate(tokens):
        if kind == "ident" and value in RUST_INCLUDES and (
            kinds(index + 1, "!", "(") or kinds(index + 1, "!", "[") or kinds(index + 1, "!", "{")
        ):
            what, first = f"{value}!", index + 3
            if kinds(first, "string"):
                spelled = tokens[first][1]
                found.append(RustRead(at(offset), what, spelled, file.parent / spelled, in_macro(index)))
                continue
            if kinds(first, "ident", "!", "(") and tokens[first][1] == "concat":
                cursor, base = first + 3, file.parent
                if kinds(cursor, "ident", "!", "(", "string", ")") and tokens[cursor][1] == "env":
                    variable = tokens[cursor + 3][1]
                    if variable == "OUT_DIR":
                        continue  # what the package's build script wrote
                    if variable != "CARGO_MANIFEST_DIR" or not kinds(cursor + 5, ","):
                        found.append(RustRead(at(offset), what, None, None, in_macro(index)))
                        continue
                    base, cursor = None, cursor + 6
                parts = []
                while kinds(cursor, "string"):
                    parts.append(tokens[cursor][1])
                    cursor += 1
                    if kinds(cursor, ","):
                        cursor += 1
                if parts and kinds(cursor, ")"):
                    spelled = "".join(parts)
                    joined = Path(f"{package}{spelled}") if base is None else base / spelled
                    found.append(RustRead(at(offset), what, spelled, joined, in_macro(index)))
                    continue
            found.append(RustRead(at(offset), what, None, None, in_macro(index)))
        elif kind == "punct" and value == "#":
            cursor = index + 1
            if kinds(cursor, "!"):
                cursor += 1
            if not kinds(cursor, "["):
                continue
            depth, cursor = 1, cursor + 1
            while cursor < len(tokens) and depth:
                token = tokens[cursor]
                if token[0] == "punct" and token[1] in "[]":
                    depth += 1 if token[1] == "[" else -1
                elif token[:2] == ("ident", "path") and kinds(cursor + 1, "=", "string"):
                    spelled = tokens[cursor + 2][1]
                    found.append(
                        RustRead(at(token[2]), "path attribute", spelled, file.parent / spelled, in_macro(index))
                    )
                cursor += 1
    return found


def rust_modules(text: str) -> list[tuple[int, str]]:
    """(line, name) of every `mod name;` the Rust source `text` declares, under
    whatever `cfg`, whose module file rustc looks for by its name: all but one
    carrying a plain `#[path = ..]` attribute (a `cfg_attr` one may not apply
    on a host, which then looks by name)."""
    tokens = rust_tokens(text)
    found = []
    plain_path = False  # the item being read carries `#[path = ..]`
    for index, (kind, value, offset) in enumerate(tokens):
        if kind == "punct" and value in ";{}":
            plain_path = False
        elif (kind, value) == ("punct", "#") and index + 3 < len(tokens) and (
            tokens[index + 1][:2] == ("punct", "[") and tokens[index + 2][:2] == ("ident", "path")
            and tokens[index + 3][:2] == ("punct", "=")
        ):
            plain_path = True
        elif (
            (kind, value) == ("ident", "mod") and index + 2 < len(tokens)
            and tokens[index + 1][0] == "ident" and tokens[index + 2][:2] == ("punct", ";")
        ):
            if not plain_path:
                found.append((text.count("\n", 0, offset) + 1, tokens[index + 1][1].removeprefix("r#")))
    return found


def module_candidates(path: Path, name: str) -> list[Path]:
    """Where rustc may look for the file of `mod name;` declared in `path`:
    beside it (a `mod.rs`, a crate root or a file a `path` attribute names) or
    beneath its stem (any other file). All are read."""
    stem = path.parent / path.stem
    return [
        Path(os.path.normpath(candidate)) for candidate in (
            path.parent / f"{name}.rs", path.parent / name / MODULE_FILE,
            stem / f"{name}.rs", stem / name / MODULE_FILE,
        )
    ]


class BuildInputs:
    """What the files of the pin name for a tool to read, read from the files
    themselves, so whichever host or configuration builds them.

    The C preprocessor and the assemblers. A build script can hand any file of
    the tree to one (`cc ../../asm/blob.S`), watched or not, on a host the
    checks do not build for, so every tracked regular file is read but the
    excluded changes themselves. A literal name is looked for in a search
    directory the build script chooses (the working directory it gives the
    tool, an `-I`), so it reads every path that some directory puts it at:
    every path agreeing with its components after its last `..`. A directive
    at the start of a statement whose name is no one string literal is
    refused: something else (a macro, a `-D` define, a template a program
    fills) makes the name. A file under a reviewed exclusion is reviewed as one
    no build reads (a shell comment there spells `# import`): its literal
    names are read, and one that is no literal is not refused, unless a build
    is seen to read it after all (`rescan_reviewed`).

    rustc. It compiles a Rust file of a closure package that no test, bench,
    example or binary target alone holds under whatever `cfg` a host gives it,
    and the checks compile this host's. So in each such file, in every Rust
    file one of those includes and in every module file one declares, what
    `include_str!`, `include_bytes!`, `include!` or a `path` attribute names
    with string literals is read, as rustc resolves it (`rust_reads`,
    `rust_modules`), and an include no literal spells is refused.

    Build scripts. One may hand a file to a tool, copy, read or test it only
    on another host: what the string literals of its files name as a path from
    its package's directory is read (`scan_build_scripts`)."""

    def __init__(
        self, tree: Path, entries: dict[str, str], excluded: Sequence[tuple[str, Exclusion]],
        exclusions: Sequence[Exclusion], reads: Reads,
    ) -> None:
        self.tree = tree
        self.entries = entries
        self.reads = reads
        self.changes = frozenset(path for path, _ in excluded)
        self.exclusions = list(exclusions)
        self.excluded: dict[str, list[str]] = {}
        for path, _ in excluded:
            self.excluded.setdefault(fold(path.rsplit("/", 1)[-1]), []).append(path)
        self.tracked: dict[str, list[str]] = {}
        for path, mode in entries.items():
            if mode in REGULAR_FILE_MODES and path not in self.changes:
                self.tracked.setdefault(fold(path.rsplit("/", 1)[-1]), []).append(path)
        # Files under a reviewed exclusion read leniently (path -> the exclusion),
        # and the tracked files a literal name of a strictly read file reaches.
        self.lenient: dict[str, str] = {}
        self.reached: set[str] = set()

    def _spelled(self, path: Path) -> str:
        try:
            return Path(os.path.normpath(path)).relative_to(self.tree).as_posix()
        except ValueError:
            return str(path)

    def scan_tree(self, closure: Sequence["Member"]) -> None:
        """Reads what every tracked regular file but the excluded changes names
        for the C preprocessor or an assembler; refuses a name no literal
        spells, outside the reviewed exclusions."""
        packages = [(self._spelled(member.directory), member.name) for member in closure]
        for name, mode in sorted(self.entries.items()):
            if mode not in REGULAR_FILE_MODES or name in self.changes:
                continue
            owner = next((package for directory, package in packages if _under(name, directory)), None)
            reviewed = next((exclusion for exclusion in self.exclusions if exclusion.covers(name)), None)
            if owner is not None:
                why = f"a file of package {owner}"
            elif reviewed is not None:
                why = f"a tracked file under exclusion {reviewed.pattern}"
            else:
                why = "a tracked file a build script can hand the tool"
            try:
                data = (self.tree / name).read_bytes()
            except OSError as error:
                raise Refusal(f"cannot read {name} ({why}): {error}") from error
            strict = owner is not None or reviewed is None
            if not strict:
                self.lenient[name] = reviewed.pattern
            self._names(data, self.tree / name, why, strict=strict)
        self.rescan_reviewed()

    def rescan_reviewed(self) -> None:
        """Reads strictly each file under a reviewed exclusion that a build does
        read after all: one a literal name of a strictly read file reaches, or
        one under a path the gate recorded as read (a symbolic link's target, a
        watched path, a Rust include). The review that no build reads it does
        not hold for it."""
        while True:
            read = [
                name for name in sorted(self.lenient)
                if name in self.reached or any(_under(name, path) for path in self.reads.paths)
            ]
            if not read:
                return
            for name in read:
                pattern = self.lenient.pop(name)
                try:
                    data = (self.tree / name).read_bytes()
                except OSError as error:
                    raise Refusal(f"cannot read {name}: {error}") from error
                self._names(
                    data, self.tree / name,
                    f"a tracked file under exclusion {pattern} that a build reads", strict=True,
                )

    def _names(self, data: bytes, path: Path, why: str, strict: bool) -> None:
        subject = f"{self._spelled(path)} ({why})"
        for match in INPUT_DIRECTIVE.finditer(data):
            token = match.group().decode("utf-8", "replace")
            line = data.count(b"\n", 0, match.start()) + 1
            operand = _skip_blanks(data, match.end())
            name = _literal_name(data, operand, match.group("cpp") is not None)
            if name is None:
                # `.include(` is a method call; a directive's operand follows a blank.
                if strict and operand > match.end() and operand < len(data) and (
                    data[operand] not in b"\r\n"
                ) and _starts_statement(data, match.start()):
                    shown = data[operand : operand + 60].split(b"\n", 1)[0].decode("utf-8", "replace")
                    raise Refusal(
                        f"{subject} spells '{token}' on line {line} with a file name that is no "
                        f"string literal ({shown.strip()!r}): a macro, a define or the program "
                        "writing it makes the name, so what the C preprocessor or the assembler "
                        "reads cannot be listed"
                    )
                continue
            spelled = _decode(name)
            parts = _name_parts(spelled)
            if not parts:
                if not strict:
                    continue
                raise Refusal(
                    f"{subject} names {spelled!r} with '{token}' on line {line}, which keeps no "
                    "component in every directory it may be looked for in"
                )
            reader = (
                f"{subject}, whose '{token}' on line {line} names {spelled!r} in whatever "
                "search directory a build script gives it,"
            )
            for excluded_path in self.excluded.get(fold(parts[-1]), []):
                if _ends_alike(excluded_path, parts):
                    self.reads.add(reader, self.tree / excluded_path)
            if strict:
                self.reached.update(
                    tracked_path for tracked_path in self.tracked.get(fold(parts[-1]), [])
                    if _ends_alike(tracked_path, parts)
                )

    def scan_rust(self, closure: Sequence["Member"]) -> None:
        """Reads what the Rust files a consumer can compile from the closure,
        the module files they declare and the Rust files they include, include
        under whatever `cfg`."""
        pending: list[tuple[Path, "Member", str]] = []
        for member in closure:
            skipped = [str(directory) for directory in member.uncompiled_roots]
            walked: set[str] = set()
            # Through a symbolic link to a directory too: rustc resolves a
            # module file through one.
            for root, directories, files in os.walk(member.directory, followlinks=True):
                if os.path.realpath(root) in walked:
                    directories[:] = []
                    continue
                walked.add(os.path.realpath(root))
                directories[:] = sorted(
                    name for name in directories
                    if not any(_under(os.path.join(root, name), directory) for directory in skipped)
                )
                pending.extend(
                    (Path(root) / name, member, f"a Rust file of package {member.name}")
                    for name in sorted(files, reverse=True) if name.endswith(".rs")
                )
        seen: set[str] = set()
        while pending:
            path, member, why = pending.pop()
            real = os.path.realpath(path)
            if real in seen or not os.path.isfile(real):
                continue
            seen.add(real)
            try:
                text = Path(real).read_bytes().decode("utf-8", "surrogateescape")
            except OSError as error:
                raise Refusal(f"cannot read {self._spelled(path)} ({why}): {error}") from error
            for read in rust_reads(text, path, member.directory):
                subject = f"{self._spelled(path)} ({why}), whose {read.what} on line {read.line}"
                if read.spelled is None or read.joined is None:
                    raise Refusal(
                        f"{subject} names a path no string literal spells: what rustc reads there "
                        "under a cfg the checks do not compile cannot be listed"
                    )
                self.reads.add(f"{subject} names {read.spelled!r} under whatever cfg,", read.joined)
                if read.in_macro and not os.path.isabs(read.spelled):
                    # Resolved from the file that calls the macro, which may be
                    # any: its name reads every path some directory puts it at.
                    parts = _name_parts(read.spelled)
                    for excluded_path in self.excluded.get(fold(parts[-1]) if parts else "", []):
                        if _ends_alike(excluded_path, parts):
                            self.reads.add(
                                f"{subject}, in a macro's body, names {read.spelled!r} from "
                                "wherever the macro is called,",
                                self.tree / excluded_path,
                            )
                if read.what in ("include!", "path attribute"):
                    pending.append(
                        (read.joined, member,
                         f"which the {read.what} on line {read.line} of {self._spelled(path)} names")
                    )
            for line, name in rust_modules(text):
                for candidate in module_candidates(path, name):
                    self.reads.add(
                        f"{self._spelled(path)} ({why}), whose `mod {name};` on line {line} "
                        "names it under whatever cfg,",
                        candidate,
                    )
                    pending.append(
                        (candidate, member, f"which `mod {name};` on line {line} of {self._spelled(path)} names")
                    )

    def scan_build_scripts(self, closure: Sequence["Member"]) -> None:
        """Reads what a string literal of a closure build script (its root, the
        module files it declares and the Rust files it includes) names as a
        path from its package's directory, which Cargo runs it in, or from
        CARGO_MANIFEST_DIR after a placeholder (`"{dir}/../x"`): a build script
        that hands a file to a tool, copies it or tests whether it exists, on a
        host the checks do not run it for, spells it so. A tracked file under a
        reviewed exclusion that such a literal names is then read strictly."""
        for member in closure:
            pending = [(Path(script), "the build script root") for script in member.build_scripts]
            seen: set[str] = set()
            while pending:
                path, why = pending.pop()
                real = os.path.realpath(path)
                if real in seen or not os.path.isfile(real):
                    continue
                seen.add(real)
                try:
                    text = Path(real).read_bytes().decode("utf-8", "surrogateescape")
                except OSError as error:
                    raise Refusal(f"cannot read {self._spelled(path)} ({why}): {error}") from error
                for _, name in rust_modules(text):
                    pending.extend(
                        (candidate, f"a module of the build script of {member.name}")
                        for candidate in module_candidates(path, name)
                    )
                for read in rust_reads(text, path, member.directory):
                    if read.joined is not None and read.what in ("include!", "path attribute"):
                        pending.append((read.joined, f"a file the build script of {member.name} includes"))
                for kind, value, offset in rust_tokens(text):
                    if kind != "string":
                        continue
                    for piece in re.split(r'[\s"=,;:]+', value.rsplit("}", 1)[-1]):
                        piece = re.sub(r"^-[A-Za-z]+", "", piece)
                        if "/" not in piece or not piece.strip("/."):
                            continue
                        resolved = Path(os.path.normpath(f"{member.directory}/{piece}"))
                        relative = self._spelled(resolved)
                        if relative.startswith("/") or relative.startswith(".."):
                            continue
                        self.reached.update(name for name in self.lenient if _under(name, relative))
                        if any(_under(change, relative) for change in self.changes):
                            self.reads.add(
                                f"{self._spelled(path)} (a file of the build script of {member.name}), "
                                f"whose string literal on line {text.count(chr(10), 0, offset) + 1} "
                                f"names {piece!r} from its package's directory,",
                                resolved,
                            )
        self.rescan_reviewed()


# The feature gate of every crate that tests `cfg(overflow_checks)`. The
# checks compile with overflow checks on exactly when debug assertions are (dev,
# release), which a build's profile need not do (trust-mc's dev profile turns
# debug assertions off for dependencies and leaves overflow checks on).
OVERFLOW_CHECKS_CFG = re.compile(rb"\bcfg_overflow_checks\b")


def refuse_overflow_checks_cfg(path: Path, reader: str) -> None:
    """Refuses when the file `path`, which `reader` compiles, enables
    `cfg(overflow_checks)`: which way a build sets it apart from debug
    assertions is unmodeled."""
    try:
        data = path.read_bytes()
    except OSError as error:
        raise Refusal(f"cannot read {path}, which {reader} compiles: {error}") from error
    if OVERFLOW_CHECKS_CFG.search(data):
        raise Refusal(
            f"{path}, which {reader} compiles, enables cfg(overflow_checks): the checks set it "
            "with debug assertions, which a build's profile need not, so what it compiles "
            "cannot be listed"
        )


# The compiler the probes' checks run in Cargo's place (Cargo runs whatever
# RUSTC names, through the consumer's wrapper). For a unit of a package in the
# tree of the pin it runs Cargo's command line once more with -Zunpretty=hir and
# records the expansion, then runs the command line as given: what a macro,
# procedural or not, expands an `asm!` or `global_asm!` template to is then
# searched as the compiler wrote it, not as the sources spell it.
EXPANDING_COMPILER = """
import json
import os
import subprocess
import sys
import time

real = os.environ["TRUST_MC_PIN_GATE_RUSTC"]
arguments = sys.argv[1:]
directory = os.environ.get("CARGO_MANIFEST_DIR")
tree = os.environ["TRUST_MC_PIN_GATE_TREE"]
if directory is not None and (os.path.realpath(directory) + os.sep).startswith(tree + os.sep):
    crate = out_dir = extra = None
    for index, argument in enumerate(arguments):
        following = arguments[index + 1] if index + 1 < len(arguments) else ""
        if argument == "--crate-name":
            crate = following
        elif argument == "--out-dir":
            out_dir = following
        elif argument == "-C" and following.startswith("extra-filename="):
            extra = following.split("=", 1)[1]
    stem = os.path.join(
        os.environ["TRUST_MC_PIN_GATE_EXPANSIONS"], f"{os.getpid()}-{time.monotonic_ns()}"
    )
    run = subprocess.run([real, *arguments, "-Zunpretty=hir", "-o", stem + ".hir"], capture_output=True)
    if run.returncode != 0:
        sys.stderr.buffer.write(run.stderr)
        sys.exit(run.returncode)
    dep_info = None
    if crate is not None and out_dir is not None:
        # rustc names it `<crate><extra-filename>.d`; Cargo compiles a build
        # script without `-C extra-filename` (`build_script_build.d`).
        dep_info = os.path.realpath(os.path.join(out_dir, crate + (extra or "") + ".d"))
    with open(stem + ".json", "w", encoding="utf-8") as record:
        json.dump(
            {"crate": crate, "directory": directory, "dep_info": dep_info, "expansion": stem + ".hir"},
            record,
        )
os.execvp(real, [real, *arguments])
"""


def cargo_compiler(cargo: str, base: Path, cwd: Path) -> str:
    """The compiler Cargo runs for a check from `cwd`, the environment and
    configuration included: the RUSTC it hands a build script."""
    crate = base / "compiler"
    crate.mkdir()
    (crate / "Cargo.toml").write_text(
        f'[package]\nname = {_toml_string(PROBE + "-compiler")}\nversion = "0.0.0"\n'
        'edition = "2021"\nbuild = "build.rs"\n\n[lib]\npath = "lib.rs"\n\n[workspace]\n',
        encoding="utf-8",
    )
    (crate / "lib.rs").write_text("", encoding="utf-8")
    (crate / "build.rs").write_text(
        'fn main() {\n    let out = std::env::var("OUT_DIR").unwrap();\n'
        '    std::fs::write(format!("{out}/rustc"), std::env::var("RUSTC").unwrap()).unwrap();\n}\n',
        encoding="utf-8",
    )
    messages = check_messages(cargo, crate / "Cargo.toml", base / "target-compiler", cwd, ())
    found = [
        Path(message["out_dir"]) / "rustc"
        for message in messages
        if message.get("reason") == "build-script-executed"
    ]
    try:
        if len(found) != 1:
            raise OSError(f"{len(found)} build script runs")
        return found[0].read_text(encoding="utf-8")
    except OSError as error:
        raise Refusal(f"cannot tell which compiler Cargo runs from {cwd}: {error}") from error


class Expansions:
    """The compiler's expansions of the units of the tree the checks compiled."""

    def __init__(self, cargo: str, base: Path, cwd: Path, tree: Path) -> None:
        self.records = base / "expansions"
        self.records.mkdir()
        compiler = base / "expanding-compiler"
        compiler.write_text(python_executable_header(sys.executable) + EXPANDING_COMPILER, encoding="utf-8")
        compiler.chmod(0o755)
        self.environment = {
            **os.environ,
            "RUSTC": str(compiler),
            "TRUST_MC_PIN_GATE_RUSTC": cargo_compiler(cargo, base, cwd),
            "TRUST_MC_PIN_GATE_TREE": os.path.realpath(tree),
            "TRUST_MC_PIN_GATE_EXPANSIONS": str(self.records),
        }
        self.environment.pop("CARGO_MANIFEST_DIR", None)
        self.expanded: set[str] = set()  # the dep-info files of the units expanded

    def search(self) -> Optional[Refusal]:
        """The refusal when an expansion recorded since the last call spells an
        assembler directive that reads a file (raised once the check's own
        files have been searched: a file that spells it names it better)."""
        found: Optional[Refusal] = None
        for record in sorted(self.records.glob("*.json")):
            try:
                data = json.loads(record.read_text(encoding="utf-8"))
                expansion = Path(data["expansion"])
                text = expansion.read_bytes()
            except (OSError, ValueError, KeyError, TypeError) as error:
                raise Refusal(
                    f"cannot read the compiler's expansion recorded in {record}: {error}"
                ) from error
            refusal = _directive_refusal(
                text, f"the compiler's expansion of {data.get('crate')} ({data.get('directory')})"
            )
            found = found or refusal
            if data.get("dep_info"):
                self.expanded.add(data["dep_info"])
            expansion.unlink()
            record.unlink()
        for leftover in self.records.glob("*.d"):  # the dep-info the expanding run writes
            leftover.unlink()
        return found

    def require(self, dep_info: Path, reader: str) -> None:
        """Refuses unless the unit that wrote `dep_info` was expanded."""
        if os.path.realpath(dep_info) not in self.expanded:
            raise Refusal(
                f"{reader} was compiled without the gate's compiler recording its expansion, so "
                "the assembler templates its macros expand to cannot be listed"
            )


# The access time the read witness gives an excluded file before each check: a
# day after the epoch, older than any modification time, so the next read moves
# it even where a file system records a read only over an access time older
# than the modification time (Linux's relatime; APFS, as measured).
UNREAD_NS = 86_400 * 10**9


class ReadWitness:
    """The excluded paths the tree of the pin holds, and which check read one.
    Before each check their access times are set back; one that moved during
    the check was read by something it ran (rustc, a procedural macro, a build
    script and what that runs), however that named or reached the file."""

    def __init__(self, tree: Path, excluded: Sequence[tuple[str, Exclusion]], base: Path) -> None:
        self.files = [
            (path, exclusion) for path, exclusion in excluded if os.path.lexists(tree / path)
        ]
        self.tree = tree
        self.read: dict[str, tuple[Exclusion, str]] = {}
        if self.files:
            self._require_recorded_reads(base)

    @staticmethod
    def _set_back_one(path: Path) -> None:
        try:
            os.utime(path, ns=(UNREAD_NS, os.stat(path).st_mtime_ns))
        except OSError as error:
            raise Refusal(f"cannot set back the access time of {path}: {error}") from error

    @staticmethod
    def _accessed(path: Path) -> int:
        try:
            return os.stat(path).st_atime_ns
        except OSError as error:
            raise Refusal(f"cannot read the access time of {path}: {error}") from error

    def _require_recorded_reads(self, base: Path) -> None:
        """Refuses unless the file system holding the tree records a read by
        another process as a moved access time (it may be mounted noatime)."""
        canary = base / "read-witness-canary"
        canary.write_bytes(b"read\n")
        self._set_back_one(canary)
        read = subprocess.run(
            [sys.executable, "-c", "import sys; open(sys.argv[1], 'rb').read()", str(canary)],
            capture_output=True, check=False,
        )
        if read.returncode != 0 or self._accessed(canary) == UNREAD_NS:
            raise Refusal(
                f"the file system holding {self.tree} does not record that a file was read (its "
                "access time), so what the checks read without naming it cannot be observed"
            )

    def paths(self) -> list[str]:
        return [path for path, _ in self.files]

    def set_back(self) -> None:
        for path, _ in self.files:
            self._set_back_one(self.tree / path)

    def collect(self, what: str) -> None:
        """Records who read each file whose access time moved: `what` ran."""
        for path, exclusion in self.files:
            if self._accessed(self.tree / path) != UNREAD_NS:
                self.read.setdefault(path, (exclusion, what))

    def refuse(self) -> None:
        if self.read:
            raise Refusal(
                "an exclusion covers what the pinned packages read; take it off "
                "scripts/pin-exclusions.toml:\n  "
                + "\n  ".join(
                    f"{exclusion.pattern} covers {path}, and {what} read it (its access time moved)"
                    for path, (exclusion, what) in sorted(self.read.items())
                )
            )


def refuse_tree_writes(checkout: Path, tree: Path) -> None:
    """Refuses when the checks changed the tree of the pin (a build script
    writing into its package: a copy of an excluded file it keeps in sync,
    which a clone makes without moving the original's access time). What the
    tree then holds is no longer the pin, and the checks without the excluded
    files would compile what the checks with them wrote."""
    index = tree.parent / f"{tree.name}.index"
    environment = {**os.environ, "GIT_INDEX_FILE": str(index)}
    work_tree = ("--work-tree", str(tree))
    try:
        subprocess.run(
            ["git", "-C", str(checkout), *work_tree, "update-index", "-q", "--refresh"],
            env=environment, capture_output=True, check=False,
        )
    except OSError as error:
        raise Refusal(f"git update-index failed in {checkout}: {error}") from error
    changed = [
        _decode(name) for name in _git(
            checkout, *work_tree, "diff-files", "--name-only", "-z", env=environment
        ).split(b"\0") if name
    ]
    added = [
        _decode(name) for name in _git(
            checkout, *work_tree, "ls-files", "--others", "-z", env=environment
        ).split(b"\0") if name
    ]
    if changed or added:
        raise Refusal(
            "checking the pinned packages changed the tree of the pin ("
            + "; ".join(
                [f"{len(changed)} tracked file(s) changed, first {changed[0]}"] if changed else []
            )
            + ("; " if changed and added else "")
            + (f"{len(added)} file(s) added, first {added[0]}" if added else "")
            + "): a build script writes into it, so what it compiles is not the pin's content "
            "and what that is made from cannot be listed"
        )


# The global header of an ar archive; each member's header then holds its
# modification time at bytes 16-28, which `ar` sets to when it archived it.
AR_MAGIC = b"!<arch>\n"


def _comparable(data: bytes) -> bytes:
    """`data` as two runs of one build script can be compared: an ar archive
    with its members' modification times blanked, anything else as it is."""
    if not data.startswith(AR_MAGIC):
        return data
    blanked = bytearray(data)
    position = len(AR_MAGIC)
    while position + 60 <= len(data):
        header = data[position : position + 60]
        try:
            size = int(header[48:58].decode("ascii").strip())
        except ValueError:
            return data
        if header[58:60] != b"`\n":
            return data
        blanked[position + 16 : position + 28] = b" " * 12
        position += 60 + size + (size & 1)
    return bytes(blanked)


def _tree_package(package_id: str, tree: Path) -> bool:
    """Whether Cargo's `package_id` is a path package in `tree`."""
    location = package_id.split("#", 1)[0]
    if not location.startswith("path+file://"):
        return False
    return _under(os.path.realpath(urllib.parse.unquote(location[len("path+file://"):])), str(tree))


def build_script_result(out_dir: Path) -> tuple[bytes, tuple[tuple[str, str, str], ...]]:
    """What one build script run left for Cargo, rustc and the linker: the
    output Cargo reads, and what its OUT_DIR holds (each entry's kind and path,
    a symbolic link's target). A file's bytes are left out: an archive holds
    its members' times."""
    try:
        printed = build_script_stdout(out_dir).read_bytes()
        held = []
        for root, directories, files in os.walk(out_dir):
            for name in [*directories, *files]:
                entry = Path(root) / name
                relative = entry.relative_to(out_dir).as_posix()
                if entry.is_symlink():
                    held.append(("link", relative, os.readlink(entry)))
                elif entry.is_dir():
                    held.append(("directory", relative, ""))
                else:
                    digest = hashlib.sha256(_comparable(entry.read_bytes())).hexdigest()
                    held.append(("file", relative, digest))
    except OSError as error:
        raise Refusal(f"cannot read what the build script run {out_dir.parent} left: {error}") from error
    return printed, tuple(sorted(held))


def _first_difference(present: tuple, absent: tuple) -> str:
    """How two `build_script_result`s differ, first of each way."""
    if present[0] != absent[0]:
        return "it printed otherwise"
    missing = sorted(set(present[1]) - set(absent[1]))
    extra = sorted(set(absent[1]) - set(present[1]))
    names = {(kind, path) for kind, path, _ in present[1]} ^ {(kind, path) for kind, path, _ in absent[1]}
    shown = [
        f"{kind} OUT_DIR/{path} only with them" for kind, path, _ in missing if (kind, path) in names
    ][:1]
    shown += [
        f"{kind} OUT_DIR/{path} only without them" for kind, path, _ in extra if (kind, path) in names
    ][:1]
    if not shown:
        shown = [f"{kind} OUT_DIR/{path} holds other bytes" for kind, path, _ in missing[:1]]
    return "; ".join(shown)


def refuse_reads_of_absent(
    cargo: str, tree: Path, absent: Sequence[str], probes: Sequence["Probe"], base: Path, cwd: Path
) -> None:
    """Refuses unless every probe, already checked, checks again in both
    profiles and a fresh target directory with the excluded paths `absent`
    removed from the tree, and every build script of a package of the tree
    leaves there what it left with them (`build_script_result`): what a check
    runs may read one without moving its access time (a copy that is a clone,
    as `std::fs::copy` makes on APFS; a test of whether it exists), and a
    build script may tolerate its absence (`let _ = std::fs::copy(..)`), so the
    check passes without it and what the build script left differs. The
    target directory of the checks with them is moved aside, so both runs
    build in one directory: a name a build script derives from it (cc-rs
    names an object file after the hash of its source's directory) is one."""
    if not absent:
        return
    for path in absent:
        (tree / path).unlink()
    present = base / "target-present"
    (base / "target").rename(present)
    named = ", ".join(absent[:3]) + (f" and {len(absent) - 3} more" if len(absent) > 3 else "")
    for index, probe_spec in enumerate(probes):
        targets = [option for target in probe_spec.targets for option in ("--target", target)]
        for profile in PROFILES:
            checked = f"checking {probe_spec.what} {' '.join(profile) or '(dev)'}"
            try:
                messages = check_messages(
                    cargo, base / f"probe-{index}" / "Cargo.toml", base / "target", cwd,
                    [*profile, *targets],
                )
            except Refusal as error:
                raise Refusal(
                    f"with the excluded {named} removed from the tree of the pin, {checked} fails "
                    "where it passed with them: something it runs reads them; take their "
                    f"exclusion off scripts/pin-exclusions.toml:\n{error}"
                ) from error
            for message in messages:
                if message.get("reason") != "build-script-executed" or not _tree_package(
                    message.get("package_id", ""), tree
                ):
                    continue
                without = Path(message["out_dir"])
                try:
                    with_them = present / without.relative_to(base / "target")
                except ValueError:
                    with_them = None
                if with_them is None or not with_them.is_dir():
                    raise Refusal(
                        f"with the excluded {named} removed from the tree of the pin, {checked} runs "
                        f"the build script of {message['package_id']} into {without}, which the "
                        "checks with them did not: what it left cannot be compared"
                    )
                left = build_script_result(with_them)
                left_without = build_script_result(without)
                if left != left_without:
                    raise Refusal(
                        f"with the excluded {named} removed from the tree of the pin, {checked} "
                        f"passes, but the build script of {message['package_id']} leaves otherwise "
                        f"than with them ({_first_difference(left, left_without)}): it reads them "
                        "and tolerates their absence; take their exclusion off "
                        "scripts/pin-exclusions.toml"
                    )


@dataclass(frozen=True)
class Probe:
    """A crate the gate checks in place of a build of the consumer."""

    what: str
    manifest: str
    build_script: bool = False
    targets: tuple[str, ...] = ()
    # When it reproduces a build: what that build compiles (identity ->
    # description), which the probe's own unit graph must list exactly.
    expected: Optional[dict[str, str]] = None


def refuse_aborting_profiles(manifest: Path) -> None:
    """Refuses when the consumer's workspace manifest builds a profile with a
    panic strategy other than unwinding, which any build of that profile uses:
    the checks unwind, so `cfg(panic)` would be unmodeled."""
    try:
        profiles = toml_loads(manifest.read_text(encoding="utf-8")).get("profile") or {}
    except (OSError, UnicodeDecodeError, TOMLDecodeError) as error:
        raise Refusal(f"cannot read the consumer's manifest {manifest}: {error}") from error
    for name, table in sorted(profiles.items()):
        panic = table.get("panic", "unwind") if isinstance(table, dict) else "unwind"
        if panic != "unwind":
            raise Refusal(
                f"{manifest} builds profile {name!r} with panic = {panic!r}; the checks unwind, "
                "so `cfg(panic)` would be unmodeled"
            )


def build_probes(
    cargo: str, consumer: Path, builds: Sequence[Build], members: dict[str, Member],
    closure: Sequence[Member], packages: Sequence[str],
) -> tuple[list[Probe], int]:
    """The probes that check `consumer`'s builds of the closure: one per feature
    set any build can give a package of it (dependencies as the package asks),
    and one per distinct thing a declared build compiles for it (every package,
    dependencies included, exactly as that build's resolver gives it); and how
    many distinct builds there are."""
    if not builds:
        raise Refusal(
            f"no build of {consumer} is declared ([{CONSUMER_BUILDS}]), so which feature sets "
            "its builds give the dependencies of the pinned packages cannot be derived"
        )
    metadata = consumer_metadata(cargo, consumer)
    refuse_aborting_profiles(Path(metadata["workspace_root"]) / "Cargo.toml")
    probes = [
        Probe(
            f"{name} [{','.join(features)}]",
            probe_manifest({name: (members[name].directory, features)}),
        )
        for name, features in consumer_feature_sets(
            cargo, consumer, members, closure, packages, metadata
        )
    ]
    by_id = {package["id"]: package for package in metadata.get("packages", [])}
    names = frozenset(member.name for member in closure)
    workspace_members = frozenset(metadata.get("workspace_members") or ())
    compiled: set[str] = set()
    distinct: dict[tuple[frozenset[str], tuple[str, ...]], Build] = {}
    for build in builds:
        graph = unit_graph(cargo, build.arguments, consumer, consumer.parent, locked=True)
        cone = build_cone(graph, names, by_id, build, workspace_members)
        compiled |= cone.compiled
        key = (frozenset(cone.units), build.targets)
        if not cone.units or key in distinct:
            continue
        distinct[key] = build
        probes.append(
            Probe(
                f"the build `{build.lane}`",
                reproducing_manifest(
                    cone,
                    by_id,
                    {pkg_id: members[name].directory for pkg_id, name in cone.closure_ids.items()},
                ),
                any(side == HOST_SIDE for _, side in cone.requests),
                build.targets,
                cone.units,
            )
        )
    missing = sorted(set(packages) - compiled)
    if missing:
        raise Refusal(
            f"no declared build of {consumer} compiles {missing}, so the declared builds are not "
            "the ones that consume the pin"
        )
    return probes, len(distinct)


def probe_units(
    cargo: str, probe: Path, cwd: Path, targets: Sequence[str], directories: dict[str, Member]
) -> dict[str, str]:
    """What checking `probe` compiles for the closure, as `build_cone` names it."""
    graph = unit_graph(
        cargo, ["check", *(option for target in targets for option in ("--target", target))],
        probe / "Cargo.toml", cwd, locked=False,
    )
    units = graph["units"]

    def closure_name(pkg_id: str) -> Optional[str]:
        location = pkg_id.split("#", 1)[0]
        if not location.startswith("path+file://"):
            return None
        member = directories.get(os.path.realpath(urllib.parse.unquote(location[len("path+file://"):])))
        return member.name if member is not None else None

    names = [closure_name(unit["pkg_id"]) for unit in units]
    identities = _unit_identities(
        units, lambda pkg_id: f"closure:{closure_name(pkg_id)}" if closure_name(pkg_id) else pkg_id
    )
    cone = _cone(units, [index for index, name in enumerate(names) if name is not None])
    return {identities[index]: _describe_unit(units[index]) for index in cone}


def pinned_reads(
    cargo: str,
    checkout: Path,
    pin: str,
    packages: Sequence[str],
    consumer: Optional[Path],
    excluded: Sequence[tuple[str, Exclusion]],
    base: Path,
    cargo_at_run_time: Optional[str] = None,
    builds: Sequence[Build] = (),
    exclusions: Optional[Sequence[Exclusion]] = None,
) -> str:
    """Refuses unless the pinned packages read none of `excluded` at `pin`;
    names the checks that listed what they read. `builds` are the consumer's,
    `exclusions` the reviewed list (by default, those `excluded` names)."""
    tree = base / "tree"
    tree.mkdir()
    entries = extract_revision(checkout, pin, tree)
    workspace = tree_workspace(cargo, tree, packages)
    members = workspace.members
    closure = package_closure(members, packages)
    refuse_other_declarations(tree, entries, closure)
    for member in closure:
        if member.links is not None:
            raise Refusal(
                f"{member.name} declares links = {member.links!r}: Cargo hands what its build "
                "script prints as metadata to the build script of every package depending on "
                "it, the consumer's included, and what they read through it cannot be listed"
            )

    reads = Reads(tree)
    scanned: set[str] = set()  # compiled files already searched

    def scan(path: Path, reader: str) -> None:
        if str(path) not in scanned:
            scanned.add(str(path))
            refuse_assembler_file_directive(path, reader)
            refuse_overflow_checks_cfg(path, reader)

    for member in closure:
        reads.add(f"package {member.name}", member.directory)
        for root in member.roots:
            reads.add(f"a crate root of {member.name}", root)
        for named in member.named:
            reads.add(f"the manifest of {member.name}", named)
    for name, mode in entries.items():
        if mode == SYMBOLIC_LINK_MODE:
            reads.add(f"symbolic link {name}", Path(os.path.realpath(tree / name)))
    if cargo_at_run_time is not None:
        for path in workspace.loaded:
            reads.add("Cargo, which a pinned package runs on its workspace at run time,", path)
    # What a file of the tree names for the C preprocessor or an assembler that
    # a build script runs, read from the files: whatever host runs it.
    if exclusions is None:
        exclusions = list({exclusion.pattern: exclusion for _, exclusion in excluded}.values())
    inputs = BuildInputs(tree, entries, excluded, exclusions, reads)
    inputs.scan_tree(closure)
    inputs.scan_build_scripts(closure)
    reads.refuse(excluded)  # before building, what the manifests, links and build inputs show

    distinct = 0
    if consumer is None:
        probes = [
            Probe(
                "the pinned packages",
                probe_manifest({name: (members[name].directory, None) for name in packages}),
            )
        ]
    else:
        probes, distinct = build_probes(cargo, consumer, builds, members, closure, packages)
    if consumer is not None and (consumer.parent / "Cargo.lock").is_file():
        lock: Optional[Path] = consumer.parent / "Cargo.lock"
    else:
        lock = None
    cwd = consumer.parent if consumer is not None else base
    directories = {os.path.realpath(member.directory): member for member in closure}
    expansions = Expansions(cargo, base, cwd, tree)
    witness = ReadWitness(tree, excluded, base)
    for index, probe_spec in enumerate(probes):
        probe = base / f"probe-{index}"
        probe.mkdir()
        (probe / "lib.rs").write_text("", encoding="utf-8")
        (probe / "Cargo.toml").write_text(probe_spec.manifest, encoding="utf-8")
        if probe_spec.build_script:
            (probe / "build.rs").write_text("fn main() {}\n", encoding="utf-8")
        if lock is not None:
            shutil.copyfile(lock, probe / "Cargo.lock")
        targets = [option for target in probe_spec.targets for option in ("--target", target)]
        if probe_spec.expected is not None:
            found = probe_units(cargo, probe, cwd, probe_spec.targets, directories)
            missing = sorted(probe_spec.expected[key] for key in set(probe_spec.expected) - set(found))
            extra = sorted(found[key] for key in set(found) - set(probe_spec.expected))
            if missing or extra:
                raise Refusal(
                    f"the probe for {probe_spec.what} does not compile what that build does "
                    f"({len(missing)} of its units missing, first {missing[:1]}; {len(extra)} "
                    f"more, first {extra[:1]}), so what the build reads cannot be listed"
                )
        for profile in PROFILES:
            witness.set_back()
            messages = check_messages(
                cargo, probe / "Cargo.toml", base / "target", cwd, [*profile, *targets],
                expansions.environment,
            )
            witness.collect(f"checking {probe_spec.what} {' '.join(profile) or '(dev)'}")
            expanded = expansions.search()
            compiled: dict[str, Member] = {}
            for message in messages:
                if message.get("reason") != "compiler-artifact":
                    continue
                manifest = Path(os.path.realpath(message["manifest_path"]))
                if manifest == probe / "Cargo.toml":  # its lib.rs and build.rs are the empty ones above
                    continue
                dep_infos = dep_info_files(message)
                named = [
                    (dep_info, path) for dep_info in dep_infos for path in dep_info_paths(dep_info)
                ]
                if tree not in manifest.parents:
                    for _, path in named:
                        scan(Path(path), f"{message['target']['name']} ({message['package_id']})")
                    continue
                member = directories.get(str(manifest.parent))
                if member is None:
                    raise Refusal(
                        f"checking the pinned packages compiled {manifest.parent}, which no "
                        "path dependency a consumer can build reaches from them; what it "
                        "reads is unmodeled"
                    )
                compiled[message["package_id"]] = member
                reader = f"{message['target']['name']} ({member.name}) {' '.join(profile)}".strip()
                for dep_info in dep_infos:
                    expansions.require(dep_info, reader)
                for dep_info, path in named:
                    reads.add(reader, Path(path))
                    if not os.path.lexists(path):
                        raise Refusal(f"{dep_info} names {path!r}, which does not exist")
                    reads.add(
                        f"{reader}, looking for module files beside {Path(path).name},",
                        module_directory(Path(path)),
                    )
                    scan(Path(path), reader)
            for message in messages:
                member = compiled.get(message.get("package_id", ""))
                if message.get("reason") != "build-script-executed" or member is None:
                    continue
                build_script_reads(reads, member, message, base / "target")
            if expanded is not None:
                raise expanded
    # What rustc includes under a cfg the checks did not compile; after them, so
    # a read rustc named is told as rustc named it.
    inputs.scan_rust(closure)
    # A file under a reviewed exclusion that a watched path, a Rust include or
    # dep-info shows a build reads is read strictly after all.
    inputs.rescan_reviewed()
    reads.refuse(excluded)  # a read rustc or Cargo names says best who reads
    witness.refuse()
    refuse_tree_writes(checkout, tree)
    refuse_reads_of_absent(cargo, tree, witness.paths(), probes, base, cwd)
    sets = len(probes) - distinct
    checked = f"{sets} feature set{'s' if sets != 1 else ''}"
    if consumer is not None:
        plural = "s" if len(builds) != 1 else ""
        checked += f" and {len(builds)} build{plural} of the consumer ({distinct} distinct)"
    return f"{checked} x dev and release"


def build_script_reads(reads: Reads, member: Member, message: dict[str, Any], target: Path) -> None:
    """What one build script of the closure tells Cargo, rustc and the linker to
    read: the paths it watches and the directories the linker searches for the
    libraries it links (`check` never links, so no dep-info names them): one
    beneath the target directory (its own OUT_DIR, which it wrote) as the
    linker opens it, through a symbolic link that is the directory or holds
    it, and there what each symbolic link resolves to. Its output is read as
    Cargo reads it, and must agree with what Cargo itself recorded: the watched
    paths in the run's fingerprint, the search paths and libraries in the
    build-script-executed message. A linker argument is refused: what the
    linker reads through one cannot be listed. Metadata reaches no one: a
    package declaring `links` was refused before building. What a watched file
    names for the C preprocessor or an assembler, BuildInputs read from every
    tracked file; what else it reads, the read witness and the absence checks
    see."""
    out_dir = Path(message["out_dir"])
    output = build_script_stdout(out_dir)
    reader = f"the build script of {member.name}"
    directives = build_script_directives(output)
    watched, search, libraries = [], [], []
    for key, value in directives:
        if key in LINK_ARGUMENTS:
            raise Refusal(
                f"{reader} passes the linker {key}={value}; what the link reads cannot be listed"
            )
        if key == "rerun-if-changed":
            watched.append(value)
        elif key == "rustc-link-search":
            search.append(value)
        elif key == "rustc-link-lib":
            libraries.append(value)
        elif key == "rustc-flags":
            paths, names = rustc_flags(value, output)
            search.extend(paths)
            libraries.extend(names)

    def spelled(paths: Sequence[str]) -> set[str]:
        return {os.path.normpath(member.directory / path) for path in paths}

    recorded = cargo_rerun_if_changed(out_dir)
    if spelled(watched) != spelled(recorded):
        raise Refusal(
            f"{reader} watches {sorted(spelled(watched))} as read here, but Cargo recorded "
            f"{sorted(spelled(recorded))}"
        )
    if (search, libraries) != (message.get("linked_paths"), message.get("linked_libs")):
        raise Refusal(
            f"{reader} links {libraries} from {search} as read here, but Cargo reported "
            f"{message.get('linked_libs')} from {message.get('linked_paths')}"
        )
    for path in watched:
        reads.add(reader, member.directory / path)
    for value in search:
        directory = Path(search_directory(value))
        if not directory.is_absolute():
            raise Refusal(
                f"{reader} adds the relative library search path {value}; the linker resolves "
                "it from its own working directory, which differs by consumer"
            )
        resolved = Path(os.path.realpath(directory))
        if not _under(os.path.normpath(directory), str(target)):
            reads.add(f"the linker, searching {value} for {reader},", directory)
        elif not _under(str(resolved), str(target)):
            # The directory is, or lies beneath, a symbolic link out of the
            # target directory: the linker searches what it resolves to, and
            # making the link read nothing.
            reads.add(f"the linker, searching {value} for {reader} through a symbolic link,", resolved)
        else:
            generated_link_reads(
                reads, resolved, target, f"the linker, searching {value} for {reader}"
            )
    for value in libraries:
        name = value.partition("=")[2] if "=" in value else value
        if "/" in name.split(":", 1)[0] or "\\" in name:
            raise Refusal(f"{reader} links {value}, a path rather than a library name")


def generated_link_reads(reads: Reads, directory: Path, target: Path, reader: str) -> None:
    """What the linker (and rustc, bundling a static library into an rlib) reads
    at codegen in a search directory a build script generated beneath the
    target directory: what each symbolic link there resolves to. Making a link
    reads nothing, even an absent target, so neither the read witness nor the
    absence check sees it. A hard link, which names a file of the tree under
    another name, is refused."""
    for root, directories, files in os.walk(directory):
        for name in sorted([*directories, *files]):
            entry = Path(root) / name
            if entry.is_symlink():
                resolved = Path(os.path.realpath(entry))
                if not _under(os.path.normpath(resolved), str(target)):
                    reads.add(f"{reader} through {entry},", resolved)
            elif entry.is_file() and os.stat(entry).st_nlink > 1:
                raise Refusal(
                    f"{reader} finds {entry}, a hard link: which file of the tree it names "
                    "cannot be listed"
                )


# --- the gate ------------------------------------------------------------------


@dataclass(frozen=True)
class Drift:
    """What changed between the pin and live main, and what of it is drift."""

    changed: int
    drifted: list[str]
    excluded: list[tuple[str, Exclusion]]
    checked: str

    def describe(self) -> str:
        if not self.changed:
            return "no path changed"
        if self.drifted:
            return f"{self.changed} changed paths, {len(self.drifted)} of them drift"
        patterns = sorted({exclusion.pattern for _, exclusion in self.excluded})
        return (
            f"{self.changed} changed paths, all under reviewed exclusions "
            f"{','.join(patterns)} that the pinned packages do not read ({self.checked})"
        )


def drift(
    cargo: str,
    checkout: Path,
    pin: str,
    main: str,
    packages: Sequence[str],
    consumer: Optional[Path] = None,
    exclusions: Sequence[Exclusion] = (),
    cargo_at_run_time: Optional[str] = None,
    builds: Sequence[Build] = (),
) -> Drift:
    """What of `pin..main` is drift. When every change is excluded, refuses
    unless each is unread by `packages` at the pin; `cargo_at_run_time` says
    why a pinned package runs Cargo on its own workspace at run time, `builds`
    are the builds of `consumer` its lanes run."""
    changed = changes(checkout, pin, main)
    drifted, excluded = classify(
        changed, exclusions, tracked(checkout, pin), tracked(checkout, main)
    )
    if drifted or not excluded:
        return Drift(len(changed), drifted, excluded, "")
    # `.noindex`: Spotlight reads no file beneath it, which the read witness would see.
    with tempfile.TemporaryDirectory(prefix="trust-mc-pin-gate-", suffix=".noindex") as scratch:
        checked = pinned_reads(
            cargo, checkout, pin, packages, consumer, excluded, Path(scratch).resolve(),
            cargo_at_run_time, builds, exclusions,
        )
    return Drift(len(changed), [], excluded, checked)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(prog=Path(argv[0]).name, description=__doc__.split("\n")[0])
    commands = parser.add_subparsers(dest="command", required=True)
    command = commands.add_parser("drift", help="exit 0: no drift, 1: drift, 2: refused")
    command.add_argument(
        "--consumer", type=Path,
        help=f"the manifest whose builds apply; the exclusion list's [{CONSUMER_BUILDS}] names them",
    )
    command.add_argument("--exclusions", type=Path, help="the reviewed exclusion list")
    command.add_argument("--repository", help="its table for the pinned repository")
    command.add_argument("targo")
    command.add_argument("checkout", type=Path)
    command.add_argument("pin")
    command.add_argument("main")
    command.add_argument("packages", nargs="+")
    try:
        arguments = parser.parse_args(argv[1:])
    except SystemExit as error:
        return int(error.code or 0)
    if (arguments.exclusions is None) != (arguments.repository is None):
        print(f"{parser.prog}: --exclusions and --repository go together", file=sys.stderr)
        return 2
    try:
        listed = arguments.exclusions is not None
        result = drift(
            arguments.targo,
            arguments.checkout,
            arguments.pin,
            arguments.main,
            arguments.packages,
            arguments.consumer.resolve() if arguments.consumer is not None else None,
            load_exclusions(arguments.exclusions, arguments.repository) if listed else [],
            load_cargo_at_run_time(arguments.exclusions, arguments.repository) if listed else None,
            load_consumer_builds(arguments.exclusions) if listed else [],
        )
    except Refusal as error:
        print(f"pinned-package-paths: error: {error}", file=sys.stderr)
        return 2
    for name in result.drifted:
        print(f"pinned-package-paths: changed: {name}", file=sys.stderr)
    print(result.describe())
    return 1 if result.drifted else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
