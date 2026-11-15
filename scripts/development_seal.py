#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Read an explicitly named, confined development seal without executing it.

This establishes only three critical artifact identities and their recorded,
completed build stamp. It does not replay the source census, authenticate the
rest of the sysroot, prove the build, establish release lineage, or make an
owner unable to chmod files.
Every path component is opened without following links; all descriptors remain
owned through the final identity check, which holds the root and everything in
it to their whole identity and each ancestor above the root to its binding. No
sibling code or subprocess is used.
"""

from __future__ import annotations

import hashlib
import os
import re
import stat
import time
from dataclasses import dataclass
from pathlib import PurePosixPath
from typing import Any, Callable, Mapping

SHA256 = re.compile(r"^[0-9a-f]{64}$")
REVISION = re.compile(r"^[0-9a-f]{40}$")
HOST = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]*$")
DRIVER_PATH = re.compile(r"^lib/librustc_driver-[A-Za-z0-9_-]+\.(so|dylib)$")
FIELD = re.compile(r"^[A-Za-z][A-Za-z0-9_:-]*$")
MAX_ARTIFACT_BYTES = 3 * 1024**3
MAX_TOTAL_BYTES = 4 * 1024**3
MAX_PROVENANCE_BYTES = 65536
READ_BYTES = 1024 * 1024
READ_TIMEOUT_SECONDS = 45.0
MAX_CENSUS_ENTRIES = 65536
MAX_CENSUS_DIRECTORIES = 4096
MAX_CENSUS_DEPTH = 32
MAX_CRITICAL_ALIASES = 64
IDENTITY_SCOPE = (
    "critical-artifact development identity at observation; completed build-stamp "
    "v1 covers top-level source state only; no complete sysroot authentication, "
    "release lineage, or certified-build claim"
)
RECURSIVE_CENSUS_SCOPE = "recursive-worktrees/v1"
RECURSIVE_IDENTITY_SCOPE = (
    "critical-artifact development identity at observation; completed build-stamp "
    "v2 binds recorded recursive-worktree source facts (source census not replayed); "
    "no complete sysroot authentication, release lineage, or certified-build claim"
)
STAMP_BASE_IDENTITY = ("head", "diff_sha256", "status_sha256", "submodule_sha256")
STAMP_RECURSIVE_IDENTITY = (
    "submodule_census_scope", "recursive_submodule_sha256", "recursive_submodule_count",
    "tree_state", "dirty_tracked", "dirty_untracked",
)


class SealRefusal(ValueError):
    """Declared development identity is malformed or cannot be established."""


@dataclass(frozen=True)
class Artifact:
    path: str
    sha256: str
    size: int


@dataclass(frozen=True)
class DevelopmentSeal:
    root: str
    host: str
    provenance_sha256: str
    trustc: Artifact
    targo: Artifact
    driver: Artifact

    @classmethod
    def parse(cls, table: Any) -> DevelopmentSeal:
        fields = {
            "root", "host", "provenance_sha256", "trustc_sha256", "trustc_bytes",
            "targo_sha256", "targo_bytes", "driver_path", "driver_sha256", "driver_bytes",
        }
        if not isinstance(table, dict) or set(table) != fields:
            raise SealRefusal("[development_seal] must contain exactly " + ", ".join(sorted(fields)))
        root = table["root"]
        if (
            not isinstance(root, str)
            or not root.startswith("/")
            or root.startswith("//")
            or root == "/"
            or str(PurePosixPath(root)) != root
            or ".." in PurePosixPath(root).parts
            or "\x00" in root
            or any(ord(char) < 32 or ord(char) == 127 or 0xD800 <= ord(char) <= 0xDFFF for char in root)
            or len(root.encode("utf-8")) > 4096
            or len(PurePosixPath(root).parts) > 128
        ):
            raise SealRefusal("development_seal.root must be a canonical absolute directory")
        host = table["host"]
        if not isinstance(host, str) or len(host) > 128 or HOST.fullmatch(host) is None:
            raise SealRefusal("development_seal.host must be an explicit native host triple")
        for field_name in ("provenance_sha256", "trustc_sha256", "targo_sha256", "driver_sha256"):
            value = table[field_name]
            if not isinstance(value, str) or SHA256.fullmatch(value) is None:
                raise SealRefusal(f"development_seal.{field_name} must be a lowercase SHA256")
        total = 0
        for field_name in ("trustc_bytes", "targo_bytes", "driver_bytes"):
            value = table[field_name]
            if type(value) is not int or not 0 < value <= MAX_ARTIFACT_BYTES:
                raise SealRefusal(f"development_seal.{field_name} must be 1..{MAX_ARTIFACT_BYTES}")
            total += value
        if total > MAX_TOTAL_BYTES:
            raise SealRefusal("development_seal critical artifacts exceed the cumulative byte bound")
        path = table["driver_path"]
        if not isinstance(path, str) or len(path) > 256 or DRIVER_PATH.fullmatch(path) is None:
            raise SealRefusal("development_seal.driver_path must name lib/librustc_driver-*.so or .dylib")
        return cls(
            root, host, table["provenance_sha256"],
            Artifact("bin/trustc", table["trustc_sha256"], table["trustc_bytes"]),
            Artifact("bin/targo", table["targo_sha256"], table["targo_bytes"]),
            Artifact(path, table["driver_sha256"], table["driver_bytes"]),
        )


def _identity(info: os.stat_result) -> tuple[int, ...]:
    return (
        info.st_dev, info.st_ino, info.st_mode, info.st_nlink, info.st_size,
        info.st_mtime_ns, info.st_ctime_ns, info.st_uid, info.st_gid,
    )


def _binding(info: os.stat_result) -> tuple[int, ...]:
    """What a traversed ancestor above the root must keep: the inode its name
    denotes, its type and permissions, and its owner.

    An unrelated entry added to or removed from an ancestor (a shared TMPDIR,
    a home directory) moves its times, size and link count, and binds no path
    to the root. A moved or replaced ancestor changes the inode its name
    denotes, which this still refuses.
    """
    return (info.st_dev, info.st_ino, info.st_mode, info.st_uid, info.st_gid)


class _Owner:
    """One original deadline and bounded, simultaneously held path authority."""

    def __init__(self, clock: Callable[[], float], timeout: float) -> None:
        self.clock = clock
        if not 0 < timeout <= READ_TIMEOUT_SECONDS:
            raise SealRefusal("development seal reader timeout is outside its finite bound")
        self.deadline = clock() + timeout
        self.owned: list[tuple[int, Callable[[os.stat_result], tuple[int, ...]], tuple[int, ...],
                               int | None, str | None]] = []

    def check(self) -> None:
        if self.clock() >= self.deadline:
            raise SealRefusal("development seal reader original deadline expired")

    def open(self, name: str, parent: int | None, *, directory: bool, frozen: bool) -> int:
        self.check()
        flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NONBLOCK
        if directory:
            flags |= os.O_DIRECTORY
        fd = os.open(name, flags, dir_fd=parent)
        try:
            info = os.fstat(fd)
            if directory:
                if not stat.S_ISDIR(info.st_mode):
                    raise SealRefusal(f"{name}: not a directory")
            elif not stat.S_ISREG(info.st_mode):
                raise SealRefusal(f"{name}: not a regular file")
            if frozen and (info.st_mode & 0o022 or info.st_uid != os.geteuid()):
                raise SealRefusal(f"{name}: development-seal input must be owned by this user without group/other write")
            if not directory and info.st_mode & 0o6000:
                raise SealRefusal(f"{name}: critical input must have no set-id bits")
            # Frozen inputs (the root and everything in it) keep their whole identity;
            # the ancestors above the root keep their binding.
            key = _identity if frozen else _binding
            self.owned.append((fd, key, key(info), parent, name))
        except BaseException:
            os.close(fd)
            raise
        self.check()
        return fd

    def alias(self, fd: int, parent: int, name: str) -> None:
        self.check()
        duplicate = os.dup(fd)
        self.owned.append((duplicate, _identity, _identity(os.fstat(duplicate)), parent, name))

    def validate(self) -> None:
        for fd, key, identity, parent, name in self.owned:
            self.check()
            if key(os.fstat(fd)) != identity:
                raise SealRefusal("development-seal owned input changed during admission")
            # Check the name still denotes the held inode, including absolute ancestors.
            if key(os.stat(name, dir_fd=parent, follow_symlinks=False)) != identity:
                raise SealRefusal("development-seal path binding changed during admission")
        self.check()

    def close(self) -> None:
        error = None
        while self.owned:
            fd, _, _, _, _ = self.owned.pop()
            try:
                os.close(fd)
            except OSError as caught:
                error = caught
        if error is not None:
            raise SealRefusal(f"development seal descriptor cleanup failed: {error}")

    def read(self, fd: int, expected_size: int, expected_sha: str, *, retain: bool) -> bytes:
        if os.fstat(fd).st_size != expected_size:
            raise SealRefusal("development-seal input size differs from the explicit identity")
        digest = hashlib.sha256()
        chunks = []
        remaining = expected_size
        while remaining:
            self.check()
            chunk = os.read(fd, min(remaining, READ_BYTES))
            if not chunk:
                raise SealRefusal("development-seal input was truncated")
            digest.update(chunk)
            if retain:
                chunks.append(chunk)
            remaining -= len(chunk)
        self.check()
        if os.read(fd, 1):
            raise SealRefusal("development-seal input grew during admission")
        if digest.hexdigest() != expected_sha:
            raise SealRefusal("development-seal input SHA256 differs from the explicit identity")
        self.check()
        return b"".join(chunks) if retain else b""


def _stamp_fingerprint(fields: Mapping[str, str]) -> str:
    """Validate Trust's versioned recorded facts, without running a source census."""
    version = fields.get("build_stamp:record_version")
    keys = STAMP_BASE_IDENTITY
    domain = ""
    if version == "2":
        for key in ("source_census_scope", "build_stamp:submodule_census_scope"):
            if fields.get(key) != RECURSIVE_CENSUS_SCOPE:
                raise SealRefusal(f"PROVENANCE {key} does not match recursive source scope")
        key = "build_stamp:recursive_submodule_sha256"
        if SHA256.fullmatch(fields.get(key, "")) is None:
            raise SealRefusal(f"PROVENANCE {key} is not a SHA256 fingerprint")
        key = "build_stamp:recursive_submodule_count"
        if re.fullmatch(r"0|[1-9][0-9]{0,18}", fields.get(key, "")) is None:
            raise SealRefusal(f"PROVENANCE {key} is not a bounded census count")
        keys += STAMP_RECURSIVE_IDENTITY
        domain = "trust-build-tree-provenance-v2\n"
    elif version == "1":
        if any("build_stamp:" + key in fields for key in STAMP_RECURSIVE_IDENTITY[:3]):
            raise SealRefusal("PROVENANCE legacy build stamp cannot declare recursive source facts")
        if "source_census_scope" in fields and fields["source_census_scope"] != "top-level-only/v1":
            raise SealRefusal("PROVENANCE legacy build stamp cannot declare another source scope")
    else:
        raise SealRefusal("PROVENANCE build stamp has an unsupported version")
    # Exact domain and field order of scripts/lib/trust_build_provenance.py.
    material = domain + "".join(fields["build_stamp:" + key] + "\n" for key in keys)
    return hashlib.sha256(material.encode("utf-8")).hexdigest()


def _stamp_identity(fields: Mapping[str, str]) -> dict[str, Any]:
    if fields["build_stamp:record_version"] == "1":
        return {"scope": IDENTITY_SCOPE, "build_stamp_scope": "top-level source state only"}
    return {
        "scope": RECURSIVE_IDENTITY_SCOPE,
        "build_stamp_scope": "recorded recursive-worktree source facts; source census not replayed",
        "recorded_source_census_scope": fields["build_stamp:submodule_census_scope"],
        "recorded_recursive_submodule_sha256": fields["build_stamp:recursive_submodule_sha256"],
        "recorded_recursive_submodule_count": int(fields["build_stamp:recursive_submodule_count"]),
    }


def _provenance(raw: bytes, seal: DevelopmentSeal, revision: str) -> dict[str, str]:
    try:
        text = raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise SealRefusal("PROVENANCE is not strict UTF-8") from error
    fields: dict[str, str] = {}
    for line in text.splitlines():
        # promote-toolchain.sh copies build-stamp comments with this prefix.
        if not line or line.startswith("#") or line.startswith("build_stamp:#"):
            continue
        key, separator, value = line.partition("=")
        if not separator or FIELD.fullmatch(key) is None or not value or len(line) > 8192:
            raise SealRefusal("PROVENANCE contains an invalid field")
        if key in fields:
            raise SealRefusal(f"PROVENANCE repeats {key}")
        fields[key] = value
        if len(fields) > 128:
            raise SealRefusal("PROVENANCE exceeds its field bound")
    expected = {
        "provenance_class": "BUILD-STAMPED-CLEAN",
        "seal_name": PurePosixPath(seal.root).name,
        "reported_commit": revision,
        "artifact_driver_name": PurePosixPath(seal.driver.path).name,
        "artifact_driver_sha256": seal.driver.sha256,
        "artifact_driver_bytes": str(seal.driver.size),
        "artifact_bin_trustc_sha256": seal.trustc.sha256,
        "artifact_bin_targo_sha256": seal.targo.sha256,
        "sealtime_repo_head": revision,
        "sealtime_repo_tree": "clean",
        "sealtime_head_matches_binary": "yes",
        "build_stamp:record_kind": "build-stamp",
        "build_stamp:head": revision,
        "build_stamp:tree_state": "clean",
        "build_stamp:dirty_tracked": "0",
        "build_stamp:dirty_untracked": "0",
        "build_stamp:exit_status": "ok",
        "build_stamp:tree_changed_during_build": "no",
        "build_stamp:diff_sha256": hashlib.sha256(b"").hexdigest(),
        "build_stamp:status_sha256": hashlib.sha256(b"").hexdigest(),
    }
    for key, value in expected.items():
        if fields.get(key) != value:
            raise SealRefusal(f"PROVENANCE {key} does not match completed development identity")
    for key in ("build_stamp:submodule_sha256", "build_stamp:tree_fingerprint", "build_stamp:end_tree_fingerprint"):
        if SHA256.fullmatch(fields.get(key, "")) is None:
            raise SealRefusal(f"PROVENANCE {key} is not a SHA256 fingerprint")
    for key in ("build_stamp:started_at", "build_stamp:completed_at"):
        if re.fullmatch(r"0|[1-9][0-9]{0,18}", fields.get(key, "")) is None:
            raise SealRefusal(f"PROVENANCE {key} is not a bounded completion timestamp")
    if int(fields["build_stamp:completed_at"]) < int(fields["build_stamp:started_at"]):
        raise SealRefusal("PROVENANCE build-stamp completion precedes its start")
    if _stamp_fingerprint(fields) != fields["build_stamp:tree_fingerprint"]:
        raise SealRefusal("PROVENANCE build-stamp fingerprint contradicts its recorded source facts")
    if fields["build_stamp:tree_fingerprint"] != fields["build_stamp:end_tree_fingerprint"]:
        raise SealRefusal("PROVENANCE build-stamp source fingerprint changed during build")
    for key in ("reported_rev", "build_stamp:head_short"):
        if key in fields and (len(fields[key]) < 7 or not revision.startswith(fields[key])):
            raise SealRefusal(f"PROVENANCE {key} contradicts the declared revision")
    return fields


def _critical_aliases(
    owner: _Owner, root_fd: int, files: list[tuple[int, Artifact]],
) -> dict[str, list[str]]:
    """Bounded metadata census; noncritical file content has no authority here.

    Keep every directory owner until the final check, so a moved ancestor or
    changed alias binding cannot silently turn an internal link into an external
    one. Do not traverse symlinks. Hardlink counts must equal all discovered
    internal aliases, including the original named input. No links are created.
    """
    inodes: dict[tuple[int, int], tuple[int, Artifact]] = {}
    aliases: dict[str, list[str]] = {}
    for fd, artifact in files:
        info = os.fstat(fd)
        key = (info.st_dev, info.st_ino)
        if not 0 < info.st_nlink <= MAX_CRITICAL_ALIASES:
            raise SealRefusal("development critical artifact exceeds its hardlink bound")
        if key in inodes:
            raise SealRefusal("development critical artifact roles share one inode")
        inodes[key] = (fd, artifact)
        aliases[artifact.path] = []
    entries = 0
    directories = 1
    pending = [(root_fd, "", 0)]
    while pending:
        owner.check()
        directory_fd, prefix, depth = pending.pop()
        with os.scandir(directory_fd) as children:
            for child in children:
                owner.check()
                entries += 1
                if entries > MAX_CENSUS_ENTRIES:
                    raise SealRefusal("development seal metadata census exceeds its entry bound")
                info = child.stat(follow_symlinks=False)
                relative = prefix + child.name
                if stat.S_ISDIR(info.st_mode):
                    directories += 1
                    if directories > MAX_CENSUS_DIRECTORIES or depth >= MAX_CENSUS_DEPTH:
                        raise SealRefusal("development seal metadata census exceeds its directory/depth bound")
                    fd = owner.open(child.name, directory_fd, directory=True, frozen=True)
                    if _identity(os.fstat(fd)) != _identity(info):
                        raise SealRefusal("development seal census directory changed during admission")
                    pending.append((fd, relative + "/", depth + 1))
                elif stat.S_ISREG(info.st_mode):
                    match = inodes.get((info.st_dev, info.st_ino))
                    if match is not None:
                        fd, artifact = match
                        if _identity(info) != _identity(os.fstat(fd)):
                            raise SealRefusal("development critical alias changed during admission")
                        aliases[artifact.path].append(relative)
                        if len(aliases[artifact.path]) > MAX_CRITICAL_ALIASES:
                            raise SealRefusal("development critical artifact exceeds its hardlink bound")
                        owner.alias(fd, directory_fd, child.name)
    for fd, artifact in files:
        if len(aliases[artifact.path]) != os.fstat(fd).st_nlink:
            raise SealRefusal("development critical artifact has unexplained external hardlinks")
        aliases[artifact.path].sort()
    return aliases


def verify(
    seal: DevelopmentSeal,
    revision: str,
    *,
    observed_sysroot: str | None,
    observed_compiler: str | None,
    verbose: Mapping[str, str],
    clock: Callable[[], float] = time.monotonic,
    timeout: float = READ_TIMEOUT_SECONDS,
) -> dict[str, Any]:
    """Establish this explicit development identity, or refuse it without execution.

    Group/other write access and foreign ownership are refused. Owner write is
    part of the sealed product's cooperative observation contract. Every link
    of each critical binary must be accounted inside a bounded root census.
    Writable ancestors outside the root are not artifacts; they are traversed
    with no-follow descriptors, and before acceptance each name must still
    denote the held inode with its mode and owner. This is a
    read-only observation, not protection against a privileged or owning writer.
    """
    owner = _Owner(clock, timeout)
    result = None
    try:
        owner.check()
        if REVISION.fullmatch(revision) is None or revision == "0" * 40:
            raise SealRefusal("development compiler revision is invalid")
        if observed_sysroot != seal.root:
            raise SealRefusal("resolved sysroot differs from the explicit development root")
        if observed_compiler != seal.root + "/bin/trustc":
            raise SealRefusal("resolved compiler is outside the explicit development identity")
        if verbose.get("commit-hash") != revision or verbose.get("host") != seal.host:
            raise SealRefusal("observed compiler commit/host differs from development identity")
        if (
            not all(hasattr(os, flag) for flag in ("O_NOFOLLOW", "O_CLOEXEC", "O_DIRECTORY", "O_NONBLOCK"))
            or os.open not in os.supports_dir_fd
            or os.stat not in os.supports_dir_fd
            or os.stat not in os.supports_follow_symlinks
            or os.scandir not in os.supports_fd
        ):
            raise SealRefusal("development identity requires no-follow descriptor admission")
        parent = owner.open("/", None, directory=True, frozen=False)
        parts = PurePosixPath(seal.root).parts[1:]
        for index, part in enumerate(parts):
            parent = owner.open(part, parent, directory=True, frozen=index == len(parts) - 1)
        root_fd = parent
        provenance_fd = owner.open("PROVENANCE", root_fd, directory=False, frozen=True)
        provenance_size = os.fstat(provenance_fd).st_size
        if not 0 < provenance_size <= MAX_PROVENANCE_BYTES:
            raise SealRefusal("PROVENANCE exceeds its positive bounded size")
        raw = owner.read(provenance_fd, provenance_size, seal.provenance_sha256, retain=True)
        fields = _provenance(raw, seal, revision)
        owner.check()
        directories: dict[str, int] = {}
        files: list[tuple[int, Artifact]] = []
        # Open all critical owners before streaming any artifact.
        for artifact in (seal.trustc, seal.targo, seal.driver):
            directory, name = artifact.path.split("/")
            if directory not in directories:
                directories[directory] = owner.open(directory, root_fd, directory=True, frozen=True)
            files.append((owner.open(name, directories[directory], directory=False, frozen=True), artifact))
        for fd, artifact in files:
            owner.read(fd, artifact.size, artifact.sha256, retain=False)
        aliases = _critical_aliases(
            owner, root_fd,
            [(provenance_fd, Artifact("PROVENANCE", seal.provenance_sha256, provenance_size)), *files],
        )
        owner.validate()
        result = {
            "classification": "development",
            **_stamp_identity(fields),
            "root": seal.root,
            "host": seal.host,
            "compiler_commit": revision,
            "provenance_sha256": seal.provenance_sha256,
            "provenance_aliases": aliases["PROVENANCE"],
            "build_stamp_version": fields["build_stamp:record_version"],
            "artifacts": [
                {
                    "path": artifact.path, "sha256": artifact.sha256, "bytes": artifact.size,
                    "aliases": aliases[artifact.path],
                }
                for artifact in (seal.trustc, seal.targo, seal.driver)
            ],
        }
    except (OSError, UnicodeError) as error:
        raise SealRefusal(f"development-seal input cannot be admitted: {error}") from error
    finally:
        owner.close()
    # Successful admission includes descriptor cleanup under the original grant.
    owner.check()
    assert result is not None
    return result
