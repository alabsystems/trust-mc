#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

"""Atomically update trust-mc's uniform AY revision and package version."""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

if sys.version_info >= (3, 11):
    from tomllib import loads as toml_loads
else:
    from tomli import loads as toml_loads


REVISION = re.compile(r"^[0-9a-f]{40}$")
VERSION = re.compile(r"^[0-9]+\.[0-9]+\.[0-9]+$")
AY_REPOSITORY = "https://github.com/alabsystems/ay.git"


def fail(message: str) -> None:
    raise SystemExit(f"bump-ay-pin: error: {message}")


def dependency_sections(document: dict[str, object]) -> list[dict[str, object]]:
    sections: list[dict[str, object]] = []
    workspace = document.get("workspace")
    if isinstance(workspace, dict):
        dependencies = workspace.get("dependencies")
        if isinstance(dependencies, dict):
            sections.append(dependencies)
    return sections


def restore_file(path: Path, existed: bool, contents: bytes) -> None:
    if existed:
        path.write_bytes(contents)
    elif path.exists():
        path.unlink()


def resolve_trust_cargo(root: Path) -> str:
    resolver = root / "scripts/resolve-trust-tool.sh"
    try:
        result = subprocess.run(
            [str(resolver), "cargo"],
            cwd=root,
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except OSError as error:
        fail(f"cannot execute pinned Trust toolchain resolver: {error}")
    if result.returncode != 0:
        detail = result.stderr.strip() or f"exit {result.returncode}"
        fail(f"cannot resolve pinned Trust cargo: {detail}")
    cargo = result.stdout.strip()
    if not cargo or not Path(cargo).is_file() or not os.access(cargo, os.X_OK):
        fail(f"resolver returned a missing Cargo executable: {cargo or '<none>'}")
    return cargo


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("revision")
    parser.add_argument("version")
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    if not REVISION.fullmatch(args.revision) or args.revision == "0" * 40:
        fail("revision must be one nonzero full 40-character lowercase SHA")
    if not VERSION.fullmatch(args.version):
        fail("version must be MAJOR.MINOR.PATCH")

    root = args.root.resolve()
    manifest = root / "Cargo.toml"
    lockfile = root / "Cargo.lock"
    cargo = resolve_trust_cargo(root)
    original = manifest.read_text(encoding="utf-8")
    lock_existed = lockfile.exists()
    original_lock = lockfile.read_bytes() if lock_existed else b""
    document = toml_loads(original)
    specs: list[tuple[str, dict[str, object]]] = []
    for dependencies in dependency_sections(document):
        for alias, raw_spec in dependencies.items():
            if not isinstance(raw_spec, dict):
                continue
            package = raw_spec.get("package", alias)
            if raw_spec.get("git") == AY_REPOSITORY or (
                isinstance(package, str) and (package == "ay" or package.startswith("ay-"))
            ):
                specs.append((alias, raw_spec))
    if not specs:
        fail("no AY workspace dependency declarations found")

    revisions = {spec.get("rev") for _, spec in specs}
    versions = {spec.get("version") for _, spec in specs}
    if len(revisions) != 1 or not all(isinstance(value, str) for value in revisions):
        fail(f"AY dependency revisions are not uniform: {sorted(map(str, revisions))}")
    if len(versions) != 1 or not all(isinstance(value, str) for value in versions):
        fail(f"AY dependency versions are not uniform: {sorted(map(str, versions))}")
    old_revision = next(iter(revisions))
    old_version = next(iter(versions))
    assert isinstance(old_revision, str)
    assert isinstance(old_version, str)

    updated = original
    for alias, spec in specs:
        if spec.get("git") != AY_REPOSITORY:
            fail(f"workspace.dependencies.{alias} must use {AY_REPOSITORY}")
        line = re.compile(
            rf'^(?P<prefix>{re.escape(alias)}\s*=\s*\{{)(?P<body>[^}}]*)(?P<suffix>\}}\s*(?:#.*)?)$',
            re.MULTILINE,
        )

        def replace(match: re.Match[str]) -> str:
            body = match.group("body")
            body, version_count = re.subn(
                rf'(\bversion\s*=\s*)"{re.escape(old_version)}"',
                rf'\g<1>"{args.version}"',
                body,
                count=1,
            )
            body, revision_count = re.subn(
                rf'(\brev\s*=\s*)"{re.escape(old_revision)}"',
                rf'\g<1>"{args.revision}"',
                body,
                count=1,
            )
            if version_count != 1 or revision_count != 1:
                fail(f"cannot rewrite exact revision/version for {alias}")
            return f"{match.group('prefix')}{body}{match.group('suffix')}"

        updated, count = line.subn(replace, updated, count=1)
        if count != 1:
            fail(f"cannot locate workspace.dependencies.{alias}")

    if updated == original:
        print(f"bump-ay-pin: already at {args.revision} ({args.version})")
        return 0

    manifest.write_text(updated, encoding="utf-8")
    try:
        subprocess.run(
            [sys.executable, str(root / "scripts/check_first_party_git_pins.py"), str(root), "ay"],
            cwd=root,
            check=True,
        )
        # Refresh first: --locked metadata cannot update an old-version lockfile,
        # so using it as the first Cargo operation made every semver bump fail.
        # Cargo's normal resolver updates only what the edited manifest requires;
        # the original lockfile is restored below if any subsequent authority
        # check rejects the result.
        subprocess.run(
            [cargo, "metadata", "--format-version", "1"],
            cwd=root,
            check=True,
            stdout=subprocess.DEVNULL,
        )
        subprocess.run(
            [
                sys.executable,
                str(root / "scripts/ay_manifest_pin.py"),
                "--locked",
                str(root),
            ],
            cwd=root,
            check=True,
            stdout=subprocess.DEVNULL,
        )
        subprocess.run(
            [cargo, "metadata", "--locked", "--format-version", "1"],
            cwd=root,
            check=True,
            stdout=subprocess.DEVNULL,
        )
    except (OSError, subprocess.CalledProcessError):
        manifest.write_text(original, encoding="utf-8")
        restore_file(lockfile, lock_existed, original_lock)
        fail("validation failed; restored Cargo.toml and Cargo.lock")

    print(
        f"bump-ay-pin: updated {len(specs)} declarations: "
        f"{old_revision} ({old_version}) -> {args.revision} ({args.version})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
