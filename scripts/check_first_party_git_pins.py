#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

"""Semantically audit exact first-party Git pins in tracked Cargo manifests."""

from __future__ import annotations

import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

if sys.version_info >= (3, 11):
    from tomllib import TOMLDecodeError, loads as toml_loads
else:
    from tomli import TOMLDecodeError, loads as toml_loads


@dataclass(frozen=True)
class Family:
    repository: str
    packages: frozenset[str]

    @property
    def url(self) -> str:
        return f"https://github.com/alabsystems/{self.repository}.git"


FAMILIES = {
    "ay": Family(
        "ay",
        frozenset(
            {
                "ay",
                "ay-bindings",
                "ay-chc",
                "ay-core",
                "ay-dpll",
                "ay-encode",
                "ay-frontend",
                "ay-sys",
            }
        ),
    ),
    "clean": Family(
        "clean",
        frozenset({"clean-kernel", "clean-mathverse", "clean-olean"}),
    ),
    "trust-ir": Family("trust-ir", frozenset({"trust-ir", "trust-ir-build"})),
    "trust-vc": Family("trust-vc", frozenset({"trust-vc-merge-contract"})),
}

REVISION = re.compile(r"^[0-9a-f]{40}$")
DEPENDENCY_TABLES = ("dependencies", "dev-dependencies", "build-dependencies")
PATH_EXCEPTIONS = {
    (
        "ay",
        Path("proofs/ay_pb_crate_link/Cargo.toml"),
        "dependencies",
        "ay-pb",
        "ay-pb",
    ): "../../../ay/crates/ay-pb",
}


@dataclass(frozen=True)
class PinAudit:
    revision: str
    declarations: int


def _tracked_manifests(root: Path) -> list[Path]:
    try:
        raw = subprocess.check_output(
            ["git", "-C", str(root), "ls-files", "-z", "--", "*Cargo.toml"],
            stderr=subprocess.DEVNULL,
        )
    except (OSError, subprocess.CalledProcessError):
        return sorted(root.rglob("Cargo.toml"))
    return [root / name.decode() for name in raw.split(b"\0") if name]


def _dependency_sections(
    document: dict[str, Any],
) -> Iterable[tuple[str, dict[str, Any]]]:
    for table in DEPENDENCY_TABLES:
        value = document.get(table)
        if isinstance(value, dict):
            yield table, value

    workspace = document.get("workspace")
    if isinstance(workspace, dict):
        value = workspace.get("dependencies")
        if isinstance(value, dict):
            yield "workspace.dependencies", value

    targets = document.get("target")
    if isinstance(targets, dict):
        for target, target_document in targets.items():
            if not isinstance(target_document, dict):
                continue
            for table in DEPENDENCY_TABLES:
                value = target_document.get(table)
                if isinstance(value, dict):
                    yield f"target.{target}.{table}", value


def _url_repository(url: object) -> str | None:
    if not isinstance(url, str):
        return None
    normalized = url.removesuffix("/").removesuffix(".git")
    for repository in FAMILIES:
        if normalized.endswith(f"/alabsystems/{repository}") or normalized.endswith(
            f":alabsystems/{repository}"
        ):
            return repository
    return None


def _package_repository(package: str) -> str | None:
    if package == "ay" or package.startswith("ay-"):
        return "ay"
    if package == "trust-ir" or package.startswith("trust-ir-"):
        return "trust-ir"
    if package == "trust-vc" or package.startswith("trust-vc-"):
        return "trust-vc"
    if package == "clean" or package.startswith("clean-"):
        return "clean"
    return None


def audit_repository(root: Path, repository: str) -> PinAudit:
    family = FAMILIES[repository]
    revisions: list[str] = []
    observed_packages: set[str] = set()
    errors: list[str] = []

    for manifest in _tracked_manifests(root):
        relative = manifest.relative_to(root)
        try:
            document = toml_loads(manifest.read_text(encoding="utf-8"))
        except (OSError, TOMLDecodeError) as error:
            errors.append(f"{relative}: cannot inspect manifest: {error}")
            continue

        for table, dependencies in _dependency_sections(document):
            for alias, raw_specification in dependencies.items():
                specification = (
                    raw_specification if isinstance(raw_specification, dict) else {}
                )
                package = specification.get("package", alias)
                if not isinstance(package, str):
                    errors.append(f"{relative}: {table}.{alias} has a non-string package")
                    continue
                named_family_member = _package_repository(package) == repository
                url_family = _url_repository(specification.get("git"))
                if not named_family_member and url_family != repository:
                    continue

                location = f"{relative}: {table}.{alias} ({package})"
                if specification.get("workspace") is True:
                    selectors = {
                        key
                        for key in ("git", "rev", "branch", "tag", "path")
                        if key in specification
                    }
                    if selectors:
                        errors.append(
                            f"{location} mixes workspace inheritance with {sorted(selectors)}"
                        )
                    continue

                path_exception = PATH_EXCEPTIONS.get(
                    (repository, relative, table, alias, package)
                )
                if path_exception is not None and specification.get("path") == path_exception:
                    conflicting = {
                        key
                        for key in ("git", "rev", "branch", "tag", "workspace")
                        if key in specification
                    }
                    if conflicting:
                        errors.append(
                            f"{location} mixes the audited sibling path with {sorted(conflicting)}"
                        )
                    continue

                if package in family.packages:
                    observed_packages.add(package)
                if specification.get("git") != family.url:
                    errors.append(
                        f"{location} must use canonical Git source {family.url!r}"
                    )
                    continue
                forbidden = [
                    selector
                    for selector in ("branch", "tag", "path")
                    if selector in specification
                ]
                if forbidden:
                    errors.append(
                        f"{location} mixes exact Git authority with {forbidden}"
                    )
                revision = specification.get("rev")
                if (
                    not isinstance(revision, str)
                    or not REVISION.fullmatch(revision)
                    or revision == "0" * 40
                ):
                    errors.append(
                        f"{location} must use one nonzero full 40-character lowercase rev"
                    )
                    continue
                revisions.append(revision)

    missing = sorted(family.packages - observed_packages)
    if missing:
        errors.append(
            f"tracked manifests are missing direct {repository} declarations for {missing}"
        )
    unique_revisions = sorted(set(revisions))
    if len(unique_revisions) != 1:
        errors.append(
            f"{repository} declarations must use one revision; found {unique_revisions}"
        )
    if errors:
        raise ValueError("\n".join(errors))
    return PinAudit(unique_revisions[0], len(revisions))


def main(argv: list[str]) -> int:
    if len(argv) != 3 or argv[2] not in FAMILIES:
        choices = "|".join(FAMILIES)
        print(
            f"usage: {Path(argv[0]).name} <workspace-root> <{choices}>",
            file=sys.stderr,
        )
        return 2
    root = Path(argv[1]).resolve()
    repository = argv[2]
    try:
        audit = audit_repository(root, repository)
    except ValueError as error:
        for finding in str(error).splitlines():
            print(f"check-first-party-git-pins: error: {finding}", file=sys.stderr)
        return 1
    print(audit.revision, audit.declarations)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
