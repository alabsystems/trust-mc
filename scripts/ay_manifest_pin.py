# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

if sys.version_info >= (3, 11):
    import tomllib
else:
    import tomli as tomllib


AY_PIN_RE = re.compile(r"[0-9a-fA-F]{40}")
_AY_GIT_REPO = "https://github.com/alabsystems/ay"
_AUTHORITATIVE_AY_PIN_DEP = "ay-chc"
_EXACT_VERSION_RE = re.compile(r"[0-9]+\.[0-9]+\.[0-9]+")


def _canonical_git_url(value: str) -> str:
    return value.rstrip("/").removesuffix(".git")


def _is_ay_package(name: str) -> bool:
    return name == "ay" or name.startswith("ay-")


def _is_ay_git_dependency(name: str, spec: Any) -> bool:
    if not isinstance(spec, dict):
        return False
    git_url = spec.get("git")
    if not isinstance(git_url, str):
        return False
    if _canonical_git_url(git_url) != _AY_GIT_REPO:
        return False
    package = spec.get("package", name)
    return isinstance(package, str) and _is_ay_package(package)


def _read_root_manifest(repo_root: Path) -> tuple[Path, dict[str, object]]:
    manifest_path = repo_root / "Cargo.toml"
    try:
        manifest = tomllib.loads(manifest_path.read_text(encoding="utf-8"))
    except OSError as err:
        raise ValueError(f"{manifest_path}: failed to read Cargo.toml: {err}") from err
    except tomllib.TOMLDecodeError as err:
        raise ValueError(f"{manifest_path}: failed to parse Cargo.toml: {err}") from err
    if not isinstance(manifest, dict):
        raise ValueError(f"{manifest_path}: expected Cargo.toml to parse as an object")
    return manifest_path, manifest


def expected_ay_pin_from_cargo_toml(repo_root: Path) -> str:
    """Return the authoritative 40-character AY rev from root ``Cargo.toml``."""
    manifest_path, manifest = _read_root_manifest(repo_root)
    workspace = manifest.get("workspace")
    if not isinstance(workspace, dict):
        raise ValueError(f"{manifest_path}: missing [workspace]")
    dependencies = workspace.get("dependencies")
    if not isinstance(dependencies, dict):
        raise ValueError(f"{manifest_path}: missing [workspace.dependencies]")

    pins: dict[str, str] = {}
    for name, spec in dependencies.items():
        if not isinstance(name, str) or not _is_ay_git_dependency(name, spec):
            continue
        rev = spec.get("rev") if isinstance(spec, dict) else None
        if not isinstance(rev, str) or AY_PIN_RE.fullmatch(rev) is None:
            raise ValueError(
                f"{manifest_path}: workspace dependency {name!r} rev {rev!r} "
                "is not a 40-character hex pin"
            )
        pins[name] = rev

    expected_pin = pins.get(_AUTHORITATIVE_AY_PIN_DEP)
    if expected_pin is None:
        raise ValueError(
            f"{manifest_path}: missing {_AUTHORITATIVE_AY_PIN_DEP!r} AY git dependency pin"
        )

    mismatched = {
        name: pin for name, pin in pins.items()
        if pin != expected_pin
    }
    if mismatched:
        details = ", ".join(f"{name}={pin}" for name, pin in sorted(mismatched.items()))
        raise ValueError(
            f"{manifest_path}: AY workspace dependency rev mismatch; "
            f"{_AUTHORITATIVE_AY_PIN_DEP}={expected_pin}, {details}"
        )
    return expected_pin


def _workspace_ay_dependencies(
    repo_root: Path,
) -> tuple[Path, dict[str, object], dict[str, tuple[str, str]]]:
    """Return package -> (version, rev) for canonical AY workspace dependencies."""
    manifest_path, manifest = _read_root_manifest(repo_root)
    workspace = manifest.get("workspace")
    if not isinstance(workspace, dict):
        raise ValueError(f"{manifest_path}: missing [workspace]")
    dependencies = workspace.get("dependencies")
    if not isinstance(dependencies, dict):
        raise ValueError(f"{manifest_path}: missing [workspace.dependencies]")

    result: dict[str, tuple[str, str]] = {}
    for alias, raw_spec in dependencies.items():
        if not isinstance(alias, str) or not isinstance(raw_spec, dict):
            continue
        package = raw_spec.get("package", alias)
        git_url = raw_spec.get("git")
        names_ay = isinstance(package, str) and _is_ay_package(package)
        points_at_ay = (
            isinstance(git_url, str)
            and _canonical_git_url(git_url) == _AY_GIT_REPO
        )
        if not names_ay and not points_at_ay:
            continue
        if not names_ay:
            raise ValueError(
                f"{manifest_path}: workspace dependency {alias!r} points at AY "
                f"but package {package!r} is not an AY package"
            )
        if not points_at_ay:
            raise ValueError(
                f"{manifest_path}: workspace dependency {alias!r} for {package!r} "
                "does not use the canonical AY Git repository"
            )
        revision = raw_spec.get("rev")
        version = raw_spec.get("version")
        if not isinstance(revision, str) or AY_PIN_RE.fullmatch(revision) is None:
            raise ValueError(
                f"{manifest_path}: workspace dependency {alias!r} rev {revision!r} "
                "is not a 40-character hex pin"
            )
        if not isinstance(version, str) or _EXACT_VERSION_RE.fullmatch(version) is None:
            raise ValueError(
                f"{manifest_path}: workspace dependency {alias!r} version {version!r} "
                "is not an exact MAJOR.MINOR.PATCH version"
            )
        previous = result.get(package)
        authority = (version, revision.lower())
        if previous is not None and previous != authority:
            raise ValueError(
                f"{manifest_path}: AY package {package!r} has conflicting "
                f"workspace authorities {previous!r} and {authority!r}"
            )
        result[package] = authority

    if _AUTHORITATIVE_AY_PIN_DEP not in result:
        raise ValueError(
            f"{manifest_path}: missing {_AUTHORITATIVE_AY_PIN_DEP!r} AY git dependency pin"
        )
    expected_pin = result[_AUTHORITATIVE_AY_PIN_DEP][1]
    mismatched = {
        name: revision
        for name, (_, revision) in result.items()
        if revision != expected_pin
    }
    if mismatched:
        details = ", ".join(
            f"{name}={revision}" for name, revision in sorted(mismatched.items())
        )
        raise ValueError(
            f"{manifest_path}: AY workspace dependency rev mismatch; "
            f"{_AUTHORITATIVE_AY_PIN_DEP}={expected_pin}, {details}"
        )
    return manifest_path, manifest, result


def _git_output(repo: Path, *args: str) -> str:
    try:
        return subprocess.check_output(
            ["git", "-C", str(repo), *args],
            stderr=subprocess.DEVNULL,
            text=True,
        ).strip()
    except (OSError, subprocess.CalledProcessError) as err:
        command = " ".join(("git", *args))
        raise ValueError(f"{repo}: failed sibling authority check `{command}`") from err


def _canonical_ay_remote_present(sibling_root: Path) -> bool:
    remotes = _git_output(sibling_root, "remote").splitlines()
    for remote in remotes:
        try:
            url = _git_output(sibling_root, "remote", "get-url", remote)
        except ValueError:
            continue
        normalized = url.rstrip("/").removesuffix(".git")
        if normalized in {
            _AY_GIT_REPO,
            "ssh://git@github.com/alabsystems/ay",
            "git@github.com:alabsystems/ay",
        }:
            return True
    return False


def _workspace_package_version(document: dict[str, object], location: str) -> str:
    workspace = document.get("workspace")
    workspace_package = workspace.get("package") if isinstance(workspace, dict) else None
    version = (
        workspace_package.get("version")
        if isinstance(workspace_package, dict)
        else None
    )
    if not isinstance(version, str) or _EXACT_VERSION_RE.fullmatch(version) is None:
        raise ValueError(f"{location}: missing exact [workspace.package] version")
    return version


def _package_identity(
    document: dict[str, object],
    location: str,
    workspace_version: str,
) -> tuple[str, str] | None:
    package = document.get("package")
    if not isinstance(package, dict):
        return None
    name = package.get("name")
    version = package.get("version")
    if isinstance(version, dict) and version.get("workspace") is True:
        version = workspace_version
    if not isinstance(name, str) or not isinstance(version, str):
        raise ValueError(f"{location}: package name/version is not a string")
    return name, version


def _committed_ay_package_catalog(sibling_root: Path) -> dict[str, tuple[str, Path]]:
    """Read AY package identities from HEAD, then verify the path manifests agree."""
    try:
        committed_root = tomllib.loads(_git_output(sibling_root, "show", "HEAD:Cargo.toml"))
        path_root = tomllib.loads(
            (sibling_root / "Cargo.toml").read_text(encoding="utf-8")
        )
    except OSError as err:
        raise ValueError(f"{sibling_root}/Cargo.toml: failed to read: {err}") from err
    except tomllib.TOMLDecodeError as err:
        raise ValueError(f"{sibling_root}/Cargo.toml: failed to parse: {err}") from err
    committed_workspace_version = _workspace_package_version(
        committed_root, f"{sibling_root}@HEAD:Cargo.toml"
    )
    path_workspace_version = _workspace_package_version(
        path_root, str(sibling_root / "Cargo.toml")
    )
    if path_workspace_version != committed_workspace_version:
        raise ValueError(
            f"{sibling_root}/Cargo.toml: path workspace version {path_workspace_version} "
            f"differs from pinned AY HEAD version {committed_workspace_version}"
        )
    names = _git_output(sibling_root, "ls-tree", "-r", "--name-only", "HEAD")
    result: dict[str, tuple[str, Path]] = {}
    for relative_text in names.splitlines():
        if not relative_text.endswith("Cargo.toml"):
            continue
        try:
            committed = _git_output(sibling_root, "show", f"HEAD:{relative_text}")
            document = tomllib.loads(committed)
        except tomllib.TOMLDecodeError as err:
            raise ValueError(
                f"{sibling_root}@HEAD:{relative_text}: invalid Cargo.toml: {err}"
            ) from err
        identity = _package_identity(
            document,
            f"{sibling_root}@HEAD:{relative_text}",
            committed_workspace_version,
        )
        if identity is None or not _is_ay_package(identity[0]):
            continue
        package, version = identity
        relative = Path(relative_text)
        previous = result.get(package)
        if previous is not None:
            raise ValueError(
                f"{sibling_root}@HEAD: duplicate AY package {package!r} in "
                f"{previous[1]} and {relative}"
            )
        path_manifest = sibling_root / relative
        try:
            path_document = tomllib.loads(path_manifest.read_text(encoding="utf-8"))
        except OSError as err:
            raise ValueError(f"{path_manifest}: failed to read patched package: {err}") from err
        except tomllib.TOMLDecodeError as err:
            raise ValueError(f"{path_manifest}: failed to parse patched package: {err}") from err
        path_identity = _package_identity(
            path_document, str(path_manifest), path_workspace_version
        )
        if path_identity != identity:
            raise ValueError(
                f"{path_manifest}: path package identity {path_identity!r} differs from "
                f"pinned AY HEAD identity {identity!r}"
            )
        result[package] = (version, relative)
    return result


def _validate_sourceless_ay_authority(
    repo_root: Path,
    manifest_path: Path,
    manifest: dict[str, object],
    dependencies: dict[str, tuple[str, str]],
    expected_pin: str,
    sourceless: dict[str, str],
) -> None:
    patches = manifest.get("patch")
    if not isinstance(patches, dict):
        raise ValueError(
            f"{manifest_path}: source-less AY lock entries require a canonical "
            "[patch] table"
        )
    ay_tables = [
        value
        for source, value in patches.items()
        if isinstance(source, str)
        and _canonical_git_url(source) == _AY_GIT_REPO
        and isinstance(value, dict)
    ]
    if len(ay_tables) != 1:
        raise ValueError(
            f"{manifest_path}: source-less AY lock entries require exactly one "
            "canonical AY [patch] table"
        )
    patch_table = ay_tables[0]
    sibling_root = (repo_root / ".." / "ay").resolve()
    try:
        git_root = Path(_git_output(sibling_root, "rev-parse", "--show-toplevel")).resolve()
    except ValueError as err:
        raise ValueError(
            f"{sibling_root}: source-less AY lock entries require a Git sibling checkout"
        ) from err
    if git_root != sibling_root:
        raise ValueError(
            f"{sibling_root}: AY sibling Git root is {git_root}, expected the exact sibling"
        )
    checkout_pin = _git_output(sibling_root, "rev-parse", "HEAD").lower()
    if checkout_pin != expected_pin:
        raise ValueError(
            f"{sibling_root}: AY sibling HEAD {checkout_pin} differs from manifest "
            f"pin {expected_pin}"
        )
    if not _canonical_ay_remote_present(sibling_root):
        raise ValueError(
            f"{sibling_root}: AY sibling has no canonical alabsystems/ay remote"
        )

    patched: dict[str, Path] = {}
    for alias, raw_spec in patch_table.items():
        if not isinstance(alias, str) or not isinstance(raw_spec, dict):
            raise ValueError(f"{manifest_path}: AY patch {alias!r} is not a table")
        package = raw_spec.get("package", alias)
        path = raw_spec.get("path")
        if not isinstance(package, str) or not _is_ay_package(package):
            raise ValueError(
                f"{manifest_path}: AY patch {alias!r} has invalid package {package!r}"
            )
        if not isinstance(path, str):
            raise ValueError(
                f"{manifest_path}: AY patch {alias!r} must use the sibling path"
            )
        conflicting = {
            key for key in ("git", "rev", "branch", "tag", "registry") if key in raw_spec
        }
        if conflicting:
            raise ValueError(
                f"{manifest_path}: AY patch {alias!r} mixes path authority with "
                f"{sorted(conflicting)}"
            )
        resolved = (repo_root / path).resolve()
        expected_path = (sibling_root / "crates" / package).resolve()
        if resolved != expected_path:
            raise ValueError(
                f"{manifest_path}: AY patch {alias!r} resolves to {resolved}, "
                f"expected {expected_path}"
            )
        if package in patched:
            raise ValueError(f"{manifest_path}: duplicate AY patch for {package!r}")
        patched[package] = resolved

    for package in sorted(set(dependencies).intersection(sourceless)):
        if package not in patched:
            raise ValueError(
                f"{manifest_path}: source-less direct AY package {package!r} has no "
                "exact sibling patch"
            )

    catalog = _committed_ay_package_catalog(sibling_root)
    for package, patched_path in sorted(patched.items()):
        identity = catalog.get(package)
        if identity is None:
            raise ValueError(
                f"{manifest_path}: AY patch {package!r} is absent from "
                f"{sibling_root}@{expected_pin}"
            )
        sibling_version, relative_manifest = identity
        catalog_path = (sibling_root / relative_manifest).parent.resolve()
        if patched_path != catalog_path:
            raise ValueError(
                f"{manifest_path}: AY patch {package!r} resolves to {patched_path}, "
                f"but pinned AY identifies it at {catalog_path}"
            )
        direct = dependencies.get(package)
        if direct is not None and direct[0] != sibling_version:
            raise ValueError(
                f"{manifest_path}: AY dependency {package!r} version {direct[0]} "
                f"differs from sibling version {sibling_version}"
            )
    for package, locked_version in sorted(sourceless.items()):
        identity = catalog.get(package)
        if identity is None:
            raise ValueError(
                f"Cargo.lock: source-less AY package {package!r} is absent from "
                f"{sibling_root}@{expected_pin}"
            )
        sibling_version, _ = identity
        if locked_version != sibling_version:
            raise ValueError(
                f"Cargo.lock: source-less AY package {package!r} version "
                f"{locked_version} differs from sibling version {sibling_version}"
            )


def expected_ay_pin_from_locked_workspace(repo_root: Path) -> str:
    """Return the authoritative AY rev after Cargo.toml/Cargo.lock consistency checks."""
    manifest_path, manifest, dependencies = _workspace_ay_dependencies(repo_root)
    expected_pin = dependencies[_AUTHORITATIVE_AY_PIN_DEP][1]
    lock_path, lockfile = _read_lockfile(repo_root)

    packages = lockfile.get("package")
    if not isinstance(packages, list):
        raise ValueError(f"{lock_path}: missing package list")

    lock_pins: dict[str, str] = {}
    lock_versions: dict[str, str] = {}
    sourceless: dict[str, str] = {}
    for package in packages:
        if not isinstance(package, dict):
            continue
        name = package.get("name")
        version = package.get("version")
        source = package.get("source")
        if not isinstance(name, str) or not _is_ay_package(name):
            continue
        if not isinstance(version, str) or _EXACT_VERSION_RE.fullmatch(version) is None:
            raise ValueError(
                f"{lock_path}: AY package {name!r} has invalid version {version!r}"
            )
        if name in lock_versions:
            raise ValueError(f"{lock_path}: duplicate AY package {name!r}")
        lock_versions[name] = version
        if source is None:
            if "checksum" in package:
                raise ValueError(
                    f"{lock_path}: source-less AY package {name!r} unexpectedly has a checksum"
                )
            sourceless[name] = version
            continue
        if not isinstance(source, str) or not source.startswith("git+"):
            raise ValueError(
                f"{lock_path}: AY package {name!r} has unauthorised source {source!r}"
            )
        if _canonical_git_url(source.split("?", 1)[0].removeprefix("git+")) != _AY_GIT_REPO:
            raise ValueError(
                f"{lock_path}: AY package {name!r} has non-canonical source {source!r}"
            )

        lock_match = re.search(r"#([0-9a-fA-F]{40})$", source)
        query_match = re.search(r"[?&]rev=([0-9a-fA-F]{40})(?:[&#]|$)", source)
        if lock_match is None or query_match is None:
            raise ValueError(
                f"{lock_path}: package {name!r} source {source!r} is missing a full AY rev"
            )
        locked_commit = lock_match.group(1).lower()
        requested_rev = query_match.group(1).lower()
        if locked_commit != requested_rev:
            raise ValueError(
                f"{lock_path}: package {name!r} requested rev {requested_rev} "
                f"but locked commit is {locked_commit}"
            )
        lock_pins[name] = locked_commit

    if sourceless:
        _validate_sourceless_ay_authority(
            repo_root,
            manifest_path,
            manifest,
            dependencies,
            expected_pin,
            sourceless,
        )

    if _AUTHORITATIVE_AY_PIN_DEP not in lock_pins and _AUTHORITATIVE_AY_PIN_DEP not in sourceless:
        raise ValueError(
            f"{lock_path}: missing locked {_AUTHORITATIVE_AY_PIN_DEP!r} AY package"
        )

    mismatched = {
        name: pin for name, pin in lock_pins.items()
        if pin != expected_pin
    }
    if mismatched:
        details = ", ".join(f"{name}={pin}" for name, pin in sorted(mismatched.items()))
        raise ValueError(
            f"Cargo.toml/Cargo.lock AY pin mismatch; "
            f"Cargo.toml {_AUTHORITATIVE_AY_PIN_DEP}={expected_pin}, Cargo.lock {details}"
        )
    for package, (manifest_version, _) in sorted(dependencies.items()):
        locked_version = lock_versions.get(package)
        if locked_version is None:
            raise ValueError(
                f"{lock_path}: missing direct AY package {package!r} from locked graph"
            )
        if locked_version != manifest_version:
            raise ValueError(
                f"Cargo.toml/Cargo.lock AY version mismatch for {package!r}: "
                f"Cargo.toml {manifest_version}, Cargo.lock {locked_version}"
            )
    return expected_pin


def _read_lockfile(repo_root: Path) -> tuple[Path, dict[str, object]]:
    lock_path = repo_root / "Cargo.lock"
    try:
        lockfile = tomllib.loads(lock_path.read_text(encoding="utf-8"))
    except OSError as err:
        raise ValueError(f"{lock_path}: failed to read Cargo.lock: {err}") from err
    except tomllib.TOMLDecodeError as err:
        raise ValueError(f"{lock_path}: failed to parse Cargo.lock: {err}") from err
    if not isinstance(lockfile, dict):
        raise ValueError(f"{lock_path}: expected Cargo.lock to parse as an object")
    return lock_path, lockfile


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo_root", nargs="?", default=".", type=Path)
    parser.add_argument(
        "--locked",
        action="store_true",
        help="also validate Cargo.lock AY entries against the workspace pin",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        if args.locked:
            pin = expected_ay_pin_from_locked_workspace(args.repo_root)
        else:
            pin = expected_ay_pin_from_cargo_toml(args.repo_root)
    except ValueError as err:
        sys.stderr.write(f"ERROR: {err}\n")
        return 1
    sys.stdout.write(f"{pin}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
