#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

"""Reject host-absolute ``path`` values in tracked Cargo manifests."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path, PureWindowsPath
from typing import Any, Iterable

if sys.version_info >= (3, 11):
    from tomllib import TOMLDecodeError, loads as toml_loads
else:
    from tomli import TOMLDecodeError, loads as toml_loads


def _tracked_manifests(root: Path) -> list[Path]:
    """Return tracked Cargo manifests, with a filesystem fallback for fixtures."""
    try:
        raw = subprocess.check_output(
            ["git", "-C", str(root), "ls-files", "-z", "--", "*Cargo.toml"],
            stderr=subprocess.DEVNULL,
        )
    except (OSError, subprocess.CalledProcessError):
        return sorted(root.rglob("Cargo.toml"))
    return [root / name.decode() for name in raw.split(b"\0") if name]


def _path_values(
    value: Any, key_path: tuple[str, ...] = ()
) -> Iterable[tuple[tuple[str, ...], str]]:
    if isinstance(value, dict):
        for key, child in value.items():
            child_path = (*key_path, str(key))
            if key == "path" and isinstance(child, str):
                yield child_path, child
            yield from _path_values(child, child_path)
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from _path_values(child, (*key_path, str(index)))


def _is_absolute_any_platform(raw: str) -> bool:
    return Path(raw).is_absolute() or PureWindowsPath(raw).is_absolute()


def find_absolute_manifest_paths(root: Path) -> list[str]:
    findings: list[str] = []
    for manifest in _tracked_manifests(root):
        try:
            document = toml_loads(manifest.read_text(encoding="utf-8"))
        except (OSError, TOMLDecodeError) as error:
            findings.append(
                f"{manifest.relative_to(root)}: cannot inspect manifest: {error}"
            )
            continue
        for key_path, raw_path in _path_values(document):
            if _is_absolute_any_platform(raw_path):
                dotted = ".".join(key_path)
                findings.append(
                    f"{manifest.relative_to(root)}: {dotted} uses host-absolute path {raw_path!r}"
                )
    return findings


def main(argv: list[str]) -> int:
    default_root = Path(__file__).resolve().parent.parent
    root = Path(argv[1] if len(argv) > 1 else default_root).resolve()
    findings = find_absolute_manifest_paths(root)
    if findings:
        for finding in findings:
            print(f"check-portable-manifests: error: {finding}", file=sys.stderr)
        return 1
    print("check-portable-manifests: ok: tracked Cargo manifests use portable paths")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
