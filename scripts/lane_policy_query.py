#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

from __future__ import annotations

import pathlib
import sys
import tomllib
from typing import Any


def normalize(path: str) -> str:
    value = path.replace("\\", "/").strip()
    while value.startswith("./"):
        value = value[2:]
    return value


def clean_text(value: Any) -> str:
    return str(value).replace("\t", " ").replace("\n", " ").strip()


def write_stdout(value: str) -> None:
    sys.stdout.write(f"{value}\n")


def fail(message: str) -> int:
    sys.stderr.write(f"{message}\n")
    return 2


def default_result() -> tuple[str, str, str, str]:
    return ("chc", "", "", "")


def load_policy(policy_file: pathlib.Path) -> list[dict[str, Any]] | None:
    if not policy_file.exists():
        return None
    with policy_file.open("rb") as f:
        data = tomllib.load(f)
    entries = data.get("entry", [])
    if not isinstance(entries, list):
        raise ValueError("lane policy parse failed: top-level 'entry' must be an array")
    return [entry for entry in entries if isinstance(entry, dict)]


def validated_fields(entry: dict[str, Any], idx: int) -> tuple[str, str, str | None, str, Any, Any]:
    path = entry.get("path")
    lane = entry.get("lane")
    harness = entry.get("harness")
    unwind = entry.get("unwind")
    reason = entry.get("reason", "")
    issue = entry.get("issue", "")

    if not isinstance(path, str) or not path.strip():
        raise ValueError(f"lane policy parse failed: entry[{idx}] path must be non-empty string")
    if not isinstance(lane, str):
        raise ValueError(f"lane policy parse failed: entry[{idx}] lane must be string")
    lane = lane.strip().lower()
    if lane not in {"chc", "bmc"}:
        raise ValueError(f"lane policy parse failed: entry[{idx}] lane must be 'chc' or 'bmc'")
    if harness is not None and not isinstance(harness, str):
        raise ValueError(f"lane policy parse failed: entry[{idx}] harness must be string if present")
    return (normalize(path), lane, harness, clean_text(reason), unwind, clean_text(issue))


def select_best_entry(
    entries: list[dict[str, Any]],
    query_path: str,
    query_harness: str,
) -> tuple[str, str, str, str]:
    best = None
    best_specificity = -1

    for idx, entry in enumerate(entries):
        path, lane, harness, reason, unwind, issue = validated_fields(entry, idx)
        if path != query_path:
            continue
        if harness is not None and harness != query_harness:
            continue

        unwind_text = ""
        if lane == "bmc":
            if not isinstance(unwind, int) or unwind <= 0:
                raise ValueError(
                    f"lane policy parse failed: entry[{idx}] bmc lane requires positive integer unwind"
                )
            unwind_text = str(unwind)

        specificity = 1 if harness else 0
        if specificity > best_specificity:
            best_specificity = specificity
            best = (lane, unwind_text, reason, issue)

    return best if best is not None else default_result()


def main() -> int:
    if len(sys.argv) != 4:
        return fail("usage: lane_policy_query.py <policy> <path> <harness>")

    policy_file = pathlib.Path(sys.argv[1])
    query_path = normalize(sys.argv[2])
    query_harness = sys.argv[3]

    try:
        entries = load_policy(policy_file)
        if entries is None:
            write_stdout("\t".join(default_result()))
            return 0
        result = select_best_entry(entries, query_path, query_harness)
        write_stdout("\t".join(result))
        return 0
    except ValueError as exc:
        return fail(str(exc))


if __name__ == "__main__":
    raise SystemExit(main())
