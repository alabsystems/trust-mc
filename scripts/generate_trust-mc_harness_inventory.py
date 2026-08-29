# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

"""Generate and check the frozen replacement harness inventory (suite at tests/trust-mc)."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shlex
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
# The suite now lives at tests/trust-mc (post-OSS rename), but the frozen
# inventory data layer keeps the historical "zani"/"tests/zani" labels: the
# pinned row_sha256 digests were computed over those strings and must stay
# reproducible. FROZEN_KEY_PREFIX keeps regenerated row keys stable regardless
# of the on-disk suite directory name.
DEFAULT_SUITE_ROOT = REPO_ROOT / "tests" / "trust-mc"
DEFAULT_OUTPUT = DEFAULT_SUITE_ROOT / "replacement-harness-inventory.json"
FROZEN_KEY_PREFIX = "zani"
KANI_FLAGS_RE = re.compile(r"^// *kani-flags:(.*)$")
KANI_EXPECT_RE = re.compile(r"^// *kani-expect:(.*)$")
KANI_HEADER_SCAN_LINES = 50
DEFAULT_EXPECTED_OUTCOME = "PROOF"
EXPECTED_OUTCOMES = frozenset({"PROOF", "CTREX", "UNKNOWN", "ERROR", "BMC_SAFE"})
EXPLICIT_SELECTOR_FALLBACKS = {
    # Mirrors z4-compiletest.sh: this file intentionally runs one command with
    # the broad selector `--harness check` to exercise ambiguous stubbing
    # diagnostics. The report row is keyed by the selected command row, not by
    # each raw extracted proof function.
    "zani/Stubbing/stub_harnesses.rs": "check",
}


def _ensure_scripts_path() -> None:
    scripts_path = str(REPO_ROOT / "scripts")
    if scripts_path not in sys.path:
        sys.path.insert(0, scripts_path)


def _extract_harnesses(path: Path) -> list[str]:
    _ensure_scripts_path()
    from extract_proof_harnesses import extract_proof_harnesses  # noqa: PLC0415

    return extract_proof_harnesses(path)


def _extract_kani_flags(path: Path) -> str:
    for line in path.read_text(encoding="utf-8").splitlines()[:20]:
        match = KANI_FLAGS_RE.match(line)
        if match:
            return " ".join(match.group(1).split())
    return ""


def _extract_kani_expect_directives(path: Path) -> list[str]:
    directives: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines()[:KANI_HEADER_SCAN_LINES]:
        match = KANI_EXPECT_RE.match(line)
        if match:
            directives.append(" ".join(match.group(1).split()).upper())
    return directives


def _validate_expected_outcome(path: Path, harness: str, outcome: str) -> str:
    if outcome not in EXPECTED_OUTCOMES:
        raise ValueError(
            f"{path}: unsupported kani-expect outcome {outcome!r} for harness {harness!r}"
        )
    return outcome


def _extract_expected_outcome(path: Path, harness: str) -> str:
    directives = _extract_kani_expect_directives(path)
    harness_key = harness.upper()

    for directive in directives:
        if directive.startswith(f"{harness_key}="):
            return _validate_expected_outcome(path, harness, directive.split("=", 1)[1])

    for directive in directives:
        if "=" not in directive:
            return _validate_expected_outcome(path, harness, directive)

    return DEFAULT_EXPECTED_OUTCOME


def _explicit_harnesses_from_flags(flags: str) -> list[str]:
    if "--harness" not in flags:
        return []
    try:
        parts = shlex.split(flags)
    except ValueError:
        parts = flags.split()
    selectors: list[str] = []
    for index, part in enumerate(parts):
        if part == "--harness" and index + 1 < len(parts):
            selectors.append(parts[index + 1])
        if part.startswith("--harness="):
            selectors.append(part.split("=", 1)[1])
    return selectors


def _selected_harnesses(path: Path, rel_file: str) -> list[str]:
    harnesses = _extract_harnesses(path)
    explicit_harnesses = _explicit_harnesses_from_flags(_extract_kani_flags(path))
    if not explicit_harnesses:
        return harnesses
    if len(explicit_harnesses) != 1:
        raise ValueError(
            f"{rel_file}: multiple --harness selectors are not supported by "
            "the frozen inventory generator"
        )

    explicit_harness = explicit_harnesses[0]
    matches = [
        harness
        for harness in harnesses
        if harness == explicit_harness or harness.endswith(f"::{explicit_harness}")
    ]
    if len(matches) == 1:
        return matches
    if EXPLICIT_SELECTOR_FALLBACKS.get(rel_file) == explicit_harness:
        return [explicit_harness]
    raise ValueError(
        f"{rel_file}: --harness {explicit_harness!r} matched {len(matches)} extracted "
        "harnesses; use an exact selector or add an explicit fallback entry"
    )


def _row_digest(rows: list[dict[str, str]]) -> str:
    payload = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _normalize_expectation_filter(
    expectation_filter: list[str] | None,
) -> frozenset[str] | None:
    if not expectation_filter:
        return None
    normalized = frozenset(expectation.upper() for expectation in expectation_filter)
    unsupported = sorted(normalized - EXPECTED_OUTCOMES)
    if unsupported:
        raise ValueError(
            "unsupported expectation filter(s): "
            f"{', '.join(unsupported)}; expected one of {', '.join(sorted(EXPECTED_OUTCOMES))}"
        )
    return normalized


def build_inventory(
    suite_root: Path,
    expectation_filter: list[str] | None = None,
) -> dict[str, object]:
    suite_root = suite_root.resolve()
    if not suite_root.is_dir():
        raise ValueError(f"suite root does not exist: {suite_root}")
    normalized_filter = _normalize_expectation_filter(expectation_filter)

    rows: list[dict[str, str]] = []
    for rust_file in sorted(suite_root.rglob("*.rs")):
        # Key rows under the frozen historical prefix so the pinned
        # row_sha256 stays reproducible after the tests/zani -> tests/trust-mc
        # directory rename.
        rel_file = (
            f"{FROZEN_KEY_PREFIX}/"
            f"{rust_file.resolve().relative_to(suite_root).as_posix()}"
        )
        for harness in _selected_harnesses(rust_file, rel_file):
            expected = _extract_expected_outcome(rust_file, harness)
            if normalized_filter is not None and expected not in normalized_filter:
                continue
            rows.append(
                {
                    "file": rel_file,
                    "harness": harness,
                    "expected": expected,
                    "lane": "tests/zani",
                }
            )

    rows.sort(key=lambda row: (row["file"], row["harness"]))
    return {
        "schema_version": 1,
        "suite": "tests/zani",
        "denominator": len(rows),
        "row_sha256": _row_digest(rows),
        "rows": rows,
    }


def _canonical_json(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate or check the frozen replacement harness inventory (suite at tests/trust-mc).",
    )
    parser.add_argument(
        "--suite-root",
        type=Path,
        default=DEFAULT_SUITE_ROOT,
        help="Path to the tests/trust-mc suite root.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Inventory JSON path to write.",
    )
    parser.add_argument(
        "--expectation-filter",
        action="append",
        type=str.upper,
        choices=sorted(EXPECTED_OUTCOMES),
        help=(
            "Only include rows with this expected outcome. May be passed more than once."
        ),
    )
    parser.add_argument(
        "--check",
        type=Path,
        help="Check that this inventory path exactly matches the regenerated inventory.",
    )
    args = parser.parse_args()

    try:
        inventory = build_inventory(args.suite_root, args.expectation_filter)
    except ValueError as err:
        sys.stderr.write(f"generate_trust-mc_harness_inventory: ERROR: {err}\n")
        return 1

    rendered = _canonical_json(inventory)
    if args.check is not None:
        actual = args.check.read_text(encoding="utf-8")
        if actual != rendered:
            sys.stderr.write(
                "generate_trust-mc_harness_inventory: ERROR: inventory is stale: "
                f"{args.check}\n"
            )
            return 1
        sys.stdout.write(
            "generate_trust-mc_harness_inventory: OK "
            f"path={args.check} denominator={inventory['denominator']} "
            f"row_sha256={inventory['row_sha256']}\n"
        )
        return 0

    args.output.write_text(rendered, encoding="utf-8")
    sys.stdout.write(
        "generate_trust-mc_harness_inventory: wrote "
        f"{args.output} denominator={inventory['denominator']} "
        f"row_sha256={inventory['row_sha256']}\n"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
