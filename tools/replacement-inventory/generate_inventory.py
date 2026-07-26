#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Generate and check the frozen trust-mc replacement harness inventory.

This is the ay / trust-mc inventory generator. Its disposition source is the
surveyed public Kani verification corpus
(``tools/replacement-inventory/public-corpus.json``): one row per
``#[kani::proof]`` harness across the real verification suites under
``tests/``, with each harness's expected disposition read from the test's
``expected`` output file (the convention compiletest's ``Expected`` mode keys
on: ``run_expected_test`` resolves ``file.with_extension("expected")`` else
``<dir>/expected`` and substring-matches the verifier's stdout — see
``tools/compiletest/src/runtest.rs``).

The generator applies a fixed *curation*: it INCLUDES the verification-verdict
suites whose harnesses carry a determinable single verdict (``expected``,
``slow``, ``std-checks``, ``prusti``, ``smack``) and EXCLUDES the diagnostic /
CLI-output suites (``ui``, ``cargo-ui``, ``script-based-pre``), whose excluded
counts are still recorded for accounting. It emits three deterministic JSON
artifacts under ``tests/trust-mc/``:

* ``replacement-harness-inventory.json`` — the mixed inventory (every included
  row; ``denominator == len(rows)``).
* ``replacement-harness-inventory.proof.json`` — the PROOF-only subset.
* ``non-proof-closure.json`` — the non-PROOF (CTREX / UNKNOWN expected-fail)
  closure, each row carrying a ``disposition`` and ``justification`` stub plus a
  ``source`` back-reference to the mixed inventory.

The corpus disposition vocabulary (``PROOF`` / ``CTREX`` / ``INDETERMINATE``)
is mapped onto the inventory vocabulary consumed by ``replacement_progress.py``
(``PROOF`` / ``CTREX`` / ``UNKNOWN`` / ``ERROR`` / ``BMC_SAFE``): ``INDETERMINATE``
(a real verification-verdict harness whose verdict the survey could not pin to a
single SUCCESS/FAILURE) becomes ``UNKNOWN``.

Determinism guarantees
----------------------
* Rows are sorted by ``(file, harness)``; the corpus input is canonical.
* ``denominator`` is exactly ``len(rows)``.
* ``row_sha256`` is the SHA-256 of the compact, key-sorted JSON encoding of the
  ``rows`` array, so re-running this generator reproduces byte-identical
  inventory files.
* The input corpus lives in-repo (no ``/tmp`` dependency), so ``--check`` is
  reproducible on a clean checkout.

The vendored ``#[kani::proof]`` harness extractor (clean-branded) is retained
below as the documented, self-contained definition of how the corpus survey
enumerated harnesses from each ``*.rs`` file.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import tempfile
from pathlib import Path

# ---------------------------------------------------------------------------
# Repository layout
# ---------------------------------------------------------------------------

# tools/replacement-inventory/generate_inventory.py -> repo root is two up.
REPO_ROOT = Path(__file__).resolve().parent.parent.parent
TESTS_ROOT = REPO_ROOT / "tests"

# The surveyed public corpus (one row per #[kani::proof] harness, disposition
# read from the test's `expected` file). Lives in-repo so --check needs no /tmp.
DEFAULT_CORPUS = Path(__file__).resolve().parent / "public-corpus.json"

# Curation. INCLUDED suites are verification-verdict suites whose harnesses
# carry a determinable single verdict. EXCLUDED suites are diagnostic /
# CLI-output tests (not single-verdict verification); their row counts are still
# recorded in the run summary for accounting. Each entry is a directory under
# ``tests/``; the per-row ``lane`` is ``tests/<suite>``.
DEFAULT_SUITES = (
    "tests/expected",
    "tests/slow",
    "tests/std-checks",
    "tests/prusti",
    "tests/smack",
)
EXCLUDED_SUITES = (
    "tests/ui",
    "tests/cargo-ui",
    "tests/script-based-pre",
)
EXCLUDED_SUITE_REASON = (
    "diagnostic / CLI-output tests (not single-verdict verification): "
    "compiletest does not run these as one verification verdict per harness"
)

# Corpus disposition vocabulary -> inventory vocabulary consumed by
# replacement_progress.py. INDETERMINATE (a real verdict harness whose verdict
# the survey could not pin to a single SUCCESS/FAILURE) maps to UNKNOWN.
CORPUS_TO_EXPECTED = {
    "PROOF": "PROOF",
    "CTREX": "CTREX",
    "INDETERMINATE": "UNKNOWN",
}

# Provenance recorded in the emitted inventory.
PROVENANCE = (
    "fresh public corpus over the included Kani verification suites, 2026-06-15"
)

# The full inventory lives in the trust-mc suite; the proof subset and the
# non-proof closure sit beside it. ``suite`` in the emitted JSON always reports
# the inventory's home suite.
HOME_SUITE = "tests/trust-mc"
DEFAULT_OUTPUT = TESTS_ROOT / "trust-mc" / "replacement-harness-inventory.json"
DEFAULT_PROOF_OUTPUT = (
    TESTS_ROOT / "trust-mc" / "replacement-harness-inventory.proof.json"
)
DEFAULT_NONPROOF_OUTPUT = TESTS_ROOT / "trust-mc" / "non-proof-closure.json"

SCHEMA_VERSION = 1

# ---------------------------------------------------------------------------
# Disposition classification
# ---------------------------------------------------------------------------

EXPECTED_OUTCOMES = frozenset({"PROOF", "CTREX", "UNKNOWN", "ERROR", "BMC_SAFE"})

# ---------------------------------------------------------------------------
# Proof-harness extraction (vendored, clean-branded)
# ---------------------------------------------------------------------------

ATTR_BODY = re.compile(r"^\s*#\[\s*(.*?)\s*\]\s*(?://.*)?$")
KANI_PROOF_META = re.compile(r"^kani::proof(?:\s*$|\s*\(.*\)\s*$)")
KANI_PROOF_FOR_CONTRACT_META = re.compile(r"^kani::proof_for_contract\s*\(.*\)\s*$")
FN_DECL = re.compile(
    r"^\s*(?:(?:pub(?:\([^)]*\))?\s+|unsafe\s+|async\s+|const\s+)*)fn\s+([A-Za-z0-9_]+)\s*\("
)
MOD_DECL = re.compile(r"^\s*(?:pub(?:\([^)]*\))?\s+)?mod\s+([A-Za-z0-9_]+)\s*\{")
MACRO_RULES_DECL = re.compile(r"^\s*macro_rules!\s+([A-Za-z0-9_]+)\s*\{")
MACRO_PARAM = re.compile(r"\$([A-Za-z_][A-Za-z0-9_]*)\s*:\s*([A-Za-z_]+)")
MACRO_FN_TEMPLATE = re.compile(r"\bfn\s+\$([A-Za-z_][A-Za-z0-9_]*)\s*\(")
MACRO_CALL = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*!\s*[\(\{\[]")
IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")

_MATCHING_CLOSER = {"(": ")", "[": "]", "{": "}"}


def _strip_string_and_comment(line: str) -> str:
    """Remove string literals and ``//`` comments so brace counts are accurate."""
    line = re.sub(r'"(?:[^"\\]|\\.)*"', "", line)
    line = re.sub(r"//.*$", "", line)
    return line


def _match_balanced(text: str, pos: int) -> tuple[int, int] | None:
    """Return ``(inner_start, close_pos)`` for a balanced delimiter group."""
    if pos >= len(text) or text[pos] not in _MATCHING_CLOSER:
        return None
    opener = text[pos]
    closer = _MATCHING_CLOSER[opener]
    depth = 1
    k = pos + 1
    start = k
    while k < len(text):
        ch = text[k]
        if ch == opener:
            depth += 1
        elif ch == closer:
            depth -= 1
            if depth == 0:
                return (start, k)
        k += 1
    return None


def _skip_ws(text: str, pos: int) -> int:
    while pos < len(text) and text[pos].isspace():
        pos += 1
    return pos


def _split_top_level_commas(text: str) -> list[str]:
    """Split ``text`` on top-level commas, honoring ()/[]/{}/<> nesting."""
    out: list[str] = []
    depth = 0
    current: list[str] = []
    for ch in text:
        if ch in "([{<":
            depth += 1
            current.append(ch)
        elif ch in ")]}>":
            depth = max(0, depth - 1)
            current.append(ch)
        elif ch == "," and depth == 0:
            out.append("".join(current).strip())
            current = []
        else:
            current.append(ch)
    tail = "".join(current).strip()
    if tail:
        out.append(tail)
    return out


def _parse_arms(inner: str) -> list[tuple[str, str]]:
    """Split a ``macro_rules!`` body into ``(param_text, body_text)`` per arm."""
    arms: list[tuple[str, str]] = []
    pos = 0
    n = len(inner)
    while pos < n:
        pos = _skip_ws(inner, pos)
        if pos >= n:
            break
        if inner[pos] not in _MATCHING_CLOSER:
            pos += 1
            continue
        params_span = _match_balanced(inner, pos)
        if params_span is None:
            break
        params = inner[params_span[0] : params_span[1]]
        pos = params_span[1] + 1
        pos = _skip_ws(inner, pos)
        if inner[pos : pos + 2] != "=>":
            continue
        pos = _skip_ws(inner, pos + 2)
        body_span = _match_balanced(inner, pos) if pos < n else None
        if body_span is None:
            break
        body = inner[body_span[0] : body_span[1]]
        pos = body_span[1] + 1
        arms.append((params, body))
        while pos < n and inner[pos] in " \t\r\n;":
            pos += 1
    return arms


def _find_macro_proof_emitters(lines: list[str]) -> dict[str, list[int]]:
    """Return ``{macro_name: [param_index, ...]}`` for proof-emitting arms."""
    emitters: dict[str, list[int]] = {}
    i = 0
    while i < len(lines):
        decl = MACRO_RULES_DECL.match(lines[i])
        if not decl:
            i += 1
            continue
        macro_name = decl.group(1)
        first = _strip_string_and_comment(lines[i])
        depth = first.count("{") - first.count("}")
        body_start = i
        j = i + 1
        while j < len(lines) and depth > 0:
            stripped = _strip_string_and_comment(lines[j])
            depth += stripped.count("{") - stripped.count("}")
            j += 1
        body_end = j
        body_text = "\n".join(lines[body_start:body_end])
        inner = body_text
        brace_pos = inner.find("{")
        if brace_pos != -1:
            inner = inner[brace_pos + 1 :]
        last_close = inner.rfind("}")
        if last_close != -1:
            inner = inner[:last_close]
        for params, body in _parse_arms(inner):
            if "kani::proof" not in body:
                continue
            param_list = [m.group(1) for m in MACRO_PARAM.finditer(params)]
            for tmpl_match in MACRO_FN_TEMPLATE.finditer(body):
                prefix = body[: tmpl_match.start()]
                last_brace = prefix.rfind("}")
                scoped_prefix = (
                    prefix[last_brace + 1 :] if last_brace != -1 else prefix
                )
                if "kani::proof" not in scoped_prefix:
                    continue
                fn_param_name = tmpl_match.group(1)
                if fn_param_name not in param_list:
                    continue
                idx = param_list.index(fn_param_name)
                emitters.setdefault(macro_name, []).append(idx)
                break
        i = body_end if body_end > i else i + 1
    return emitters


def _qualify(name: str, mod_stack: list[tuple[str, int]]) -> str:
    if not mod_stack:
        return name
    return "::".join(n for n, _ in mod_stack) + "::" + name


def _update_mod_stack(
    line: str,
    stripped: str,
    mod_stack: list[tuple[str, int]],
    brace_depth: int,
) -> int:
    mod_match = MOD_DECL.match(line)
    if mod_match:
        mod_stack.append((mod_match.group(1), brace_depth))
    brace_depth += stripped.count("{") - stripped.count("}")
    while mod_stack and brace_depth <= mod_stack[-1][1]:
        mod_stack.pop()
    return brace_depth


def _extract_macro_call_args(line: str, bang_index: int) -> str | None:
    k = bang_index
    while k < len(line) and line[k] not in _MATCHING_CLOSER:
        k += 1
    span = _match_balanced(line, k) if k < len(line) else None
    if span is None:
        return None
    return line[span[0] : span[1]]


def _expand_macro_call(
    line: str,
    macro_emitters: dict[str, list[int]],
    mod_stack: list[tuple[str, int]],
) -> list[str]:
    call_match = MACRO_CALL.match(line)
    if not call_match or call_match.group(1) not in macro_emitters:
        return []
    macro_name = call_match.group(1)
    bang_idx = line.index("!", call_match.start(1))
    args_text = _extract_macro_call_args(line, bang_idx)
    if args_text is None:
        return []
    args = _split_top_level_commas(args_text)
    out: list[str] = []
    for idx in macro_emitters[macro_name]:
        if idx < len(args):
            ident = args[idx].strip()
            if IDENT_RE.match(ident):
                out.append(_qualify(ident, mod_stack))
    return out


def _is_skippable_between_attr_and_fn(line: str) -> bool:
    return bool(re.match(r"^\s*(#\[|//|/\*|\*|\*/)", line)) or line.strip() == ""


def _is_kani_harness_meta(meta: str) -> bool:
    meta = meta.strip()
    return bool(
        KANI_PROOF_META.match(meta) or KANI_PROOF_FOR_CONTRACT_META.match(meta)
    )


def _meta_call_args(meta: str, name: str) -> list[str] | None:
    prefix = re.match(rf"^{re.escape(name)}\s*", meta)
    if not prefix:
        return None
    open_pos = _skip_ws(meta, prefix.end())
    span = _match_balanced(meta, open_pos)
    if span is None or meta[span[1] + 1 :].strip():
        return None
    return _split_top_level_commas(meta[span[0] : span[1]])


def _is_cfg_attr_kani_harness(meta: str) -> bool:
    args = _meta_call_args(meta, "cfg_attr")
    if args is None:
        return False
    if len(args) < 2 or args[0].strip() != "kani":
        return False
    return any(_is_kani_harness_meta(arg) for arg in args[1:])


def _cfg_expr_active_by_default(expr: str) -> bool:
    expr = expr.strip()
    if expr == "kani":
        return True
    all_args = _meta_call_args(expr, "all")
    if all_args is not None:
        return all(_cfg_expr_active_by_default(arg) for arg in all_args)
    any_args = _meta_call_args(expr, "any")
    if any_args is not None:
        return any(_cfg_expr_active_by_default(arg) for arg in any_args)
    not_args = _meta_call_args(expr, "not")
    if not_args is not None:
        return len(not_args) == 1 and not _cfg_expr_active_by_default(not_args[0])
    return False


def _is_inactive_cfg_meta(meta: str) -> bool:
    args = _meta_call_args(meta.strip(), "cfg")
    return (
        args is not None
        and len(args) == 1
        and not _cfg_expr_active_by_default(args[0])
    )


def _attr_meta(line: str) -> str | None:
    attr = ATTR_BODY.match(line)
    if not attr:
        return None
    return attr.group(1).strip()


def _apply_attr_meta(
    meta: str,
    *,
    want_fn: bool,
    want_fn_blocked: bool,
    pending_inactive_cfg: bool,
) -> tuple[bool, bool, bool]:
    if _is_inactive_cfg_meta(meta):
        pending_inactive_cfg = True
        want_fn_blocked = want_fn_blocked or want_fn
    if _is_kani_harness_meta(meta) or _is_cfg_attr_kani_harness(meta):
        want_fn = True
        want_fn_blocked = want_fn_blocked or pending_inactive_cfg
    return want_fn, want_fn_blocked, pending_inactive_cfg


def _append_macro_expansions(
    line: str,
    *,
    macro_emitters: dict[str, list[int]],
    mod_stack: list[tuple[str, int]],
    harnesses: list[str],
    pending_inactive_cfg: bool,
) -> bool:
    if not macro_emitters:
        return pending_inactive_cfg
    expanded = _expand_macro_call(line, macro_emitters, mod_stack)
    if not expanded:
        return pending_inactive_cfg
    if not pending_inactive_cfg:
        harnesses.extend(expanded)
    return False


def extract_proof_harnesses(path: Path) -> list[str]:
    """Return sorted, fully-qualified ``#[kani::proof]`` harness names."""
    lines = path.read_text(encoding="utf-8").splitlines()
    macro_emitters = _find_macro_proof_emitters(lines)

    mod_stack: list[tuple[str, int]] = []
    brace_depth = 0
    harnesses: list[str] = []
    want_fn = False
    want_fn_blocked = False
    pending_inactive_cfg = False

    for line in lines:
        stripped = _strip_string_and_comment(line)
        brace_depth = _update_mod_stack(line, stripped, mod_stack, brace_depth)

        meta = _attr_meta(line)
        if meta is not None:
            want_fn, want_fn_blocked, pending_inactive_cfg = _apply_attr_meta(
                meta,
                want_fn=want_fn,
                want_fn_blocked=want_fn_blocked,
                pending_inactive_cfg=pending_inactive_cfg,
            )
            continue

        pending_inactive_cfg = _append_macro_expansions(
            line,
            macro_emitters=macro_emitters,
            mod_stack=mod_stack,
            harnesses=harnesses,
            pending_inactive_cfg=pending_inactive_cfg,
        )

        if not want_fn:
            if not _is_skippable_between_attr_and_fn(line):
                pending_inactive_cfg = False
            continue
        if _is_skippable_between_attr_and_fn(line):
            continue

        fn_match = FN_DECL.match(line)
        if fn_match and not want_fn_blocked:
            harnesses.append(_qualify(fn_match.group(1), mod_stack))
        want_fn = False
        want_fn_blocked = False
        pending_inactive_cfg = False

    return sorted(set(harnesses))


# ---------------------------------------------------------------------------
# Surveyed corpus ingestion + disposition mapping
# ---------------------------------------------------------------------------


def _normalize_lane(suite: str) -> str:
    """Return the canonical ``tests/<name>`` lane for a corpus suite token."""
    suite = suite.strip()
    return suite if suite.startswith("tests/") else f"tests/{suite}"


def _map_corpus_disposition(file: str, harness: str, corpus_expected: str) -> str:
    """Map a survey disposition onto the inventory vocabulary.

    ``PROOF`` / ``CTREX`` pass through; ``INDETERMINATE`` (a real verdict
    harness whose verdict the survey could not pin to a single SUCCESS/FAILURE)
    becomes ``UNKNOWN``. There is no silent default: an unrecognized survey
    disposition is a hard error.
    """
    key = corpus_expected.strip().upper()
    mapped = CORPUS_TO_EXPECTED.get(key)
    if mapped is None:
        raise ValueError(
            f"{file}::{harness}: unrecognized corpus disposition "
            f"{corpus_expected!r}; expected one of "
            f"{', '.join(sorted(CORPUS_TO_EXPECTED))}"
        )
    if mapped not in EXPECTED_OUTCOMES:
        raise ValueError(
            f"{file}::{harness}: mapped disposition {mapped!r} is not a valid "
            f"inventory outcome ({', '.join(sorted(EXPECTED_OUTCOMES))})"
        )
    return mapped


def load_corpus_rows(corpus_path: Path) -> list[dict[str, str]]:
    """Load and validate the surveyed corpus rows from ``corpus_path``."""
    data = json.loads(corpus_path.read_text(encoding="utf-8"))
    rows = data.get("rows") if isinstance(data, dict) else None
    if not isinstance(rows, list):
        raise ValueError(
            f"{corpus_path}: not a corpus survey (missing a 'rows' array)"
        )
    out: list[dict[str, str]] = []
    for row in rows:
        out.append(
            {
                "file": str(row["file"]),
                "harness": str(row["harness"]),
                "suite": _normalize_lane(str(row["suite"])),
                "expected": str(row["expected"]),
            }
        )
    return out


# ---------------------------------------------------------------------------
# Inventory assembly
# ---------------------------------------------------------------------------


def _row_digest(rows: list[dict[str, str]]) -> str:
    payload = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _normalize_expectation_filter(
    expectation_filter: list[str] | None,
) -> frozenset[str] | None:
    if not expectation_filter:
        return None
    normalized = frozenset(item.upper() for item in expectation_filter)
    unsupported = sorted(normalized - EXPECTED_OUTCOMES)
    if unsupported:
        raise ValueError(
            "unsupported expectation filter(s): "
            f"{', '.join(unsupported)}; expected one of "
            f"{', '.join(sorted(EXPECTED_OUTCOMES))}"
        )
    return normalized


def _collect_rows(
    corpus_rows: list[dict[str, str]],
    suites: tuple[str, ...],
    normalized_filter: frozenset[str] | None,
) -> list[dict[str, str]]:
    """Build mixed inventory rows from the included corpus suites."""
    included = frozenset(_normalize_lane(s) for s in suites)
    rows: list[dict[str, str]] = []
    for corpus_row in corpus_rows:
        lane = corpus_row["suite"]
        if lane not in included:
            continue
        expected = _map_corpus_disposition(
            corpus_row["file"], corpus_row["harness"], corpus_row["expected"]
        )
        if normalized_filter is not None and expected not in normalized_filter:
            continue
        rows.append(
            {
                "file": corpus_row["file"],
                "harness": corpus_row["harness"],
                "expected": expected,
                "lane": lane,
            }
        )
    rows.sort(key=lambda row: (row["file"], row["harness"]))
    return rows


def excluded_suite_counts(corpus_rows: list[dict[str, str]]) -> list[dict[str, object]]:
    """Return per-suite row counts for the curation-excluded suites."""
    out: list[dict[str, object]] = []
    for suite in EXCLUDED_SUITES:
        lane = _normalize_lane(suite)
        count = sum(1 for row in corpus_rows if row["suite"] == lane)
        out.append({"suite": lane, "count": count, "reason": EXCLUDED_SUITE_REASON})
    return out


def build_inventory(
    corpus_rows: list[dict[str, str]],
    suites: tuple[str, ...] = DEFAULT_SUITES,
    expectation_filter: list[str] | None = None,
    *,
    with_provenance: bool = False,
) -> dict[str, object]:
    """Build the inventory mapping for the included ``suites``."""
    normalized_filter = _normalize_expectation_filter(expectation_filter)
    rows = _collect_rows(corpus_rows, suites, normalized_filter)
    inventory: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "suite": HOME_SUITE,
        "denominator": len(rows),
        "row_sha256": _row_digest(rows),
        "rows": rows,
    }
    if with_provenance:
        inventory["provenance"] = PROVENANCE
    return inventory


def build_non_proof_closure(
    corpus_rows: list[dict[str, str]],
    suites: tuple[str, ...] = DEFAULT_SUITES,
) -> dict[str, object]:
    """Build the non-PROOF (expected-fail) closure with a source back-ref.

    The closure is the exact complement of the PROOF subset within the mixed
    inventory: ``mixed == proof + non_proof``. Every closure row carries an
    expected-fail ``disposition`` plus a ``justification`` stub.
    """
    mixed = _collect_rows(corpus_rows, suites, None)
    closure_rows: list[dict[str, str]] = []
    for row in mixed:
        if row["expected"] == "PROOF":
            continue
        closure_rows.append(
            {
                "file": row["file"],
                "harness": row["harness"],
                "lane": row["lane"],
                "expected": row["expected"],
                "disposition": "expected-fail",
                "justification": (
                    "expected non-PROOF verdict carried by the test's `expected` "
                    f"output file (survey disposition: {row['expected']})"
                ),
            }
        )
    closure_rows.sort(key=lambda row: (row["file"], row["harness"]))
    mixed_digest = _row_digest(mixed)
    return {
        "schema_version": SCHEMA_VERSION,
        "suite": HOME_SUITE,
        "denominator": len(closure_rows),
        "row_sha256": _row_digest(closure_rows),
        "rows": closure_rows,
        "source": {
            "inventory": "replacement-harness-inventory.json",
            "denominator": len(mixed),
            "row_sha256": mixed_digest,
        },
    }


def _canonical_json(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _write_inventory(path: Path, inventory: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(_canonical_json(inventory), encoding="utf-8")


def _check_inventory(path: Path, inventory: dict[str, object]) -> bool:
    """Return True if ``path`` already matches the regenerated ``inventory``."""
    rendered = _canonical_json(inventory)
    if not path.exists():
        sys.stderr.write(
            f"generate_inventory: ERROR: missing inventory: {path}\n"
        )
        return False
    actual = path.read_text(encoding="utf-8")
    if actual == rendered:
        sys.stdout.write(
            f"generate_inventory: OK path={path} "
            f"denominator={inventory['denominator']} "
            f"row_sha256={inventory['row_sha256']}\n"
        )
        return True

    # Drift: emit a unified diff against a regenerated temp file for context.
    import difflib

    with tempfile.NamedTemporaryFile(
        "w", suffix=".json", prefix="inventory-", delete=False, encoding="utf-8"
    ) as handle:
        handle.write(rendered)
        temp_path = handle.name
    diff = difflib.unified_diff(
        actual.splitlines(keepends=True),
        rendered.splitlines(keepends=True),
        fromfile=f"{path} (committed)",
        tofile=f"{temp_path} (regenerated)",
    )
    sys.stderr.write(
        f"generate_inventory: ERROR: inventory is stale: {path}\n"
        f"  regenerated copy written to {temp_path}\n"
    )
    sys.stderr.writelines(diff)
    return False


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="generate_inventory.py",
        description=(
            "Generate or check the frozen trust-mc replacement harness "
            "inventory (ay / trust-mc) from the surveyed public corpus."
        ),
    )
    parser.add_argument(
        "--corpus",
        type=Path,
        default=DEFAULT_CORPUS,
        help=(
            "Surveyed public corpus JSON (default: "
            "tools/replacement-inventory/public-corpus.json)."
        ),
    )
    parser.add_argument(
        "--suite",
        action="append",
        dest="suites",
        metavar="NAME",
        help=(
            "Included verification suite under tests/ (repeatable). "
            f"Default: {', '.join(DEFAULT_SUITES)}."
        ),
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="Mixed inventory JSON path to write.",
    )
    parser.add_argument(
        "--proof-output",
        type=Path,
        default=DEFAULT_PROOF_OUTPUT,
        help="PROOF-only subset inventory JSON path to write.",
    )
    parser.add_argument(
        "--non-proof-output",
        type=Path,
        default=DEFAULT_NONPROOF_OUTPUT,
        help="Non-PROOF (expected-fail) closure JSON path to write.",
    )
    parser.add_argument(
        "--no-proof-subset",
        action="store_true",
        help="Do not write or check the PROOF-only subset inventory.",
    )
    parser.add_argument(
        "--no-non-proof-closure",
        action="store_true",
        help="Do not write or check the non-PROOF closure.",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help=(
            "Regenerate the artifacts in memory and diff them against the "
            "committed file(s). Exit nonzero on any drift; write nothing."
        ),
    )
    args = parser.parse_args(argv)

    suites = tuple(args.suites) if args.suites else DEFAULT_SUITES

    try:
        corpus_rows = load_corpus_rows(args.corpus)
        full = build_inventory(corpus_rows, suites, with_provenance=True)
        proof = build_inventory(
            corpus_rows, suites, expectation_filter=["PROOF"], with_provenance=True
        )
        non_proof = build_non_proof_closure(corpus_rows, suites)
    except (OSError, KeyError, ValueError, json.JSONDecodeError) as err:
        sys.stderr.write(f"generate_inventory: ERROR: {err}\n")
        return 1

    targets: list[tuple[Path, dict[str, object]]] = [(args.output, full)]
    if not args.no_proof_subset:
        targets.append((args.proof_output, proof))
    if not args.no_non_proof_closure:
        targets.append((args.non_proof_output, non_proof))

    if args.check:
        ok = True
        for path, inventory in targets:
            ok = _check_inventory(path, inventory) and ok
        return 0 if ok else 1

    for path, inventory in targets:
        _write_inventory(path, inventory)
        sys.stdout.write(
            f"generate_inventory: wrote {path} "
            f"denominator={inventory['denominator']} "
            f"row_sha256={inventory['row_sha256']}\n"
        )

    # Print the curation accounting (included + excluded suite counts).
    excluded = excluded_suite_counts(corpus_rows)
    sys.stdout.write(
        "generate_inventory: included suites: "
        f"{', '.join(_normalize_lane(s) for s in suites)}\n"
    )
    for entry in excluded:
        sys.stdout.write(
            f"generate_inventory: excluded suite {entry['suite']} "
            f"count={entry['count']} ({entry['reason']})\n"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
