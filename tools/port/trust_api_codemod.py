#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Rewrite trust-mc-compiler onto the dual-toolchain compat layer (src/rustc_compat.rs).

Every pass is idempotent: running the script twice leaves the tree unchanged
the second time, so it can be re-applied after rebasing onto a moving main.
Each pass rewrites only spellings whose meaning is identical on the frozen
nightly (see rustc_compat.rs for the per-shim argument), and reports every
occurrence it could not classify instead of guessing.

Usage:
    tools/port/trust_api_codemod.py [--root DIR] [--pass NAME ...] [--check] [--report FILE]

--check exits 1 if any file would change (for CI-style drift detection).
Passes, in application order: mir_ctor, mir_span, rvalue_use, reify_fn_pointer,
variant_idx, unused_ctor_imports, removed_variants, prelude.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import rust_lex  # noqa: E402
from rust_lex import IDENT, PUNCT, Code  # noqa: E402

REPO = Path(__file__).resolve().parents[2]
DEFAULT_ROOT = REPO / "trust-mc-compiler" / "src"
COMPAT_FILE = "rustc_compat.rs"
# The stable->internal MIR converter must map WithRetag, RuntimeChecks, Reborrow and
# SourceInfo field by field; it is ported by hand, never by these rewrites.
DEFAULT_EXCLUDES = ["kani_middle/transform/internal_mir.rs"]
PRELUDE_USE = "use crate::rustc_compat::prelude::*;"

REPORT: list[str] = []


def report(path: Path, src: str, offset: int, what: str) -> None:
    if under_toolchain_cfg(src, offset):
        return  # already ported by hand behind a toolchain cfg
    line, col = rust_lex.line_col(src, offset)
    REPORT.append(f"{path}:{line}:{col}: {what}")


_CFG_CACHE: dict[int, tuple[str, Code]] = {}


def under_toolchain_cfg(src: str, offset: int) -> bool:
    """Is `offset` inside a brace-delimited item or arm carrying a `trust_toolchain` cfg?"""
    cached = _CFG_CACHE.get(id(src))
    if cached is None or cached[0] is not src:
        cached = (src, Code(src))
        _CFG_CACHE.clear()
        _CFG_CACHE[id(src)] = cached
    code = cached[1]
    idx = next((i for i, t in enumerate(code.t) if t.start >= offset), len(code) - 1)
    o = code.enclosing_open(idx)
    while o >= 0:
        if code.text(o) == "{":
            # the item or arm head: back to the previous `;`, `{`, `}` or `,` at this depth
            k = o - 1
            while k >= 0 and code.text(k) not in (";", "{", "}", ","):
                if code.text(k) in (")", "]") and code.m[k] >= 0:
                    k = code.m[k]
                k -= 1
            head = src[code.t[k].end if k >= 0 else 0:code.t[o].start]
            if "trust_toolchain" in head:
                return True
        o = code.enclosing_open(o)
    return False


class Edits:
    """Non-overlapping text edits applied back to front."""

    def __init__(self) -> None:
        self.items: list[tuple[int, int, int, str]] = []

    def replace(self, start: int, end: int, text: str) -> None:
        self.items.append((start, end, len(self.items), text))

    def insert(self, at: int, text: str) -> None:
        self.replace(at, at, text)

    def apply(self, src: str) -> str:
        # later offsets first; for equal offsets apply later-recorded first so that
        # earlier-recorded inserts end up to the left
        for start, end, _, text in sorted(self.items, key=lambda e: (e[0], e[1], e[2]), reverse=True):
            src = src[:start] + text + src[end:]
        return src


def path_text(code: Code, start: int, last: int) -> str:
    return "".join(code.text(k) for k in range(start, last + 1))


def top_level_args(code: Code, open_idx: int) -> list[tuple[int, int]]:
    """Significant-token ranges of the comma-separated items inside a delimiter group."""
    close = code.m[open_idx]
    items: list[tuple[int, int]] = []
    k, begin = open_idx + 1, open_idx + 1
    while k < close:
        tx = code.text(k)
        if code.kind(k) == PUNCT and tx in ("(", "[", "{") and code.m[k] >= 0:
            k = code.m[k] + 1
            continue
        if code.kind(k) == PUNCT and tx == ",":
            items.append((begin, k - 1))
            begin = k + 1
        k += 1
    if begin <= close - 1:
        items.append((begin, close - 1))
    return items


# ---------------------------------------------------------------------------------------
# rvalue_use: Rvalue::Use(op) -> pattern `Rvalue::Use(op, ..)`, expression `rvalue_use!(Rvalue::Use(op))`


def pass_rvalue_use(path: Path, src: str) -> str:
    code = Code(src)
    edits = Edits()
    for i in range(len(code)):
        if not (code.kind(i) == IDENT and code.text(i) == "Use"):
            continue
        if code.text(i - 1) != "::" or code.text(i - 2) != "Rvalue" or code.text(i + 1) != "(":
            continue
        start = code.path_start(i)
        if any(code.text(k) == "syn" for k in range(start, i)):
            continue
        open_idx = i + 1
        close = code.m[open_idx]
        if close < 0:
            report(path, src, code.t[i].start, "rvalue_use: unmatched parenthesis")
            continue
        # already wrapped?
        if code.text(start - 1) == "(" and code.text(start - 2) == "!" and code.text(start - 3) == "rvalue_use":
            continue
        args = top_level_args(code, open_idx)
        ctx = code.classify(start, close)
        if ctx == "pattern":
            if len(args) != 1:
                continue  # already `Use(op, ..)` / `Use(op, _)`
            if args[0][0] == args[0][1] and code.text(args[0][0]) == "..":
                continue  # `Use(..)` already matches both shapes
            # insert `, ..` after the single argument (before any trailing comma)
            last = args[0][1]
            edits.insert(code.t[last].end, ", ..")
        elif ctx == "expr":
            if len(args) != 1:
                report(path, src, code.t[start].start, "rvalue_use: expression with != 1 argument left as is")
                continue
            edits.insert(code.t[start].start, "rvalue_use!(")
            edits.insert(code.t[close].end, ")")
        else:
            report(path, src, code.t[start].start, f"rvalue_use: unclassified context for {path_text(code, start, i)}")
    return edits.apply(src)


# ---------------------------------------------------------------------------------------
# reify_fn_pointer: pattern `PointerCoercion::ReifyFnPointer` -> `PointerCoercion::ReifyFnPointer { .. }`


def pass_reify_fn_pointer(path: Path, src: str) -> str:
    code = Code(src)
    edits = Edits()
    for i in range(len(code)):
        if not (code.kind(i) == IDENT and code.text(i) == "ReifyFnPointer"):
            continue
        if code.text(i - 1) != "::" or code.text(i - 2) != "PointerCoercion":
            continue
        if code.text(i + 1) in ("(", "{"):
            continue
        start = code.path_start(i)
        ctx = code.classify(start, i)
        if ctx == "pattern":
            edits.insert(code.t[i].end, " { .. }")
        else:
            report(path, src, code.t[start].start, f"reify_fn_pointer: {ctx} use left as is (needs Safety on Trust)")
    return edits.apply(src)


# ---------------------------------------------------------------------------------------
# mir_ctor: `Statement { kind: K, span: S }` -> `crate::rustc_compat::mir_statement(K, S)`

CTOR = {"Statement": "mir_statement", "Terminator": "mir_terminator"}


def pass_mir_ctor(path: Path, src: str) -> str:
    code = Code(src)
    edits = Edits()
    for i in range(len(code)):
        name = code.text(i)
        if code.kind(i) != IDENT or name not in CTOR or code.text(i + 1) != "{":
            continue
        start = code.path_start(i)
        prefix = [code.text(k) for k in range(start, i) if code.text(k) != "::"]
        if prefix and prefix not in (["rustc_public", "mir"], ["mir"]):
            continue  # SourceInstruction::Statement, rustc_middle::mir::Terminator, ...
        if code.text(start - 1) in ("struct", "enum", "for", "impl", "fn") or code.text(start - 1) == "->":
            continue
        open_idx = i + 1
        close = code.m[open_idx]
        if close < 0:
            continue
        fields: dict[str, tuple[int, int] | None] = {}
        order: list[str] = []
        ok = True
        for a, b in top_level_args(code, open_idx):
            if code.kind(a) != IDENT:
                ok = False
                break
            fname = code.text(a)
            if a == b:
                fields[fname] = None  # shorthand
            elif code.text(a + 1) == ":" and a + 2 <= b:
                fields[fname] = (a + 2, b)
            else:
                ok = False  # `..`, attributes, ...
                break
            order.append(fname)
        if not ok or set(fields) != {"kind", "span"}:
            continue
        ctx = code.classify(start, close)
        if ctx != "expr":
            report(path, src, code.t[start].start, f"mir_ctor: {ctx} `{name} {{ kind, span }}` left as is")
            continue

        def field_src(fname: str) -> str:
            rng = fields[fname]
            if rng is None:
                return fname
            return src[code.t[rng[0]].start:code.t[rng[1]].end]

        if order != ["kind", "span"]:
            span_rng = fields["span"]
            simple = span_rng is None or all(
                code.kind(k) == IDENT or code.text(k) in (".", "::") for k in range(span_rng[0], span_rng[1] + 1)
            )
            if not simple:
                report(path, src, code.t[start].start, "mir_ctor: span-before-kind with a non-trivial span left as is")
                continue
        edits.replace(
            code.t[start].start,
            code.t[close].end,
            f"crate::rustc_compat::{CTOR[name]}({field_src('kind')}, {field_src('span')})",
        )
    return edits.apply(src)


# ---------------------------------------------------------------------------------------
# mir_span: `<statement or terminator>.span` -> `mir_span!(<statement or terminator>)`

RECEIVER_RE = re.compile(r"^(?:[a-z0-9]+_)*(?:terminator|term|stmt|statement)(?:_[a-z0-9]+)*$")
INDEXED_RE = re.compile(r"^(?:[a-z0-9]+_)*(?:statements|stmts)$")


def postfix_chain_start(code: Code, last: int) -> int | None:
    """First token of the postfix expression (`a.b[i].c(x)?`) ending at `last`."""
    k = last
    while k >= 0:
        tx = code.text(k)
        if code.kind(k) == PUNCT and tx in (")", "]") and code.m[k] >= 0:
            o = code.m[k]
            prev = o - 1
            if code.text(prev) == ">":
                return None  # generic call: leave to a human
            if code.kind(prev) == IDENT or code.text(prev) in (")", "]", "?"):
                k = prev
                continue
            return o  # parenthesized receiver
        if code.kind(k) == PUNCT and tx == "?":
            k -= 1
            continue
        if code.kind(k) == IDENT:
            if code.text(k - 1) in (".", "::") and code.kind(k - 2) in (IDENT, PUNCT):
                k -= 2
                continue
            return k
        return None
    return None


def pass_mir_span(path: Path, src: str) -> str:
    code = Code(src)
    edits = Edits()
    for i in range(2, len(code)):
        if not (code.text(i) == "span" and code.kind(i) == IDENT and code.text(i - 1) == "."):
            continue
        if code.text(i + 1) in ("(", "::", "!"):
            continue
        r = i - 2
        hit = False
        if code.kind(r) == IDENT and RECEIVER_RE.match(code.text(r)):
            hit = True
        elif code.text(r) == "]" and code.m[r] >= 0:
            o = code.m[r]
            if code.kind(o - 1) == IDENT and INDEXED_RE.match(code.text(o - 1)):
                hit = True
        if not hit:
            continue
        if code.text(i + 1) == "=":
            report(path, src, code.t[i].start, "mir_span: assignment to .span left as is")
            continue
        start = postfix_chain_start(code, r)
        if start is None:
            report(path, src, code.t[i].start, "mir_span: receiver not a plain postfix chain; left as is")
            continue
        receiver = src[code.t[start].start:code.t[r].end]
        edits.replace(code.t[start].start, code.t[i].end, f"mir_span!({receiver})")
    return edits.apply(src)


# ---------------------------------------------------------------------------------------
# variant_idx: `<variant>.idx` field read -> `.variant_idx()`

VARIANT_RE = re.compile(r"^(?:var|variant|variant_def|vdef)$")


def pass_variant_idx(path: Path, src: str) -> str:
    code = Code(src)
    edits = Edits()
    for i in range(2, len(code)):
        if not (code.text(i) == "idx" and code.kind(i) == IDENT and code.text(i - 1) == "."):
            continue
        if code.text(i + 1) in ("(", "=", "::"):
            continue
        if code.kind(i - 2) == IDENT and VARIANT_RE.match(code.text(i - 2)):
            edits.replace(code.t[i].start, code.t[i].end, "variant_idx()")
    return edits.apply(src)


# ---------------------------------------------------------------------------------------
# removed_variants: arms for variants the Trust API removed get #[cfg(not(trust_toolchain))]

REMOVED = {
    ("StatementKind", "Retag"),
    ("Rvalue", "ShallowInitBox"),
    ("Rvalue", "NullaryOp"),
}
REMOVED_IMPORTS = {"NullOp", "RetagKind"}
CFG_NIGHTLY = "#[cfg(not(trust_toolchain))]"
MAX_DUPLICATED_BODY_LINES = 4


def removed_variant_at(code: Code, i: int) -> bool:
    return (
        code.kind(i) == IDENT
        and code.text(i - 1) == "::"
        and (code.text(i - 2), code.text(i)) in REMOVED
    )


def match_arms(code: Code, open_idx: int) -> list[dict]:
    """Split a match body `{ ... }` into arms: pattern range, `=>` index, body range, end index."""
    close = code.m[open_idx]
    arms = []
    k = open_idx + 1
    while k < close:
        arm_start = k
        # attributes on the arm
        while code.text(k) == "#" and code.text(k + 1) == "[":
            k = code.m[k + 1] + 1
        pat_start = k
        while k < close and code.text(k) != "=>":
            if code.text(k) in ("(", "[", "{") and code.m[k] >= 0:
                k = code.m[k] + 1
                continue
            k += 1
        if k >= close:
            return []
        arrow = k
        body_start = k + 1
        k = body_start
        blocky = code.text(body_start) in ("{", "if", "match", "loop", "while", "for", "unsafe")
        body_end = None
        while k < close:
            tx = code.text(k)
            if tx in ("(", "[", "{") and code.m[k] >= 0:
                end = code.m[k]
                if blocky and tx == "{" and code.text(end + 1) != "else":
                    body_end = end
                    k = end + 1
                    break
                k = end + 1
                continue
            if tx == "," and code.kind(k) == PUNCT:
                body_end = k - 1
                break
            k += 1
        if body_end is None:
            body_end = close - 1
        arm_end = body_end
        if code.text(body_end + 1) == ",":
            arm_end = body_end + 1
        arms.append(dict(start=arm_start, pat=(pat_start, arrow - 1), arrow=arrow, body=(body_start, body_end), end=arm_end))
        k = arm_end + 1
    return arms


def split_alternatives(code: Code, a: int, b: int) -> list[tuple[int, int]]:
    """Top-level `|` alternatives of a pattern range (a guard, if any, is excluded)."""
    alts = []
    k = a
    if code.text(k) == "|":
        k += 1
    begin = k
    while k <= b:
        tx = code.text(k)
        if tx in ("(", "[", "{") and code.m[k] >= 0:
            k = code.m[k] + 1
            continue
        if tx == "|" and code.kind(k) == PUNCT:
            alts.append((begin, k - 1))
            begin = k + 1
        if tx == "if" and code.kind(k) == IDENT:
            break
        k += 1
    alts.append((begin, min(k - 1, b)))
    return alts


def pass_removed_variants(path: Path, src: str) -> str:
    code = Code(src)
    edits = Edits()
    lines = src.split("\n")
    handled: set[int] = set()
    # 1. match arms
    for o in range(len(code)):
        if code.text(o) != "{" or code.m[o] < 0:
            continue
        # a match body: preceded by `match <scrutinee>`
        k = code.enclosing_open(o)
        j = o - 1
        # walk back over the scrutinee to find `match`
        depth_ok = False
        while j >= 0 and code.text(j) not in (";", "{", "}", "=>"):
            if code.text(j) in (")", "]", "}") and code.m[j] >= 0:
                j = code.m[j] - 1
                continue
            if code.text(j) == "match" and code.kind(j) == IDENT:
                depth_ok = True
                break
            j -= 1
        if not depth_ok:
            continue
        arms = match_arms(code, o)
        for arm in arms:
            pa, pb = arm["pat"]
            if not any(removed_variant_at(code, x) for x in range(pa, pb + 1)):
                continue
            for x in range(pa, pb + 1):
                if removed_variant_at(code, x):
                    handled.add(x)
            # already cfg'd?
            attrs = src[code.t[arm["start"]].start:code.t[pa].start]
            if "trust_toolchain" in attrs:
                handled.update(range(arm["start"], arm["end"] + 1))
                continue
            alts = split_alternatives(code, pa, pb)
            guard_start = None
            for x in range(pa, pb + 1):
                if code.text(x) == "if" and code.kind(x) == IDENT:
                    # only a top-level guard
                    if x > alts[-1][1]:
                        guard_start = x
                        break
            removed_alts = [al for al in alts if any(removed_variant_at(code, x) for x in range(al[0], al[1] + 1))]
            kept_alts = [al for al in alts if al not in removed_alts]
            arm_line_start = src.rfind("\n", 0, code.t[arm["start"]].start) + 1
            indent = re.match(r"[ \t]*", src[arm_line_start:]).group(0)
            if not kept_alts:
                handled.update(range(arm["start"], arm["end"] + 1))
                edits.insert(code.t[arm["start"]].start, f"{CFG_NIGHTLY}\n{indent}")
                continue
            body_a, body_b = arm["body"]
            body_text = src[code.t[body_a].start:code.t[body_b].end]
            if body_text.count("\n") + 1 > MAX_DUPLICATED_BODY_LINES:
                report(path, src, code.t[pa].start, "removed_variants: mixed or-pattern with a long body; split by hand")
                continue
            guard_text = ""
            if guard_start is not None:
                guard_text = " " + src[code.t[guard_start].start:code.t[pb].end]
            kept_text = " | ".join(src[code.t[a].start:code.t[b].end] for a, b in kept_alts)
            removed_text = " | ".join(src[code.t[a].start:code.t[b].end] for a, b in removed_alts)
            new_arm_tail = f"\n{indent}{CFG_NIGHTLY}\n{indent}{removed_text}{guard_text} => {body_text},"
            # rewrite the pattern to the kept alternatives
            lead = code.t[pa].start
            if code.text(pa) == "|":
                lead = code.t[pa].start
            edits.replace(lead, code.t[pb].end, kept_text + guard_text)
            end_tok = arm["end"]
            if code.text(end_tok) != ",":
                edits.insert(code.t[end_tok].end, ",")
            edits.insert(code.t[end_tok].end, new_arm_tail)
    # 2. `matches!(E, P)` is defined as `match E { P => true, _ => false }`; spell it out
    #    so the removed alternatives can carry a cfg attribute
    for x in range(len(code) - 2):
        if not (code.text(x) == "matches" and code.text(x + 1) == "!" and code.text(x + 2) == "("):
            continue
        o = x + 2
        close = code.m[o]
        if close < 0:
            continue
        args = top_level_args(code, o)
        if len(args) < 2:
            continue
        pa, pb = args[1][0], args[-1][1]
        if not any(removed_variant_at(code, y) for y in range(pa, pb + 1)):
            continue
        handled.update(range(pa, pb + 1))
        alts = split_alternatives(code, pa, pb)
        guard_text = ""
        for y in range(alts[-1][1] + 1, pb + 1):
            if code.text(y) == "if" and code.kind(y) == IDENT:
                guard_text = " " + src[code.t[y].start:code.t[pb].end]
                break
        removed_alts = [al for al in alts if any(removed_variant_at(code, y) for y in range(al[0], al[1] + 1))]
        kept_alts = [al for al in alts if al not in removed_alts]
        line_start = src.rfind("\n", 0, code.t[x].start) + 1
        indent = re.match(r"[ \t]*", src[line_start:]).group(0)
        inner = indent + "    "
        scrutinee = src[code.t[args[0][0]].start:code.t[args[0][1]].end]
        lines = [f"match {scrutinee} {{"]
        if kept_alts:
            kept_text = f"\n{inner}| ".join(src[code.t[a].start:code.t[b].end] for a, b in kept_alts)
            lines.append(f"{inner}{kept_text}{guard_text} => true,")
        removed_text = f"\n{inner}| ".join(src[code.t[a].start:code.t[b].end] for a, b in removed_alts)
        lines.append(f"{inner}{CFG_NIGHTLY}")
        lines.append(f"{inner}{removed_text}{guard_text} => true,")
        lines.append(f"{inner}_ => false,")
        lines.append(f"{indent}}}")
        edits.replace(code.t[x].start, code.t[close].end, "\n".join(lines))
    # 3. anything else mentioning a removed variant
    for x in range(len(code)):
        if removed_variant_at(code, x) and x not in handled:
            report(path, src, code.t[x].start, f"removed_variants: `{code.text(x - 2)}::{code.text(x)}` outside a match arm; port by hand")
    # 4. imports of removed types
    for x in range(len(code)):
        if code.text(x) != "use" or code.kind(x) != IDENT:
            continue
        semi = x
        while semi < len(code) and code.text(semi) != ";":
            semi += 1
        names = [k for k in range(x, semi) if code.kind(k) == IDENT and code.text(k) in REMOVED_IMPORTS]
        if not names:
            continue
        before = src[:code.t[x].start]
        if before.rstrip().endswith(CFG_NIGHTLY):
            continue
        stmt_text = src[code.t[x].start:code.t[semi].end]
        if "{" not in stmt_text:
            line_start = src.rfind("\n", 0, code.t[x].start) + 1
            indent = src[line_start:code.t[x].start]
            if src[line_start:code.t[x].start].strip() == "":
                edits.insert(code.t[x].start, f"{CFG_NIGHTLY}\n{indent}")
            continue
        # remove each name from a braced list and add a cfg'd single import
        prefix_end = stmt_text.index("{")
        prefix = stmt_text[len("use"):prefix_end].strip()
        for k in names:
            a = code.t[k].start
            b = code.t[k].end
            # swallow a following `,` and whitespace, or a preceding `, `
            if code.text(k + 1) == ",":
                b = code.t[k + 2].start if k + 2 < len(code) else code.t[k + 1].end
            elif code.text(k - 1) == ",":
                a = code.t[k - 1].start
            edits.replace(a, b, "")
        line_start = src.rfind("\n", 0, code.t[x].start) + 1
        indent = src[line_start:code.t[x].start]
        pub = ""
        added = "".join(
            f"\n{indent}{CFG_NIGHTLY}\n{indent}use {prefix}{code.text(k)};" for k in names
        )
        edits.insert(code.t[semi].end, added)
    return edits.apply(src)


# ---------------------------------------------------------------------------------------
# unused_ctor_imports: after mir_ctor, `Statement` / `Terminator` imports whose only users
# were the rewritten struct literals are unused; drop them so no new warnings appear

CTOR_IMPORTS = ("Statement", "Terminator")


def use_items(code: Code) -> list[tuple[int, int]]:
    items = []
    k = 0
    while k < len(code):
        if code.kind(k) == IDENT and code.text(k) == "use":
            j = k
            while j < len(code) and code.text(j) != ";":
                if code.text(j) in ("{", "(", "[") and code.m[j] >= 0:
                    j = code.m[j]
                j += 1
            items.append((k, j))
            k = j
        k += 1
    return items


def mod_blocks(code: Code) -> list[tuple[int, int]]:
    """Token ranges of inline `mod name { ... }` bodies."""
    return [
        (k + 2, code.m[k + 2])
        for k in range(len(code) - 2)
        if code.kind(k) == IDENT and code.text(k) == "mod" and code.kind(k + 1) == IDENT
        and code.text(k + 2) == "{" and code.m[k + 2] >= 0
    ]


def pass_unused_ctor_imports(path: Path, src: str) -> str:
    code = Code(src)
    edits = Edits()
    items = use_items(code)
    in_use = set()
    for a, b in items:
        in_use.update(range(a, b + 1))
    blocks = mod_blocks(code)
    for a, b in items:
        item_text = "".join(code.text(k) for k in range(a, b + 1))
        if "rustc_public" not in item_text:
            continue
        # the import's scope: the innermost inline module holding it (uses in nested
        # modules count too, since they may reach it through `use super::*`)
        lo, hi = 0, len(code) - 1
        for o, c in blocks:
            if o < a < c and c - o < hi - lo:
                lo, hi = o, c
        for k in range(a, b + 1):
            name = code.text(k)
            if code.kind(k) != IDENT or name not in CTOR_IMPORTS or code.text(k + 1) == "as":
                continue
            if code.text(k - 1) == "::":
                if code.text(k - 2) != "mir":
                    continue
            else:
                o = code.enclosing_open(k)
                if not (o >= 0 and code.text(o) == "{" and code.text(o - 1) == "::" and code.text(o - 2) == "mir"):
                    continue
            used = any(
                code.kind(q) == IDENT and code.text(q) == name and q not in in_use and code.text(q - 1) != "::"
                for q in range(lo, hi + 1)
            )
            if used:
                continue
            if code.text(k - 1) == "::":
                if code.text(k + 1) != ";":
                    continue
                line_start = src.rfind("\n", 0, code.t[a].start) + 1
                if src[line_start:code.t[a].start].strip():
                    report(path, src, code.t[k].start, f"unused_ctor_imports: `{name}` import shares its line; left as is")
                    continue
                line_end = src.find("\n", code.t[b].end)
                edits.replace(line_start, len(src) if line_end < 0 else line_end + 1, "")
            elif code.text(k + 1) == ",":
                edits.replace(code.t[k].start, code.t[k + 2].start, "")
            elif code.text(k - 1) == ",":
                edits.replace(code.t[k - 1].start, code.t[k].end, "")
            else:
                report(path, src, code.t[k].start, f"unused_ctor_imports: `{name}` is its group's sole member; left as is")
    return edits.apply(src)


# ---------------------------------------------------------------------------------------
# prelude: glob-import rustc_compat::prelude where method resolution needs it

PRELUDE_NEEDED_RE = re.compile(r"\.variant_idx\(\)|\.ty_with_args\(|\bFieldDef\b|\bfields\(\)")


def pass_prelude(path: Path, src: str) -> str:
    if path.name == COMPAT_FILE or PRELUDE_USE in src:
        return src
    code = Code(src)
    # search significant tokens only, so comments and strings never trigger an import
    joined = "".join(t.text for t in code.t)
    if not PRELUDE_NEEDED_RE.search(joined):
        return src
    # insert before the first top-level `use`
    for t in code.t:
        if t.kind == IDENT and t.text == "use":
            line_start = src.rfind("\n", 0, t.start) + 1
            if t.start == line_start or src[line_start:t.start].strip() in ("pub", "pub(crate)"):
                if src[line_start:t.start].strip():
                    continue
                # step back over attributes directly attached to this use
                ins = line_start
                while True:
                    prev_end = src.rfind("\n", 0, ins - 1) + 1
                    prev_line = src[prev_end:ins - 1] if ins > 0 else ""
                    if prev_line.startswith("#[") and ins > 0:
                        ins = prev_end
                        continue
                    break
                return src[:ins] + f"#[allow(unused_imports)]\n{PRELUDE_USE}\n" + src[ins:]
    # no top-level use: after the leading comment / inner-attribute block
    lines = src.split("\n")
    k = 0
    while k < len(lines) and (lines[k].startswith("//") or lines[k].startswith("#![") or lines[k].strip() == ""):
        k += 1
    head = "\n".join(lines[:k])
    rest = "\n".join(lines[k:])
    sep = "" if head.endswith("\n") or not head else "\n"
    return head + sep + f"#[allow(unused_imports)]\n{PRELUDE_USE}\n\n" + rest


# Cheap substring prefilters: a pass only tokenizes files that can contain a site.
PREFILTER = {
    "mir_ctor": ("Statement {", "Terminator {"),
    "mir_span": (".span",),
    "rvalue_use": ("Rvalue::Use",),
    "reify_fn_pointer": ("ReifyFnPointer",),
    "variant_idx": (".idx",),
    "unused_ctor_imports": ("rustc_compat::mir_statement", "rustc_compat::mir_terminator"),
    "removed_variants": ("Retag", "ShallowInitBox", "NullaryOp", "NullOp"),
    "prelude": ("variant_idx()", "ty_with_args(", "FieldDef", "fields()"),
}

PASSES = {
    "mir_ctor": pass_mir_ctor,
    "mir_span": pass_mir_span,
    "rvalue_use": pass_rvalue_use,
    "reify_fn_pointer": pass_reify_fn_pointer,
    "variant_idx": pass_variant_idx,
    "unused_ctor_imports": pass_unused_ctor_imports,
    "removed_variants": pass_removed_variants,
    "prelude": pass_prelude,
}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", type=Path, default=DEFAULT_ROOT)
    ap.add_argument("--pass", dest="passes", action="append", choices=list(PASSES))
    ap.add_argument("--check", action="store_true", help="report files that would change; do not write")
    ap.add_argument("--report", type=Path, help="write unclassified/skipped sites here")
    ap.add_argument("--exclude", action="append", default=[], help="path substring to skip")
    args = ap.parse_args()
    passes = args.passes or list(PASSES)
    changed = []
    for path in sorted(args.root.rglob("*.rs")):
        rel = path.relative_to(REPO) if path.is_relative_to(REPO) else path
        if path.name == COMPAT_FILE or any(e in str(rel) for e in DEFAULT_EXCLUDES + args.exclude):
            continue
        original = path.read_text(encoding="utf-8")
        src = original
        for name in passes:
            if any(needle in src for needle in PREFILTER[name]):
                src = PASSES[name](rel, src)
        if src != original:
            changed.append(rel)
            if not args.check:
                path.write_text(src, encoding="utf-8")
    for line in REPORT:
        print(line)
    if args.report:
        args.report.write_text("".join(f"{r}\n" for r in REPORT), encoding="utf-8")
    verb = "would change" if args.check else "changed"
    print(f"trust_api_codemod: {verb} {len(changed)} files; {len(REPORT)} sites reported", file=sys.stderr)
    return 1 if args.check and changed else 0


if __name__ == "__main__":
    sys.exit(main())
