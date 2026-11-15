#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""A small Rust lexer and syntactic-context classifier for the Trust API codemods.

This is not a Rust parser. It tokenizes well enough to never rewrite inside a
comment, string, char or raw-string literal, matches delimiters, and answers one
question the codemods need: is a given path occurrence in PATTERN position or in
EXPRESSION position? Every rewrite it drives is checked by compiling on both the
frozen nightly and the Trust toolchain, so a misclassification is a compile
error on at least one lane, never a silent change of meaning.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

IDENT = "ident"
LIFETIME = "lifetime"
PUNCT = "punct"
LITERAL = "literal"
COMMENT = "comment"
SPACE = "space"

KEYWORDS = {
    "as", "break", "const", "continue", "crate", "else", "enum", "extern", "false", "fn",
    "for", "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut", "pub", "ref",
    "return", "self", "Self", "static", "struct", "super", "trait", "true", "type", "unsafe",
    "use", "where", "while", "async", "await", "dyn", "yield",
}


@dataclass
class Tok:
    kind: str
    text: str
    start: int
    end: int
    # index of the matching delimiter for ( [ { and ) ] }
    match: int = -1


_MASTER = re.compile(
    r"""
    (?P<space>\s+)
  | (?P<line_comment>//[^\n]*)
  | (?P<block_comment>/\*)
  | (?P<raw_str>(?:br|cr|r)(?P<hashes>\#*)")
  | (?P<str>[bc]?"(?:[^"\\]|\\.)*")
  | (?P<char>b?'(?:[^'\\\n]|\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]{1,6}\}|.))')
  | (?P<lifetime>'(?:r\#)?[A-Za-z_][A-Za-z0-9_]*)
  | (?P<ident>(?:r\#)?[A-Za-z_][A-Za-z0-9_]*)
  | (?P<number>[0-9][0-9A-Za-z_]*(?:\.[0-9][0-9A-Za-z_]*)?(?:[eE][+-]?[0-9_]+)?)
  | (?P<punct>\.\.=|\.\.\.|<<=|>>=|::|->|=>|==|!=|<=|>=|&&|\|\||\+=|-=|\*=|/=|%=|\^=|&=|\|=|<<|>>|\.\.|.)
    """,
    re.VERBOSE | re.DOTALL,
)


def tokenize(src: str) -> list[Tok]:
    toks: list[Tok] = []
    append = toks.append
    i, n = 0, len(src)
    match = _MASTER.match
    while i < n:
        m = match(src, i)
        kind = m.lastgroup
        if kind == "hashes":
            kind = "raw_str"
        j = m.end()
        if kind == "space":
            append(Tok(SPACE, m.group(0), i, j))
        elif kind == "line_comment":
            append(Tok(COMMENT, m.group(0), i, j))
        elif kind == "block_comment":
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/*", j):
                    depth, j = depth + 1, j + 2
                elif src.startswith("*/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            append(Tok(COMMENT, src[i:j], i, j))
        elif kind == "raw_str" or m.group("raw_str"):
            hashes = m.group("hashes") or ""
            end = src.find('"' + hashes, m.end())
            j = n if end < 0 else end + 1 + len(hashes)
            append(Tok(LITERAL, src[i:j], i, j))
        elif kind in ("str", "char"):
            append(Tok(LITERAL, m.group(0), i, j))
        elif kind == "lifetime":
            append(Tok(LIFETIME, m.group(0), i, j))
        elif kind == "ident":
            append(Tok(IDENT, m.group(0), i, j))
        elif kind == "number":
            text = m.group(0)
            if "." in text:
                dot = text.index(".")
                if not text[dot + 1:dot + 2].isdigit():
                    j = i + dot
            append(Tok(LITERAL, src[i:j], i, j))
        else:
            append(Tok(PUNCT, m.group(0), i, j))
        i = j
    stack: list[int] = []
    pairs = {")": "(", "]": "[", "}": "{"}
    for idx, t in enumerate(toks):
        if t.kind != PUNCT:
            continue
        tx = t.text
        if tx in ("(", "[", "{"):
            stack.append(idx)
        elif tx in (")", "]", "}"):
            if stack and toks[stack[-1]].text == pairs[tx]:
                o = stack.pop()
                toks[o].match = idx
                t.match = o
    return toks


def significant(toks: list[Tok]) -> list[int]:
    """Indices of tokens that are not whitespace or comments."""
    return [i for i, t in enumerate(toks) if t.kind not in (SPACE, COMMENT)]


class Code:
    """Token view over one source file, restricted to significant tokens."""

    def __init__(self, src: str):
        self.src = src
        self.all = tokenize(src)
        self.sig = significant(self.all)
        self.pos = {ti: si for si, ti in enumerate(self.sig)}
        # remap delimiter matches into significant-index space
        self.t = [self.all[i] for i in self.sig]
        self.m = [self.pos.get(tok.match, -1) if tok.match >= 0 else -1 for tok in self.t]

    def __len__(self) -> int:
        return len(self.t)

    def text(self, i: int) -> str:
        return self.t[i].text if 0 <= i < len(self.t) else ""

    def kind(self, i: int) -> str:
        return self.t[i].kind if 0 <= i < len(self.t) else ""

    def path_start(self, i: int) -> int:
        """Given index of the last segment of a path, return index of its first segment."""
        j = i
        while j - 2 >= 0 and self.text(j - 1) == "::" and self.kind(j - 2) == IDENT:
            j -= 2
        if j - 1 >= 0 and self.text(j - 1) == "::":  # leading `::rustc_public`
            j -= 1
        return j

    def enclosing_open(self, i: int) -> int:
        """Index of the nearest unmatched opening delimiter before token i, or -1."""
        j = i - 1
        while j >= 0:
            tx = self.text(j)
            if tx in (")", "]", "}") and self.kind(j) == PUNCT and self.m[j] >= 0:
                j = self.m[j] - 1
                continue
            if tx in ("(", "[", "{") and self.kind(j) == PUNCT:
                return j
            j -= 1
        return -1

    # ---- context classification -------------------------------------------------

    def classify(self, start: int, end: int, _depth: int = 0) -> str:
        """Classify the syntactic unit spanning significant tokens [start, end].

        Returns "pattern", "expr" or "unknown".
        """
        if _depth > 40:
            return "unknown"
        # Keyword directly before the unit.
        prev = self.text(start - 1)
        if prev in ("let",):
            return "pattern"
        if prev in ("return", "break", "in", "match", "while", "if", "else", "=", "+=", "-=",
                    "==", "!=", "&&", "||", "=>", ";", "as", "?", "..", "..="):
            # `if let` / `while let` are handled by the `let` check above; `x == Path(..)`
            # and `match Path(..)` are expressions. `in` is expression for `for x in EXPR`.
            if prev in ("=",) and self._eq_is_let_binding(start - 1):
                return "expr"
            return "expr"
        if prev == "@":
            return "pattern"
        # Scan forward at depth 0 from the end of the unit.
        j = end + 1
        while j < len(self.t):
            tx, kd = self.text(j), self.kind(j)
            if kd == PUNCT and tx in ("(", "[", "{"):
                if tx == "{":
                    return "expr"  # `match X {`, `if X {` or a struct/block after the unit
                j = self.m[j] + 1 if self.m[j] >= 0 else j + 1
                continue
            if kd == PUNCT and tx == "=>":
                return "pattern"
            if kd == PUNCT and tx == "=":
                return "pattern"
            if kd == IDENT and tx == "in":
                return "pattern"  # `for PAT in`
            if kd == IDENT and tx == "if":
                return "pattern"  # match guard
            if kd == PUNCT and tx == "|":
                # or-pattern alternative separator; keep scanning (closure bars only occur
                # in expression position *before* a body, never directly after a unit)
                j += 1
                continue
            if kd == PUNCT and tx == ":":
                return "pattern"  # typed binding `let PAT: T`
            if kd == PUNCT and tx in (";",):
                return "expr"
            if kd == PUNCT and tx in (",", ")", "]", "}"):
                return self._classify_by_container(start, _depth)
            if kd == PUNCT and tx in (".", "?", "as", "+", "-", "*", "/", "%", "&&", "||", "==",
                                      "!=", "<", ">", "<=", ">=", "..", "..="):
                return "expr"
            if kd == IDENT and tx in ("as", "else"):
                return "expr"
            # anything else: skip (e.g. tokens of the following or-alternative)
            j += 1
        return "unknown"

    def _eq_is_let_binding(self, eq: int) -> bool:
        return False

    def _classify_by_container(self, start: int, depth: int) -> str:
        o = self.enclosing_open(start)
        if o < 0:
            return "unknown"
        opener = self.text(o)
        before = o - 1
        btx, bkd = self.text(before), self.kind(before)
        if opener == "(":
            if btx == "!" and self.kind(before - 1) == IDENT:
                macro = self.text(before - 1)
                if macro == "matches":
                    # pattern iff the unit comes after the first depth-0 comma
                    k = o + 1
                    while k < start:
                        if self.text(k) in ("(", "[", "{") and self.m[k] >= 0:
                            k = self.m[k] + 1
                            continue
                        if self.text(k) == ",":
                            return "pattern"
                        k += 1
                    return "expr"
                return "expr"
            if bkd == IDENT and btx not in KEYWORDS:
                # call / method call / tuple-struct: the latter inherits its context
                if btx[:1].isupper():
                    ps = self.path_start(before)
                    if self.text(ps - 1) == ".":
                        return "expr"
                    return self.classify(ps, self.m[o], depth + 1)
                return "expr"
            if btx in (">",) or btx == "::":
                return "expr"  # turbofish call
            # bare tuple / parenthesized unit: classify the group itself
            return self.classify(o, self.m[o], depth + 1)
        if opener == "[":
            if btx == "!":
                return "expr"
            if bkd == IDENT and btx not in KEYWORDS:
                return "expr"  # indexing
            if btx in (")", "]"):
                return "expr"
            return self.classify(o, self.m[o], depth + 1)
        if opener == "{":
            if bkd == IDENT and btx[:1].isupper() and btx not in KEYWORDS:
                ps = self.path_start(before)
                p2 = self.text(ps - 1)
                if p2 in ("match", "if", "while", "in"):
                    return "expr"  # block after a scrutinee like `match CONST {`
                return self.classify(ps, self.m[o], depth + 1)
            return "expr"  # a block: its contents are expressions/statements
        return "unknown"


def line_col(src: str, offset: int) -> tuple[int, int]:
    line = src.count("\n", 0, offset) + 1
    col = offset - (src.rfind("\n", 0, offset) + 1) + 1
    return line, col
