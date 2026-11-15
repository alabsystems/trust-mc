# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Lexical scan of Rust sources for Kani harnesses.

Not a parser: it strips comments, strings and char literals, then follows
`mod`/`fn`/`impl`/`trait` brace scopes so a harness gets the pretty name Kani
prints (`def_path_str` without the crate: `module::inner::harness`). Harness
attributes are `#[kani::proof]`, `#[kani::proof_for_contract(..)]` and their
`#[cfg_attr(<pred>, kani::..)]` spellings; the attributes Kani reads beside
them (`should_panic`, `unwind`, `solver`, `stub`, `stub_verified`) are
recorded. Attributes inside `macro_rules!` bodies are reported as templates
because their expansions are not tracked.
"""
from __future__ import annotations

import re

IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
HARNESS_KINDS = ("proof_for_contract", "proof")
ITEM_KEYWORDS = {"fn", "struct", "enum", "union", "const", "static", "impl", "trait",
                 "mod", "use", "type", "extern", "macro_rules"}


def strip_code(src: str) -> str:
    """Blank out comments, strings and char literals, preserving newlines."""
    out = []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if src.startswith("//", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        elif src.startswith("/*", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/*", j):
                    depth, j = depth + 1, j + 2
                elif src.startswith("*/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append("".join(ch if ch == "\n" else " " for ch in src[i:j]))
            i = j
        elif c in "rb" and re.match(r"(?:br|rb|r)#*\"", src[i:i + 40]) and (i == 0 or not (src[i - 1].isalnum() or src[i - 1] == "_")):
            m = re.match(r"(?:br|rb|r)(#*)\"", src[i:])
            hashes = m.group(1)
            end = src.find('"' + hashes, i + m.end())
            j = n if end < 0 else end + 1 + len(hashes)
            out.append('"' + "".join(ch if ch == "\n" else " " for ch in src[i + 1:j - 1]) + '"')
            i = j
        elif c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            j = min(j + 1, n)
            out.append('"' + "".join(ch if ch == "\n" else " " for ch in src[i + 1:j - 1]) + '"')
            i = j
        elif c == "'":
            m = re.match(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]{1,6}\}|.)|[^\\'\n])'", src[i:])
            if m:
                out.append("' '".ljust(m.end()))
                i += m.end()
            else:
                out.append(c)
                i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def _tokens(code: str, orig: str | None = None):
    """(kind, text, line) with kind in ident|punct|lit; `::` is one token.

    strip_code preserves offsets, so string literals are reported with their
    original text from `orig` (cfg predicates need `feature = "x"` values).
    """
    orig = code if orig is None else orig
    line = 1
    i, n = 0, len(code)
    while i < n:
        c = code[i]
        if c == "\n":
            line += 1
            i += 1
        elif c.isspace():
            i += 1
        elif c.isalpha() or c == "_":
            m = IDENT_RE.match(code, i)
            yield ("ident", m.group(0), line)
            i = m.end()
        elif c.isdigit():
            m = re.compile(r"[0-9][0-9A-Za-z_.]*").match(code, i)
            yield ("lit", m.group(0), line)
            i = m.end()
        elif code.startswith("::", i):
            yield ("punct", "::", line)
            i += 2
        elif c == '"':
            j = code.find('"', i + 1)
            j = n if j < 0 else j + 1
            yield ("lit", orig[i:j] if orig[i:i + 1] == '"' else '""', line)
            line += code.count("\n", i, j)
            i = j
        else:
            yield ("punct", c, line)
            i += 1


def _attr_paths(tokens):
    """Kani attribute entries of one attribute body: [(name, args_text)]."""
    text = "".join(t[1] if t[0] != "ident" else f" {t[1]} " for t in tokens)
    compact = re.sub(r"\s+", " ", text).strip()
    squeezed = compact.replace(" ", "")
    entries = []
    if squeezed.startswith("cfg_attr("):
        inner = squeezed[len("cfg_attr("):-1] if squeezed.endswith(")") else squeezed[len("cfg_attr("):]
        parts = _split_top(inner)
        for part in parts[1:]:
            entries.extend(_kani_entry(part))
    else:
        entries.extend(_kani_entry(squeezed))
    return entries


def _split_top(s: str):
    parts, depth, cur = [], 0, []
    for ch in s:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append("".join(cur))
            cur = []
        else:
            cur.append(ch)
    if cur:
        parts.append("".join(cur))
    return parts


def _kani_entry(s: str):
    m = re.match(r"^kani::([A-Za-z_]+)(?:\((.*)\))?$", s)
    if not m:
        return []
    return [(m.group(1), m.group(2))]


def scan(src: str) -> dict:
    """Return {"harnesses": [...], "mod_decls": [(name, path_attr, scope)]}."""
    toks = list(_tokens(strip_code(src), src))
    harnesses, mod_decls = [], []
    scopes = []          # stack of (segment|None, depth_at_open, is_macro)
    depth = 0
    pending = []         # kani attribute entries awaiting an item
    pending_path = None  # #[path = "..."] for the next `mod x;`
    pending_line = None
    pending_fn = None    # segment to push when the next `{` opens a fn body
    pending_scope = None
    pending_cfgs = []    # #[cfg(..)] predicates awaiting an item
    file_cfgs = []       # #![cfg(..)] at the top of the file
    i, n = 0, len(toks)
    raw = strip_code(src)

    def in_macro():
        return any(s[2] for s in scopes)

    def path_prefix():
        return [s[0] for s in scopes if s[0]]

    def scope_cfgs():
        out = list(file_cfgs)
        for sc in scopes:
            out.extend(sc[3])
        return out

    while i < n:
        kind, text, line = toks[i]
        if text == "#" and i + 1 < n and toks[i + 1][1] in ("[", "!"):
            inner = toks[i + 1][1] == "!"
            j = i + (2 if not inner else 3)
            if inner and (j - 1 >= n or toks[j - 1][1] != "["):
                i += 1
                continue
            d, k = 1, j
            while k < n and d:
                if toks[k][1] == "[":
                    d += 1
                elif toks[k][1] == "]":
                    d -= 1
                k += 1
            body = toks[j:k - 1]
            if body and body[0][1] == "cfg" and len(body) > 1 and body[1][1] == "(":
                pred = _join_tokens(body[2:-1])
                if inner and depth == 0:
                    file_cfgs.append(pred)
                elif not inner:
                    pending_cfgs.append(pred)
            if not inner:
                entries = _attr_paths(body)
                if entries:
                    pending.extend(entries)
                    pending_line = pending_line or line
                if body and body[0][1] == "path":
                    m = re.search(r'#\s*\[\s*path\s*=\s*"([^"]*)"', src.split("\n")[line - 1])
                    pending_path = m.group(1) if m else ""
            i = k
            continue
        if kind == "ident" and text == "macro_rules" and i + 1 < n and toks[i + 1][1] == "!":
            pending_scope = (None, True, [])
            i += 2
            continue
        if kind == "ident" and text in ("mod", "fn", "impl", "trait", "struct", "enum", "union",
                                         "const", "static") :
            nxt = toks[i + 1] if i + 1 < n else ("", "", line)
            if text in ("const", "static") and nxt[1] in ("fn", "unsafe", "async", "extern"):
                i += 1
                continue
            kani = [e for e in pending if e[0] in HARNESS_KINDS]
            if text == "mod" and nxt[0] == "ident":
                after = toks[i + 2][1] if i + 2 < n else ""
                if after == ";":
                    mod_decls.append({"name": nxt[1], "path_attr": pending_path,
                                      "scope": path_prefix(), "cfgs": scope_cfgs() + pending_cfgs})
                elif after == "{":
                    pending_scope = (nxt[1], False, list(pending_cfgs))
                pending, pending_path, pending_line, pending_cfgs = [], None, None, []
                i += 2
                continue
            if text == "fn" and nxt[0] == "ident":
                if kani:
                    h = _harness(nxt[1], path_prefix(), pending, pending_line or line, "fn", in_macro())
                    h["cfgs"] = scope_cfgs() + pending_cfgs
                    harnesses.append(h)
                pending_fn = (nxt[1], list(pending_cfgs))
                pending, pending_path, pending_line, pending_cfgs = [], None, None, []
                i += 2
                continue
            if text == "fn" and nxt[1] == "$" and in_macro():
                name = "$" + (toks[i + 2][1] if i + 2 < n else "")
                if kani:
                    h = _harness(name, path_prefix(), pending, pending_line or line, "fn", True)
                    h["cfgs"] = scope_cfgs() + pending_cfgs
                    harnesses.append(h)
                pending, pending_path, pending_line, pending_cfgs = [], None, None, []
                i += 3
                continue
            if text in ("impl", "trait"):
                # collect header tokens until `{` or `;`
                k = i + 1
                header = []
                while k < n and toks[k][1] not in ("{", ";"):
                    header.append(toks[k][1])
                    k += 1
                seg = _impl_segment(text, header)
                if kani:
                    h = _harness(seg or text, path_prefix(), pending, pending_line or line, text, in_macro())
                    h["cfgs"] = scope_cfgs() + pending_cfgs
                    harnesses.append(h)
                pending_scope = (seg, False, list(pending_cfgs))
                pending, pending_path, pending_line, pending_cfgs = [], None, None, []
                i = k
                continue
            if kani:
                name = nxt[1] if nxt[0] == "ident" else text
                h = _harness(name, path_prefix(), pending, pending_line or line, text, in_macro())
                h["cfgs"] = scope_cfgs() + pending_cfgs
                harnesses.append(h)
            pending, pending_path, pending_line, pending_cfgs = [], None, None, []
            i += 1
            continue
        if text == "{":
            depth += 1
            if pending_scope is not None:
                scopes.append((pending_scope[0], depth, pending_scope[1], pending_scope[2]))
                pending_scope = None
            elif pending_fn is not None:
                scopes.append((pending_fn[0], depth, False, pending_fn[1]))
            else:
                scopes.append((None, depth, False, []))
            pending_fn = None
        elif text == "}":
            if scopes and scopes[-1][1] == depth:
                scopes.pop()
            depth = max(0, depth - 1)
        elif text == ";":
            pending_fn = None
            if pending_scope is not None and not pending_scope[1]:
                pending_scope = None
        elif text in ("(", "[") and pending_scope is not None and pending_scope[1]:
            # macro_rules! name ( ... ) / [ ... ]: treat as a macro scope too
            pass
        i += 1
    del raw
    return {"harnesses": harnesses, "mod_decls": mod_decls, "file_cfgs": file_cfgs}


def _join_tokens(tokens) -> str:
    out = []
    for kind, text, _ in tokens:
        if out and kind in ("ident", "lit") and out[-1][0] in ("ident", "lit"):
            out.append(("sp", " "))
        out.append((kind, text))
    return "".join(t for _, t in out)


def _impl_segment(kind: str, header: list) -> str | None:
    words = [w for w in header if w not in ("unsafe",)]
    text = " ".join(words)
    text = re.sub(r"^<[^>]*>\s*", "", text) if kind == "impl" else text
    if kind == "trait":
        return words[0] if words else None
    if " for " in f" {text} ":
        trait, _, ty = text.partition(" for ")
        ty = ty.split(" where ")[0]
        return f"<{_squash(ty)} as {_squash(trait)}>"
    return _squash(text.split(" where ")[0])


def _squash(s: str) -> str:
    s = re.sub(r"\s*::\s*", "::", s.strip())
    s = re.sub(r"\s*([<>,&()\[\]])\s*", r"\1", s)
    return s.replace(",", ", ")


def _harness(name, prefix, entries, line, item_kind, macro):
    kinds = [e for e in entries if e[0] in HARNESS_KINDS]
    kind = "proof_for_contract" if any(e[0] == "proof_for_contract" for e in kinds) else "proof"
    target = next((e[1] for e in kinds if e[0] == "proof_for_contract"), None)
    unwind = next((e[1] for e in entries if e[0] == "unwind"), None)
    solver = next((e[1] for e in entries if e[0] == "solver"), None)
    stubs = sorted(e[1] or "" for e in entries if e[0] == "stub")
    stub_verified = sorted(e[1] or "" for e in entries if e[0] == "stub_verified")
    segs = [p for p in prefix]
    pretty = "::".join(segs + [name])
    return {
        "name": name,
        "pretty_name": pretty,
        "line": line,
        "kind": kind,
        "contract_target": target,
        "should_panic": any(e[0] == "should_panic" for e in entries),
        "unwind": unwind,
        "solver": solver,
        "stubs": stubs,
        "stub_verified": stub_verified,
        "item_kind": item_kind,
        "macro_template": bool(macro),
        "attribute_count": len(kinds),
    }


# ---------------------------------------------------------------- cfg predicates
_CFG_TOKEN = re.compile(r'\s*(?:(?P<ident>[A-Za-z_][A-Za-z0-9_]*)|(?P<str>"(?:[^"\\]|\\.)*")|(?P<punct>[(),=]))')
# Identifiers Kani's build sets (cfg(kani) via kani-compiler; debug build; the
# unix CI hosts). `test` is set only for `cargo kani --tests`.
TRUE_IDENTS = {"kani", "debug_assertions", "unix", "panic_unwind"}
FALSE_KEY_VALUES = {("target_arch", "wasm32"), ("target_family", "wasm"), ("target_family", "windows"),
                    ("target_os", "windows")}


def cfg_active(pred: str, features=None, tests: bool = False, extra_true=()):
    """Evaluate a cfg predicate. `features=None` means unknown (treated as set).

    Unknown bare identifiers (cfg(disabled), cfg(loom)) are unset, as cargo
    never sets them; unknown key/value pairs other than the listed non-unix
    targets are treated as satisfied so the scan never drops a harness on a
    platform guess.
    """
    toks = []
    pos = 0
    while pos < len(pred):
        m = _CFG_TOKEN.match(pred, pos)
        if not m or m.end() == pos:
            return True
        pos = m.end()
        if m.group("ident"):
            toks.append(("i", m.group("ident")))
        elif m.group("str"):
            toks.append(("s", m.group("str")[1:-1]))
        elif m.group("punct"):
            toks.append(("p", m.group("punct")))
    idx = 0

    def parse():
        nonlocal idx
        if idx >= len(toks) or toks[idx][0] != "i":
            raise ValueError
        name = toks[idx][1]
        idx += 1
        if name in ("all", "any", "not") and idx < len(toks) and toks[idx] == ("p", "("):
            idx += 1
            vals = []
            while idx < len(toks) and toks[idx] != ("p", ")"):
                vals.append(parse())
                if idx < len(toks) and toks[idx] == ("p", ","):
                    idx += 1
            idx += 1
            if name == "all":
                return all(vals)
            if name == "any":
                return any(vals)
            return not vals[0] if vals else True
        if idx < len(toks) and toks[idx] == ("p", "="):
            idx += 1
            value = toks[idx][1] if idx < len(toks) else ""
            idx += 1
            if name == "feature":
                return True if features is None else value in features
            return (name, value) not in FALSE_KEY_VALUES
        if name == "test":
            return tests
        return name in TRUE_IDENTS or name in extra_true

    try:
        return bool(parse())
    except (ValueError, IndexError):
        return True
