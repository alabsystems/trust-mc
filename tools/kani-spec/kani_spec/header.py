# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Mirror of Kani tools/compiletest/src/header.rs.

Only the behaviour that decides collection and oracles is reproduced:
`iter_header` (directives end at the first line starting with `fn` or `mod`;
the comment prefix is `//` for `.rs` files and `#` for anything else),
`parse_name_directive` (whole-word match), `parse_name_value_directive`
(`name:` prefix), and `make_test_description`'s fixme/ignore and kani-fixme
rules.
"""
from __future__ import annotations

FAIL_STEPS = (("kani-check-fail", "check"), ("kani-codegen-fail", "codegen"),
              ("kani-verify-fail", "verify"))


def iter_header(text: str, is_rs: bool):
    comment = "//" if is_rs else "#"
    # Rust `read_line` splits on '\n' only; `trim` strips surrounding whitespace.
    for raw in text.split("\n"):
        ln = raw.strip()
        if ln.startswith("fn") or ln.startswith("mod"):
            return
        if ln.startswith(comment):
            yield ln[len(comment):].lstrip()


def name_directive(line: str, directive: str) -> bool:
    if not line.startswith(directive):
        return False
    nxt = line[len(directive):len(directive) + 1]
    return nxt in ("", " ", ":")


def name_value_directive(line: str, directive: str):
    if line.startswith(directive) and line[len(directive):len(directive) + 1] == ":":
        return line[len(directive) + 1:]
    return None


def parse_props(text: str | None, is_rs: bool) -> dict:
    """TestProps::load_from. `text is None` models a directory test file."""
    props = {"compile_flags": [], "kani_flags": [], "cbmc_flags": [], "edition": None,
             "kani_fail_step": None, "should_fail_directive": False,
             "multiple_fail_steps": False}
    if text is None:
        return props
    for ln in iter_header(text, is_rs):
        for key, field in (("compile-flags", "compile_flags"), ("kani-flags", "kani_flags"),
                           ("cbmc-flags", "cbmc_flags")):
            value = name_value_directive(ln, key)
            if value is not None:
                props[field].extend(value.split())
        edition = name_value_directive(ln, "edition")
        if edition is not None:
            props["edition"] = edition.strip()
            props["compile_flags"].append(f"--edition={edition}")
        for directive, step in FAIL_STEPS:
            if name_directive(ln, directive):
                if props["kani_fail_step"] is not None:
                    props["multiple_fail_steps"] = True
                else:
                    props["kani_fail_step"] = step
                break
        if name_directive(ln, "should-fail"):
            props["should_fail_directive"] = True
    return props


def test_description(test_path: str, mode: str, props: dict) -> dict:
    """make_test_description: ignore flag, ignore message, should_panic.

    `test_path` is the checkout-relative path compiletest would see under
    `tests/<suite>/...`. Upstream applies the substring rule to the absolute
    path; a checkout directory whose own path contains "fixme" or "ignore"
    would ignore every test upstream, which is a location artefact the spec
    deliberately does not reproduce.
    """
    if "fixme" in test_path:
        ignore, message = True, "fixme test"
    elif "ignore" in test_path:
        ignore, message = True, "ignore test"
    else:
        ignore, message = False, None
    should_fail = False
    if mode == "kani-fixme":
        base = test_path.rsplit("/", 1)[-1]
        if "fixme" in base:
            ignore, message = False, None
        elif "ignore" in base:
            ignore, message = True, "ignore test"
        else:
            ignore, message = True, "regular test"
        should_fail = True
    should_fail = should_fail or props.get("should_fail_directive", False)
    return {"ignore": ignore, "ignore_message": message, "should_panic": should_fail}
