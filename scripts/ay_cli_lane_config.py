#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Derive the cargo config for trust-mc's UNVERIFIED ay-CLI lane from ay's own.

scripts/build-pinned-ay-cli.sh builds the external `ay` CLI with
`targo --unverified`: a working binary, no proof claim. ay's repository
`.cargo/config.toml` states ay's OWN verification posture on every unit
(`[host] rustflags`, `[target.'cfg(all())'] rustflags`, per-profile package
rustflags, per-triple rustflags) with `-Ztrust-*` options: at ay 501caafdf
`-Ztrust-verify=off` on host and dependency units and `-Ztrust-policy=advisory`
on the triple; at 4cadc2bf1 `-Ztrust-verify=on -Ztrust-policy=certify
-Ztrust-ir-lower=strict ...` everywhere. `targo --unverified` lifts the
verification claim and forwards the rest, and on seal 8590
`-Ztrust-ir-lower=strict` fails libc's and proc-macro2's build scripts
("the direct trust-ir producer could not fully lower this body"), so the CLI
could not be built at the pin. A `--config` override cannot clear those arrays
(cargo concatenates array values across config sources), so the lane runs
cargo from a directory of its own whose `.cargo/config.toml` is this derived
copy, with `--manifest-path` naming ay's manifest; cargo discovers config from
the working directory, never from the manifest, so ay's file is not read.

The derivation removes every `-Ztrust-*` token (and the `-Z trust-*` two-token
spelling) from every `rustflags` / `rustdocflags` array, wherever the array
sits, and changes nothing else: profiles (lto), `target-cpu=native`, `[env]`
and `[unstable]` stay as ay states them, so the binary is ay's release build
minus the posture. Two kinds of value are config-relative in cargo and would
otherwise be resolved against the LANE directory instead of ay's worktree:
`[env] KEY = { value = "...", relative = true }` (relative to the parent of the
`.cargo` directory) and a `[target.<triple>] linker` naming a path with a
separator (the same base). Both are rewritten to absolute paths under the
source tree: the env entry becomes a plain string, the linker an absolute
path. Nothing else moves. The output is validated: it must parse, and it
must equal the input document with exactly those edits applied (checked on
the parsed trees, so a rewrite that touched anything else fails closed).

usage: ay_cli_lane_config.py <ay worktree>/.cargo/config.toml <output config.toml>
The input must be a `.cargo/config.toml`: its grandparent is the source tree
config-relative paths resolve against.
exit 0 written; 2 on a malformed input, an input that is not a
`.cargo/config.toml`, an array or inline table this tool cannot rewrite
textually, or a derived file that does not parse to the expected tree.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import Any

if sys.version_info >= (3, 11):
    from tomllib import TOMLDecodeError, loads as toml_loads
else:
    from tomli import TOMLDecodeError, loads as toml_loads

FLAG_KEYS = ("rustflags", "rustdocflags")
# `rustflags = [ ... ]`, the array possibly spanning lines; arrays of strings only.
ARRAY = re.compile(
    r"^(?P<lead>[ \t]*(?:rustflags|rustdocflags)[ \t]*=[ \t]*)\[(?P<body>[^\]]*)\]",
    re.MULTILINE,
)
STRING = re.compile(r'"(?:[^"\\]|\\.)*"|\'[^\']*\'')
# `KEY = { value = "<path>", relative = true }` in either key order (cargo's [env] relative form).
ENV_RELATIVE = re.compile(
    r"^(?P<lead>[ \t]*[A-Za-z0-9_\-]+[ \t]*=[ \t]*)\{[ \t]*"
    r"(?:value[ \t]*=[ \t]*(?P<v1>\"(?:[^\"\\\\]|\\\\.)*\"|'[^']*')[ \t]*,[ \t]*relative[ \t]*=[ \t]*true"
    r"|relative[ \t]*=[ \t]*true[ \t]*,[ \t]*value[ \t]*=[ \t]*(?P<v2>\"(?:[^\"\\\\]|\\\\.)*\"|'[^']*'))"
    r"[ \t]*,?[ \t]*\}",
    re.MULTILINE,
)
# `linker = "<path>"` (one string literal on the line).
LINKER = re.compile(
    r"^(?P<lead>[ \t]*linker[ \t]*=[ \t]*)(?P<lit>\"(?:[^\"\\\\]|\\\\.)*\"|'[^']*')[ \t]*$", re.MULTILINE
)


def fail(message: str) -> None:
    print(f"ay-cli-lane-config: error: {message}", file=sys.stderr)
    raise SystemExit(2)


def is_posture(token: str) -> bool:
    return token.startswith("-Ztrust-") or token.startswith("-Ztrust_")


def source_root(config: Path) -> Path:
    """The tree a `.cargo/config.toml`'s config-relative paths resolve against."""
    resolved = config.resolve()
    if resolved.parent.name != ".cargo" or resolved.name != "config.toml":
        fail(f"input must be a <tree>/.cargo/config.toml, not {config}")
    return resolved.parent.parent


def is_config_relative_linker(value: str) -> bool:
    """cargo resolves a linker with a path separator relative to the config's tree."""
    return ("/" in value or "\\" in value) and not Path(value).is_absolute()


def absolute_under(root: Path, value: str) -> str:
    return str(root / value) if not Path(value).is_absolute() else value


def toml_string(value: str) -> str:
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def filter_tokens(tokens: list[str]) -> list[str]:
    """Drop `-Ztrust-*` and the two-token `-Z trust-*` spelling."""
    out: list[str] = []
    skip_next = False
    for token in tokens:
        if skip_next:
            skip_next = False
            continue
        if is_posture(token):
            continue
        if token == "-Z":
            out.append(token)
            continue
        out.append(token)
    # Second pass for `-Z`, `trust-...` pairs.
    result: list[str] = []
    i = 0
    while i < len(out):
        if out[i] == "-Z" and i + 1 < len(out) and (
            out[i + 1].startswith("trust-") or out[i + 1].startswith("trust_")
        ):
            i += 2
            continue
        result.append(out[i])
        i += 1
    return result


def expected_tree(value: Any, root: Path, key: str | None = None) -> Any:
    if isinstance(value, dict):
        if set(value) == {"value", "relative"} and value["relative"] is True:
            if not isinstance(value["value"], str):
                fail(f"{key}: a relative [env] value must be a string")
            return absolute_under(root, value["value"])
        return {k: expected_tree(v, root, k) for k, v in value.items()}
    if isinstance(value, list) and key in FLAG_KEYS:
        if not all(isinstance(item, str) for item in value):
            fail(f"{key} is not an array of strings")
        return filter_tokens(value)
    if isinstance(value, list):
        return [expected_tree(v, root) for v in value]
    if key == "linker" and isinstance(value, str) and is_config_relative_linker(value):
        return absolute_under(root, value)
    return value


def rewrite(text: str, root: Path) -> str:
    def replace(match: re.Match[str]) -> str:
        body = match.group("body")
        literals = STRING.findall(body)
        rest = STRING.sub("", body)
        if re.sub(r"[\s,]", "", rest):
            fail(f"cannot rewrite an array that is not a list of string literals: {body.strip()!r}")
        kept = [lit for lit in literals if not is_posture(toml_loads(f"x = {lit}")["x"])]
        # `-Z`, `trust-*` pairs.
        final: list[str] = []
        i = 0
        while i < len(kept):
            value = toml_loads(f"x = {kept[i]}")["x"]
            if value == "-Z" and i + 1 < len(kept):
                following = toml_loads(f"x = {kept[i + 1]}")["x"]
                if following.startswith(("trust-", "trust_")):
                    i += 2
                    continue
            final.append(kept[i])
            i += 1
        return f"{match.group('lead')}[{', '.join(final)}]"

    def replace_env_relative(match: re.Match[str]) -> str:
        literal = match.group("v1") or match.group("v2")
        value = toml_loads(f"x = {literal}")["x"]
        return f"{match.group('lead')}{toml_string(absolute_under(root, value))}"

    def replace_linker(match: re.Match[str]) -> str:
        value = toml_loads(f"x = {match.group('lit')}")["x"]
        if not is_config_relative_linker(value):
            return match.group(0)
        return f"{match.group('lead')}{toml_string(absolute_under(root, value))}"

    text = ARRAY.sub(replace, text)
    text = ENV_RELATIVE.sub(replace_env_relative, text)
    return LINKER.sub(replace_linker, text)


def derive(text: str, root: Path) -> str:
    try:
        document = toml_loads(text)
    except TOMLDecodeError as error:
        fail(f"input is not TOML: {error}")
    expected = expected_tree(document, root)
    derived = rewrite(text, root)
    try:
        observed = toml_loads(derived)
    except TOMLDecodeError as error:
        fail(f"derived config does not parse: {error}")
    if observed != expected:
        fail(
            "derived config differs from the input with the posture tokens removed and the "
            "config-relative paths made absolute; refusing to write it"
        )
    return derived


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        print("usage: ay_cli_lane_config.py <ay .cargo/config.toml> <output config.toml>", file=sys.stderr)
        return 2
    source, target = Path(argv[1]), Path(argv[2])
    root = source_root(source)
    try:
        text = source.read_text(encoding="utf-8")
    except OSError as error:
        fail(f"cannot read {source}: {error}")
    header = (
        "# DERIVED by trust-mc scripts/ay_cli_lane_config.py for the unverified ay-CLI lane:\n"
        f"# {source}\n# with every -Ztrust-* rustflags/rustdocflags token removed and every\n"
        f"# config-relative path ([env] relative = true, a relative linker) made absolute under\n"
        f"# {root}. Do not edit.\n\n"
    )
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(header + derive(text, root), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
