# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""pins.toml loader."""
from __future__ import annotations

import re
import tomllib
from dataclasses import dataclass, field
from pathlib import Path

from . import SpecError

SHA_RE = re.compile(r"^[0-9a-f]{40}$")


@dataclass(frozen=True)
class RevPin:
    name: str
    rev: str
    nightly: str
    submodules: dict = field(default_factory=dict)


@dataclass(frozen=True)
class Pins:
    upstream: str
    revs: dict
    submodule_urls: dict

    def by_rev(self, rev: str) -> RevPin:
        for pin in self.revs.values():
            if pin.rev == rev or pin.name == rev:
                return pin
        raise SpecError(f"no pin named or matching {rev!r}")


def load_pins(path: Path) -> Pins:
    data = tomllib.loads(Path(path).read_text(encoding="utf-8"))
    if data.get("schema") != "trust-mc.kani-spec.pins/v1":
        raise SpecError(f"{path}: unexpected schema {data.get('schema')!r}")
    revs = {}
    for name, body in sorted(data.get("revs", {}).items()):
        rev = body.get("rev", "")
        if not SHA_RE.match(rev):
            raise SpecError(f"{path}: revs.{name}.rev must be a full 40-hex sha")
        subs = dict(sorted(body.get("submodules", {}).items()))
        for sub, sha in subs.items():
            if not SHA_RE.match(sha):
                raise SpecError(f"{path}: revs.{name}.submodules.{sub} must be a full sha")
        revs[name] = RevPin(name=name, rev=rev, nightly=body.get("nightly", ""), submodules=subs)
    if not revs:
        raise SpecError(f"{path}: no revs pinned")
    return Pins(upstream=data["upstream"], revs=revs,
                submodule_urls=dict(sorted(data.get("submodule_urls", {}).items())))
