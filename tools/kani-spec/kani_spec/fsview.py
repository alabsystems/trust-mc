# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Read-only view of a Kani checkout with optional overlay files.

Paths are POSIX strings relative to the checkout root ("tests/kani/foo.rs").
Symlinks are followed exactly as compiletest's `fs::read_dir` + `is_dir`
follow them. Overlays model scripts/kani-perf.sh's `cp -r overlays/<d>/*
tests/perf/<d>/` without mutating the checkout: an overlay file shadows (or
adds) the file at its virtual path.
"""
from __future__ import annotations

import hashlib
import os
from pathlib import Path


class Tree:
    def __init__(self, root: Path, overlays: dict | None = None):
        self.root = Path(root)
        # vpath -> real Path of the overlay source file
        self.overlays = dict(overlays or {})
        self._overlay_dirs: dict[str, set] = {}
        for vpath in self.overlays:
            parts = vpath.split("/")
            for i in range(1, len(parts)):
                parent = "/".join(parts[:i])
                self._overlay_dirs.setdefault(parent, set()).add(parts[i])

    def with_overlays(self, overlays: dict) -> "Tree":
        merged = dict(self.overlays)
        merged.update(overlays)
        return Tree(self.root, merged)

    def real(self, vpath: str) -> Path:
        return self.root / vpath if vpath else self.root

    def is_file(self, vpath: str) -> bool:
        return vpath in self.overlays or self.real(vpath).is_file()

    def is_dir(self, vpath: str) -> bool:
        return vpath in self._overlay_dirs or self.real(vpath).is_dir()

    def exists(self, vpath: str) -> bool:
        # Rust `Path::exists` follows symlinks: a dangling link does not exist.
        return self.is_file(vpath) or self.is_dir(vpath) or self.real(vpath).exists()

    def listdir(self, vpath: str) -> list:
        names = set()
        real = self.real(vpath)
        if real.is_dir():
            names.update(os.listdir(real))
        names.update(self._overlay_dirs.get(vpath, ()))
        return sorted(names)

    def read_bytes(self, vpath: str) -> bytes:
        if vpath in self.overlays:
            return Path(self.overlays[vpath]).read_bytes()
        return self.real(vpath).read_bytes()

    def read_text(self, vpath: str) -> str:
        # compiletest reads with `read_to_string` (strict UTF-8); every file in
        # the pinned corpora decodes, and a lossy decode keeps generation total.
        return self.read_bytes(vpath).decode("utf-8", errors="replace")

    def sha256(self, vpath: str) -> str:
        return hashlib.sha256(self.read_bytes(vpath)).hexdigest()

    def walk_files(self, vpath: str) -> list:
        """Every file under vpath (following symlinks, cycle-safe), sorted."""
        out = []
        seen = set()

        def rec(v):
            real = self.real(v)
            try:
                key = real.resolve()
            except OSError:
                key = real
            if key in seen and v not in self._overlay_dirs:
                return
            seen.add(key)
            for name in self.listdir(v):
                child = f"{v}/{name}" if v else name
                if self.is_dir(child):
                    rec(child)
                elif self.is_file(child):
                    out.append(child)

        if self.is_dir(vpath):
            rec(vpath)
        return sorted(out)
