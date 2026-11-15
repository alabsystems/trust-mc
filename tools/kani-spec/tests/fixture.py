# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""A miniature Kani checkout exercising every collection rule."""
from __future__ import annotations

import os
import subprocess
import sys
import tempfile
from pathlib import Path

TOOL_DIR = Path(__file__).resolve().parents[1]
if str(TOOL_DIR) not in sys.path:
    sys.path.insert(0, str(TOOL_DIR))

REGRESSION = """#!/usr/bin/env bash
cargo run -p compiletest --quiet -- --suite kani --mode cargo-kani --dry-run --verbose
TESTS=(
    "kani kani"
    "expected expected"
    "cargo-kani cargo-kani"
    "script-based-pre exec"
    "kani-fixme kani-fixme"
)
for testp in "${TESTS[@]}"; do
  cargo run -p compiletest --quiet -- --suite $suite --mode $mode
done
cargo kani --manifest-path "$FEATURES_MANIFEST_PATH" --harness trivial_success
cargo test -p kani_macros --features syn/extra-traits --lib
codegen-firecracker.sh
"""
PERF = """#!/usr/bin/env bash
for overlay_dir in ${PERF_DIR}/overlays/*/; do
  cp -r -v ${overlay_dir}* ${PERF_DIR}/${orig_dir}/
done
suite="perf"
mode="cargo-kani-test"
cargo run -p compiletest -- --suite $suite --mode $mode --no-fail-fast
"""
FILES = {
    "rust-toolchain.toml": '[toolchain]\nchannel = "nightly-2099-01-01"\n',
    "Cargo.toml": '[workspace.package]\nversion = "0.99.0"\n',
    "scripts/kani-regression.sh": REGRESSION,
    "scripts/kani-perf.sh": PERF,
    ".github/workflows/verify-std-check.yml": "run: kani verify-std ./library\n",
    ".github/workflows/bench-e2e.yml": "run: benchcomp\n",
    ".github/workflows/kani.yml": "run: test/run\n",
    ".github/workflows/cbmc-latest.yml": "run: compiletest --suite perf --mode cargo-kani-test ignore --ignored\n",
    # kani mode
    "tests/kani/Arith/add.rs": "// kani-flags: --default-unwind 3\n#[kani::proof]\nfn check_add() { assert!(1 + 1 == 2); }\n",
    "tests/kani/Arith/fail.rs": "// kani-verify-fail\n#[kani::proof]\nfn check_fail() { assert!(false); }\n",
    "tests/kani/Arith/reject.rs": "// kani-check-fail\n#[kani::proof]\nfn check_reject() { undefined(); }\n",
    "tests/kani/Arith/.hidden.rs": "#[kani::proof]\nfn hidden() {}\n",
    "tests/kani/Arith/#temp.rs": "#[kani::proof]\nfn temp() {}\n",
    "tests/kani/Arith/notes.txt": "not a test\n",
    "tests/kani/Arith/auxiliary/helper.rs": "#[kani::proof]\nfn aux() {}\n",
    "tests/kani/Gaps/fixme_loop.rs": "#[kani::proof]\nfn gap() { assert!(1 == 2); }\n",
    "tests/kani/Gaps/ignore_me.rs": "#[kani::proof]\nfn skipped() {}\n",
    "tests/kani/fixme_dir/main.rs": "#[kani::proof]\nfn in_fixme_dir() {}\n",
    # expected mode
    "tests/expected/multi/a.rs": "#[kani::proof]\nfn a() {}\n",
    "tests/expected/multi/b.rs": "#[kani::proof]\n#[kani::should_panic]\nfn b() { panic!() }\n",
    "tests/expected/multi/b.expected": "VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)\n",
    "tests/expected/multi/expected": "Status: SUCCESS\\\nDescription: \"assertion failed: x\"\n\nVERIFICATION:- SUCCESSFUL\n",
    "tests/expected/nofile/main.rs": "#[kani::proof]\nfn no_expected() {}\n",
    # cargo-kani mode
    "tests/cargo-kani/pkg/Cargo.toml": '[package]\nname = "pkg"\nversion = "0.1.0"\n\n[package.metadata.kani.flags]\ndefault-unwind = "2"\n',
    "tests/cargo-kani/pkg/src/lib.rs": "mod inner;\n#[kani::proof]\nfn top() {}\n",
    "tests/cargo-kani/pkg/src/inner.rs": "#[cfg_attr(kani, kani::proof)]\nfn nested_check() {}\n#[kani::proof]\nfn other() {}\n#[cfg(disabled)]\n#[kani::proof]\nfn off() {}\n",
    "tests/cargo-kani/pkg/nested_check.expected": "Checking harness inner::nested_check...\nVERIFICATION:- SUCCESSFUL\n",
    "tests/cargo-kani/pkg/expected": "Complete - 3 successfully verified harnesses, 0 failures, 3 total.\n",
    "tests/cargo-kani/pkg/src/stray.expected": "not collected: src has no Cargo.toml\n",
    "tests/cargo-kani/loose/orphan.expected": "not collected: no Cargo.toml\n",
    # exec mode
    "tests/script-based-pre/playback/config.yml": "# comment\nscript: run.sh\nexpected: run.expected\nexit_code: 1\n",
    "tests/script-based-pre/playback/run.sh": "#!/bin/sh\nkani test.rs --concrete-playback=print\n",
    "tests/script-based-pre/playback/run.expected": "VERIFICATION:- FAILED\n",
    "tests/script-based-pre/playback/test.rs": "#[kani::proof]\nfn play() { assert!(false); }\n",
    "tests/script-based-pre/minimal/config.yml": "script: go.sh\n",
    "tests/script-based-pre/minimal/go.sh": "#!/bin/sh\ncargo kani\n",
    # perf with an overlay onto a Cargo package that ships no expected file
    "tests/cargo-kani/ws/Cargo.toml": '[package]\nname = "top"\nversion = "0.1.0"\n[workspace]\nmembers = ["a", "b"]\n[workspace.metadata.kani.flags]\npackage = ["a"]\n',
    "tests/cargo-kani/ws/src/lib.rs": "#[kani::proof]\nfn in_top() {}\n",
    "tests/cargo-kani/ws/a/Cargo.toml": '[package]\nname = "a"\nversion = "0.1.0"\n[features]\ndefault = ["x"]\nx = []\n',
    "tests/cargo-kani/ws/a/src/lib.rs": "#![cfg(feature = \"x\")]\n#[kani::proof]\nfn in_a() {}\n#[cfg(test)]\n#[kani::proof]\nfn only_tests() {}\n",
    "tests/cargo-kani/ws/b/Cargo.toml": '[package]\nname = "b"\nversion = "0.1.0"\n',
    "tests/cargo-kani/ws/b/src/lib.rs": "#[kani::proof]\nfn in_b() {}\n",
    "tests/cargo-kani/ws/expected": "Complete - 1 successfully verified harnesses, 0 failures, 1 total.\n",
    "tests/perf/lib/Cargo.toml": '[package]\nname = "lib"\nversion = "0.1.0"\n',
    "tests/perf/lib/src/lib.rs": "#[kani::proof]\nfn perf_check() {}\n",
    "tests/perf/overlays/lib/expected": "VERIFICATION:- SUCCESSFUL\n",
}


def git(args, cwd):
    env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@t", GIT_COMMITTER_NAME="t",
               GIT_COMMITTER_EMAIL="t@t", GIT_AUTHOR_DATE="2026-01-01T00:00:00Z",
               GIT_COMMITTER_DATE="2026-01-01T00:00:00Z")
    return subprocess.run(["git", *args], cwd=cwd, env=env, check=True, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout.strip()


def make_repo(root: Path, extra: dict | None = None) -> str:
    root.mkdir(parents=True, exist_ok=True)
    files = dict(FILES)
    files.update(extra or {})
    for rel, content in files.items():
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")
    (root / "tests" / "kani-fixme").symlink_to("kani")
    git(["init", "--quiet", "."], root)
    git(["add", "-A", "-f"], root)
    git(["commit", "--quiet", "-m", "fixture"], root)
    return git(["rev-parse", "HEAD"], root)


def write_pins(path: Path, rev: str) -> None:
    path.write_text(
        'schema = "trust-mc.kani-spec.pins/v1"\n'
        'upstream = "https://invalid.example/kani"\n'
        f'[revs.fixture]\nrev = "{rev}"\nnightly = "nightly-2099-01-01"\n',
        encoding="utf-8")


OVERLAY = 'schema = "trust-mc.kani-spec.overlay/v1"\n'


class Workspace:
    """Temp cache + fixture checkout + spec dir, cleaned up on exit."""

    def __enter__(self):
        self._tmp = tempfile.TemporaryDirectory(prefix="kani-spec-test-")
        base = Path(self._tmp.name)
        self.cache = base / "cache"
        self.scratch = base / "scratch"
        self.scratch.mkdir()
        repo = self.scratch / "src"
        self.rev = make_repo(repo)
        self.checkout = self.cache / self.rev
        self.cache.mkdir()
        repo.rename(self.checkout)
        self.pins = base / "pins.toml"
        write_pins(self.pins, self.rev)
        self.spec = base / "spec"
        self.spec.mkdir()
        (self.spec / "overlay.toml").write_text(OVERLAY, encoding="utf-8")
        self._old_env = os.environ.get("KANI_SPEC_CACHE")
        os.environ["KANI_SPEC_CACHE"] = str(self.cache)
        return self

    def __exit__(self, *exc):
        if self._old_env is None:
            os.environ.pop("KANI_SPEC_CACHE", None)
        else:
            os.environ["KANI_SPEC_CACHE"] = self._old_env
        self._tmp.cleanup()
